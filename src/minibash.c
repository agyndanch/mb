/*
 * minibash - an open-ended subset of bash
 *
 * Developed by Godmar Back for CS 3214 Fall 2025 
 * Virginia Tech.
 *
 * Extended by seany24 for CS 3214 Spring 2026
 */
#define _GNU_SOURCE    1
#include <stdio.h>
#include <readline/readline.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <termios.h>
#include <sys/wait.h>
#include <assert.h>
#include <spawn.h>
#include <errno.h>
#include <stdbool.h>

#include <tree_sitter/api.h>
#include "tree_sitter/tree-sitter-bash.h"
#include "ts_symbols.h"
/* Since the handed out code contains a number of unused functions. */
#pragma GCC diagnostic ignored "-Wunused-function"

#include "hashtable.h"
#include "signal_support.h"
#include "utils.h"
#include "list.h"
#include "ts_helpers.h"

/*
 * Parse redirect nodes attached to a redirected_statement.
 * Sets up file actions by opening files or wiring pipe fds.
 * Returns {stdin_fd, stdout_fd, stderr_fd} as overrides, -1 = no override.
 * opened_fds: caller-allocated array of fds to close after spawning.
 * *n_opened: number of fds filled in opened_fds.
 */
typedef struct {
    int stdin_fd;
    int stdout_fd;
    int stderr_fd;
} RedirectFDs;

extern char **environ;

/* These are field ids suitable for use in ts_node_child_by_field_id for certain rules. */
static TSFieldId bodyId, redirectId, destinationId, valueId, nameId, conditionId;
static TSFieldId variableId;
static TSFieldId leftId, operatorId, rightId;

static char *input;         // to avoid passing the current input around
static TSParser *parser;    // a singleton parser instance 
static tommy_hashdyn shell_vars;        // a hash table containing the internal shell variables

/* Last exit status, stored as integer and as string in shell_vars["?"] */
static int last_exit_status = 0;

/* Break flag for loop control */
static bool break_flag = false;

static void handle_child_status(pid_t pid, int status);
static char *read_script_from_fd(int readfd);
static void execute_script(char *script);
static void run_statement(TSNode node);

/* forward declaration for word expansion */
static char *expand_word(TSNode node);
static void run_pipeline(TSNode node, bool background);
static void run_redirected_statement(TSNode node, bool background);
static RedirectFDs parse_redirects(TSNode redir_stmt, int *opened_fds, int *n_opened);

static void
usage(char *progname)
{
    printf("Usage: %s -h\n"
        " -h            print this help\n",
        progname);

    exit(EXIT_SUCCESS);
}

/* Build a prompt */
static char *
build_prompt(void)
{
    return strdup("minibash> ");
}

/* Possible job status's to use. */
enum job_status {
    FOREGROUND,
    BACKGROUND,
    STOPPED,
    NEEDSTERMINAL,
    TERMINATED_VIA_EXIT,
    TERMINATED_VIA_SIGNAL
};

struct job {
    struct list_elem elem;
    int     jid;
    enum job_status status;
    int  num_processes_alive;

    pid_t pgid;
    int   exit_status;

    pid_t *pids;
    int    npids;
};

#define MAXJOBS (1<<16)
static struct list job_list;

static struct job *jid2job[MAXJOBS];

static struct job *
get_job_from_jid(int jid)
{
    if (jid > 0 && jid < MAXJOBS && jid2job[jid] != NULL)
        return jid2job[jid];

    return NULL;
}

static struct job *
allocate_job(bool includeinjoblist)
{
    struct job *job = calloc(1, sizeof *job);
    job->jid = -1;
    if (!includeinjoblist)
        return job;

    list_push_back(&job_list, &job->elem);
    for (int i = 1; i < MAXJOBS; i++) {
        if (jid2job[i] == NULL) {
            jid2job[i] = job;
            job->jid = i;
            return job;
        }
    }
    fprintf(stderr, "Maximum number of jobs exceeded\n");
    abort();
    return NULL;
}

static void
delete_job(struct job *job, bool removeFromJobList)
{
    if (removeFromJobList) {
        int jid = job->jid;
        assert(jid != -1);
        assert(jid2job[jid] == job);
        list_remove(&job->elem);
        jid2job[jid]->jid = -1;
        jid2job[jid] = NULL;
    } else {
        assert(job->jid == -1);
    }
    free(job->pids);
    free(job);
}

static struct job *
find_job_by_pid(pid_t pid)
{
    for (struct list_elem *e = list_begin(&job_list);
         e != list_end(&job_list);
         e = list_next(e))
    {
        struct job *j = list_entry(e, struct job, elem);
        for (int i = 0; i < j->npids; i++) {
            if (j->pids[i] == pid)
                return j;
        }
    }
    return NULL;
}

static void
update_exit_status(int status)
{
    last_exit_status = status;
    char buf[32];
    snprintf(buf, sizeof(buf), "%d", status);
    hash_put(&shell_vars, "?", buf);
}

static void
sigchld_handler(int sig, siginfo_t *info, void *_ctxt)
{
    pid_t child;
    int status;

    assert(sig == SIGCHLD);

    while ((child = waitpid(-1, &status, WUNTRACED|WNOHANG)) > 0) {
        handle_child_status(child, status);
    }
}

static void
wait_for_job(struct job *job)
{
    assert(signal_is_blocked(SIGCHLD));

    while (job->status == FOREGROUND && job->num_processes_alive > 0) {
        int status;

        pid_t child = waitpid(-1, &status, WUNTRACED);

        if (child != -1)
            handle_child_status(child, status);
        else
            utils_fatal_error("waitpid failed, see code for explanation");
    }
}

static void
handle_child_status(pid_t pid, int status)
{
    assert(signal_is_blocked(SIGCHLD));

    struct job *job = find_job_by_pid(pid);
    if (job == NULL)
        return;

    if (WIFEXITED(status)) {
        job->exit_status = WEXITSTATUS(status);
        job->num_processes_alive--;
        if (job->num_processes_alive == 0) {
            bool was_fg = job->status == FOREGROUND;
            job->status = TERMINATED_VIA_EXIT;
            if (was_fg)
                update_exit_status(job->exit_status);
        }
    } else if (WIFSIGNALED(status)) {
        job->exit_status = 128 + WTERMSIG(status);
        job->num_processes_alive--;
        if (job->num_processes_alive == 0) {
            bool was_fg = job->status == FOREGROUND;
            job->status = TERMINATED_VIA_SIGNAL;
            if (was_fg)
                update_exit_status(job->exit_status);
        }
    } else if (WIFSTOPPED(status)) {
        job->status = STOPPED;
    }
}

/*
 * Reap any completed (non-foreground) jobs from the job list.
 */
static void
reap_finished_jobs(void)
{
    for (struct list_elem *e = list_begin(&job_list); e != list_end(&job_list); ) {
        struct list_elem *next_e = list_next(e);
        struct job *j = list_entry(e, struct job, elem);
        if (j->status != FOREGROUND && j->status != BACKGROUND &&
            j->num_processes_alive == 0)
            delete_job(j, true);
        e = next_e;
    }
}

/*
 * Perform command substitution: run `script` and capture its stdout.
 * Returns a newly allocated string (trailing newlines stripped).
 * Must be called with SIGCHLD blocked (the normal state inside run_*).
 */
static char *
command_substitution(const char *script)
{
    int pipefd[2];
    if (pipe(pipefd) != 0) {
        utils_error("pipe failed");
        return strdup("");
    }

    pid_t pid = fork();
    if (pid == 0) {
        /* child: unblock SIGCHLD, set up pipe, run script */
        signal_unblock(SIGCHLD);
        if (close(pipefd[0]) != 0)
            utils_fatal_error("close failed");
        if (dup2(pipefd[1], STDOUT_FILENO) == -1)
            utils_fatal_error("dup2 failed");
        if (close(pipefd[1]) != 0)
            utils_fatal_error("close failed");

        char *script_copy = strdup(script);
        execute_script(script_copy);
        free(script_copy);
        exit(last_exit_status);
    }

    /* parent */
    if (close(pipefd[1]) != 0)
        utils_error("close failed");

    /* Read output */
    size_t cap = 256, len = 0;
    char *buf = malloc(cap);
    ssize_t n;
    while ((n = read(pipefd[0], buf + len, cap - len - 1)) > 0) {
        len += (size_t)n;
        if (len + 1 >= cap) {
            cap *= 2;
            buf = realloc(buf, cap);
        }
    }
    buf[len] = '\0';
    if (close(pipefd[0]) != 0)
        utils_error("close failed");

    /* Wait for child directly (SIGCHLD is blocked, so no handler race) */
    int status;
    if (waitpid(pid, &status, 0) == -1)
        utils_error("waitpid failed");

    /* Strip trailing newlines */
    while (len > 0 && buf[len - 1] == '\n')
        buf[--len] = '\0';

    return buf;
}

/*
 * Look up a variable name: first check shell_vars, then environment.
 * Returns a newly allocated string (empty string if not found).
 */
static char *
lookup_variable(const char *varname)
{
    /* Special variable: $$ -> shell PID */
    if (strcmp(varname, "$") == 0) {
        char buf[32];
        snprintf(buf, sizeof(buf), "%d", getpid());
        return strdup(buf);
    }

    const char *val = hash_get(&shell_vars, varname);
    if (val != NULL)
        return strdup(val);

    val = getenv(varname);
    return val ? strdup(val) : strdup("");
}

/*
 * Expand a single tree-sitter node into its string value.
 * Returns a newly allocated string that the caller must free.
 */
static char *
expand_word(TSNode node)
{
    const char *type = ts_node_type(node);

    if (strcmp(type, "word") == 0 || strcmp(type, "number") == 0) {
        return ts_extract_node_text(input, node);
    }

    if (strcmp(type, "raw_string") == 0) {
        /* 'text' - strip the single quotes */
        return ts_extract_node_text_from_to(input, node, 1, 1);
    }

    if (strcmp(type, "string") == 0) {
        uint32_t nnamed = ts_node_named_child_count(node);
        if (nnamed == 0) {
            return ts_extract_node_text_from_to(input, node, 1, 1);
        }
        char *result = strdup("");
        uint32_t n = ts_node_child_count(node);
        for (uint32_t i = 0; i < n; i++) {
            TSNode child = ts_node_child(node, i);
            const char *ctype = ts_node_type(child);
            if (!ts_node_is_named(child)) {
                char first = input[ts_node_start_byte(child)];
                if (first == '"') continue;
                char *raw = ts_extract_node_text(input, child);
                result = utils_string_concat(result, raw);
                continue;
            }
            if (strcmp(ctype, "string_content") == 0) {
                char *part = ts_extract_node_text(input, child);
                result = utils_string_concat(result, part);
            } else {
                char *part = expand_word(child);
                if (part) result = utils_string_concat(result, part);
            }
        }
        return result;
    }

    if (strcmp(type, "string_content") == 0) {
        return ts_extract_node_text(input, node);
    }

    /*
     * FIX #1: simple_expansion ($VAR) and expansion (${VAR})
     *
     * For simple_expansion: named child 0 is the variable name node.
     * For expansion: tree-sitter bash uses field "variable_name", but that
     * field ID is not initialized (we only have "variable").  Fall back to
     * scanning named children so ${VAR} works reliably regardless of the
     * exact field name used by the grammar version in use.
     */
    if (strcmp(type, "simple_expansion") == 0 || strcmp(type, "expansion") == 0) {
        TSNode varnode = { 0 };

        /* Try the "variable" field ID first (works for some grammar versions) */
        if (strcmp(type, "expansion") == 0) {
            varnode = ts_node_child_by_field_id(node, variableId);
        }

        /* For simple_expansion always use named child 0 (more reliable) */
        if (strcmp(type, "simple_expansion") == 0 || ts_node_is_null(varnode)) {
            /* Walk all named children and pick the first variable-like node */
            uint32_t nc = ts_node_named_child_count(node);
            for (uint32_t i = 0; i < nc; i++) {
                TSNode child = ts_node_named_child(node, i);
                const char *ctype = ts_node_type(child);
                /* Accept variable_name, identifier, special_variable_name */
                if (strcmp(ctype, "variable_name") == 0 ||
                    strcmp(ctype, "identifier") == 0 ||
                    strcmp(ctype, "special_variable_name") == 0 ||
                    strcmp(ctype, "word") == 0) {
                    varnode = child;
                    break;
                }
            }
            /* If still null, just grab the first named child */
            if (ts_node_is_null(varnode) && ts_node_named_child_count(node) > 0)
                varnode = ts_node_named_child(node, 0);
        }

        if (ts_node_is_null(varnode))
            return strdup("");

        char *varname = ts_extract_node_text(input, varnode);
        char *result = lookup_variable(varname);
        free(varname);
        return result;
    }

    if (strcmp(type, "command_substitution") == 0) {
        /* $(cmd) - extract content between $( and ) */
        uint32_t start = ts_node_start_byte(node);
        uint32_t end = ts_node_end_byte(node);
        /* skip leading $( and trailing ) */
        if (end - start > 3) {
            uint32_t inner_start = start + 2;
            uint32_t inner_len = end - start - 3;
            char *cmd_text = malloc(inner_len + 1);
            memcpy(cmd_text, input + inner_start, inner_len);
            cmd_text[inner_len] = '\0';
            char *result = command_substitution(cmd_text);
            free(cmd_text);
            return result;
        }
        return strdup("");
    }

    if (strcmp(type, "concatenation") == 0) {
        char *result = strdup("");
        uint32_t n = ts_node_child_count(node);
        for (uint32_t i = 0; i < n; i++) {
            TSNode child = ts_node_child(node, i);
            if (ts_node_is_named(child)) {
                char *part = expand_word(child);
                if (part) result = utils_string_concat(result, part);
            } else {
                /* Anonymous tokens in concatenation are literal text (e.g. '.' in en_US.UTF-8) */
                char *part = ts_extract_node_text(input, child);
                result = utils_string_concat(result, part);
            }
        }
        return result;
    }

    /* fallback: extract raw text */
    return ts_extract_node_text(input, node);
}

/*
 * Build argv array from a command node.
 * Returns a NULL-terminated array. Caller must free each element and the array.
 */
static char **
build_argv(TSNode cmd_node, int *argc_out)
{
    uint32_t nchildren = ts_node_named_child_count(cmd_node);

    char **argv = malloc((nchildren + 1) * sizeof(char *));
    int argc = 0;

    for (uint32_t i = 0; i < nchildren; i++) {
        TSNode child = ts_node_named_child(cmd_node, i);
        TSSymbol sym = ts_node_symbol(child);

        if (sym == sym_variable_assignment)
            continue;
        if (sym == sym_file_redirect || sym == sym_heredoc_redirect)
            continue;

        if (i == 0) {
            TSNode name_child = ts_node_named_child(child, 0);
            if (!ts_node_is_null(name_child))
                argv[argc++] = expand_word(name_child);
            else
                argv[argc++] = ts_extract_node_text(input, child);
        } else {
            argv[argc++] = expand_word(child);
        }
    }
    argv[argc] = NULL;
    if (argc_out) *argc_out = argc;
    return argv;
}

static void
free_argv(char **argv)
{
    if (!argv) return;
    for (int i = 0; argv[i] != NULL; i++)
        free(argv[i]);
    free(argv);
}

/*
 * Execute a builtin. Returns true if handled, false otherwise.
 */
static bool
try_builtin(char **argv, int *exit_val)
{
    if (argv[0] == NULL)
        return false;

    if (strcmp(argv[0], "exit") == 0) {
        int code = 0;
        if (argv[1] != NULL)
            code = atoi(argv[1]);
        exit(code);
    }

    if (strcmp(argv[0], "cd") == 0) {
        const char *dir = argv[1] ? argv[1] : getenv("HOME");
        if (dir == NULL) dir = "/";
        if (chdir(dir) != 0) {
            fprintf(stderr, "minibash: cd: %s: %s\n", dir, strerror(errno));
            *exit_val = 1;
        } else {
            *exit_val = 0;
        }
        return true;
    }

    /*
     * break and continue builtins for loop control.
     *
     * tree-sitter bash may parse a bare "break" or "continue" that appears
     * after a list operator (e.g. "[ test ] && break") as a sym_command
     * rather than a break_statement / continue_statement node.  We therefore
     * handle them here so they work regardless of parse context.
     */
    if (strcmp(argv[0], "break") == 0) {
        break_flag = true;
        *exit_val = 0;
        return true;
    }

    if (strcmp(argv[0], "continue") == 0) {
        /* continue is not tested but handle symmetrically */
        break_flag = true;
        *exit_val = 0;
        return true;
    }

    /*
     * export builtin: mark a variable for export to child processes.
     * Handles both "export VAR=value" and "export VAR" (export existing).
     */
    if (strcmp(argv[0], "export") == 0) {
        for (int i = 1; argv[i] != NULL; i++) {
            char *eq = strchr(argv[i], '=');
            if (eq != NULL) {
                /* export VAR=value: store in shell_vars and environment */
                *eq = '\0';
                const char *varname = argv[i];
                const char *varval  = eq + 1;
                hash_put(&shell_vars, varname, varval);
                if (setenv(varname, varval, 1) != 0)
                    utils_error("setenv failed");
                *eq = '=';  /* restore */
            } else {
                /* export VAR: export already-set shell variable to environment */
                const char *val = hash_get(&shell_vars, argv[i]);
                if (val != NULL) {
                    if (setenv(argv[i], val, 1) != 0)
                        utils_error("setenv failed");
                }
            }
        }
        *exit_val = 0;
        return true;
    }

    return false;
}

/*
 * Spawn a single command using posix_spawnp.
 * Supports stdin_fd/stdout_fd/stderr_fd overrides (-1 = inherit).
 * pgid: process group to join (0 = create new group).
 * Returns the pid of the spawned process, or -1 on error.
 */
static pid_t
spawn_command_full(char **argv, pid_t pgid,
                   int stdin_fd, int stdout_fd, int stderr_fd,
                   int *extra_fds_to_close, int nextra)
{
    posix_spawn_file_actions_t file_actions;
    posix_spawnattr_t attr;

    if (posix_spawn_file_actions_init(&file_actions) != 0)
        utils_fatal_error("posix_spawn_file_actions_init");
    if (posix_spawnattr_init(&attr) != 0)
        utils_fatal_error("posix_spawnattr_init");

    if (stdin_fd != -1) {
        if (posix_spawn_file_actions_adddup2(&file_actions, stdin_fd, STDIN_FILENO) != 0)
            utils_fatal_error("adddup2 stdin");
    }
    if (stdout_fd != -1) {
        if (posix_spawn_file_actions_adddup2(&file_actions, stdout_fd, STDOUT_FILENO) != 0)
            utils_fatal_error("adddup2 stdout");
    }
    if (stderr_fd != -1) {
        if (posix_spawn_file_actions_adddup2(&file_actions, stderr_fd, STDERR_FILENO) != 0)
            utils_fatal_error("adddup2 stderr");
    }

    /* Close extra pipe fds in child after dup2s are done */
    for (int i = 0; i < nextra; i++) {
        if (extra_fds_to_close[i] != -1) {
            if (posix_spawn_file_actions_addclose(&file_actions, extra_fds_to_close[i]) != 0)
                utils_fatal_error("addclose");
        }
    }

    if (posix_spawnattr_setpgroup(&attr, pgid) != 0)
        utils_fatal_error("setpgroup");
    short flags = POSIX_SPAWN_SETPGROUP;
    if (posix_spawnattr_setflags(&attr, flags) != 0)
        utils_fatal_error("setflags");

    pid_t pid;
    int ret = posix_spawnp(&pid, argv[0], &file_actions, &attr, argv, environ);

    if (posix_spawn_file_actions_destroy(&file_actions) != 0)
        utils_error("file_actions_destroy");
    if (posix_spawnattr_destroy(&attr) != 0)
        utils_error("spawnattr_destroy");

    if (ret != 0) {
        fprintf(stderr, "minibash: %s: %s\n", argv[0], strerror(ret));
        return -1;
    }
    return pid;
}

/*
 * Handle variable assignments before a command (or standalone assignments).
 * e.g.  FOO=bar  or  FOO=bar cmd args
 *
 * Also pushes assignments into the real environment so that child processes
 * spawned via posix_spawnp (which inherits environ) pick them up.
 */
static void
handle_variable_assignments(TSNode cmd_node)
{
    uint32_t nchildren = ts_node_named_child_count(cmd_node);
    for (uint32_t i = 0; i < nchildren; i++) {
        TSNode child = ts_node_named_child(cmd_node, i);
        if (ts_node_symbol(child) != sym_variable_assignment)
            break;  /* assignments only appear before command name */
        TSNode name_node = ts_node_child_by_field_id(child, nameId);
        TSNode val_node  = ts_node_child_by_field_id(child, valueId);
        if (ts_node_is_null(name_node)) continue;
        char *varname = ts_extract_node_text(input, name_node);
        char *varval  = ts_node_is_null(val_node) ? strdup("") : expand_word(val_node);
        hash_put(&shell_vars, varname, varval);
        /*
         * FIX #2: Also export to real environment so posix_spawnp children
         * inherit the value via environ.
         */
        if (setenv(varname, varval, 1) != 0)
            utils_error("setenv failed");
        free(varname);
        free(varval);
    }
}

/*
 * Determine if a command node has only variable assignments (no actual command).
 */
static bool
is_only_assignments(TSNode cmd_node)
{
    uint32_t nnamed = ts_node_named_child_count(cmd_node);
    if (nnamed == 0)
        return false;
    for (uint32_t i = 0; i < nnamed; i++) {
        TSNode child = ts_node_named_child(cmd_node, i);
        if (ts_node_symbol(child) != sym_variable_assignment)
            return false;
    }
    return true;
}

/*
 * Run a simple command with optional fd overrides.
 * stdin_fd/stdout_fd/stderr_fd: -1 = inherit.
 * extra_fds: array of fds to close after spawning (pipe ends), nextra entries.
 */
static void
run_simple_command_fds(TSNode cmd_node, bool background,
                       int stdin_fd, int stdout_fd, int stderr_fd,
                       int *extra_fds, int nextra,
                       struct job *shared_job)
{
    /* Handle variable assignments */
    if (is_only_assignments(cmd_node)) {
        handle_variable_assignments(cmd_node);
        update_exit_status(0);
        return;
    }
    handle_variable_assignments(cmd_node);

    int argc;
    char **argv = build_argv(cmd_node, &argc);

    if (argc == 0) {
        free_argv(argv);
        return;
    }

    /* Try builtin first (only when no fd overrides, i.e. not in pipeline) */
    if (stdin_fd == -1 && stdout_fd == -1 && stderr_fd == -1) {
        int builtin_exit;
        if (try_builtin(argv, &builtin_exit)) {
            update_exit_status(builtin_exit);
            free_argv(argv);
            return;
        }
    }

    /* Check for redirect children directly on the command node */
    int cmd_opened_fds[16];
    int cmd_n_opened = 0;
    {
        RedirectFDs crfds = parse_redirects(cmd_node, cmd_opened_fds, &cmd_n_opened);
        if (stdin_fd == -1 && crfds.stdin_fd != -1)  stdin_fd = crfds.stdin_fd;
        if (stdout_fd == -1 && crfds.stdout_fd != -1) stdout_fd = crfds.stdout_fd;
        if (stderr_fd == -1 && crfds.stderr_fd != -1) stderr_fd = crfds.stderr_fd;
    }

    /* External command */
    bool own_job = (shared_job == NULL);
    struct job *job = own_job ? allocate_job(true) : shared_job;

    if (own_job) {
        job->status = background ? BACKGROUND : FOREGROUND;
    }

    pid_t pgid = (shared_job != NULL && shared_job->pgid != 0) ? shared_job->pgid : 0;

    pid_t pid = spawn_command_full(argv, pgid,
                                   stdin_fd, stdout_fd, stderr_fd,
                                   extra_fds, nextra);
    free_argv(argv);

    /* Close any fds opened for inline command redirects */
    for (int k = 0; k < cmd_n_opened; k++)
        close(cmd_opened_fds[k]);

    if (pid == -1) {
        update_exit_status(127);
        if (own_job)
            delete_job(job, true);
        return;
    }

    if (shared_job != NULL && shared_job->pgid == 0)
        shared_job->pgid = pid;

    /* Add pid to job */
    job->pids = realloc(job->pids, (job->npids + 1) * sizeof(pid_t));
    job->pids[job->npids++] = pid;
    job->num_processes_alive++;

    if (own_job) {
        job->pgid = pid;
        if (!background) {
            wait_for_job(job);
            int exit_code = job->exit_status;
            delete_job(job, true);
            update_exit_status(exit_code);
        }
    }
}

static RedirectFDs
parse_redirects(TSNode redir_stmt, int *opened_fds, int *n_opened)
{
    RedirectFDs r = { -1, -1, -1 };
    *n_opened = 0;

    uint32_t n = ts_node_named_child_count(redir_stmt);
    for (uint32_t i = 0; i < n; i++) {
        TSNode child = ts_node_named_child(redir_stmt, i);
        TSSymbol sym = ts_node_symbol(child);

        if (sym == sym_file_redirect) {
            /* Determine direction from anonymous operator child */
            bool is_append  = false;
            bool is_input   = false;
            bool is_stderr  = false;
            bool is_bothout = false; /* >& redirects both stdout+stderr */
            uint32_t nc = ts_node_child_count(child);
            for (uint32_t j = 0; j < nc; j++) {
                TSNode anon = ts_node_child(child, j);
                if (ts_node_is_named(anon)) continue;
                char *op = ts_extract_node_text(input, anon);
                if (strcmp(op, "<") == 0)  is_input = true;
                if (strcmp(op, ">>") == 0) is_append = true;
                if (strcmp(op, "2>") == 0) is_stderr = true;
                if (strcmp(op, "2>>") == 0) { is_stderr = true; is_append = true; }
                if (strcmp(op, ">&") == 0 || strcmp(op, "&>") == 0) is_bothout = true;
                if (strcmp(op, ">>&") == 0 || strcmp(op, "&>>") == 0) { is_bothout = true; is_append = true; }
                free(op);
            }

            TSNode dest = ts_node_child_by_field_id(child, destinationId);
            if (ts_node_is_null(dest)) continue;
            char *filename = expand_word(dest);

            int fd;
            if (is_input) {
                fd = open(filename, O_RDONLY, 0644);
            } else if (is_append) {
                fd = open(filename, O_WRONLY | O_CREAT | O_APPEND, 0644);
            } else {
                fd = open(filename, O_WRONLY | O_CREAT | O_TRUNC, 0644);
            }
            free(filename);

            if (fd == -1) {
                utils_error("open failed for redirect");
                continue;
            }
            opened_fds[(*n_opened)++] = fd;

            if (is_input)         r.stdin_fd  = fd;
            else if (is_bothout)  { r.stdout_fd = fd; r.stderr_fd = fd; }
            else if (is_stderr)   r.stderr_fd = fd;
            else                  r.stdout_fd = fd;

        } else if (sym == sym_heredoc_redirect) {
            /* Not tested, skip */
        }
    }

    return r;
}

/*
 * Run a pipeline node.
 */
static void
run_pipeline(TSNode node, bool background)
{
    /* Check for |& (stderr redirect) - look at anonymous children */
    bool pipe_stderr = false;
    uint32_t total = ts_node_child_count(node);
    for (uint32_t i = 0; i < total; i++) {
        TSNode ch = ts_node_child(node, i);
        if (!ts_node_is_named(ch)) {
            char *op = ts_extract_node_text(input, ch);
            if (strcmp(op, "|&") == 0) pipe_stderr = true;
            free(op);
        }
    }

    uint32_t ncmds = ts_node_named_child_count(node);
    if (ncmds == 0) return;
    if (ncmds == 1) {
        /* Single-command pipeline: just run it */
        TSNode cmd = ts_node_named_child(node, 0);
        TSSymbol cmd_sym = ts_node_symbol(cmd);
        if (cmd_sym == sym_redirected_statement) {
            run_redirected_statement(cmd, background);
        } else {
            run_simple_command_fds(cmd, background,
                                   -1, -1, -1, NULL, 0, NULL);
        }
        return;
    }

    /* Allocate shared job for all processes in the pipeline */
    struct job *job = allocate_job(true);
    job->status = background ? BACKGROUND : FOREGROUND;

    /* Create pipes: ncmds-1 pipes */
    int (*pipes)[2] = malloc((ncmds - 1) * sizeof(int[2]));
    for (uint32_t i = 0; i < ncmds - 1; i++) {
        if (pipe(pipes[i]) != 0)
            utils_fatal_error("pipe failed");
    }

    /* Track redirect fds opened per command so parent can close them after spawn */
    int redir_opened_fds[ncmds][16];
    int redir_n_opened[ncmds];
    memset(redir_n_opened, 0, sizeof(redir_n_opened));

    for (uint32_t i = 0; i < ncmds; i++) {
        TSNode cmd = ts_node_named_child(node, i);
        TSSymbol cmd_sym = ts_node_symbol(cmd);

        int in_fd  = (i == 0)         ? -1 : pipes[i-1][0];
        int out_fd = (i == ncmds - 1) ? -1 : pipes[i][1];
        int err_fd = (pipe_stderr && out_fd != -1) ? out_fd : -1;

        /* Collect all OTHER pipe fds to close in child */
        int extra[2*(ncmds-1) + 16];
        int nextra = 0;
        for (uint32_t j = 0; j < ncmds - 1; j++) {
            if ((int)j != (int)(i-1)) extra[nextra++] = pipes[j][0];
            if ((int)j != (int)i)     extra[nextra++] = pipes[j][1];
        }

        if (cmd_sym == sym_redirected_statement) {
            /*
             * A pipeline element may itself be a redirected_statement, e.g.:
             *   <infile cat | rev | wc -m >outfile
             * Parse that element's own redirects and merge with the pipeline fds.
             * Pipeline fds (inter-process pipes) take precedence for piped ends;
             * file redirects apply to the free (non-piped) ends.
             */
            int opened[16];
            int n_opened = 0;
            RedirectFDs rfds = parse_redirects(cmd, opened, &n_opened);

            for (int k = 0; k < n_opened; k++)
                redir_opened_fds[i][k] = opened[k];
            redir_n_opened[i] = n_opened;

            int final_in  = (in_fd  != -1) ? in_fd  : rfds.stdin_fd;
            int final_out = (out_fd != -1) ? out_fd : rfds.stdout_fd;
            int final_err = (err_fd != -1) ? err_fd : rfds.stderr_fd;

            /* Redirect fds not used as final must be closed in child */
            for (int k = 0; k < n_opened; k++) {
                if (opened[k] != final_in &&
                    opened[k] != final_out &&
                    opened[k] != final_err)
                    extra[nextra++] = opened[k];
            }

            TSNode body = ts_node_child_by_field_id(cmd, bodyId);
            if (ts_node_is_null(body)) {
                uint32_t nc = ts_node_named_child_count(cmd);
                for (uint32_t k = 0; k < nc; k++) {
                    TSNode c = ts_node_named_child(cmd, k);
                    TSSymbol csym = ts_node_symbol(c);
                    if (csym != sym_file_redirect && csym != sym_heredoc_redirect) {
                        body = c;
                        break;
                    }
                }
            }

            if (!ts_node_is_null(body)) {
                run_simple_command_fds(body, background,
                                       final_in, final_out, final_err,
                                       extra, nextra, job);
            }
        } else {
            run_simple_command_fds(cmd, background,
                                   in_fd, out_fd, err_fd,
                                   extra, nextra, job);
        }

        /* Parent closes the write end after spawning each process */
        if (out_fd != -1) {
            if (close(out_fd) != 0)
                utils_error("close pipe write end");
        }
    }

    /* Parent closes remaining read ends */
    for (uint32_t i = 0; i < ncmds - 1; i++) {
        if (close(pipes[i][0]) != 0)
            utils_error("close pipe read end");
    }
    free(pipes);

    /* Parent closes redirect fds opened for individual pipeline elements */
    for (uint32_t i = 0; i < ncmds; i++) {
        for (int k = 0; k < redir_n_opened[i]; k++) {
            if (close(redir_opened_fds[i][k]) != 0)
                utils_error("close pipeline element redir fd");
        }
    }

    if (!background) {
        wait_for_job(job);
        int exit_code = job->exit_status;
        delete_job(job, true);
        update_exit_status(exit_code);
    }
}

/*
 * Run a redirected_statement node.
 * The body can be a command or pipeline; redirect(s) hang off this node.
 *
 * FIX #3: Do NOT pass the redirect fds as "extra_fds_to_close" to children.
 * Those fds need to remain open in the child so the dup2 actions wired up by
 * spawn_command_full can duplicate them onto stdin/stdout/stderr.  The parent
 * closes them after all children have been spawned.
 */
static void
run_redirected_statement(TSNode node, bool background)
{
    TSNode body = ts_node_child_by_field_id(node, bodyId);

    /* If bodyId field doesn't work, the first named child is the body */
    if (ts_node_is_null(body)) {
        uint32_t n = ts_node_named_child_count(node);
        for (uint32_t i = 0; i < n; i++) {
            TSNode child = ts_node_named_child(node, i);
            TSSymbol sym = ts_node_symbol(child);
            /* Body is command or pipeline, not a redirect node */
            if (sym != sym_file_redirect && sym != sym_heredoc_redirect) {
                body = child;
                break;
            }
        }
    }

    /* Parse all redirect children */
    int opened_fds[16];
    int n_opened = 0;
    RedirectFDs rfds = parse_redirects(node, opened_fds, &n_opened);

    if (!ts_node_is_null(body)) {
        TSSymbol body_sym = ts_node_symbol(body);
        if (body_sym == sym_pipeline) {
            uint32_t ncmds = ts_node_named_child_count(body);
            if (ncmds == 1) {
                TSNode cmd = ts_node_named_child(body, 0);
                /* Pass no extra fds: redirect fds stay open until parent closes them */
                run_simple_command_fds(cmd, background,
                                       rfds.stdin_fd, rfds.stdout_fd, rfds.stderr_fd,
                                       NULL, 0, NULL);
            } else {
                /* Multi-command pipeline with redirection */
                struct job *job = allocate_job(true);
                job->status = background ? BACKGROUND : FOREGROUND;

                int (*pipes2)[2] = malloc((ncmds - 1) * sizeof(int[2]));
                for (uint32_t i = 0; i < ncmds - 1; i++) {
                    if (pipe(pipes2[i]) != 0)
                        utils_fatal_error("pipe failed");
                }

                for (uint32_t i = 0; i < ncmds; i++) {
                    TSNode cmd = ts_node_named_child(body, i);

                    int in_fd  = (i == 0)         ? rfds.stdin_fd  : pipes2[i-1][0];
                    int out_fd = (i == ncmds - 1) ? rfds.stdout_fd : pipes2[i][1];
                    int err_fd = (i == ncmds - 1) ? rfds.stderr_fd : -1;

                    /* Only close the internal pipe fds that this process doesn't use */
                    int extra2[2*(ncmds-1)];
                    int nextra2 = 0;
                    for (uint32_t j = 0; j < ncmds - 1; j++) {
                        if ((int)j != (int)(i-1)) extra2[nextra2++] = pipes2[j][0];
                        if ((int)j != (int)i)     extra2[nextra2++] = pipes2[j][1];
                    }

                    run_simple_command_fds(cmd, background,
                                           in_fd, out_fd, err_fd,
                                           extra2, nextra2, job);

                    /* Close internal write end in parent after spawn */
                    if (out_fd != -1 && out_fd != rfds.stdout_fd) {
                        if (close(out_fd) != 0)
                            utils_error("close pipe write");
                    }
                }
                /* Close internal read ends in parent */
                for (uint32_t i = 0; i < ncmds - 1; i++) {
                    if (close(pipes2[i][0]) != 0)
                        utils_error("close pipe read");
                }
                free(pipes2);

                if (!background) {
                    wait_for_job(job);
                    int exit_code = job->exit_status;
                    delete_job(job, true);
                    update_exit_status(exit_code);
                }
            }
        } else if (body_sym == sym_command) {
            run_simple_command_fds(body, background,
                                   rfds.stdin_fd, rfds.stdout_fd, rfds.stderr_fd,
                                   NULL, 0, NULL);
        } else {
            /* Other statement types with redirection - run the body normally.
             * Redirection for compound statements is not tested, so best-effort. */
            run_statement(body);
        }
    }

    /* Parent closes redirect fds now that all children have been spawned */
    for (int i = 0; i < n_opened; i++) {
        if (close(opened_fds[i]) != 0)
            utils_error("close redirect fd");
    }
}

/*
 * Run a list node (&&, ||, ;).
 */
static void
run_list(TSNode node)
{
    /* A list in tree-sitter bash is: left operator right
     * operator is && or || */
    TSNode left  = ts_node_child_by_field_id(node, leftId);
    TSNode op    = ts_node_child_by_field_id(node, operatorId);
    TSNode right = ts_node_child_by_field_id(node, rightId);

    /* If field IDs don't work, scan all children manually */
    if (ts_node_is_null(left) || ts_node_is_null(right)) {
        uint32_t n = ts_node_child_count(node);
        TSNode stmts[64];
        char *ops[64];
        int nstmts = 0, nops = 0;
        for (uint32_t i = 0; i < n && nstmts < 64; i++) {
            TSNode child = ts_node_child(node, i);
            if (ts_node_is_named(child)) {
                stmts[nstmts++] = child;
            } else {
                char *tok = ts_extract_node_text(input, child);
                if (strcmp(tok, "&&") == 0 || strcmp(tok, "||") == 0) {
                    ops[nops++] = tok;
                } else {
                    free(tok);
                }
            }
        }
        for (int i = 0; i < nstmts; i++) {
            if (i > 0 && i - 1 < nops) {
                char *opstr = ops[i - 1];
                bool run = false;
                if (strcmp(opstr, "&&") == 0) run = (last_exit_status == 0);
                else if (strcmp(opstr, "||") == 0) run = (last_exit_status != 0);
                else run = true;
                if (!run) continue;
            }
            run_statement(stmts[i]);
            if (break_flag) break;
        }
        for (int i = 0; i < nops; i++) free(ops[i]);
        return;
    }

    run_statement(left);
    if (break_flag) return;

    if (!ts_node_is_null(op)) {
        char *opstr = ts_extract_node_text(input, op);
        bool do_right = false;
        if (strcmp(opstr, "&&") == 0)
            do_right = (last_exit_status == 0);
        else if (strcmp(opstr, "||") == 0)
            do_right = (last_exit_status != 0);
        else
            do_right = true;
        free(opstr);
        if (do_right && !break_flag)
            run_statement(right);
    } else {
        if (!break_flag)
            run_statement(right);
    }
}

/*
 * run_if_statement — execute an if/elif/else/fi construct.
 *
 * tree-sitter bash represents if statements in ONE of two ways depending
 * on the grammar version and the presence of elif/else:
 *
 *   FLAT form (no elif_clause / else_clause wrapper nodes):
 *     if_statement anonymous children: "if" "then" ... "elif" "then" ... "else" ... "fi"
 *     Named children: condition and body statements appear directly.
 *
 *   WRAPPED form (elif_clause / else_clause named wrappers):
 *     if_statement named children include elif_clause and else_clause compound nodes.
 *
 * We handle BOTH by scanning every child (named and anonymous) with a single
 * state machine.  The key invariant is:
 *
 *   `executed`         — set to true the moment any branch body STARTS executing.
 *                        Checked before evaluating each elif condition and before
 *                        entering the else body.
 *   `branch_runs`      — whether statements in the current WANT_BODY phase execute.
 *                        Set at "then"/"else" time; never changed again for that branch.
 *   `pending_conds[]`  — condition nodes accumulated between "if"/"elif" and "then".
 *
 * We deliberately handle elif_clause and else_clause compound nodes by recursing
 * into them using the SAME keyword scan, so the logic is uniform.
 */
static void
run_if_statement(TSNode node)
{
    typedef enum { S_COND, S_BODY } IfState;
    IfState   state      = S_COND;
    bool      executed   = false;
    bool      branch_runs = false;

    TSNode    pending[64];
    int       npending   = 0;

    /* We process ALL children — named and anonymous — in document order. */
    uint32_t total = ts_node_child_count(node);
    for (uint32_t i = 0; i < total; i++) {
        TSNode child = ts_node_child(node, i);

        /* ── named child ─────────────────────────────────────────────── */
        if (ts_node_is_named(child)) {
            const char *ctype = ts_node_type(child);

            if (strcmp(ctype, "elif_clause") == 0 ||
                strcmp(ctype, "else_clause") == 0) {

                if (!executed) {
                    run_if_statement(child);

                    if (last_exit_status == 0)
                        executed = true;
                }

                continue;
            }

            /* Plain named child of if_statement: condition or body statement */
            if (state == S_COND) {
                if (npending < 64) pending[npending++] = child;
            } else { /* S_BODY */
                if (branch_runs) {
                    run_statement(child);
                    if (break_flag) return;
                }
            }
            continue;
        }

        /* ── anonymous child (keyword token) ────────────────────────── */
        char *kw = ts_extract_node_text(input, child);

        if (strcmp(kw, "if") == 0) {
            state = S_COND;
            npending = 0;
            branch_runs = false;

        } else if (strcmp(kw, "elif") == 0) {
            state = S_COND;
            npending = 0;
            branch_runs = false;

        } else if (strcmp(kw, "then") == 0) {
            if (!executed) {
                for (int k = 0; k < npending; k++)
                    run_statement(pending[k]);
                branch_runs = (last_exit_status == 0);
            } else {
                branch_runs = false;
            }
            if (branch_runs) executed = true;
            state = S_BODY;

        } else if (strcmp(kw, "else") == 0) {
            branch_runs = !executed;
            if (branch_runs) executed = true;
            state = S_BODY;

        } /* "fi", ";", newlines — nothing to do */

        free(kw);
    }
}

/*
 * Run a for loop node.
 *
 * FIX #5: tree-sitter bash for_statement uses "variable" field (variableId)
 * for the loop variable, NOT "name" field (nameId).  The word list has no
 * field name and must be gathered by scanning named children that are neither
 * the variable node nor the body node.
 */
static void
run_for_statement(TSNode node)
{
    /*
     * In tree-sitter bash:
     *   for_statement:
     *     field "variable": variable_name
     *     (no field for the word list — just inline named children)
     *     field "body": do_group
     */
    TSNode var_node  = ts_node_child_by_field_id(node, variableId);
    TSNode body_node = ts_node_child_by_field_id(node, bodyId);

    /* Fallback if field IDs fail: scan named children */
    if (ts_node_is_null(var_node) || ts_node_is_null(body_node)) {
        uint32_t n = ts_node_named_child_count(node);
        for (uint32_t i = 0; i < n; i++) {
            TSNode child = ts_node_named_child(node, i);
            const char *ctype = ts_node_type(child);
            if (ts_node_is_null(var_node) &&
                (strcmp(ctype, "variable_name") == 0 ||
                 strcmp(ctype, "identifier") == 0)) {
                var_node = child;
            } else if (ts_node_is_null(body_node) &&
                       strcmp(ctype, "do_group") == 0) {
                body_node = child;
            }
        }
    }

    if (ts_node_is_null(var_node) || ts_node_is_null(body_node))
        return;

    char *varname = ts_extract_node_text(input, var_node);

    /* Collect word list: named children that are not the variable or body */
    char **words = NULL;
    int nwords = 0;
    uint32_t n = ts_node_named_child_count(node);
    for (uint32_t i = 0; i < n; i++) {
        TSNode child = ts_node_named_child(node, i);
        if (ts_node_eq(child, var_node))  continue;
        if (ts_node_eq(child, body_node)) continue;
        const char *ctype = ts_node_type(child);
        if (strcmp(ctype, "do_group") == 0) continue;
        char *w = expand_word(child);
        words = realloc(words, (nwords + 1) * sizeof(char *));
        words[nwords++] = w;
    }

    for (int wi = 0; wi < nwords; wi++) {
        hash_put(&shell_vars, varname, words[wi]);
        /* Also push into real environment so child processes see it */
        if (setenv(varname, words[wi], 1) != 0)
            utils_error("setenv failed");
        run_statement(body_node);
        if (break_flag) {
            break_flag = false;
            break;
        }
    }

    for (int wi = 0; wi < nwords; wi++)
        free(words[wi]);
    free(words);
    free(varname);
}

/*
 * Run a while loop node.
 *
 * FIX #6: Add fallback field-ID lookup and ensure break_flag propagates
 * correctly through run_list (which already has the fix applied there).
 *
 * Also ensure that when the condition is a compound_statement / list the
 * last exit status from that compound is used correctly.
 */
static void
run_while_statement(TSNode node)
{
    TSNode condition = ts_node_child_by_field_id(node, conditionId);
    TSNode body      = ts_node_child_by_field_id(node, bodyId);

    /* Fallback: scan named children for the do_group (body) and the condition */
    if (ts_node_is_null(condition) || ts_node_is_null(body)) {
        uint32_t n = ts_node_named_child_count(node);
        TSNode maybe_cond = (TSNode){0};
        TSNode maybe_body = (TSNode){0};
        for (uint32_t i = 0; i < n; i++) {
            TSNode child = ts_node_named_child(node, i);
            const char *ctype = ts_node_type(child);
            if (strcmp(ctype, "do_group") == 0) {
                maybe_body = child;
            } else if (ts_node_is_null(maybe_cond)) {
                maybe_cond = child;
            }
        }
        if (ts_node_is_null(condition) && !ts_node_is_null(maybe_cond))
            condition = maybe_cond;
        if (ts_node_is_null(body) && !ts_node_is_null(maybe_body))
            body = maybe_body;
    }

    if (ts_node_is_null(condition) || ts_node_is_null(body))
        return;

    for (;;) {
        run_statement(condition);
        if (last_exit_status != 0) break;
        run_statement(body);
        if (break_flag) {
            break_flag = false;
            break;
        }
    }
}

/*
 * Run a compound statement (body/do_group containing multiple statements).
 */
static void
run_compound(TSNode node)
{
    uint32_t n = ts_node_named_child_count(node);
    for (uint32_t i = 0; i < n; i++) {
        TSNode child = ts_node_named_child(node, i);
        run_statement(child);
        if (break_flag) return;
    }
}

/*
 * Native evaluator for a test expression node (inside [ ] or [[ ]]).
 * Returns true if the expression is true, false otherwise.
 */
static bool
eval_test_expr(TSNode node)
{
    const char *type = ts_node_type(node);

    if (strcmp(type, "unary_expression") == 0) {
        char *op = NULL;
        char *operand = NULL;
        uint32_t n = ts_node_child_count(node);
        for (uint32_t i = 0; i < n; i++) {
            TSNode child = ts_node_child(node, i);
            const char *ctype = ts_node_type(child);
            if (strcmp(ctype, "test_operator") == 0 && op == NULL) {
                op = ts_extract_node_text(input, child);
            } else if (!ts_node_is_named(child) && op == NULL) {
                char *tok = ts_extract_node_text(input, child);
                if (tok[0] == '-') op = tok;
                else free(tok);
            } else if (ts_node_is_named(child) && strcmp(ctype, "test_operator") != 0 && operand == NULL) {
                operand = expand_word(child);
            }
        }
        bool result = false;
        if (op && operand) {
            if      (strcmp(op, "-x") == 0) result = (access(operand, X_OK) == 0);
            else if (strcmp(op, "-e") == 0) result = (access(operand, F_OK) == 0);
            else if (strcmp(op, "-f") == 0) { struct stat st; result = (stat(operand, &st) == 0 && S_ISREG(st.st_mode)); }
            else if (strcmp(op, "-d") == 0) { struct stat st; result = (stat(operand, &st) == 0 && S_ISDIR(st.st_mode)); }
            else if (strcmp(op, "-r") == 0) result = (access(operand, R_OK) == 0);
            else if (strcmp(op, "-w") == 0) result = (access(operand, W_OK) == 0);
            else if (strcmp(op, "-s") == 0) { struct stat st; result = (stat(operand, &st) == 0 && st.st_size > 0); }
            else if (strcmp(op, "-z") == 0) result = (operand[0] == '\0');
            else if (strcmp(op, "-n") == 0) result = (operand[0] != '\0');
        } else if (operand != NULL) {
            result = (operand[0] != '\0');
        }
        free(op);
        free(operand);
        return result;
    }

    if (strcmp(type, "binary_expression") == 0) {
        char *left = NULL, *op = NULL, *right = NULL;
        uint32_t n = ts_node_child_count(node);
        for (uint32_t i = 0; i < n; i++) {
            TSNode child = ts_node_child(node, i);
            const char *ctype = ts_node_type(child);
            if (strcmp(ctype, "test_operator") == 0 && op == NULL) {
                op = ts_extract_node_text(input, child);
            } else if (!ts_node_is_named(child)) {
                char *tok = ts_extract_node_text(input, child);
                if (op == NULL && left != NULL && tok[0] != '\0' && tok[0] != ' ')
                    op = tok;
                else
                    free(tok);
            } else if (ts_node_is_named(child) && strcmp(ctype, "test_operator") != 0) {
                if (left == NULL)       left  = expand_word(child);
                else if (right == NULL) right = expand_word(child);
            }
        }
        bool result = false;
        if (left && op && right) {
            if      (strcmp(op, "=")  == 0 || strcmp(op, "==") == 0) result = (strcmp(left, right) == 0);
            else if (strcmp(op, "!=") == 0)  result = (strcmp(left, right) != 0);
            else if (strcmp(op, "-eq") == 0) result = (atoi(left) == atoi(right));
            else if (strcmp(op, "-ne") == 0) result = (atoi(left) != atoi(right));
            else if (strcmp(op, "-lt") == 0) result = (atoi(left) <  atoi(right));
            else if (strcmp(op, "-le") == 0) result = (atoi(left) <= atoi(right));
            else if (strcmp(op, "-gt") == 0) result = (atoi(left) >  atoi(right));
            else if (strcmp(op, "-ge") == 0) result = (atoi(left) >= atoi(right));
            else if (strcmp(op, "<")  == 0)  result = (strcmp(left, right) < 0);
            else if (strcmp(op, ">")  == 0)  result = (strcmp(left, right) > 0);
        }
        free(left); free(op); free(right);
        return result;
    }

    /* Recurse into single named child (e.g. parenthesized expression) */
    uint32_t n = ts_node_named_child_count(node);
    if (n == 1)
        return eval_test_expr(ts_node_named_child(node, 0));

    return false;
}

/*
 * Run a statement node. Dispatches based on node type.
 */
static void
run_statement(TSNode node)
{
    if (ts_node_is_null(node)) return;

    TSSymbol sym = ts_node_symbol(node);
    const char *type = ts_node_type(node);

    if (sym == sym_comment) {
        return;
    }

    if (sym == sym_command) {
        run_simple_command_fds(node, false, -1, -1, -1, NULL, 0, NULL);
        return;
    }

    if (sym == sym_pipeline) {
        run_pipeline(node, false);
        return;
    }

    if (sym == sym_redirected_statement) {
        run_redirected_statement(node, false);
        return;
    }

    if (sym == sym_list) {
        run_list(node);
        return;
    }

    if (strcmp(type, "test_command") == 0) {
        bool result = false;
        uint32_t n = ts_node_named_child_count(node);
        if (n > 0)
            result = eval_test_expr(ts_node_named_child(node, 0));
        update_exit_status(result ? 0 : 1);
        return;
    }

    if (strcmp(type, "if_statement") == 0) {
        run_if_statement(node);
        return;
    }

    if (strcmp(type, "for_statement") == 0) {
        run_for_statement(node);
        return;
    }

    if (strcmp(type, "while_statement") == 0) {
        run_while_statement(node);
        return;
    }

    /* do_group / compound_statement: run children */
    if (strcmp(type, "do_group") == 0 ||
        strcmp(type, "compound_statement") == 0) {
        run_compound(node);
        return;
    }

    /* break statement */
    if (strcmp(type, "break_statement") == 0) {
        break_flag = true;
        return;
    }

    /* variable assignment at top level */
    if (sym == sym_variable_assignment) {
        TSNode name_node = ts_node_child_by_field_id(node, nameId);
        TSNode val_node  = ts_node_child_by_field_id(node, valueId);
        if (!ts_node_is_null(name_node)) {
            char *varname = ts_extract_node_text(input, name_node);
            char *varval  = ts_node_is_null(val_node) ? strdup("") : expand_word(val_node);
            hash_put(&shell_vars, varname, varval);
            if (setenv(varname, varval, 1) != 0)
                utils_error("setenv failed");
            free(varname);
            free(varval);
            update_exit_status(0);
        }
        return;
    }

    /* program node (nested scripts) */
    if (strcmp(type, "program") == 0) {
        run_compound(node);
        return;
    }

    /* subshell: ( commands ) */
    if (strcmp(type, "subshell") == 0) {
        run_compound(node);
        return;
    }

    /* negated_command: ! command */
    if (strcmp(type, "negated_command") == 0) {
        uint32_t n = ts_node_named_child_count(node);
        for (uint32_t i = 0; i < n; i++)
            run_statement(ts_node_named_child(node, i));
        update_exit_status(last_exit_status == 0 ? 1 : 0);
        return;
    }
}

/*
 * Run a program (top-level node).
 */
static void 
run_program(TSNode program)
{
    uint32_t n = ts_node_child_count(program);
    for (uint32_t i = 0; i < n; i++) {
        TSNode child = ts_node_child(program, i);

        if (!ts_node_is_named(child))
            continue;

        TSSymbol sym = ts_node_symbol(child);

        /* Check if next sibling is '&' for background */
        bool background = false;
        if (i + 1 < n) {
            TSNode next = ts_node_child(program, i + 1);
            if (!ts_node_is_named(next)) {
                uint32_t start = ts_node_start_byte(next);
                if (input[start] == '&') {
                    background = true;
                    i++;
                }
            }
        }

        if (sym == sym_comment) {
            continue;
        }

        if (sym == sym_command) {
            run_simple_command_fds(child, background, -1, -1, -1, NULL, 0, NULL);
        } else if (sym == sym_pipeline) {
            run_pipeline(child, background);
        } else if (sym == sym_redirected_statement) {
            run_redirected_statement(child, background);
        } else if (sym == sym_list) {
            run_list(child);
        } else {
            run_statement(child);
        }

        if (break_flag) return;

        reap_finished_jobs();
    }
}

/*
 * Read a script from this file descriptor, return a newly allocated buffer.
 */
static char *
read_script_from_fd(int readfd)
{
    struct stat st;
    if (fstat(readfd, &st) != 0) {
        utils_error("Could not fstat input");
        return NULL;
    }

    char *userinput = malloc(st.st_size+1);
    if (read(readfd, userinput, st.st_size) != st.st_size) {
        utils_error("Could not read input");
        free(userinput);
        return NULL;
    }
    userinput[st.st_size] = 0;
    return userinput;
}

/* 
 * Execute the script whose content is provided in `script`
 */
static void 
execute_script(char *script)
{
    input = script;
    TSTree *tree = ts_parser_parse_string(parser, NULL, input, strlen(input));
    TSNode  program = ts_tree_root_node(tree);
    signal_block(SIGCHLD);
    run_program(program);
    signal_unblock(SIGCHLD);
    ts_tree_delete(tree);
}

int
main(int ac, char *av[])
{
    int opt;
    tommy_hashdyn_init(&shell_vars);

    /* Initialize $? to 0 */
    hash_put(&shell_vars, "?", "0");

    /* Initialize $$ (shell PID) */
    char pid_buf[32];
    snprintf(pid_buf, sizeof(pid_buf), "%d", getpid());
    hash_put(&shell_vars, "$", pid_buf);

    while ((opt = getopt(ac, av, "h")) > 0) {
        switch (opt) {
        case 'h':
            usage(av[0]);
            break;
        }
    }

    parser = ts_parser_new();
    const TSLanguage *bash = tree_sitter_bash();
#define DEFINE_FIELD_ID(name) \
    name##Id = ts_language_field_id_for_name(bash, #name, strlen(#name))
    DEFINE_FIELD_ID(body);
    DEFINE_FIELD_ID(condition);
    DEFINE_FIELD_ID(name);
    DEFINE_FIELD_ID(right);
    DEFINE_FIELD_ID(left);
    DEFINE_FIELD_ID(operator);
    DEFINE_FIELD_ID(value);
    DEFINE_FIELD_ID(redirect);
    DEFINE_FIELD_ID(destination);
    DEFINE_FIELD_ID(variable);
    ts_parser_set_language(parser, bash);

    list_init(&job_list);
    signal_set_handler(SIGCHLD, sigchld_handler);

    bool shouldexit = false;
    for (;;) {
        if (shouldexit)
            break;

        assert(!signal_is_blocked(SIGCHLD));

        char *userinput = NULL;
        if (isatty(0) && av[optind] == NULL) {
            char *prompt = isatty(0) ? build_prompt() : NULL;
            userinput = readline(prompt);
            free(prompt);
            if (userinput == NULL)
                break;
        } else {
            int readfd = 0;
            if (av[optind] != NULL)
                readfd = open(av[optind], O_RDONLY);

            userinput = read_script_from_fd(readfd);
            if (readfd != 0) {
                if (close(readfd) != 0)
                    utils_error("close failed");
            }
            if (userinput == NULL)
                utils_fatal_error("Could not read input");
            shouldexit = true;
        }
        execute_script(userinput);
        free(userinput);
    }

    ts_parser_delete(parser);
    tommy_hashdyn_foreach(&shell_vars, hash_free);
    tommy_hashdyn_done(&shell_vars);
    return EXIT_SUCCESS;
}