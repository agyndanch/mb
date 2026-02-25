/*
 * minibash - an open-ended subset of bash
 *
 * Developed by Godmar Back for CS 3214 Fall 2025 
 * Virginia Tech.
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

extern char **environ;

/* These are field ids suitable for use in ts_node_child_by_field_id for certain rules. 
   e.g., to obtain the body of a while loop, you can use:
    TSNode body = ts_node_child_by_field_id(child, bodyId);
*/
static TSFieldId bodyId, redirectId, destinationId, valueId, nameId, conditionId;
static TSFieldId variableId;
static TSFieldId leftId, operatorId, rightId;

static char *input;         // to avoid passing the current input around
static TSParser *parser;    // a singleton parser instance 
static tommy_hashdyn shell_vars;        // a hash table containing the internal shell variables

/* Last exit status, stored as integer and as string in shell_vars["?"] */
static int last_exit_status = 0;

static void handle_child_status(pid_t pid, int status);
static char *read_script_from_fd(int readfd);
static void execute_script(char *script);
static void run_statement(TSNode node);

/* forward declaration for word expansion */
static char *expand_word(TSNode node);


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

/* Possible job status's to use.
 *
 * Some are specific to interactive job control which may not be needed
 * for this assignment.
 */
enum job_status {
    FOREGROUND,     /* job is running in foreground.  Only one job can be
                       in the foreground state. */
    BACKGROUND,     /* job is running in background */
    STOPPED,        /* job is stopped via SIGSTOP */
    NEEDSTERMINAL,  /* job is stopped because it was a background job
                       and requires exclusive terminal access */
    TERMINATED_VIA_EXIT,    /* job terminated via normal exit. */
    TERMINATED_VIA_SIGNAL   /* job terminated via signal. */
};

struct job {
    struct list_elem elem;   /* Link element for jobs list. */
    int     jid;             /* Job id. */
    enum job_status status;  /* Job status. */ 
    int  num_processes_alive;   /* The number of processes that we know to be alive */

    pid_t pgid;              /* Process group id for this job */
    int   exit_status;       /* Exit status of last process in this job */

    /* pid array for all processes in this pipeline */
    pid_t *pids;
    int    npids;
};

/* Utility functions for job list management.
 * We use 2 data structures: 
 * (a) an array jid2job to quickly find a job based on its id
 * (b) a linked list to support iteration
 */
#define MAXJOBS (1<<16)
static struct list job_list;

static struct job *jid2job[MAXJOBS];

/* Return job corresponding to jid */
static struct job *
get_job_from_jid(int jid)
{
    if (jid > 0 && jid < MAXJOBS && jid2job[jid] != NULL)
        return jid2job[jid];

    return NULL;
}

/* Allocate a new job, optionally adding it to the job list. */
static struct job *
allocate_job(bool includeinjoblist)
{
    struct job * job = malloc(sizeof *job);
    job->num_processes_alive = 0;
    job->jid = -1;
    job->pgid = 0;
    job->exit_status = 0;
    job->pids = NULL;
    job->npids = 0;
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

/* Delete a job.
 * This should be called only when all processes that were
 * forked for this job are known to have terminated.
 */
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
    /* add any other job cleanup here. */
    free(job->pids);
    free(job);
}

/*
 * Find which job a pid belongs to by scanning all jobs' pid arrays.
 */
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

/*
 * Update shell_vars["?"] to reflect last_exit_status.
 */
static void
update_exit_status(int status)
{
    last_exit_status = status;
    char buf[32];
    snprintf(buf, sizeof(buf), "%d", status);
    hash_put(&shell_vars, "?", buf);
}

/*
 * Suggested SIGCHLD handler.
 *
 * Call waitpid() to learn about any child processes that
 * have exited or changed status (been stopped, needed the
 * terminal, etc.)
 * Just record the information by updating the job list
 * data structures.  Since the call may be spurious (e.g.
 * an already pending SIGCHLD is delivered even though
 * a foreground process was already reaped), ignore when
 * waitpid returns -1.
 * Use a loop with WNOHANG since only a single SIGCHLD 
 * signal may be delivered for multiple children that have 
 * exited. All of them need to be reaped.
 */
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

/* Wait for all processes in this job to complete, or for
 * the job no longer to be in the foreground.
 *
 * You should call this function from where you wait for
 * jobs started without the &; you would only use this function
 * if you were to implement the 'fg' command (job control only).
 * 
 * Implement handle_child_status such that it records the 
 * information obtained from waitpid() for pid 'child.'
 *
 * If a process exited, it must find the job to which it
 * belongs and decrement num_processes_alive.
 *
 * However, note that it is not safe to call delete_job
 * in handle_child_status because wait_for_job assumes that
 * even jobs with no more num_processes_alive haven't been
 * deallocated.  You should postpone deleting completed
 * jobs from the job list until when your code will no
 * longer touch them.
 *
 * The code below relies on `job->status` having been set to FOREGROUND
 * and `job->num_processes_alive` having been set to the number of
 * processes successfully forked for this job.
 */
static void
wait_for_job(struct job *job)
{
    assert(signal_is_blocked(SIGCHLD));

    while (job->status == FOREGROUND && job->num_processes_alive > 0) {
        int status;

        pid_t child = waitpid(-1, &status, WUNTRACED);

        // When called here, any error returned by waitpid indicates a logic
        // bug in the shell.
        // In particular, ECHILD "No child process" means that there has
        // already been a successful waitpid() call that reaped the child, so
        // there's likely a bug in handle_child_status where it failed to update
        // the "job" status and/or num_processes_alive fields in the required
        // fashion.
        // Since SIGCHLD is blocked, there cannot be races where a child's exit
        // was handled via the SIGCHLD signal handler.
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

    /* Step 1: find which job this pid belongs to */
    struct job *job = find_job_by_pid(pid);
    if (job == NULL)
        return;  /* spurious, ignore */

    /* Step 2 & 3: check what happened and update job state */
    if (WIFEXITED(status)) {
        job->exit_status = WEXITSTATUS(status);
        job->num_processes_alive--;
        if (job->num_processes_alive == 0) {
            if (job->status == FOREGROUND) {
                job->status = TERMINATED_VIA_EXIT;
                /* update $? for foreground job when last process exits */
                update_exit_status(job->exit_status);
            } else {
                job->status = TERMINATED_VIA_EXIT;
            }
        }
    } else if (WIFSIGNALED(status)) {
        job->exit_status = 128 + WTERMSIG(status);
        job->num_processes_alive--;
        if (job->num_processes_alive == 0) {
            if (job->status == FOREGROUND) {
                job->status = TERMINATED_VIA_SIGNAL;
                update_exit_status(job->exit_status);
            } else {
                job->status = TERMINATED_VIA_SIGNAL;
            }
        }
    } else if (WIFSTOPPED(status)) {
        job->status = STOPPED;
    }
}

/*
 * Expand a single tree-sitter node into its string value.
 * Handles: word, string, simple_expansion ($VAR, $?), concatenation.
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
            /* No named children: pure literal (possibly whitespace-only).
             * Strip the outer quote characters. */
            return ts_extract_node_text_from_to(input, node, 1, 1);
        }
        /* Has named children: could be expansions mixed with literal content.
         * Walk all children (including anonymous string_content tokens). */
        char *result = strdup("");
        uint32_t n = ts_node_child_count(node);
        for (uint32_t i = 0; i < n; i++) {
            TSNode child = ts_node_child(node, i);
            const char *ctype = ts_node_type(child);
            /* Skip the surrounding quote characters */
            if (!ts_node_is_named(child)) {
                /* Anonymous node: check if it's a quote delimiter */
                char first = input[ts_node_start_byte(child)];
                if (first == '"') continue;
                /* Other anonymous content: include as-is */
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

    if (strcmp(type, "simple_expansion") == 0) {
        /* $VAR, $?, $#, etc. */
        TSNode varnode = ts_node_named_child(node, 0);
        if (ts_node_is_null(varnode)) {
            return strdup("");
        }
        char *varname = ts_extract_node_text(input, varnode);
        const char *val = hash_get(&shell_vars, varname);
        if (val == NULL)
            val = getenv(varname);
        char *result = val ? strdup(val) : strdup("");
        free(varname);
        return result;
    }

    if (strcmp(type, "expansion") == 0) {
        /* ${VAR} */
        TSNode varnode = ts_node_child_by_field_id(node, variableId);
        if (ts_node_is_null(varnode)) {
            return strdup("");
        }
        char *varname = ts_extract_node_text(input, varnode);
        const char *val = hash_get(&shell_vars, varname);
        if (val == NULL) val = getenv(varname);
        char *result = val ? strdup(val) : strdup("");
        free(varname);
        return result;
    }

    if (strcmp(type, "concatenation") == 0) {
        char *result = strdup("");
        uint32_t n = ts_node_child_count(node);
        for (uint32_t i = 0; i < n; i++) {
            TSNode child = ts_node_child(node, i);
            if (!ts_node_is_named(child)) continue;
            char *part = expand_word(child);
            if (part) {
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
 * command has: name (command_name) and arguments.
 * Returns a NULL-terminated array. Caller must free each element and the array.
 */
static char **
build_argv(TSNode cmd_node, int *argc_out)
{
    /* first child (named) is command_name, rest are arguments */
    uint32_t nchildren = ts_node_named_child_count(cmd_node);

    /* allocate max possible + 1 for NULL */
    char **argv = malloc((nchildren + 1) * sizeof(char *));
    int argc = 0;

    for (uint32_t i = 0; i < nchildren; i++) {
        TSNode child = ts_node_named_child(cmd_node, i);
        TSSymbol sym = ts_node_symbol(child);

        /* skip variable_assignment prefix nodes (env vars before command) */
        if (sym == sym_variable_assignment)
            continue;

        if (i == 0) {
            /* command_name node: its first named child is the actual name */
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
 * Execute a builtin. Returns true if it was a builtin, false otherwise.
 * Sets *exit_val to the builtin's exit code.
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
        /* Flush and exit */
        exit(code);
    }

    return false;
}

/*
 * Spawn a single command using posix_spawnp.
 * pgid: process group to join (0 = create new group with own pid as pgid)
 * Returns the pid of the spawned process, or -1 on error.
 */
static pid_t
spawn_command(char **argv, pid_t pgid)
{
    posix_spawn_file_actions_t file_actions;
    posix_spawnattr_t attr;

    posix_spawn_file_actions_init(&file_actions);
    posix_spawnattr_init(&attr);

    /* Set process group */
    posix_spawnattr_setpgroup(&attr, pgid);
    short flags = POSIX_SPAWN_SETPGROUP;
    posix_spawnattr_setflags(&attr, flags);

    pid_t pid;
    int ret = posix_spawnp(&pid, argv[0], &file_actions, &attr, argv, environ);

    posix_spawn_file_actions_destroy(&file_actions);
    posix_spawnattr_destroy(&attr);

    if (ret != 0) {
        fprintf(stderr, "minibash: %s: %s\n", argv[0], strerror(ret));
        return -1;
    }
    return pid;
}

/*
 * Run a simple command (no pipeline, no redirection).
 * background: whether to run in background.
 */
static void
run_simple_command(TSNode cmd_node, bool background)
{
    int argc;
    char **argv = build_argv(cmd_node, &argc);

    if (argc == 0) {
        free_argv(argv);
        return;
    }

    /* Try builtin first */
    int builtin_exit;
    if (try_builtin(argv, &builtin_exit)) {
        update_exit_status(builtin_exit);
        free_argv(argv);
        return;
    }

    /* External command */
    struct job *job = allocate_job(true);
    job->status = background ? BACKGROUND : FOREGROUND;

    pid_t pid = spawn_command(argv, 0);  /* 0 = new process group */
    free_argv(argv);

    if (pid == -1) {
        /* spawn failed */
        update_exit_status(127);
        delete_job(job, true);
        return;
    }

    /* record the pid in the job */
    job->pgid = pid;  /* first process becomes pgid leader */
    job->pids = malloc(sizeof(pid_t));
    job->pids[0] = pid;
    job->npids = 1;
    job->num_processes_alive = 1;

    if (!background) {
        wait_for_job(job);
        /* collect exit status from job */
        int exit_code = job->exit_status;
        delete_job(job, true);
        update_exit_status(exit_code);
    }
    /* background: job stays in list, cleaned up by sigchld handler */
}

/*
 * Run a statement node. Dispatches based on node type.
 */
static void
run_statement(TSNode node)
{
    TSSymbol sym = ts_node_symbol(node);

    if (sym == sym_comment) {
        return;
    }

    if (sym == sym_command) {
        run_simple_command(node, false);
        return;
    }

    /* Background: the grammar wraps things in a list node with & */
    /* Actually in tree-sitter bash, background is represented by an
     * anonymous '&' child at the statement level, but the node itself
     * is still a 'command'. We check for this in run_program below. */

    printf("node type `%s` not implemented\n", ts_node_type(node));
}

/*
 * Run a program.
 *
 * A program's named children are various types of statements which 
 * you can start implementing here.
 */
static void 
run_program(TSNode program)
{
    uint32_t n = ts_node_child_count(program);
    for (uint32_t i = 0; i < n; i++) {
        TSNode child = ts_node_child(program, i);

        if (!ts_node_is_named(child))
            continue;  /* skip anonymous tokens (handled below) */

        TSSymbol sym = ts_node_symbol(child);

        /* Check if the next sibling is '&' for background */
        bool background = false;
        if (i + 1 < n) {
            TSNode next = ts_node_child(program, i + 1);
            if (!ts_node_is_named(next)) {
                uint32_t start = ts_node_start_byte(next);
                if (input[start] == '&') {
                    background = true;
                    i++;  /* consume the '&' token */
                }
            }
        }

        if (sym == sym_comment) {
            continue;
        }

        if (sym == sym_command) {
            run_simple_command(child, background);
            /* reap finished background jobs */
            struct list_elem *e = list_begin(&job_list);
            while (e != list_end(&job_list)) {
                struct list_elem *next_e = list_next(e);
                struct job *j = list_entry(e, struct job, elem);
                if (j->status != FOREGROUND && j->status != BACKGROUND &&
                    j->num_processes_alive == 0) {
                    delete_job(j, true);
                }
                e = next_e;
            }
            continue;
        }

        printf("node type `%s` not implemented\n", ts_node_type(child));
    }
}

/*
 * Read a script from this (already opened) file descriptor,
 * return a newly allocated buffer.
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

    /* Process command-line arguments. See getopt(3) */
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


    /* Read/eval loop. */
    bool shouldexit = false;
    for (;;) {
        if (shouldexit)
            break;

        /* If you fail this assertion, you were about to enter readline()
         * while SIGCHLD is blocked.  This means that your shell would be
         * unable to receive SIGCHLD signals, and thus would be unable to
         * wait for background jobs that may finish while the
         * shell is sitting at the prompt waiting for user input.
         */
        assert(!signal_is_blocked(SIGCHLD));

        char *userinput = NULL;
        /* Do not output a prompt unless shell's stdin is a terminal */
        if (isatty(0) && av[optind] == NULL) {
            char *prompt = isatty(0) ? build_prompt() : NULL;
            userinput = readline(prompt);
            free (prompt);
            if (userinput == NULL)
                break;
        } else {
            int readfd = 0;
            if (av[optind] != NULL)
                readfd = open(av[optind], O_RDONLY);

            userinput = read_script_from_fd(readfd);
            close(readfd);
            if (userinput == NULL)
                utils_fatal_error("Could not read input");
            shouldexit = true;
        }
        execute_script(userinput);
        free(userinput);
    }

    /* 
     * Even though it is not necessary for the purposes of resource
     * reclamation, we free all allocated data structure prior to exiting
     * so that we can use valgrind's leak checker.
     */
    ts_parser_delete(parser);
    tommy_hashdyn_foreach(&shell_vars, hash_free);
    tommy_hashdyn_done(&shell_vars);
    return EXIT_SUCCESS;
}