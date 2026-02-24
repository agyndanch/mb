/* This file courtesy GPT o3; comments added by GPT-5 */
#ifndef TOMMY_HELPERS_H
#define TOMMY_HELPERS_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "tommyds/tommyhashdyn.h"
#include "tommyds/tommyhash.h"      /* tommy_hash_u32() */

/* user payload ----------------------------------------------------------- */
typedef struct entry {
    tommy_node node;
    char *key;
    char *val;
} entry;

/* helpers ---------------------------------------------------------------- */
static tommy_hash_t str_hash(const char *s)
{
    return tommy_hash_u32(0 /*seed*/, s, strlen(s));
}

/* tommy_search_func: return 0 when *obj* matches *arg* */
static int str_cmp(const void *arg, const void *obj)
{
    return strcmp((const char *)arg, ((const entry *)obj)->key);
}

/* wrapped API ------------------------------------------------------------ */
/**
 * @brief Inserts or updates a key-value pair in the hash table.
 * 
 * If the key already exists, the corresponding value is updated.
 * Otherwise, a new entry is created.
 * 
 * @param ht The hash table.
 * @param k The key.
 * @param v The value.
 */
static void
hash_put(tommy_hashdyn* ht, const char* k, const char* v)
{
    tommy_hash_t h = str_hash(k);

    // Look for an existing entry
    entry* old = tommy_hashdyn_search(ht, str_cmp, k, h);
    if (old) {
        // update in place
        char* nv = strdup(v);
        free(old->val);
        old->val = nv;
        return;
    }

    // otherwise insert a new one
    entry* e = malloc(sizeof *e);
    e->key = strdup(k);
    e->val = strdup(v);
    tommy_hashdyn_insert(ht, &e->node, e, h);
}

/**
 * @brief Retrieves the value associated with a key.
 * 
 * @param ht The hash table.
 * @param k The key.
 * @return The value associated with the key, or NULL if the key is not found.
 */
static const char *
hash_get(tommy_hashdyn *ht, const char *k)
{
    entry *e = tommy_hashdyn_search(ht, str_cmp, k, str_hash(k));
    return e ? e->val : NULL;
}

/**
 * @brief Deletes a key-value pair from the hash table.
 * 
 * @param ht The hash table.
 * @param k The key to delete.
 */
static void
hash_del(tommy_hashdyn *ht, const char *k)
{
    entry *e = tommy_hashdyn_remove(ht, str_cmp, k, str_hash(k));
    if (e) {                         /* found → free payload */
        free(e->key);
        free(e->val);
        free(e);
    }
}

/**
 * @brief Frees the memory allocated for a hash table entry.
 * 
 * @param _e A pointer to the entry to be freed.
 */
static void
hash_free(void *_e)
{
    entry *e = _e;
    free(e->key);
    free(e->val);
    free(e);
}
#endif /* TOMMY_HELPERS_H */
