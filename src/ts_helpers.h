#ifndef _TS_HELPERS
#define _TS_HELPERS

/*
 * A small collection of helper routines for using the tree sitter library
 */

/*
 * Print information about a TSNode, prefixed with label
 */
static void 
ts_print_node_info(TSNode node, const char *label)
{
    TSPoint start = ts_node_start_point(node);
    TSPoint end = ts_node_end_point(node);

    printf("Info for %s\n", label);
    printf("Node type: %s\n", ts_node_type(node));
    printf("Start: row %u, column %u\n", start.row, start.column);
    printf("End: row %u, column %u\n", end.row, end.column);
    printf("Child count: %u\n", ts_node_child_count(node));
    printf("Named child count: %u\n", ts_node_named_child_count(node));
    printf("Is named: %s\n", ts_node_is_named(node) ? "yes" : "no");
    printf("Is extra: %s\n", ts_node_is_extra(node) ? "yes" : "no");
}

/* 
 * Determine the length of the actual text corresponding to
 * a TSNode (without extracting it).
 */
static uint32_t
ts_extract_node_length(TSNode node) 
{
    uint32_t start_byte = ts_node_start_byte(node);
    uint32_t end_byte = ts_node_end_byte(node);
    return end_byte - start_byte;
}

/*
 * Extract the actual text in the input corresponding to
 * a TSNode, but add soffset to the start and subtract eoffset
 * from the end.
 */
static char *
ts_extract_node_text_from_to(char *source_text, TSNode node, int soffset, int eoffset) 
{
    uint32_t start_byte = ts_node_start_byte(node) + soffset;
    uint32_t end_byte = ts_node_end_byte(node) - eoffset;
    return strndup(source_text + start_byte, end_byte - start_byte);
}

/*
 * Extract the actual text in the input for a given TSNode
 * Return a newly allocated zero-terminated string of which
 * the caller must take ownership.
 */
static char *
ts_extract_node_text(char *source_text, TSNode node) 
{
    return ts_extract_node_text_from_to(source_text, node, 0, 0);
}

/*
 * For TSNodes that correspond to a single char, extract that char
 */
static char
ts_extract_single_node_char(char *source_text, TSNode node) 
{
    return source_text[ts_node_start_byte(node)];
}

/*
 * Peek at the parsed node text corresponding to a node.
 * Does not extract it. Does not return a zero-terminated string.
 * Use cautiously.
 */
static char *
ts_peek_at_node_text(char *source_text, TSNode node) 
{
    uint32_t start_byte = ts_node_start_byte(node);
    return source_text + start_byte;
}

#endif /* _TS_HELPERS */
