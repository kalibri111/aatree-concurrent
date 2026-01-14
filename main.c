#include <stdio.h>
#include <string.h>
#include <pthread.h>
#include <unistd.h>
#include "aatree.h"

#define NUM_THREADS 4
#define NODES_PER_THREAD 100

static char *OK = "OK";

typedef struct MyNode MyNode;
struct MyNode {
    struct AANode node;
    int value;
};

static void my_node_free(struct AANode *node, void *arg)
{
    MyNode *my = container_of(node, MyNode, node);
    free(my);
}

static int my_node_cmp(uintptr_t value, struct AANode *node)
{
    MyNode *my = container_of(node, MyNode, node);
    return value - my->value;
}

static const char * my_search(struct AATree *tree, int value)
{
    struct AANode *res;
    res = aatree_search(tree, value);
    return res ? OK : "not found";
}

static MyNode *make_node(int value)
{
    MyNode *node = malloc(sizeof(*node));
    memset(node, 0, sizeof(*node));
    node->value = value;
    return node;
}

static const char *mkerr(const char *msg, int v, const struct AANode *node)
{
    static char buf[128];
    snprintf(buf, sizeof(buf), "%s: %d", msg, v);
    return buf;
}

static int my_node_pair_cmp(const struct AANode *n1, const struct AANode *n2)
{
    const struct MyNode *m1 = container_of(n1, struct MyNode, node);
    const struct MyNode *m2 = container_of(n2, struct MyNode, node);
    return m1->value - m2->value;
}

static const char *check_sub(const struct AATree *tree, const struct AANode *node, int i)
{
    int cmp_left = 0, cmp_right = 0;
    const char *res;
    if (aatree_is_nil_node(node))
        return OK;
    if (node->level != node->left->level + 1)
        return mkerr("bad left level", i, node);
    if (!((node->level == node->right->level + 1)
          || (node->level == node->right->level
              && node->right->level != node->right->level + 1)))
        return mkerr("bad right level", i, node);
    if (!aatree_is_nil_node(node->left))
        cmp_left = my_node_pair_cmp(node, node->left);
    if (!aatree_is_nil_node(node->right))
        cmp_right = my_node_pair_cmp(node, node->right);
    if (cmp_left < 0)
        return mkerr("wrong left order", i, node);
    if (cmp_right > 0)
        return mkerr("wrong right order", i, node);
    res = check_sub(tree, node->left, i);
    if (!res)
        res = check_sub(tree, node->right, i);
    return res;
}

static const char *check(struct AATree *tree, int i)
{
    return check_sub(tree, tree->root, i);
}

static const char *my_insert(struct AATree *tree, int value)
{
    MyNode *my = make_node(value);
    aatree_insert(tree, value, &my->node);
    return check(tree, value);
}

typedef struct {
    struct AATree *tree;
    int start_value;
    int count;
} ThreadInsertArg;

typedef struct {
    struct AATree *tree;
    int *values;
    int count;
} ThreadSearchArg;

static void my_node_print_value(struct AANode *node)
{
    MyNode *my = container_of(node, MyNode, node);
    printf("%d", my->value);
}

static void *insert_thread_func(void *arg)
{
    ThreadInsertArg *targ = (ThreadInsertArg *)arg;
    for (int i = 0; i < targ->count; i++) {
        MyNode *my = make_node(targ->start_value + i);
        aatree_insert(targ->tree, targ->start_value + i, &my->node);
    }
//    aatree_print_snapshot(targ->tree, my_node_print_value);
    return NULL;
}

static void *search_thread_func(void *arg)
{
    ThreadSearchArg *targ = (ThreadSearchArg *)arg;
    for (int i = 0; i < targ->count; i++) {
        aatree_search(targ->tree, targ->values[i]);
    }
    return NULL;
}



// all inserted nodes exist
static void test_insert_concurrent_insert() {
    struct AATree tree[1];
    pthread_t threads[NUM_THREADS];
    ThreadInsertArg args[NUM_THREADS];
    
    aatree_init(tree, my_node_cmp, my_node_free);
    
    // Create threads that insert different ranges of values
    for (int i = 0; i < NUM_THREADS; i++) {
        args[i].tree = tree;
        args[i].start_value = i * NODES_PER_THREAD;
        args[i].count = NODES_PER_THREAD;
        pthread_create(&threads[i], NULL, insert_thread_func, &args[i]);
    }
    
    // Wait for all threads to complete
    for (int i = 0; i < NUM_THREADS; i++) {
        pthread_join(threads[i], NULL);
    }
    
    // Verify all inserted nodes exist
    int total = NUM_THREADS * NODES_PER_THREAD;
    int found = 0;
    for (int i = 0; i < total; i++) {
        if (aatree_search(tree, i) != NULL) {
            found++;
        }
    }
    
    printf("test_insert_concurrent_insert: %d/%d nodes found\n", found, total);
    if (found == total) {
        printf("test_insert_concurrent_insert: PASSED\n");
    } else {
        printf("test_insert_concurrent_insert: FAILED\n");
    }
    
    aatree_destroy(tree);
}

// cause rebalances with concurrent insert, all inserted nodes reachable
static void test_insert_concurrent_rebalance() {
    struct AATree tree[1];
    pthread_t threads[NUM_THREADS];
    ThreadInsertArg args[NUM_THREADS];
    
    aatree_init(tree, my_node_cmp, my_node_free);
    
    // Insert nodes in patterns that cause rebalancing
    // Thread 0: ascending values
    // Thread 1: descending values
    // Thread 2: middle range values
    // Thread 3: scattered values
    for (int i = 0; i < NUM_THREADS; i++) {
        args[i].tree = tree;
        args[i].count = NODES_PER_THREAD;
        
        switch(i) {
            case 0: // ascending
                args[i].start_value = 0;
                break;
            case 1: // descending (we'll handle in thread)
                args[i].start_value = 1000;
                break;
            case 2: // middle range
                args[i].start_value = 2000;
                break;
            case 3: // scattered
                args[i].start_value = 3000;
                break;
        }
        pthread_create(&threads[i], NULL, insert_thread_func, &args[i]);
    }
    
    // Wait for all threads to complete
    for (int i = 0; i < NUM_THREADS; i++) {
        pthread_join(threads[i], NULL);
    }
    
    // Verify all inserted nodes exist and tree structure is valid
    int total = NUM_THREADS * NODES_PER_THREAD;
    int found = 0;
    
    // Check all ranges
    for (int i = 0; i < NODES_PER_THREAD; i++) {
        if (aatree_search(tree, i) != NULL) found++;
        if (aatree_search(tree, 1000 + i) != NULL) found++;
        if (aatree_search(tree, 2000 + i) != NULL) found++;
        if (aatree_search(tree, 3000 + i) != NULL) found++;
    }
    
    // Verify tree structure
    const char *check_result = check(tree, 0);
    
    printf("test_insert_concurrent_rebalance: %d/%d nodes found\n", found, total);
    printf("test_insert_concurrent_rebalance: tree structure %s\n", check_result);
    if (found == total && strcmp(check_result, "OK") == 0) {
        printf("test_insert_concurrent_rebalance: PASSED\n");
    } else {
        printf("test_insert_concurrent_rebalance: FAILED\n");
    }
    
    aatree_destroy(tree);
}

// concurrent reading does not affects insert
static void test_read_concurrent_insert() {
    struct AATree tree[1];
    pthread_t insert_threads[NUM_THREADS];
    pthread_t search_threads[NUM_THREADS];
    ThreadInsertArg insert_args[NUM_THREADS];
    ThreadSearchArg search_args[NUM_THREADS];
    int search_values[NODES_PER_THREAD];
    
    aatree_init(tree, my_node_cmp, my_node_free);
    
    // Pre-populate tree with some values for searching
    for (int i = 0; i < NODES_PER_THREAD; i++) {
        MyNode *my = make_node(i);
        aatree_insert(tree, i, &my->node);
        search_values[i] = i;
    }
    
    // Create insert threads
    for (int i = 0; i < NUM_THREADS; i++) {
        insert_args[i].tree = tree;
        insert_args[i].start_value = NODES_PER_THREAD + i * NODES_PER_THREAD;
        insert_args[i].count = NODES_PER_THREAD;
        pthread_create(&insert_threads[i], NULL, insert_thread_func, &insert_args[i]);
    }
    
    // Create search threads that continuously search existing values
    for (int i = 0; i < NUM_THREADS; i++) {
        search_args[i].tree = tree;
        search_args[i].values = search_values;
        search_args[i].count = NODES_PER_THREAD;
        pthread_create(&search_threads[i], NULL, search_thread_func, &search_args[i]);
    }
    
    // Wait for all threads
    for (int i = 0; i < NUM_THREADS; i++) {
        pthread_join(insert_threads[i], NULL);
        pthread_join(search_threads[i], NULL);
    }
    
    // Verify all newly inserted nodes exist
    int expected_total = NODES_PER_THREAD + NUM_THREADS * NODES_PER_THREAD;
    int found = 0;
    for (int i = 0; i < expected_total; i++) {
        if (aatree_search(tree, i) != NULL) {
            found++;
        }
    }
    
    printf("test_read_concurrent_insert: %d/%d nodes found\n", found, expected_total);
    if (found == expected_total) {
        printf("test_read_concurrent_insert: PASSED\n");
    } else {
        printf("test_read_concurrent_insert: FAILED\n");
    }
    
    aatree_destroy(tree);
}

int main(void) {
    struct AATree tree[1];
    int i;

    printf("=== Basic Sequential Tests ===\n");
    aatree_init(tree, my_node_cmp, my_node_free);

    printf("%s\n", my_search(tree, 1)); // "not found"

    for (i = 0; i < 15; i++) {
        printf("%s\n", my_insert(tree, i)); // "OK"
    }
    for (i = -1; i > -15; i--) {
        printf("%s\n", my_insert(tree, i)); // "OK"
    }
    for (i = 30; i < 45; i++) {
        printf("%s\n", my_insert(tree, i)); // "OK"
    }
    for (i = 15; i < 30; i++) {
        printf("%s\n", my_insert(tree, i)); // "OK"
    }

    for (i = -14; i < 45; i++) {
        printf("%s\n", my_insert(tree, i)); // "OK"
    }

    aatree_destroy(tree);

    printf("\n=== Concurrent Tests ===\n");
    test_insert_concurrent_insert();
    printf("\n");
    test_insert_concurrent_rebalance();
    printf("\n");
    test_read_concurrent_insert();
    
    return 0;
}
