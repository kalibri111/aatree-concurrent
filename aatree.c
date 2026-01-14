/*
 * AA-Tree - Binary tree with embeddable nodes.
 *
 * Copyright (c) 2007-2009  Marko Kreen, Skype Technologies OÜ
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

/*
 * Self-balancing binary tree.
 *
 * Here is an implementation of AA-tree (Arne Andersson tree)
 * which is simplification of Red-Black tree.
 *
 * Red-black tree has following properties that must be kept:
 * 1. A node is either red or black.
 * 2. The root is black.
 * 3. All leaves (NIL nodes) are black.
 * 4. Both childen of red node are black.
 * 5. Every path from root to leaf contains same number of black nodes.
 *
 * AA-tree adds additional property:
 * 6. Red node can exist only as a right node.
 *
 * Red-black tree properties quarantee that the longest path is max 2x longer
 * than shortest path (B-R-B-R-B-R-B vs. B-B-B-B) thus the tree will be roughly
 * balanced.  Also it has good worst-case guarantees for insertion and deletion,
 * which makes it good tool for real-time applications.
 *
 * AA-tree removes most special cases from RB-tree, thus making resulting
 * code lot simpler.  It requires slightly more rotations when inserting
 * and deleting but also keeps the tree more balanced.
 */


#include "aatree.h"

#include <stddef.h>   /* for NULL */
#include <stdio.h>    /* for printf */

typedef struct AATree Tree;
typedef struct AANode Node;

/*
 * NIL node
 */
#define NIL ((struct AANode *)&_nil)
static const struct AANode _nil = { NIL, NIL, NIL, 0, Open };

/*
 * Concurrency
 */
static void node_atomic_set_left(struct AANode* self, Node* value) {
    atomic_store_explicit(&self->left, value, memory_order_seq_cst);
}

static void node_atomic_set_right(Node* self, Node* value) {
    atomic_store_explicit(&self->right, value, memory_order_seq_cst);
}

static void node_atomic_set_parent(Node* self, Node* value) {
    atomic_store_explicit(&self->parent, value, memory_order_seq_cst);
}

static void node_atomic_set_level(Node* self, int level) {
    atomic_store_explicit(&self->level, level, memory_order_seq_cst);
}

static void node_atomic_set_state(Node* self, enum AANodeState state) {
    atomic_store_explicit(&self->state, state, memory_order_seq_cst);
//    switch (state) {
//        case Open:
//            printf("Open\n");
//            break;
//        case Insert:
//            printf("Insert\n");
//            break;
//        case Balancing:
//            printf("Balancing\n");
//            break;
//    }

}

static Node* node_atomic_get_left(Node* self) {
    return atomic_load_explicit(&self->left, memory_order_seq_cst);
}

static Node* node_atomic_get_right(Node* self) {
    return atomic_load_explicit(&self->right, memory_order_seq_cst);
}

static Node* node_atomic_get_parent(Node* self) {
    return atomic_load_explicit(&self->parent, memory_order_seq_cst);
}

static int node_atomic_get_level(Node* self) {
    return atomic_load_explicit(&self->level, memory_order_seq_cst);
}

static int node_atomic_get_state(Node* self) {
    return atomic_load_explicit(&self->state, memory_order_seq_cst);
}

/*
 * Rebalancing.  AA-tree needs only 2 operations
 * to keep the tree balanced.
 */
static inline bool atomic_rebalancing_state_compare_exchange_weak(Node* node, enum AANodeState state) {
    enum AANodeState expected_open = Open;

    if (atomic_compare_exchange_weak(&node->state, &state, Balancing) ||
        atomic_compare_exchange_weak(&node->state, &expected_open, Balancing)) {
        return true;
    }
    return false;
}
/*
 * X might be participant of rebalancing up to 2 parents.
 * We need to acquire: x, parent, grandparent, children, and grandchildren
 * that will be modified during skew/split operations.
 */
#define MAX_ACQUIRED_NODES 10
static inline bool rebalancing_acquire(Node *x, Node *acquired[MAX_ACQUIRED_NODES], enum AANodeState state_from) {
    Node *x_parent = node_atomic_get_parent(x);
    Node *x_parent_parent = node_atomic_get_parent(node_atomic_get_parent(x));
    Node *x_left = node_atomic_get_left(x);
    Node *x_right = node_atomic_get_right(x);
    Node *x_left_right = (x_left != NIL) ? node_atomic_get_right(x_left) : NIL;
    Node *x_right_left = (x_right != NIL) ? node_atomic_get_left(x_right) : NIL;
    Node *x_right_right = (x_right != NIL) ? node_atomic_get_right(x_right) : NIL;

    for (int i = 0; i < MAX_ACQUIRED_NODES; i++) {
        acquired[i] = NIL;
    }

    /* Helper function to check if node is already acquired */
    #define is_already_acquired(node, count) ({ \
        bool found = false; \
        for (int j = 0; j < (count); j++) { \
            if (acquired[j] == (node)) { \
                found = true; \
                break; \
            } \
        } \
        found; \
    })

    int acq_count = 0;

    /* Acquire x */
    if (!atomic_rebalancing_state_compare_exchange_weak(x, state_from)) {
        return false;
    }
    acquired[acq_count++] = x;

    /* Acquire parent */
    if (x_parent != NIL && !is_already_acquired(x_parent, acq_count)) {
        if (!atomic_rebalancing_state_compare_exchange_weak(x_parent, state_from)) {
            goto release_and_fail;
        }
        acquired[acq_count++] = x_parent;
    }

    /* Acquire grandparent */
    if (x_parent_parent != NIL && !is_already_acquired(x_parent_parent, acq_count)) {
        if (!atomic_rebalancing_state_compare_exchange_weak(x_parent_parent, state_from)) {
            goto release_and_fail;
        }
        acquired[acq_count++] = x_parent_parent;
    }

    /* Acquire left child */
    if (x_left != NIL && !is_already_acquired(x_left, acq_count)) {
        if (!atomic_rebalancing_state_compare_exchange_weak(x_left, state_from)) {
            goto release_and_fail;
        }
        acquired[acq_count++] = x_left;
    }

    /* Acquire right child */
    if (x_right != NIL && !is_already_acquired(x_right, acq_count)) {
        if (!atomic_rebalancing_state_compare_exchange_weak(x_right, state_from)) {
            goto release_and_fail;
        }
        acquired[acq_count++] = x_right;
    }

    /* Acquire grandchildren that will be modified in rotations */
    if (x_left_right != NIL && !is_already_acquired(x_left_right, acq_count)) {
        if (!atomic_rebalancing_state_compare_exchange_weak(x_left_right, state_from)) {
            goto release_and_fail;
        }
        acquired[acq_count++] = x_left_right;
    }

    if (x_right_left != NIL && !is_already_acquired(x_right_left, acq_count)) {
        if (!atomic_rebalancing_state_compare_exchange_weak(x_right_left, state_from)) {
            goto release_and_fail;
        }
        acquired[acq_count++] = x_right_left;
    }

    if (x_right_right != NIL && !is_already_acquired(x_right_right, acq_count)) {
        if (!atomic_rebalancing_state_compare_exchange_weak(x_right_right, state_from)) {
            goto release_and_fail;
        }
        acquired[acq_count++] = x_right_right;
    }

    #undef is_already_acquired
    return true;

    release_and_fail:
    for (int i = 0; i < MAX_ACQUIRED_NODES; i++) {
        if (acquired[i] != NIL) {
            node_atomic_set_state(acquired[i], Open);
        }
    }
    return false;
}

static inline void rebalancing_release(Node* acquired[MAX_ACQUIRED_NODES]) {
    for (int i = 0; i < MAX_ACQUIRED_NODES; ++i) {
        if (acquired[i] != NIL) {
            node_atomic_set_state(acquired[i], Open);
        }
    }
}

/*
 * Fix red on left.
 *
 *     X          Y
 *    /     -->    \
 *   Y              X
 *    \            /
 *     a          a
 */
static inline Node * skew(Node *x)
{
    Node *y = node_atomic_get_left(x);
    int x_level = node_atomic_get_level(x);
    int y_level = node_atomic_get_level(y);
    if (x_level == y_level && x != NIL) {
        Node *y_right = node_atomic_get_right(y);
        node_atomic_set_left(x, y_right);
        if (y_right != NIL) {
            node_atomic_set_parent(y_right, x);
        }
        node_atomic_set_right(y, x);
        /* Update parent pointers - y is new root of subtree */
        Node *x_parent = node_atomic_get_parent(x);
        node_atomic_set_parent(y, x_parent);
        node_atomic_set_parent(x, y);
        /* we are done */
        return y;
    }
    return x;
}

/*
 * Fix 2 reds on right.
 *
 *    X                Y
 *     \              / \
 *      Y      -->   X   Z
 *     / \            \
 *    a   Z            a
 */
static inline Node * split(Node *x)
{
    Node *y = node_atomic_get_right(x);
    Node *y_right = node_atomic_get_right(y);
    int x_level = node_atomic_get_level(x);
    int y_right_level = node_atomic_get_level(y_right);
    if (x_level == y_right_level && x != NIL) {
        Node *y_left = node_atomic_get_left(y);
        node_atomic_set_right(x, y_left);
        if (y_left != NIL) {
            node_atomic_set_parent(y_left, x);
        }
        node_atomic_set_left(y, x);
        node_atomic_set_level(y, node_atomic_get_level(y) + 1);
        /* Update parent pointers - y is new root of subtree */
        Node *x_parent = node_atomic_get_parent(x);
        node_atomic_set_parent(y, x_parent);
        node_atomic_set_parent(x, y);

        return y;
    }
    return x;
}

/* insert is easy */
static Node *rebalance_on_insert(Node *current)
{
    Node* new_head;
    Node* acquired[MAX_ACQUIRED_NODES];

    while (true) {
        if (rebalancing_acquire(current, acquired, Insert))
            break;
    }

    /* Apply skew and split */
    Node *skewed = skew(current);
    new_head = split(skewed);

    /* Release all nodes that were in the acquired array */
    rebalancing_release(acquired);

    return new_head;
}

/* remove is bit more tricky */
static Node *rebalance_on_remove(Node *current)
{
    enum AANodeState expected;
    Node* acquired[MAX_ACQUIRED_NODES];

    /*
     * Removal can create a gap in levels,
     * fix it by lowering current->level.
     */

    /* announce rebalancing by CAS */
    if (current != NIL) {
        while (true) {
            if (rebalancing_acquire(current, acquired, Open))
                break;
        }
    }

    Node *left_node = node_atomic_get_left(current);
    Node *right_node = node_atomic_get_right(current);
    int left_level = node_atomic_get_level(left_node);
    int right_level = node_atomic_get_level(right_node);
    int current_level = node_atomic_get_level(current);

    if (left_level < current_level - 1
        || right_level < current_level - 1)
    {
        node_atomic_set_level(current, current_level - 1);
        current_level--;

        /* if ->right is red, change it's level too */
        right_level = node_atomic_get_level(right_node);
        if (right_level > current_level)
            node_atomic_set_level(right_node, current_level);

        /* reshape, ask Arne about those */
        current = skew(current);
        right_node = node_atomic_get_right(current);
        node_atomic_set_right(current, skew(right_node));
        right_node = node_atomic_get_right(current);
        Node *right_right = node_atomic_get_right(right_node);
        node_atomic_set_right(right_node, skew(right_right));
        current = split(current);  /* State needs to follow current through split too */
        right_node = node_atomic_get_right(current);
        node_atomic_set_right(current, split(right_node));
    }

    rebalancing_release(acquired);

    return current;
}

/*
 * Recursive insertion
 */

static Node * insert_sub(Tree *tree, Node *current, Node *prev, uintptr_t value, Node *node)
{
    int cmp;

    if (current == NIL) {
        enum AANodeState expected = Open;

        /*
         * Retry insert if acquiring node failed.
         */
        Assert(node->state == Open);

        if (prev != NIL && !atomic_compare_exchange_weak(&prev->state, &expected, Insert)) {
            printf("fallback\n");
            return NIL;
        }

        /*
         * Init node as late as possible, to avoid corrupting
         * the tree in case it is already added.
         */
        node_atomic_set_parent(node, NIL);
        node_atomic_set_left(node, NIL);
        node_atomic_set_right(node, NIL);
        node_atomic_set_level(node, 1);

        atomic_fetch_add(&tree->count, 1);

        return node;
    }

    /* recursive insert */

    cmp = tree->node_cmp(value, current);
    if (cmp > 0) {
        Node* current_right = node_atomic_get_right(current);

        if (current_right == current) {
            printf("broken\n");
            abort();
        }

        Node* tmp = insert_sub(tree, current_right, current, value, node);

        if (tmp == NIL) {
            /*
             * CAS fail retry
             */
            return NIL;
        }

        if (tmp != current_right) {
            node_atomic_set_right(current, tmp);
            node_atomic_set_parent(tmp, current);
        }

    } else if (cmp < 0) {
        Node* current_left = node_atomic_get_left(current);

        // debug
        if (current_left == current) {
            printf("broken\n");
            abort();
        }

        Node* tmp = insert_sub(tree, current_left, current, value, node);

        if (tmp == NIL) {
            /*
             * CAS fail retry
             */
            return NIL;
        }

        if (tmp != current_left) {
            node_atomic_set_left(current, tmp);
            node_atomic_set_parent(tmp, current);
        }

    } else {
        /* already exists? */
        return current;
    }

    return rebalance_on_insert(current);
}

void aatree_insert(Tree *tree, uintptr_t value, Node *node)
{
    /* Ensure node is in Open state before insertion */
    node_atomic_set_state(node, Open);
    
    /* Acquire write lock - serializes insertions but keeps internal algorithm lock-free */
    pthread_rwlock_wrlock(&tree->rw_lock);
    
    while (true) {
        Node* old_root = atomic_load_explicit(&tree->root, memory_order_acquire);
        Node* new_root = insert_sub(tree, old_root, NIL, value, node);
        
        if (new_root == NIL) {
            /* CAS failed in insert_sub, retry */
            continue;
        }
        
        /* Update root */
        atomic_store_explicit(&tree->root, new_root, memory_order_release);
        break;
    }
    
    pthread_rwlock_unlock(&tree->rw_lock);
}

/*
 * Recursive removal
 */

/* remove_sub could be used for that, but want to avoid comparisions */
static Node *steal_leftmost(Tree *tree, Node *current, Node **save_p)
{
    Node *left = node_atomic_get_left(current);
    if (left == NIL) {
        *save_p = current;
        return node_atomic_get_right(current);
    }

    node_atomic_set_left(current, steal_leftmost(tree, left, save_p));
    return rebalance_on_remove(current);
}

/* drop this node from tree */
static Node *drop_this_node(Tree *tree, Node *old)
{
    Node *new = NIL;
    Node *left = node_atomic_get_left(old);
    Node *right = node_atomic_get_right(old);

    if (left == NIL)
        new = right;
    else if (right == NIL)
        new = left;
    else {
        /*
         * Picking nearest from right is better than from left,
         * due to asymmetry of the AA-tree.  It will result in
         * less tree operations in the long run,
         */
        node_atomic_set_right(old, steal_leftmost(tree, right, &new));

        /* take old node's place */
        *new = *old;
    }

    /* cleanup for old node */
    if (tree->release_cb)
        tree->release_cb(old, tree);

    int old_count = atomic_load(&tree->count);
    atomic_store(&tree->count, old_count - 1);

    return new;
}

static Node *remove_sub(Tree *tree, Node *current, uintptr_t value)
{
    int cmp;

    /* not found? */
    if (current == NIL)
        return current;

    cmp = tree->node_cmp(value, current);
    if (cmp > 0) {
        Node *right = node_atomic_get_right(current);
        node_atomic_set_right(current, remove_sub(tree, right, value));
    } else if (cmp < 0) {
        Node *left = node_atomic_get_left(current);
        node_atomic_set_left(current, remove_sub(tree, left, value));
    } else {
        current = drop_this_node(tree, current);
    }

    return rebalance_on_remove(current);
}

void aatree_remove(Tree *tree, uintptr_t value)
{
    tree->root = remove_sub(tree, tree->root, value);
}

/*
 * Walking all nodes
 */

static void walk_sub(Node *current, enum AATreeWalkType wtype,
                     aatree_walker_f walker, void *arg)
{
    Node* current_left = node_atomic_get_left(current);
    Node* current_right = node_atomic_get_right(current);

    if (current == NIL)
        return;

    switch (wtype) {
        case AA_WALK_IN_ORDER:
            walk_sub(current_left, wtype, walker, arg);
            walker(current, arg);
            walk_sub(current_right, wtype, walker, arg);
            break;
        case AA_WALK_POST_ORDER:
            walk_sub(current_left, wtype, walker, arg);
            walk_sub(current_right, wtype, walker, arg);
            walker(current, arg);
            break;
        case AA_WALK_PRE_ORDER:
            walker(current, arg);
            walk_sub(current_left, wtype, walker, arg);
            walk_sub(current_right, wtype, walker, arg);
            break;
    }
}

/* walk tree in correct order */
void aatree_walk(Tree *tree, enum AATreeWalkType wtype, aatree_walker_f walker, void *arg)
{
    walk_sub(tree->root, wtype, walker, arg);
}

/* walk tree in bottom-up order, so that walker can destroy the nodes */
void aatree_destroy(Tree *tree)
{
    walk_sub(tree->root, AA_WALK_POST_ORDER, tree->release_cb, tree);

    /* reset tree */
    tree->root = NIL;
    tree->count = 0;
    pthread_rwlock_destroy(&tree->rw_lock);
}

/* prepare tree */
void aatree_init(Tree *tree, aatree_cmp_f cmpfn, aatree_walker_f release_cb)
{
    tree->root = NIL;
    tree->count = 0;
    tree->node_cmp = cmpfn;
    tree->release_cb = release_cb;
    pthread_rwlock_init(&tree->rw_lock, NULL);
}

/*
 * search function
 */
Node *aatree_search(Tree *tree, uintptr_t value)
{
    /* Acquire read lock - allows concurrent readers */
    pthread_rwlock_rdlock(&tree->rw_lock);
    
    Node *current = atomic_load_explicit(&tree->root, memory_order_acquire);

    /* Traverse tree */
    while (current != NIL) {
        int cmp = tree->node_cmp(value, current);
        if (cmp > 0)
            current = node_atomic_get_right(current);
        else if (cmp < 0)
            current = node_atomic_get_left(current);
        else {
            pthread_rwlock_unlock(&tree->rw_lock);
            return current;
        }
    }
    
    pthread_rwlock_unlock(&tree->rw_lock);
    return NULL;
}

/*
 * Print tree snapshot with state information (thread-safe)
 */

static const char* state_to_string(enum AANodeState state)
{
    switch (state) {
        case Open: return "Open";
        case Insert: return "Insert";
        case Balancing: return "Balancing";
        default: return "Unknown";
    }
}

static void print_node_snapshot(Node *node, void (*value_printer)(Node *), int depth, const char* prefix, int* node_count)
{
    if (node == NIL) {
        return;
    }

    /* Atomically read all node properties for consistent snapshot */
    Node *left = node_atomic_get_left(node);
    Node *right = node_atomic_get_right(node);
    Node *parent = node_atomic_get_parent(node);
    int level = node_atomic_get_level(node);
    enum AANodeState state = node_atomic_get_state(node);

    (*node_count)++;

    /* Print indentation */
    for (int i = 0; i < depth; i++) {
        printf("  ");
    }

    /* Print node information */
    printf("%s[Node@%p] level=%d state=%s parent=%p",
           prefix, (void*)node, level, state_to_string(state), (void*)parent);

    /* If value printer provided, call it */
    if (value_printer) {
        printf(" value=");
        value_printer(node);
    }
    printf("\n");

    /* Recursively print children */
    if (left != NIL) {
        print_node_snapshot(left, value_printer, depth + 1, "L:", node_count);
    }
    if (right != NIL) {
        print_node_snapshot(right, value_printer, depth + 1, "R:", node_count);
    }
}

void aatree_print_snapshot(struct AATree *tree, void (*value_printer)(struct AANode *))
{
    int count = atomic_load_explicit(&tree->count, memory_order_seq_cst);
    int printed_nodes = 0;

    printf("\n=== AA-Tree Snapshot ===\n");
    printf("Tree root: %p\n", (void*)tree->root);
    printf("Node count: %d\n", count);
    printf("========================\n");

    if (tree->root == NIL) {
        printf("(empty tree)\n");
    } else {
        print_node_snapshot(tree->root, value_printer, 0, "ROOT:", &printed_nodes);
    }

    printf("========================\n");
    printf("Printed %d nodes\n", printed_nodes);
    printf("\n");
}

