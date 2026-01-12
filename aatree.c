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

/*
 * X might be participant of rebalancing up to 2 parents.
 * Start rebalancing x iff:
 * 1) x state transints Open -> Rebalancing
 * 2) x parent not transits Open -> Rebalancing
 * 3) x parent parent transits Open -> Rebalancing
 * 4) x left and right child transits Open -> Balancing for skew and split
 */
static inline bool rebalancing_acquire(Node *x, Node *acquired[5]) {
    enum AANodeState expected = Open;
    Node *x_parent = node_atomic_get_parent(x);
    Node *x_parent_parent = node_atomic_get_parent(node_atomic_get_parent(x));
    Node *x_left = node_atomic_get_left(x);
    Node *x_right = node_atomic_get_right(x);

    for (int i = 0; i < 5; i++) {
        acquired[i] = NIL;
    }

    expected = Open;
    if (!atomic_compare_exchange_weak(&x->state, &expected, Balancing)) {
        return false;
    }
    acquired[0] = x;

    if (x_parent != NIL && x_parent != x) {
        /* Check if x_parent is different from x (can be same after rotations) */
        expected = Open;
        if (!atomic_compare_exchange_weak(&x_parent->state, &expected, Balancing)) {
            goto release_and_fail;
        }
        acquired[1] = x_parent;
    }

    if (x_parent_parent != NIL && x_parent_parent != x && x_parent_parent != x_parent) {
        /* Check if x_parent_parent is not already acquired */
        expected = Open;
        if (!atomic_compare_exchange_weak(
                &x_parent_parent->state,
                &expected,
                Balancing)
                ) {
            goto release_and_fail;
        }
        acquired[2] = x_parent_parent;
    }

    if (x_left != NIL) {
        /* Check if x_left is already in acquired array (can happen after rotations) */
        bool already_acquired = false;
        for (int i = 0; i < 3; i++) {
            if (acquired[i] == x_left) {
                already_acquired = true;
                break;
            }
        }
        if (!already_acquired) {
            expected = Open;
            if (!atomic_compare_exchange_weak(&x_left->state, &expected, Balancing)) {
                goto release_and_fail;
            }
            acquired[3] = x_left;
        }
    }

    if (x_right != NIL) {
        /* Check if x_right is already in acquired array (can happen after rotations) */
        bool already_acquired = false;
        for (int i = 0; i < 4; i++) {
            if (acquired[i] == x_right) {
                already_acquired = true;
                break;
            }
        }
        if (!already_acquired) {
            expected = Open;
            if (!atomic_compare_exchange_weak(&x_right->state, &expected, Balancing)) {
                goto release_and_fail;
            }
            acquired[4] = x_right;
        }
    }

    return true;

    release_and_fail:
    for (int i = 0; i < 5; i++) {
        if (acquired[i] != NIL) {
            node_atomic_set_state(acquired[i], Open);
        }
    }
    return false;
}

static inline void rebalancing_release(Node* acquired[5]) {
    for (int i = 0; i < 5; ++i) {
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
        node_atomic_set_right(y, x);
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
        node_atomic_set_left(y, x);
        node_atomic_set_level(y, node_atomic_get_level(y) + 1);

        return y;
    }
    return x;
}

/* insert is easy */
static Node *rebalance_on_insert(Node *current)
{
    Node* new_head;
    Node* acquired[5];

    while (true) {
        if (rebalancing_acquire(current, acquired))
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
    Node* acquired[5];

    /*
     * Removal can create a gap in levels,
     * fix it by lowering current->level.
     */

    /* announce rebalancing by CAS */
    if (current != NIL) {
        while (true) {
            if (rebalancing_acquire(current, acquired))
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
        if (!atomic_compare_exchange_weak(&node->state, &expected, Insert)) {
            return NIL;
        }

        if (prev != NIL && !atomic_compare_exchange_weak(&prev->state, &expected, Insert)) {
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
        bool need_restore = current_right == NIL;

        Node* tmp = insert_sub(tree, current_right, current, value, node);

        if (tmp == NIL) {
            /*
             * CAS fail retry
             */
            return NIL;
        }

        node_atomic_set_right(current, tmp);
        node_atomic_set_parent(tmp, current);

        if (need_restore) {
            node_atomic_set_state(node, Open);
            node_atomic_set_state(current, Open);
        }

    } else if (cmp < 0) {
        Node* current_left = node_atomic_get_left(current);
        bool need_restore = current_left == NIL;

        Node* tmp = insert_sub(tree, current_left, current, value, node);

        if (tmp == NIL) {
            /*
             * CAS fail retry
             */
            return NIL;
        }

        node_atomic_set_left(current, tmp);
        node_atomic_set_parent(tmp, current);

        if (need_restore) {
            node_atomic_set_state(node, Open);
            node_atomic_set_state(current, Open);
        }

    } else {
        /* already exists? */
        return current;
    }

    return rebalance_on_insert(current);
}

void aatree_insert(Tree *tree, uintptr_t value, Node *node)
{
    Node* inserted = NIL;
    bool first_insert = tree->root == NIL;

    while (inserted == NIL) {
        inserted = insert_sub(tree, tree->root, NIL, value, node);
    }
    tree->root = inserted;

    if (first_insert) {
        node_atomic_set_state(tree->root, Open);
    }
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
}

/* prepare tree */
void aatree_init(Tree *tree, aatree_cmp_f cmpfn, aatree_walker_f release_cb)
{
    tree->root = NIL;
    tree->count = 0;
    tree->node_cmp = cmpfn;
    tree->release_cb = release_cb;
}

/*
 * search function
 */
Node *aatree_search(Tree *tree, uintptr_t value)
{
    Node *current = tree->root;

    /* not allowed to visit Balancing stated nodes */
    while (current != NIL) {
        int cmp = tree->node_cmp(value, current);
        if (cmp > 0)
            current = node_atomic_get_right(current);
        else if (cmp < 0)
            current = node_atomic_get_left(current);
        else
            return current;
    }
    return NULL;
}
