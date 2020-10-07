/** @license 2020 Neil Edelman, distributed under the terms of the
 [MIT License](https://opensource.org/licenses/MIT).

 @subtitle Trie

 Tries are isomorphic to <Morrison, 1968 PATRICiA>. For speed, instead of
 being packed in an array, they are broken down into a linked-forest, as
 <Bayer, McCreight, 1972 Large (B-Trees)>, but defines the order as the maximum
 branching factor, as <Knuth, 1998 Art 3>.

 In B-Tree parlance, a group of contiguous data, (implicitly nodes,) is a node.
 We explicitly refer to these data as nodes, thus, a B-Trie is a forest of
 _trees_. Leaves, which contain keys, and branches are called nodes. These are
 all non-empty complete binary trees; `branches = (leaves \in [1, order]) - 1`.
 The forest, as a whole, is a complete binary tree except the links to
 different trees, having `\sum_{trees} branches = \sum_{trees} leaves - trees`.
 However, a B-Trie is a variable-length encoding, so every path through the
 forest doesn't have to have the same number of trees.

 @fixme Strings can not be more then 8 characters the same. Have a leaf value
 255->leaf.bigskip+255. May double the code.

 @param[TRIE_NAME, TRIE_TYPE]
 <typedef:<PN>type> that satisfies `C` naming conventions when mangled and an
 optional returnable type that is declared, (it is used by reference only
 except if `TRIE_TEST`.) `<PN>` is private, whose names are prefixed in a
 manner to avoid collisions; any should be re-defined prior to use elsewhere.

 @param[TRIE_KEY]
 A function that satisfies <typedef:<PN>key_fn>. Must be defined if and only if
 `TRIE_TYPE` is defined.

 @param[TRIE_TO_STRING]
 Defining this includes `ToString.h` with the keys as the string.

 @param[TRIE_TEST]
 Unit testing framework <fn:<N>trie_test>, included in a separate header,
 <../test/TreeTest.h>. Must be defined equal to a (random) filler function,
 satisfying <typedef:<PN>action_fn>. Requires that `NDEBUG` not be defined.

 @std C89
 @cf [Array](https://github.com/neil-edelman/Array)
 @cf [Heap](https://github.com/neil-edelman/Heap)
 @cf [List](https://github.com/neil-edelman/List)
 @cf [Orcish](https://github.com/neil-edelman/Orcish)
 @cf [Pool](https://github.com/neil-edelman/Pool)
 @cf [Set](https://github.com/neil-edelman/Set) */

#include <string.h> /* size_t memmove strcmp memcpy */
#include <errno.h>  /* errno EILSEQ */
#include <stdint.h> /* C99: uint*_t */
#include <assert.h> /* assert */


/* X-macro for a minimal dynamic array. */
#define ARRAY_IDLE { 0, 0, 0 }
#define MIN_ARRAY(name, type) \
struct name##_array { type *data; size_t size, capacity; }; \
/* Initialises `a` to idle. */ \
static void name##_array(struct name##_array *const a) \
	{ assert(a), a->data = 0, a->capacity = a->size = 0; } \
/* Destroys `a` and returns it to idle. */ \
static void name##_array_(struct name##_array *const a) \
	{ assert(a), free(a->data), name##_array(a); } \
/* Ensures `min_capacity` of `a`. @param[min_capacity] If zero, does nothing.
@return Success; otherwise, `errno` will be set.
@throws[ERANGE] Tried allocating more then can fit in `size_t` or `realloc`
doesn't follow POSIX. @throws[realloc, ERANGE] */ \
static int name##_array_reserve(struct name##_array *const a, \
	const size_t min_capacity) { \
	size_t c0; \
	type *data; \
	const size_t max_size = (size_t)-1 / sizeof *a->data; \
	assert(a); \
	if(a->data) { \
		if(min_capacity <= a->capacity) return 1; c0 = a->capacity; \
	} else { /* Idle. */ \
		if(!min_capacity) return 1; c0 = 1; \
	} \
	if(min_capacity > max_size) return errno = ERANGE, 0; \
	/* `c_n = a1.625^n`, approximation golden ratio `\phi ~ 1.618`. */ \
	while(c0 < min_capacity) { \
		size_t c1 = c0 + (c0 >> 1) + (c0 >> 3) + 1; \
		if(c0 > c1) { c0 = max_size; break; } \
		c0 = c1; \
	} \
	if(!(data = realloc(a->data, sizeof *a->data * c0))) \
		{ if(!errno) errno = ERANGE; return 0; } \
	a->data = data, a->capacity = c0; \
	return 1; \
} \
/* @return Push back a new un-initialized datum of `a`.
 @throws[realloc, ERANGE] */ \
static type *name##_array_new(struct name##_array *const a) { \
	assert(a); \
	return name##_array_reserve(a, a->size + 1) ? a->data + a->size++ : 0; \
}

#define TRIESTR_TEST(a, i) (a[i >> 3] & (128 >> (i & 7)))
#define TRIESTR_DIFF(a, b, i) ((a[i >> 3] ^ b[i >> 3]) & (128 >> (i & 7)))
#define TRIESTR_SET(a, i) (a[i >> 3] |= 128 >> (i & 7))
#define TRIESTR_CLEAR(a, i) (a[i >> 3] &= ~(128 >> (i & 7)))
#define TRIE_MAX_LEFT 1 /* All-left worst-case, `[0, max(tree.left=255)]`. */
#define TRIE_BRANCH (TRIE_MAX_LEFT + 1) /* Maximum branches. */
#define TRIE_ORDER (TRIE_BRANCH + 1) /* Maximum branching factor / leaves. */

/** Fixed-maximum-size trees in the trie-forest. A PATRICiA trie encodes the
 length of the bits in `skip`, so instead of going with in-order branches, it
 is natural to go with pre-order. These are semi-implicit in that `right` is
 all the remaining branches after `left`; don't have enough data to go up. */
struct tree {
	unsigned char bsize; /* +1 is the rank */
	struct branch { unsigned char left, skip; } branches[TRIE_BRANCH];
	union leaf { const char *data; size_t bigskip; size_t link; }
		leaves[TRIE_ORDER];
};
MIN_ARRAY(tree, struct tree)
/** Trie-forest. Link-trees are on top by design choice,
 `empty and !links or links < forest.size`. */
struct trie { size_t links; struct tree_array forest; };
#ifndef TRIE_IDLE /* <!-- !zero */
#define TRIE_IDLE { 0, ARRAY_IDLE }
#endif /* !zero --> */
/** Only used in moving items as a temporary construct. */
struct link { struct branch branch; union leaf lr[2]; };


/** New idle `f`. */
static void trie(struct trie *const t)
	{ assert(t), t->links = 0, tree_array(&t->forest); }

/** Erase `f` to idle. */
static void trie_(struct trie *const t)
	{ assert(t), tree_array_(&t->forest), trie(t); }

/** Erase `f` but preserve the memory. */
static void trie_clear(struct trie *const t)
	{ assert(t), t->links = 0, t->forest.size = 0; }

/** @return Only looks at the index for an item that possibly matches `key` or
 null if `key` is definitely not in `f`. @order \O(`key.length`) */
static const char *trie_match(const struct trie *const f,
	const char *const key) { /* `f` for forest; `t`, `trie` conflict. */
	size_t bit, t;
	struct { size_t key, trie; } byte;
	assert(f && key);
	if(!f->forest.size) return 0; /* Empty. */
	for(byte.key = 0, bit = 0, t = 0; ; ) { /* Descend tree in forest. */
		struct tree *const tree = f->forest.data + t;
		struct { size_t b0, b1, i; } n; /* Branch range and leaf accumulator. */
		assert(t < f->forest.size);
		n.b0 = 0, n.b1 = tree->bsize, n.i = 0;
		while(n.b0 < n.b1) { /* Branches. */
			struct branch *const branch = tree->branches + n.b0;
			for(byte.trie = (bit += branch->skip) >> 3; byte.key < byte.trie;
				byte.key++) if(key[byte.key] == '\0') return 0;
			if(!TRIESTR_TEST(key, bit)) n.b1 = ++n.b0 + branch->left;
			else n.b0 += branch->left + 1, n.i += branch->left + 1;
			bit++;
		}
		assert(n.b0 == n.b1); /* Leaf. */
		if(t < f->links) t = tree->leaves[n.i].link;
		else return tree->leaves[n.i].data;
	}
}

/** @return `key` in `t` or null. @order \O(`key.length`) */
static const char *trie_get(const struct trie *const t, const char *const key) {
	const char *const leaf = trie_match(t, key);
	return leaf && !strcmp(leaf, key) ? leaf : 0;
}



/* Debug. */
static void print_tree(const struct trie *const t, const size_t tr);
static int trie_graph(const struct trie *const t, const char *const fn);
static void print_trie(const struct trie *const t);

/** @return Sample of left key of leaf index `i` of link-tree `tree` in `f`. */
static const char *link_key(struct trie *const f, size_t link) {
	assert(f && link < f->forest.size);
	while(link < f->links) link = f->forest.data[link].leaves[0].link;
	return f->forest.data[link].leaves[0].data;
}

/** @return Leaf link-reference in the link-tree just above the data-tree that
 holds `key` in `f`. If there is none, returns null. */
static size_t *key_link(const struct trie *const f, const char *const key) {
	struct tree* tree;
	struct { unsigned b0, b1, i; } n;
	size_t bit = 0, t = 0;
	assert(f && key);
	if(!f->links) return 0;
	assert(f->forest.size);
	do {
		tree = f->forest.data + t;
		n.b0 = 0, n.b1 = tree->bsize, n.i = 0;
		while(n.b0 < n.b1) {
			struct branch *const branch = tree->branches + n.b0;
			bit += branch->skip;
			if(!TRIESTR_TEST(key, bit)) n.b1 = ++n.b0 + branch->left;
			else n.b0 += branch->left + 1, n.i += branch->left + 1;
			bit++;
		}
		assert(n.b0 == n.b1);
	} while((t = tree->leaves[n.i].link) < f->links);
	return &tree->leaves[n.i].link;
}

/* Swap data-tree with index `tree_ref` in `f`, who's leaf index in the parent
 is also `parent_ref`, (if existing,) to be the first data-tree, index
 `f.forest[f.links]`. */
static struct tree *swap_with_first_data(struct trie *const f,
	size_t *const tree_ref, size_t *const parent_ref) {
	struct tree *const tree = f->forest.data + *tree_ref;
	assert(f && tree_ref && parent_ref && f->links < f->forest.size &&
		*tree_ref >= f->links);
	if(*tree_ref > f->links) {
		/* Link on the link-tree that goes to `f.links`, (any key in
		 `f.links`, 0 will do,) and `t`. */
		size_t *const zero_ref
			= key_link(f, f->forest.data[f->links].leaves[0].data);
		/* This is very trusting of the user to not modify strings. */
		assert(zero_ref && *zero_ref == f->links && *parent_ref == *tree_ref);
		memcpy(tree, f->forest.data + f->links, sizeof *tree);
		*zero_ref = *tree_ref;
		*tree_ref = *parent_ref = f->links;
	}
	return f->forest.data + f->links;
}

/** Must already be a tree reserved from `f`. Alters the order. */
static struct tree *new_link_tree(struct trie *const f) {
	struct tree *const newtree = tree_array_new(&f->forest),
		*const datatree0 = f->forest.data + f->links;
	assert(f->links < f->forest.size && newtree);
	if(f->links) { /* Adjust the indices of the parent. */
		size_t *const datatree0_ref
			= key_link(f, f->forest.data[f->links].leaves[0].data);
		assert(datatree0_ref && *datatree0_ref == f->links);
		*datatree0_ref = newtree - f->forest.data;
	}
	memcpy(newtree, datatree0, sizeof *datatree0);
	f->links++;
	return datatree0; /* It is a new link-tree now. */
}

/** `t` must be a full-data tree, which will be split at the root and placed in
 a new tree, which must already have been reserved from `f`.
 @return The root, which must be placed in a link-tree above. */
static struct link split_root(struct trie *const f, const size_t t) {
	struct tree *const left = f->forest.data + t,
		*const right = tree_array_new(&f->forest);
	struct branch *branch;
	unsigned lt = left->branches[0].left, rt = left->bsize - lt - 1;
	struct link root;
	assert(f && t >= f->links && t < f->forest.size && right && left->bsize);
	right->bsize = rt;
	memcpy(right->branches, left->branches + lt + 1, sizeof root.branch * rt);
	memcpy(right->leaves, left->leaves + lt + 1, sizeof *root.lr * (rt + 1));
	left->bsize = (branch = left->branches + 0)->left;
	root.branch.left = 0;
	root.branch.skip = branch->skip;
	root.lr[0].link = t;
	root.lr[1].link = right - f->forest.data;
	memmove(branch, branch + 1, sizeof *branch * left->bsize);
	printf("split (%u,%u)[%lu,%lu]\n", root.branch.left, root.branch.skip, root.lr[0].link, root.lr[1].link);
	return root;
}

/** Adds `e` to a new link-tree, which must be reserved, below `i` in `t` in
 `f`. Must be full. */
static void add_to_new_linktree(struct trie *const f, struct link root) {
	struct tree *const top = new_link_tree(f);
	struct branch *branch = top->branches + 0;
	union leaf *leaves = top->leaves + 0;
	assert(top && !root.branch.left && f->links
		&& root.lr[0].link >= f->links - 1 && f->links < f->forest.size);
	printf("new (%u,%u)[%lu,%lu]\n", root.branch.left, root.branch.skip, root.lr[0].link, root.lr[1].link);
	/* Update link from <fn:new_link_tree>. */
	if(root.lr[0].link == f->links - 1) root.lr[0].link = f->forest.size - 1;
	top->bsize = 1;
	branch->left = 0;
	branch->skip = root.branch.skip;
	leaves[0].link = root.lr[0].link;
	leaves[1].link = root.lr[1].link;
}

/** Adds `e` to position `i` in `t` in `f`. Must not be full. */
static void add_to_vacant_linktree(struct trie *const f, const size_t t,
	const unsigned i, const struct link e) {
	struct tree *const tree = f->forest.data + t;
	struct branch *branch;
	union leaf *leaf;
	struct { unsigned b0, b1, i; } n;
	unsigned lt;
	assert(f && t < f->forest.size && tree->bsize < TRIE_BRANCH);
	assert(i <= tree->bsize && e.branch.left == 0);
	n.b0 = 0, n.b1 = tree->bsize, n.i = 0;
	while(n.b0 < n.b1) { /* Expand tree. */
		lt = (branch = tree->branches + n.b0)->left + 1;
		if(i < n.i + lt) n.b1 = n.b0++ + (branch->left = lt);
		else n.b0 += lt, n.i += lt;
	}
	assert(n.b0 == n.b1 && n.b0 <= tree->bsize
		&& i == n.i && n.i <= tree->bsize);
	branch = tree->branches + n.b0;
	memmove(branch + 1, branch, sizeof *branch * (tree->bsize - n.b0));
	branch->left = 0;
	branch->skip = e.branch.skip;
	leaf = tree->leaves + i + 1;
	memmove(leaf + 1, leaf, sizeof *leaf * (tree->bsize - i));
	assert(e.lr[0].link == leaf[-1].link); /* Brings down the left. */
	leaf->link = e.lr[1].link;
	tree->bsize++;
}

static int trie_add_unique(struct trie *const f, const char *const key) {
	struct { size_t b, b0, b1; } bit; /* `b \in [b0, b1]` inside branch. */
	struct { struct tree *tree; size_t t; size_t bit; const char *key;
		unsigned b0, b1, i; /* Node branch range, leaf accumulator. */
		enum { VACANT_DATA, LINK, FULL, LINK_FULL } leaves;
		enum { TREE_LEFT, RIGHT, TOP, TOP_RIGHT } in; } t; /* `t \in f`. */
	struct { size_t t; size_t bit; unsigned i; } p; /* Parent valid if `t.t`. */
	const char *sample; /* String from trie to compare with `key`. */
	struct branch *branch;
	union leaf *leaf;
	unsigned lt;
	int is_allocated = 0; /* Debug; kill with `-DNDEBUG -O`. */

	assert(f && key);
	printf("*** ADD \"%s\" ***\n", key);
	/* Empty special case is exception. */
	if(!f->forest.size) return assert(!f->links),
		(t.tree = tree_array_new(&f->forest)) && (t.tree->bsize = 0,
		t.tree->leaves[0].data = key, 1);

	/* Start at the beginning of the key and root of the forest. */
	bit.b = 0, t.t = 0;
	do {
		t.bit = bit.b; /* Cache bit value for backtracking. */
tree: /* Descend tree. */
		printf("tree "), print_tree(f, t.t);
		assert(t.t < f->forest.size);
		t.b0 = 0, t.b1 = (t.tree = f->forest.data + t.t)->bsize, t.i = 0;
		assert(t.tree->bsize <= TRIE_BRANCH);
		/* Is it a link-tree? Is it full? */
		t.leaves = (t.t < f->links) | ((t.tree->bsize == TRIE_BRANCH) << 1);
		bit.b0 = bit.b;
		sample = (t.leaves & LINK)
			? link_key(f, t.tree->leaves[t.i].link) : t.tree->leaves[t.i].data;
		while(t.b0 < t.b1) { /* Branches. */
			branch = t.tree->branches + t.b0;
			for(bit.b1 = bit.b + branch->skip; bit.b < bit.b1; bit.b++)
				if(TRIESTR_DIFF(key, sample, bit.b)) goto insert;
			lt = branch->left + 1;
			if(!TRIESTR_TEST(key, bit.b)) {
				if(!t.leaves) branch->left = lt;
				t.b1 = t.b0++ + lt;
			} else {
				t.b0 += lt, t.i += lt;
				sample = (t.leaves & LINK) ? link_key(f,
					t.tree->leaves[t.i].link) : t.tree->leaves[t.i].data;
			}
			bit.b++, bit.b0 = bit.b1;
		}
		assert(t.b0 == t.b1 && t.i <= t.tree->bsize);
		/* If link-tree, `t.t` is updated and we continue down another tree. */
	} while((t.leaves & LINK) && (p.t = t.t, p.bit = t.bit,
		t.t = t.tree->leaves[p.i = t.i].link, 1));
	while(!TRIESTR_DIFF(key, sample, bit.b)) bit.b++; /* Got to the leaves. */
insert:
	/* Is it a right insertion? Is it above the root of the tree? */
	t.in = !!TRIESTR_TEST(key, bit.b) | ((!t.b0 && t.tree->bsize) << 1);
	printf("key is: %s, %s.\n", t.in & RIGHT ? "right" : "left", t.in & TOP ? "top" : "tree");
	if(t.in & RIGHT) t.i += (lt = t.b1 - t.b0) + 1; else lt = 0;
	assert(t.i <= t.tree->bsize + 1u);

	/* Split and backtrack if the leaf status is `FULL` or `LINK`. */
	if(t.leaves) {
		unsigned rt;
		int is_vacant_parent = t.t && f->forest.data[p.t].bsize < TRIE_BRANCH;
		assert(!is_allocated && (is_allocated = 1)); /* Loop very Bad. */
		printf("parent %s -> reseving %u.\n",
			is_vacant_parent ? "vacant" : "full", 1 + !is_vacant_parent);
		/* Fail-fast; single-point-of-failure before modification. */
		if(!tree_array_reserve(&f->forest,
			f->forest.size + 1 + !is_vacant_parent)) return 0;
		if(t.in & TOP) { /* The new branch wants to go on top of the root. */
			struct tree *const tree = f->forest.data + t.t;
			assert(t.i == 0 || t.i == tree->bsize + 1u);
			printf("insert top; branches %u\n", tree->bsize);
			if(is_vacant_parent) {
				/* Remeber it could be a link-tree. */
				/* P->tree ... P,branch->{key|tree} */
				struct tree *const parent = f->forest.data + p.t;
				printf("parent branches %u, tree branches %u\n",
					parent->bsize, tree->bsize);
				assert(0);
			} else {
				/* It could be root; swap? */
				/* [P->]tree ... [P->]branch->{key|tree} */
			}
			assert(0);
			/*memcpy();*/
		} else if(is_vacant_parent) {
			add_to_vacant_linktree(f, p.t, p.i, split_root(f, t.t));
			t.t = p.t, bit.b = p.bit;
			if(!trie_graph(f, "graph/split-parent.gv")) perror("output");
		} else { /* Split: root goes to it's own node. */
#if 0
			/* FIXMEEEE */
			add_to_new_linktree(f, split_root(f, t.t));
			/* and... */
			t.t = f->links - 1, bit.b = t.bit;
#else
			struct tree *top = f->forest.data + t.t,
				*const left = tree_array_new(&f->forest),
				*const right = tree_array_new(&f->forest);
			const size_t l = left - f->forest.data, r = right - f->forest.data;
			assert(left && right);
			left->bsize = (lt = (branch = top->branches + 0)->left);
			assert(top->bsize > lt);
			memcpy(left->branches, top->branches + 1, sizeof *branch * lt);
			memcpy(left->leaves, top->leaves, sizeof *leaf * (lt + 1));
			right->bsize = (rt = top->bsize - lt - 1);
			memcpy(right->branches, top->branches + lt + 1, sizeof *branch*rt);
			memcpy(right->leaves, top->leaves + lt + 1, sizeof *leaf * (rt +1));
			(top = swap_with_first_data(f, &t.t,
				&f->forest.data[p.t].leaves[p.i].link))->bsize = 1;
			top->branches[0].left = 0;
			top->leaves[0].link = l;
			top->leaves[1].link = r;
			f->links++;
			bit.b = t.bit;
#endif
			if(!trie_graph(f, "graph/split-full.gv")) perror("output");
		}
		goto tree; /* Backtrack. It's possible to not do this, but explodes. */
	}

	/* Insert a leaf into the vacant leaf tree. */
	leaf = t.tree->leaves + t.i;
	/*printf("leaf[%u] memmove(%u, %u, %u) ", t.tree->bsize+1, n.i+1, n.i, t.tree->bsize + 1 -n.i), print_tree(f, 0);*/
	memmove(leaf + 1, leaf, sizeof *leaf * (t.tree->bsize + 1 - t.i));
	leaf->data = key;

	/* Insert a branch into the vacant branch tree; must be widened already. */
	branch = t.tree->branches + t.b0;
	/*printf("branch[%u] memmove(%u, %u, %u) ", t.tree->bsize, n.b0+1, n.b0, t.tree->bsize - n.b0), print_tree(f, 0);*/
	if(t.b0 != t.b1) { /* Split `skip` with the existing branch. */
		assert(bit.b0 <= bit.b && bit.b + !t.b0 <= bit.b0 + branch->skip);
		/*printf("branch skip %u -> ", branch->skip);*/
		branch->skip -= bit.b - bit.b0 + !t.b0;
		/*printf("%u\n", branch->skip);*/
	}
	memmove(branch + 1, branch, sizeof *branch * (t.tree->bsize - t.b0));
	branch->left = lt;
	assert(bit.b >= bit.b0 + !!t.b0), branch->skip = bit.b - bit.b0 - !!t.b0;
	t.tree->bsize++;

	return 1;
}

/** @return If `key` is already in `t`, returns false, otherwise success.
 @throws[realloc, ERANGE] */
static int trie_add(struct trie *const t, const char *const key)
	{ return trie_get(t, key) ? 0 : trie_add_unique(t, key); }



/** @return Whether `a` and `b` are equal up to the minimum. Used in
 <fn:trie_prefix>. */
/*static int trie_is_prefix(const char *a, const char *b) {
	for( ; ; a++, b++) {
		if(*a == '\0') return 1;
		if(*a != *b) return *b == '\0';
	}
}*/

static void print_tree(const struct trie *const t, const size_t tr) {
	const struct tree *const tree = t->forest.data + tr;
	unsigned i;
	assert(t && tr < t->forest.size);
	printf("tree%lu:skip[", (unsigned long)(tree - t->forest.data));
	for(i = 0; i < tree->bsize; i++)
		printf("%s%u", i ? "," : "", tree->branches[i].skip);
	printf("],left[");
	for(i = 0; i < tree->bsize; i++)
		printf("%s%u", i ? "," : "", tree->branches[i].left);
	printf("],leaf[");
	if((size_t)(tree - t->forest.data) < t->links) {
		for(i = 0; i <= tree->bsize; i++)
			printf("%s%lu", i ? ", " : "", (unsigned long)tree->leaves[i].link);
	} else {
		for(i = 0; i <= tree->bsize; i++)
			printf("%s%s", i ? ", " : "", tree->leaves[i].data);
	}
	printf("].\n");
}

static void print_trie(const struct trie *const t) {
	size_t i;
	assert(t);
	printf("forest {\n");
	for(i = 0; i < t->forest.size; i++)
		printf("\t"), print_tree(t, i);
	printf("}\n");
}

/** Given branch index `b` in `tree`, calculate (inefficiently) the right
 child branches. Used in <fn:trie_graph>. @order \O(log `size`) */
static unsigned trie_right(const struct tree *const tree, const unsigned b) {
	unsigned remaining = tree->bsize, n0 = 0, left, right;
	assert(tree && b < remaining);
	for( ; ; ) {
		left = tree->branches[n0].left;
		right = remaining - left - 1;
		assert(left < remaining && right < remaining);
		if(n0 >= b) break;
		if(b <= n0 + left) remaining = left, n0++;
		else remaining = right, n0 += left + 1;
	}
	assert(n0 == b);
	return right;
}

/** @return Finds (inefficiently) the leftmost leaf index given branch index
 `n` in `tree`. Used in <fn:trie_graph>. */
static unsigned trie_left_leaf(const struct tree *const tree,
	const size_t n) {
	unsigned remaining = tree->bsize, n0 = 0, left, right, i = 0;
	assert(tree && n < remaining);
	for( ; ; ) {
		left = tree->branches[n0].left;
		right = remaining - left - 1;
		assert(left < remaining && right < remaining);
		if(n0 >= n) break;
		if(n <= n0 + left) remaining = left, n0++;
		else remaining = right, n0 += left + 1, i += left + 1;
	}
	assert(n0 == n);
	return i;
}

static void tree_graph(const struct trie *const f, const unsigned t,
	FILE *const fp) {
	struct tree *const tree = f->forest.data + t;
	unsigned br, lf;
	assert(f && t < f->forest.size && fp);
	fprintf(fp, "\tsubgraph cluster_tree%lu {\n"
		"\t\tstyle = filled; fillcolor = lightgray; label = \"tree %lu\";\n",
		(unsigned long)t, (unsigned long)t);
	fprintf(fp, "\t\t// branches\n");
	for(br = 0; br < tree->bsize; br++) {
		struct branch *const branch = tree->branches + br;
		const unsigned left = branch->left, right = trie_right(tree, br);
		fprintf(fp, "\t\tbranch%u_%u "
			"[label = \"%u\", shape = none, fillcolor = none];\n",
			t, br, branch->skip);
		if(left) {
			fprintf(fp, "\t\tbranch%u_%u -> branch%u_%u [style = dashed];\n",
				t, br, t, br + 1);
		} else if(t >= f->links) {
			fprintf(fp, "\t\tbranch%u_%u -> leaf%u_%u "
				"[style = dashed, color = royalblue];\n",
				t, br, t, trie_left_leaf(tree, br));
		}
		if(right) {
			fprintf(fp, "\t\tbranch%u_%u -> branch%u_%u;\n",
				t, br, t, br + left + 1);
		} else if(t >= f->links) {
			fprintf(fp, "\t\tbranch%u_%u -> leaf%u_%u "
				"[color = royalblue];\n",
				t, br, t, trie_left_leaf(tree, br) + left + 1);
		}
	}
	if(t >= f->links) { /* Data tree. */
		fprintf(fp, "\t\t// leaves\n");
		for(lf = 0; lf <= tree->bsize; lf++) fprintf(fp,
			"\t\tleaf%u_%u [label = \"%s\"];\n",
			t, lf, tree->leaves[lf].data);
		fprintf(fp, "\t}\n");
	} else { /* Link-tree. */
		fprintf(fp, "\t}\n");
		for(lf = 0; lf <= tree->bsize; lf++) {
			struct { unsigned b0, b1, i; } n;
			unsigned parent = 0, lt;
			unsigned l = (unsigned)tree->leaves[lf].link;
			struct tree *link = f->forest.data + l;
			unsigned is_left = 0;
			n.b0 = 0, n.b1 = tree->bsize, n.i = 0;
			assert(tree && lf <= n.b1);
			while(n.b0 < n.b1) {
				parent = n.b0;
				lt = tree->branches[n.b0].left + 1;
				if(lf < n.i + lt) n.b1 = n.b0++ + lt, is_left = 1;
				else n.b0 += lt, n.i += lt, is_left = 0;
			}
			assert(n.b0 == n.b1 && n.b0 <= tree->bsize && lf == n.i);
			fprintf(fp,
				"\t%s%u_%u -> %s%u_%u [ltail=cluster_tree%u, "
				"lhead=cluster_tree%u, color = firebrick, style = %s];\n",
				tree->bsize ? "branch" : "leaf", t, parent,
				link->bsize ? "branch" : "leaf", l, 0,
				t, l, is_left ? "dashed" : "solid");
		}
	}
	fprintf(fp, "\n");
}

static void tree_subgraph(const struct trie *const f, const size_t t,
	unsigned char *visited, FILE *const fp) {
	const unsigned ut = (unsigned)t;
	assert(f && t < f->forest.size && fp && t <= (unsigned)-1 && visited);
	tree_graph(f, ut, fp), TRIESTR_SET(visited, t);
	if(t < f->links) {
		unsigned lf;
		for(lf = 0; lf <= f->forest.data[t].bsize; lf++)
			tree_subgraph(f, f->forest.data[t].leaves[lf].link, visited, fp);
	}
}

static int trie_graph(const struct trie *const f, const char *const fn) {
	FILE *fp = 0;
	int success = 0;
	unsigned char *visited = 0; /* Fixme: visited is not the right condition. */
	assert(f && fn);
	if(!(visited = calloc((f->forest.size >> 3) + !!(f->forest.size & 7), 1)))
		goto finally;
	if(!(fp = fopen(fn, "w"))) goto finally;
	printf("(trie graph %s)\n", fn);
	fprintf(fp, "digraph {\n"
		"\trankdir=TB;\n"
		"\tnode [shape = box, style = filled, fillcolor = lightsteelblue];\n"
		"\t// forest size %lu.\n"
		"\n", (unsigned long)f->forest.size);
	if(!f->forest.size) {
		fprintf(fp, "\tlabel = \"empty\";\n");
	} else {
		unsigned t = 0;
		/* An additional constraint not present in code: if this is not met,
		 GraphViz probably can't handle it anyway. */
		assert(f->forest.size <= (unsigned)-1);
		tree_subgraph(f, t, visited, fp);
		fprintf(fp, "\t// the following are not reachable from the root\n"
			"\tnode [fillcolor = red];\n"
			"\n");
		for(t = 0; t < f->forest.size; t++)
			if(!TRIESTR_TEST(visited, t)) tree_graph(f, t, fp);
	}
	fprintf(fp, "}\n");
	success = 1;
finally:
	if(fp) fclose(fp);
	free(visited);
	return success;
}
