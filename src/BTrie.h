/** @license 2020 Neil Edelman, distributed under the terms of the
 [MIT License](https://opensource.org/licenses/MIT).

 @subtitle Trie

 Trie pre-order internal nodes in the style of <Morrison, 1968 PATRICiA>.
 Mixed with BTree.

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
/* Order is the maximum is number of `data` leaves, and maximum branching
 factor of `link` leaves, as <Knuth, 1998 Art 3>. A non-empty, complete binary
 tree, so `branches + 1 = leaves`. */
#define TRIE_MAX_LEFT 3 /* `<= max(tree:left)` set by data type, `> 0`. */
#define TRIE_BRANCH (TRIE_MAX_LEFT + 1) /* (Improbable) worst-case, all left. */
#define TRIE_ORDER (TRIE_BRANCH + 1)

/** Splits trie into a forest, as <Bayer, McCreight, 1972 Large> B-Trees.
 Packed less strictly than possble to save space and confine updates to
 `\O(1)`, while being in an array. */
struct tree {
	unsigned char branch_size;
	struct branch { unsigned char left, skip; } branches[TRIE_BRANCH];
	union leaf { const char *data; size_t link; } leaves[TRIE_ORDER];
};
MIN_ARRAY(tree, struct tree)
/** Tries are isomophic to <Morrison, 1968 PATRICiA>, but in a linked forest of
 order-height-limited trees. Link trees, who's leaves are indices to another,
 are on top, `empty or links < forest.size`. */
struct trie { size_t links; struct tree_array forest; };
#ifndef TRIE_IDLE /* <!-- !zero */
#define TRIE_IDLE { 0, ARRAY_IDLE }
#endif /* !zero --> */



/** @return Whether `a` and `b` are equal up to the minimum. */
/*static int trie_is_prefix(const char *a, const char *b) {
	for( ; ; a++, b++) {
		if(*a == '\0') return 1;
		if(*a != *b) return *b == '\0';
	}
}*/



static void trie(struct trie *const t)
	{ assert(t), t->links = 0, tree_array(&t->forest); }

static void trie_(struct trie *const t)
	{ assert(t), tree_array_(&t->forest), trie(t); }

static const char *trie_match(const struct trie *const t, const char *key) {
	size_t bit, link;
	struct { size_t key, trie; } byte;
	assert(t && key);
	if(!t->forest.size) return 0; /* Empty. */
	for(byte.key = 0, bit = 0, link = 0; ; ) { /* `link` tree in forest. */
		struct tree *const tree = t->forest.data + link;
		struct { size_t b0, b1, i; } n;
		assert(link < t->forest.size);
		/* Node branch range (binary search low, high) and leaf accumulator. */
		n.b0 = 0, n.b1 = tree->branch_size, n.i = 0;
		while(n.b0 < n.b1) { /* Descend branches until leaf. */
			struct branch *const branch = tree->branches + n.b0;
			for(byte.trie = (bit += branch->skip) >> 3; byte.key < byte.trie;
				byte.key++) if(key[byte.key] == '\0') return 0;
			if(!TRIESTR_TEST(key, bit)) n.b1 = ++n.b0 + branch->left;
			else n.b0 += branch->left + 1, n.i += branch->left + 1;
			bit++;
		}
		assert(n.b0 == n.b1);
		if(link < t->links) link = tree->leaves[n.i].link;
		else return tree->leaves[n.i].data;
	}
}

static const char *trie_get(const struct trie *const t, const char *const key) {
	const char *const leaf = trie_match(t, key);
	return leaf && !strcmp(leaf, key) ? leaf : 0;
}

/** Use this when calculatating the left key of a link tree. */
static const char *trie_left_link_key(struct trie *const t, struct tree *tree,
	const unsigned br) {
	size_t link = tree->leaves[br].link;
	assert(t->forest.data <= tree && t->forest.data + t->links > tree
		&& br < tree->branch_size && link < tree->branch_size && br != link);
	do { link = t->forest.data[link].leaves[0].link; } while(link < t->links);
	return t->forest.data[link].leaves[0].data;
}
static int trie_graph(const struct trie *const t, const char *const fn);

/** Add `datum` to `trie`. Must not be the same as any key of `trie`; _ie_ it
 does not check for the end of the string. @return Success. @order \O(|`trie`|)
 @throws[realloc, ERANGE] */
static int trie_add_unique(struct trie *const t, const char *const key) {
	/* Counter state `b \in [b0, b1]`. */
	struct { size_t b, b0, b1; } bit = { 0, 0, 0 };
	struct { /* Node state. */
		size_t t; struct tree *tree; /* Tree index and tree. */
		unsigned b0, b1, i; /* Branch range and leaf accumulator. */
		const char *key; /* Left key of branch, (temporary.) */
	} n;
	/* Temporary variables. */
	struct tree *a, *b;
	struct branch *branch;
	unsigned left, right;
	const char **leaf;
	assert(t && key);

	/* Empty special case. */
	if(!t->forest.size) return (a = tree_array_new(&t->forest))
		&& (assert(!t->links), a->branch_size = 0, a->leaves[0].data = key, 1);

	/* Tree starts at the top. */
	n.tree = t->forest.data + (n.t = 0), n.b0 = 0,
		n.b1 = n.tree->branch_size, n.i = 0;
	if(n.t >= t->links) {
		if(n.tree->branch_size < TRIE_BRANCH) goto vacant_data_tree;
		else goto full_data_tree;
	} else {
		if(n.tree->branch_size < TRIE_BRANCH) goto vacant_link_tree;
		goto full_link_tree;
	}

vacant_data_tree: /* Insert into vacancy. */
	n.key = n.tree->leaves[n.i].data;
	while(n.b0 < n.b1) {
		branch = n.tree->branches + n.b0;
		for(bit.b1 = bit.b + branch->skip; bit.b < bit.b1; bit.b++)
			if(TRIESTR_DIFF(key, n.key, bit.b)) goto vacant_data_insert;
		left = branch->left + 1;
		if(!TRIESTR_TEST(key, bit.b)) n.b1 = n.b0++ + (branch->left = left);
		else n.b0 += left, n.i += left, n.key = n.tree->leaves[n.i].data;
		bit.b++, bit.b0 = bit.b1;
	}
	/* Branch from leaf; find the first difference bit-by-bit. Fall-through. */
	assert(n.b0 == n.b1);
	while(!TRIESTR_DIFF(key, n.key, bit.b)) bit.b++;
vacant_data_insert:
	assert(n.i <= n.tree->branch_size && !n.b0 == !bit.b0
		&& TRIESTR_DIFF(key, n.key, bit.b));
	/* Left or right leaf. */
	if(TRIESTR_TEST(key, bit.b)) n.i += (left = n.b1 - n.b0) + 1; else left = 0;
	/* Insert leaf-and-branch pair. */
	leaf = &n.tree->leaves[n.i].data;
	memmove(leaf + 1, leaf, sizeof *leaf * (n.tree->branch_size + 1 - n.i));
	*leaf = key;
	branch = n.tree->branches + n.b0;
	if(n.b0 != n.b1) { /* Split skip value with the existing branch. */
		assert(bit.b0 + branch->skip >= bit.b + !n.b0);
		branch->skip += bit.b0 - bit.b - !n.b0;
	}
	memmove(branch + 1, branch, sizeof *branch * (n.tree->branch_size - n.b0));
	branch->left = left;
	branch->skip = bit.b - bit.b0 - !!n.b0;
	n.tree->branch_size++;
	return 1;

full_data_tree: /* Split at root of tree; move root up to link. `tree` */
	assert(n.tree->branch_size == n.b1 && n.b1 == TRIE_BRANCH
		&& t->links == n.t /* Fixme: or else have to swap size<->link. */);
	branch = n.tree->branches + 0;
	n.key = n.tree->leaves[n.i].data;
	for(bit.b1 = bit.b + branch->skip; bit.b < bit.b1; bit.b++)
		if(TRIESTR_DIFF(key, n.key, bit.b)) goto full_data_before_root;
	/* The difference is past the root of the tree, split it at root. */
	/* Fixme: only at [0]; more code. */
	if(!tree_array_reserve(&t->forest, t->forest.size + 2)) return 0;
	/* Invalidated; root. */
	branch = (n.tree = t->forest.data + n.t)->branches + 0;
	a = tree_array_new(&t->forest), assert(a);
	a->branch_size = (left = branch->left);
	memcpy(a->branches, n.tree->branches + 1, sizeof *branch * left);
	memcpy(a->leaves, n.tree->leaves, sizeof(union leaf) * (left + 1));
	b = tree_array_new(&t->forest), assert(b && n.b1 > branch->left);
	b->branch_size = (right = n.b1 - branch->left - 1);
	memcpy(b->branches, n.tree->branches + left + 1, sizeof *branch * right);
	memcpy(b->leaves, n.tree->leaves + left + 1, sizeof(union leaf) *(right+1));
	/* Make the first a link. */
	n.tree->branch_size = 1;
	branch->left = 0;
	n.tree->leaves[0].link = (size_t)(a - t->forest.data);
	n.tree->leaves[1].link = (size_t)(b - t->forest.data);
	t->links++;
	trie_graph(t, "graph/split.gv");
	/* Left or right. */
	n.tree = TRIESTR_TEST(key, bit.b) ? b : a, bit.b++;
	n.t = n.tree - t->forest.data, n.b0 = 0, n.b1 = n.tree->branch_size;
	assert(n.b1 < TRIE_BRANCH);
	goto vacant_data_tree;
full_data_before_root:
	assert(0);

vacant_link_tree: /* Go to another tree. `tree` */
	branch = n.tree->branches + 0;
	n.key = trie_left_link_key(t, n.tree, 0);
	for(bit.b1 = bit.b + branch->skip; bit.b < bit.b1; bit.b++)
		if(TRIESTR_DIFF(key, n.key, bit.b)) goto full_link_before_root;
	assert(0);
full_link_before_root:
	assert(0);
full_link_tree:
	assert(0);
	return 0;
}

static int trie_add(struct trie *const t, const char *const key) {
	assert(t && key);
	return trie_get(t, key) ? 0 : trie_add_unique(t, key);
}

/** Given branch index `b` in `tree`, calculate (inefficiently) the right
 child branches. Used in <fn:trie_graph>. @order \O(log `size`) */
static unsigned trie_right(const struct tree *const tree, const unsigned b) {
	unsigned remaining = tree->branch_size, n0 = 0, left, right;
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
	unsigned remaining = tree->branch_size, n0 = 0, left, right, i = 0;
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

/* This is actually the same function as `trie_left_key(trie_left_leaf())`. */
static const char *trie_string(const struct trie *const t,
	const struct tree *tree, size_t branch) {
	unsigned leaf = trie_left_leaf(tree, branch);
	assert(t && tree);
	while((size_t)(tree - t->forest.data) < t->links)
		tree = t->forest.data + tree->leaves[leaf].link, leaf = 0;
	return tree->leaves[leaf].data;
}

static int trie_graph(const struct trie *const t, const char *const fn) {
	FILE *fp = 0;
	int success = 0;
	assert(t && fn);
	printf("(output %s)\n", fn);
	if(!(fp = fopen(fn, "w"))) goto finally;
	fprintf(fp, "digraph {\n"
		"\trankdir=TB;\n"
		"\tnode [shape = none, fillcolor = none];\n");
	if(!t->forest.size) {
		fprintf(fp, "\tlabel=\"empty\";\n");
	} else {
		unsigned tr;
		for(tr = 0; tr < t->forest.size; tr++) {
			struct { size_t b0, b1; } bit = { 0, 0 };
			struct tree *const tree = t->forest.data + tr;
			unsigned br, lf;
			const char *sample;
			for(br = 0; br < tree->branch_size; br++) {
				struct branch *branch = tree->branches + br;
				const unsigned left = branch->left,
					right = trie_right(tree, br);
				fprintf(fp, "\tbranch%u_%u [label = \"", tr, br);
				sample = trie_string(t, tree, br);
				for(bit.b1 = bit.b0 + branch->skip; bit.b0 < bit.b1; bit.b0++)
					fprintf(fp, "%c", TRIESTR_TEST(sample, bit.b0) ? '1' : '0');
				fprintf(fp, "\"];\n"
					"\tbranch%u_%u -> ", tr, br);
				if(left) {
					fprintf(fp, "branch%u_%u [style = dashed];\n", tr, br + 1);
				} else {
					if(tr < t->links) fprintf(fp,
						"branch%lu_0 [style = dashed, color = firebrick];"
						" // left link\n", (unsigned long)
						tree->leaves[trie_left_leaf(tree, br)].link);
					else fprintf(fp, "leaf%u_%u [style = dashed]; "
						"// left leaf\n", tr, trie_left_leaf(tree, br));
				}
				fprintf(fp, "\tbranch%u_%u -> ", tr, br);
				if(right) {
					fprintf(fp, "branch%u_%u; // right branch\n",
						tr, br + left + 1);
				} else {
					if(tr < t->links) fprintf(fp,
						"branch%lu_0 [color = firebrick]; // right link\n",
						/*"darkseagreen" "firebrick" "orchid"*/
						(unsigned long)
						tree->leaves[trie_left_leaf(tree, br) + left + 1].link);
					else fprintf(fp, "leaf%u_%u; // right leaf\n",
						tr, trie_left_leaf(tree, br) + left + 1);
				}
			}
			/* This must be after the branches, or it will mix up the order. */
			if(tr >= t->links) { /* Data tree. */
				for(lf = 0; lf <= tree->branch_size; lf++) fprintf(fp,
					"\tleaf%u_%u [label = \"%s\", shape = box, "
					"fillcolor = lightsteelblue, style = filled];\n",
					tr, lf, tree->leaves[lf].data /*fixme*/);
			}
		}
	}
	fprintf(fp, "\tnode [colour=red, style=filled];\n"
		"}\n");
	success = 1;
finally:
	if(fp) fclose(fp);
	return success;
}
