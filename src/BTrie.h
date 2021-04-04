/** @license 2020 Neil Edelman, distributed under the terms of the
 [MIT License](https://opensource.org/licenses/MIT).

 @subtitle Prefix Tree

 ![Example of trie.](../web/trie.png)

 An <tag:<N>trie> is a prefix, or digital tree, and is isomorphic to
 <Morrison, 1968 PATRICiA>. It is an index of pointers-to-`N` entries in a
 (semi)-compact [binary radix trie](https://en.wikipedia.org/wiki/Radix_tree).
 While in a trie, the key part of the entry is a necessarily read-only,
 null-terminated, (including
 [modified UTF-8](https://en.wikipedia.org/wiki/UTF-8#Modified_UTF-8),) that
 uniquely identifies the data.

 Internally, it is a dynamic array of fixed-size-trees in a linked-forest, as
 <Bayer, McCreight, 1972 Large (B-Trees)>. The order is the maximum branching
 factor of a tree, as <Knuth, 1998 Art 3>.

 @fixme Strings can not be more then 8 characters the same. Have a leaf value
 255->leaf.bigskip+255. May double the code. Maybe 8+8+8...?

 @param[TRIE_NAME, TRIE_ENTRY]
 A name that satisfies `C` naming conventions when mangled and an optional
 returnable type <typedef:<PN>entry> for an associative map, (it is used by
 reference only except if `TRIE_TEST`.) If not defined, the key-value entry is
 only the key, thus a string set. `<PN>` is private, whose names are prefixed
 in a manner to avoid collisions; any should be re-defined prior to use
 elsewhere.

 @param[TRIE_KEY]
 A function that satisfies <typedef:<PN>key_fn>. Must be defined if and only if
 `TRIE_ENTRY` is defined.

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
#include <errno.h>  /* errno */
#include <assert.h> /* assert */
#include <stdlib.h> /* abs */

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
doesn't follow POSIX. @throws[realloc] */ \
static int name##_array_reserve(struct name##_array *const a, \
	const size_t min_capacity) { \
	size_t c0; \
	type *data; \
	const size_t max_size = (size_t)-1 / sizeof *a->data; \
	assert(a); \
	if(a->data) { \
		if(min_capacity <= a->capacity) return 1; \
		c0 = a->capacity; \
	} else { /* Idle. */ \
		if(!min_capacity) return 1; \
		c0 = 1; \
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
	if(sizeof *a->data == 1 && a->size >= (size_t)-1) \
		{ errno = ERANGE; return 0; } /* Unlikely. */ \
	return name##_array_reserve(a, a->size + 1) ? a->data + a->size++ : 0; \
}

#define TRIESTR_TEST(a, i) (a[(i) >> 3] & (128 >> ((i) & 7)))
#define TRIESTR_DIFF(a, b, i) ((a[(i) >> 3] ^ b[(i) >> 3]) & (128 >> ((i) & 7)))
#define TRIESTR_SET(a, i) (a[(i) >> 3] |= 128 >> ((i) & 7))
#define TRIESTR_CLEAR(a, i) (a[(i) >> 3] &= ~(128 >> ((i) & 7)))
#define TRIE_MAX_LEFT 3 /* Worst-case all-left cap. `[0,max(tree.left=255)]` */
#define TRIE_BRANCH (TRIE_MAX_LEFT + 1) /* Maximum branches. */
#define TRIE_ORDER (TRIE_BRANCH + 1) /* Maximum branching factor / leaves. */
#define TRIE_BITMAP ((TRIE_ORDER - 1) / 8 + 1) /* Bitmap size in bytes. */

/** Non-empty complete binary tree of a fixed-maximum-size. Semi-implicit in
 that `right` is all the remaining pre-order branches after `left`. */
struct tree {
	unsigned short bsize; /* +1 is the rank. */
	unsigned char link[TRIE_BITMAP]; /* Bitmap associated to leaf. */
	struct branch { unsigned char left, skip; } branches[TRIE_BRANCH];
	union leaf { const char *data; size_t link; } leaves[TRIE_ORDER];
};
MIN_ARRAY(tree, struct tree)
/** Trie-forest. To resolve the conflicting terminology: a group of contiguous
 data is a tree in a forest. This is a variable-length encoding, so the B-Tree
 rules about balance are not maintained, (_ie_, every path through the forest
 doesn't have to have the same number of trees.) By design-choice, the
 root-tree is always first. */
struct trie { struct tree_array forest; };
#ifndef TRIE_IDLE /* <!-- !zero */
#define TRIE_IDLE { ARRAY_IDLE }
#endif /* !zero --> */

static void tree_print(const struct tree *const tree, const size_t label) {
	size_t i;
	struct { int is_right; unsigned left, right; }
		edge[TRIE_BRANCH + TRIE_ORDER], e, *e1;
	unsigned lf = 0;
	assert(tree);
	printf("tree %lu: skip[", (unsigned long)label);
	for(i = 0; i < tree->bsize; i++)
		printf("%s%u", i ? "," : "", tree->branches[i].skip);
	printf("], left[");
	for(i = 0; i < tree->bsize; i++)
		printf("%s%u", i ? "," : "", tree->branches[i].left);
	printf("], leaf[");
	for(i = 0; i <= tree->bsize; i++) {
		printf("%s", i ? ", " : "");
		if(TRIESTR_TEST(tree->link, i)) printf("<%lu>", tree->leaves[i].link);
		else printf("%s", tree->leaves[i].data);
	}
	printf("].\n");
	edge[0].is_right = 0, edge[0].left = 0, edge[0].right = tree->bsize, i = 1;
	do {
		e = edge[--i];
		if(e.left == e.right) {
			const union leaf *leaf = tree->leaves + lf;
			printf("leaf%u %s: ", lf, e.is_right ? "right" : "left");
			if(TRIESTR_TEST(tree->link, lf)) printf("<%lu>", leaf->link);
			else printf("%s", leaf->data);
			printf("\n");
			lf++;
		} else {
			const struct branch *branch = tree->branches + e.left;
			printf("branch%u skip %u %s\n", e.left, branch->skip,
				e.is_right ? "right" : "left");
			e1 = edge + i++;
			e1->is_right = 1;
			e1->left = e.left + 1 + branch->left;
			e1->right = e.right;
			e1 = edge + i++;
			e1->is_right = 0;
			e1->left = e.left + 1;
			e1->right = e.left + 1 + branch->left;
		}
	} while(i);
}
static void trie_print(const struct trie *const trie) {
	size_t t;
	if(!trie->forest.size) printf("Empty forest.\n");
	else for(t = 0; t < trie->forest.size; t++)
		tree_print(trie->forest.data + t, t);
}

static void tree_graph(const struct trie *const trie, const size_t t,
	FILE *const fp) {
	const struct tree_array *const forest = &trie->forest;
	const struct tree *const tree = forest->data + t;
	unsigned long tlu = t;
	struct { enum { ROOT, UP, RIGHT, UP_RIGHT } flags; unsigned up, br0, br1; }
		edge[TRIE_BRANCH + TRIE_ORDER], e, *e1;
	unsigned i, lf;
	assert(forest && t < forest->size && fp);

	printf("(tree %lu: bmp", tlu);
	for(i = 0; i <= tree->bsize; i++)
		printf("%u", !!TRIESTR_TEST(tree->link, i));
	printf("'");
	for( ; i < TRIE_BITMAP<<3; i++)
		printf("%u", !!TRIESTR_TEST(tree->link, i));
	printf(")\n");

	fprintf(fp, "\tsubgraph cluster_tree%lu {\n"
		"\t\tstyle = filled; fillcolor = lightgray; label = \"tree %lu\";\n",
		tlu, tlu);
	edge[0].flags = ROOT, edge[0].br0 = 0, edge[0].br1 = tree->bsize, i = 1;
	lf = 0;
	do {
		e = edge[--i];
		if(e.br0 == e.br1) {
			const union leaf *leaf = tree->leaves + lf;
			if(TRIESTR_TEST(tree->link, lf)) {
				fprintf(fp,
					"\t\t// branch%lu_%u -> leaf%lu_%u directed to tree %lu\n",
					tlu, e.up, tlu, lf, leaf->link);
			} else {
				if(e.flags & UP) fprintf(fp,
					"\t\tbranch%lu_%u -> leaf%lu_%u [%scolor = royalblue];\n",
					tlu, e.up, tlu, lf,
					e.flags & RIGHT ? "" : "style = dashed, ");
				fprintf(fp, "\t\tleaf%lu_%u [label = \"%s\"];\n",
					tlu, lf, tree->leaves[lf].data);
			}
			lf++;
		} else {
			const struct branch *branch = tree->branches + e.br0;
			if(e.flags & UP)
				fprintf(fp, "\t\tbranch%lu_%u -> branch%lu_%u%s;\n",
				tlu, e.up, tlu, e.br0,
				e.flags & RIGHT ? "" : " [style = dashed]");
			fprintf(fp, "\t\tbranch%lu_%u "
				"[label = \"%u\", shape = none, fillcolor = none];\n",
				tlu, e.br0, branch->skip);
			e1 = edge + i++;
			e1->flags = UP | RIGHT;
			e1->up = e.br0;
			e1->br0 = e.br0 + 1 + branch->left;
			e1->br1 = e.br1;
			e1 = edge + i++;
			e1->flags = UP;
			e1->up = e.br0;
			e1->br0 = e.br0 + 1;
			e1->br1 = e.br0 + 1 + branch->left;
		}
	} while(i);
	fprintf(fp, "\t}\n");
	/* Do it a second time for inter-subgraph edges. */
	edge[0].flags = ROOT, edge[0].br0 = 0, edge[0].br1 = tree->bsize, i = 1;
	lf = 0;
	do {
		e = edge[--i];
		if(e.br0 == e.br1) {
			const union leaf *leaf = tree->leaves + lf;
			if(TRIESTR_TEST(tree->link, lf)) {
				const int dst_branch = leaf->link < forest->size
					&& forest->data[leaf->link].bsize;
				fprintf(fp,
					"\tbranch%lu_%u -> %s%lu_0 "
					"[lhead = cluster_tree%lu, ltail = cluster_tree%lu, "
					"color = firebrick%s];\n",
					tlu, e.up, dst_branch ? "branch" : "leaf",
					(unsigned long)leaf->link, tlu, (unsigned long)leaf->link,
					e.flags & RIGHT ? "" : ", style = dashed");
			}
			lf++;
		} else {
			const struct branch *branch = tree->branches + e.br0;
			e1 = edge + i++;
			e1->flags = UP | RIGHT;
			e1->up = e.br0;
			e1->br0 = e.br0 + 1 + branch->left;
			e1->br1 = e.br1;
			e1 = edge + i++;
			e1->flags = UP;
			e1->up = e.br0;
			e1->br0 = e.br0 + 1;
			e1->br1 = e.br0 + 1 + branch->left;
		}
	} while(i);
	fprintf(fp, "\n");
}
static int trie_graph(const struct trie *const trie, const char *const fn) {
	FILE *fp = 0;
	int success = 0;
	assert(trie && fn);
	if(!(fp = fopen(fn, "w"))) goto finally;
	printf("(trie graph %s)\n", fn);
	fprintf(fp, "digraph {\n"
		"\trankdir=TB;\n"
		"\tnode [shape = box, style = filled, fillcolor = lightsteelblue];\n"
		"\t// forest size %lu.\n"
		"\n", (unsigned long)trie->forest.size);
	if(!trie->forest.size) {
		fprintf(fp, "\tlabel = \"empty\";\n");
	} else {
		size_t t;
		for(t = 0; t < trie->forest.size; t++) tree_graph(trie, t, fp);
	}
	fprintf(fp, "}\n");
	success = 1;
finally:
	if(fp) fclose(fp);
	return success;
}

/** New idle `f`. */
static void trie(struct trie *const t) { assert(t), tree_array(&t->forest); }

/** Erase `f` to idle. */
static void trie_(struct trie *const t) { assert(t), tree_array_(&t->forest); }

/** Erase `f` but preserve any memory allocated. */
static void trie_clear(struct trie *const t) { assert(t), t->forest.size = 0; }

/** @return Only looks at the index for an item that possibly matches `key` or
 null if `key` is definitely not in `trie`. @order \O(`key.length`) */
static const char *trie_match(const struct trie *const trie,
	const char *const key) {
	struct { size_t i, next; } byte; /* `key` null checks. */
	size_t bit, t; /* `bit \in key`, `t \in forest`.  */
	struct { unsigned br0, br1, lf; } in_tree;
	struct tree *tree; /* `forest[t]`. */
	struct branch *branch;
	assert(trie && key);
	if(!trie->forest.size) return 0; /* Empty. */
	byte.i = 0, bit = 0, t = 0;
	do {
		tree = trie->forest.data + t, assert(t < trie->forest.size);
		in_tree.br0 = 0, in_tree.br1 = tree->bsize, in_tree.lf = 0;
		while(in_tree.br0 < in_tree.br1) { /* Tree branches. */
			branch = tree->branches + in_tree.br0;
			for(byte.next = (bit += branch->skip) >> 3; byte.i < byte.next;
				byte.i++) if(key[byte.i] == '\0') return 0;
			if(!TRIESTR_TEST(key, bit))
				in_tree.br1 = ++in_tree.br0 + branch->left;
			else
				in_tree.br0 += branch->left + 1, in_tree.lf += branch->left + 1;
			bit++;
		}
		assert(in_tree.br0 == in_tree.br1 && in_tree.lf <= tree->bsize);
	} while(TRIESTR_TEST(tree->link, in_tree.lf)
		&& (t = tree->leaves[in_tree.lf].link, 1));
	return tree->leaves[in_tree.lf].data;
}

/** @return `key` in `t` or null. @order \O(`key.length`) */
static const char *trie_get(const struct trie *const t, const char *const key) {
	const char *const leaf = trie_match(t, key);
	return leaf && !strcmp(leaf, key) ? leaf : 0;
}

/** @order O(trie.size) */
static size_t trie_size(const struct trie *const trie) {
	size_t i, count = 0;
	assert(trie);
	for(i = 0; i < trie->forest.size; i++)
		count += trie->forest.data[i].bsize + 1;
	assert(count >= trie->forest.size);
	count -= trie->forest.size - 1;
	return count;
}

/** @return Success splitting the `tree_idx` of `forest` where the added leaf
 is `tree_i`. */
static int trie_split(struct trie *const trie, const size_t forest_idx) {
	/* This is very unoptimised. */
	char fn[256];
	struct tree_array *const forest = &trie->forest;
	struct { struct tree *old, *new; } tree;
	struct {
		struct { unsigned branches; int balance; } parent, edge[2];
		struct { unsigned br0, br1, lf; } node;
	} go;
	struct { unsigned br0, br1; } dec;
	union leaf *leaf;
	struct branch *branch;
	unsigned i;
	assert(trie && forest_idx < forest->size);
	/* Create a new tree; after the pointers are stable. */
	if(!(tree.new = tree_array_new(forest))) return 0;
	tree.new->bsize = 0, memset(&tree.new->link, 0, TRIE_BITMAP),
		tree.new->leaves[0].data = 0;
	tree.old = forest->data + forest_idx;
	assert(tree.old->bsize == TRIE_BRANCH);
	printf("__split__(%lu)\n", forest_idx), trie_print(trie);

	/* Pick the greedy optimum balance for edge splitting. */
	go.parent.branches = go.parent.balance = tree.old->bsize;
	go.node.br0 = 0, go.node.br1 = tree.old->bsize, go.node.lf = 0;
	while(go.node.br0 < go.node.br1) {
		branch = tree.old->branches + go.node.br0;
		go.edge[0].branches = branch->left;
		go.edge[0].balance = (int)(tree.old->bsize - 2 * go.edge[0].branches);
		go.edge[1].branches = go.node.br1 - go.node.br0 - 1 - branch->left;
		go.edge[1].balance = (int)(tree.old->bsize - 2 * go.edge[1].branches);
		{
			unsigned j = 0, k;
			while(j < go.node.br0) printf("%u,", branch[j++].left);
			printf("[");
			while(j < go.node.br0 + 1) printf("%u,", branch[j++].left);
			printf("(");
			k = j;
			for( ; j < go.node.br0 + 1 + branch->left; j++)
				printf("%s%u", j == k ? "" : ",", branch[j].left);
			printf(")(");
			k = j;
			for( ; j < go.node.br1; j++)
				printf("%s%u", j == k ? "" : ",", branch[j].left);
			printf(")]");
			k = j;
			for( ; j < tree.old->bsize; j++)
				printf("%s%u", j == k ? "" : ",", branch[j].left);
			printf("; branch %u/%u, balance %d/%d.\n", go.edge[0].branches, go.edge[1].branches, go.edge[0].balance, go.edge[1].balance);
		}
		if(abs(go.parent.balance) < abs(go.edge[0].balance)) {
			if(abs(go.parent.balance) < abs(go.edge[1].balance)) break;
			else goto right;
		} else {
			if(abs(go.edge[0].balance) < abs(go.edge[1].balance)) goto left;
			else goto right;
		}
	left:
		printf("left\n");
		go.parent.branches = go.edge[0].branches;
		go.parent.balance = go.edge[0].balance;
		go.node.br1 = ++go.node.br0 + branch->left;
		continue;
	right:
		printf("right\n");
		go.parent.branches = go.edge[1].branches;
		go.parent.balance = go.edge[1].balance;
		go.node.br0 += branch->left + 1;
		go.node.lf  += branch->left + 1;
		continue;
	}
	printf("branches %u balance %d\n"
		"node br %u/%u lf %u\n", go.parent.branches, go.parent.balance,
		go.node.br0, go.node.br1, go.node.lf);
	/* Again and decrement the `left` by `parent.branches` from above. */
	dec.br0 = 0, dec.br1 = tree.old->bsize;
	while(dec.br0 < go.node.br0) {
		branch = tree.old->branches + dec.br0;
		if(go.node.br0 < dec.br0 + branch->left) {
			printf("left\n");
			dec.br1 = ++dec.br0 + branch->left;
			branch->left -= go.parent.branches;
		} else {
			printf("right\n");
			dec.br0 += branch->left + 1;
		}
	}
	/* Move leaves. */
	assert(go.node.lf + go.parent.branches + 1 <= tree.old->bsize + 1
		&& go.parent.branches /* Even for `TRIE_MAX_LEFT 0`? */);
	memcpy(tree.new->leaves, tree.old->leaves + go.node.lf,
		sizeof *leaf * (go.parent.branches + 1));
	memmove(tree.old->leaves + go.node.lf + 1,
		tree.old->leaves + go.node.lf + go.parent.branches + 1,
		sizeof *leaf * (tree.old->bsize - go.node.lf - go.parent.branches));
	tree.old->leaves[go.node.lf].link = (size_t)(tree.new - forest->data);
	{
		unsigned char *const bmp0 = tree.old->link,
			*const bmp1 = tree.new->link;
		const unsigned offset = go.node.lf, extent = go.parent.branches + 1,
			size = tree.old->bsize + 1;
		assert(offset + extent <= size);
		for(i = 0; i <= tree.old->bsize; i++) printf("%u", !!TRIESTR_TEST(bmp0, i)); printf("<-bmp0\n");
		for(i = 0; i <= tree.new->bsize; i++) printf("%u", !!TRIESTR_TEST(bmp1, i)); printf("<-bmp1\n");
		for(i = 0; i < extent; i++) /* Move bitmap into 0-filled. */
			if(TRIESTR_TEST(bmp0, i + offset)) TRIESTR_SET(bmp1, i);
		TRIESTR_SET(bmp0, offset); /* New link. */
		for(i = offset + 1 + extent; i < size; i++) /* Splice. */
			if(TRIESTR_TEST(bmp0, i)) TRIESTR_SET(bmp0, i - extent + 1);
			else TRIESTR_CLEAR(bmp0, i - extent + 1);
		for(i = offset + 1 + extent; i < size; i++) TRIESTR_CLEAR(bmp0, i);
		for(i = 0; i <= tree.old->bsize - go.parent.branches; i++) printf("%u", !!TRIESTR_TEST(bmp0, i)); printf("<-bmp0\n");
		for(i = 0; i <= tree.new->bsize + go.parent.branches; i++) printf("%u", !!TRIESTR_TEST(bmp1, i)); printf("<-bmp1\n");
	}
	/* Move branches. */
	assert(go.node.br1 - go.node.br0 == go.parent.branches);
	memcpy(tree.new->branches, tree.old->branches + go.node.br0,
		sizeof *branch * go.parent.branches);
	memmove(tree.old->branches + go.node.br0, tree.old->branches
		+ go.node.br1, sizeof *branch * (tree.old->bsize - go.node.br1));
	/* Move branch size. */
	tree.old->bsize -= go.parent.branches;
	tree.new->bsize += go.parent.branches;
	trie_print(trie);
	sprintf(fn, "graph/split-%lu-tree-%lu.gv", (unsigned long)trie_size(trie), (unsigned long)forest_idx);
	trie_graph(trie, fn);
	return 1;
}

/** @return The leftmost key of the `b` branch of tree `t` in `f`. */
static const char *key_sample(const struct tree_array *const ta,
	size_t tr, const unsigned br) {
	struct tree *tree = ta->data + tr;
	assert(ta && tr < ta->size && br <= tree->bsize);
	if(!TRIESTR_TEST(tree->link, br)) return tree->leaves[br].data;
	tr = tree->leaves[br].link;
	for( ; ; ) {
		tree = ta->data + tr;
		if(!TRIESTR_TEST(tree->link, 0)) return tree->leaves[0].data;
		tr = tree->leaves[0].link;
	}
}

static int trie_add_unique(struct trie *const trie, const char *const key) {
	struct tree_array *const forest = &trie->forest;
	static const char zero[TRIE_BITMAP]; /* For `memcmp`. */
	struct { size_t b, b0, b1; } in_bit;
	struct { size_t idx, tree_start_bit; } in_forest;
	struct { unsigned br0, br1, lf; } in_tree;
	struct tree *tree;
	struct branch *branch;
	union leaf *leaf;
	const char *sample;
	int is_write, is_right;

	assert(forest && key);
	printf("___*** ADD \"%s\" ***\n", key);
	/* Empty case: make a new tree with one leaf. */
	if(!forest->size) return (tree = tree_array_new(forest))
		&& (tree->bsize = 0, memset(&tree->link, 0, TRIE_BITMAP),
		tree->leaves[0].data = key, 1);

	in_bit.b = 0, in_forest.idx = 0, is_write = 0;
	do {
		in_forest.tree_start_bit = in_bit.b;
tree:
		assert(in_forest.idx < forest->size);
		tree = forest->data + in_forest.idx;
		sample = key_sample(forest, in_forest.idx, 0);
		printf("At the top of tree %lu, bit %lu, sample %s:\n", in_forest.idx,
			in_bit.b, sample), tree_print(tree, in_forest.idx);
		/* Pre-select `is_write` if the tree is not full and has no links. */
		if(!is_write && tree->bsize < TRIE_BRANCH
			&& !memcmp(&tree->link, zero, TRIE_BITMAP)) is_write = 1,
			printf("pre-select\n");
		in_bit.b0 = in_bit.b;
		in_tree.br0 = 0, in_tree.br1 = tree->bsize, in_tree.lf = 0;
		while(in_tree.br0 < in_tree.br1) {
			branch = tree->branches + in_tree.br0;
			/* Test all the skip bits. */
			for(in_bit.b1 = in_bit.b + branch->skip; in_bit.b < in_bit.b1;
				in_bit.b++) if(TRIESTR_DIFF(key, sample, in_bit.b)) goto leaf;
			/* Decision bit. */
			if(!TRIESTR_TEST(key, in_bit.b)) {
				in_tree.br1 = ++in_tree.br0 + branch->left;
				if(is_write) branch->left++;
			} else {
				in_tree.br0 += branch->left + 1;
				in_tree.lf  += branch->left + 1;
				sample = key_sample(forest, in_forest.idx, in_tree.lf);
			}
			in_bit.b0 = in_bit.b1, in_bit.b++;
		}
		assert(in_tree.br0 == in_tree.br1 && in_tree.lf <= tree->bsize);
	} while(TRIESTR_TEST(tree->link, in_tree.lf)
		&& (in_forest.idx = tree->leaves[in_tree.lf].link, 1));
	/* Got to the leaves; uniqueness guarantees that this is safe. */
	while(!TRIESTR_DIFF(key, sample, in_bit.b)) in_bit.b++;

leaf:
	if(TRIESTR_TEST(key, in_bit.b))
		is_right = 1, in_tree.lf += in_tree.br1 - in_tree.br0 + 1;
	else
		is_right = 0;
	printf("insert %s, at index %u bit %lu.\n", key, in_tree.lf, in_bit.b);
	assert(in_tree.lf <= tree->bsize + 1u);

	if(is_write) goto insert;
	/* If the tree is full, split it. */
	assert(tree->bsize <= TRIE_BRANCH);
	if(tree->bsize == TRIE_BRANCH
		&& !trie_split(trie, in_forest.idx)) return 0;
	/* Now we are sure that this tree is the one getting modified. */
	is_write = 1, in_bit.b = in_forest.tree_start_bit;
	goto tree;

insert:
	leaf = tree->leaves + in_tree.lf;
	printf("leaf[%u] memmove(%u, %u, %u)\n", tree->bsize, in_tree.lf+1, in_tree.lf, tree->bsize + 1 - in_tree.lf);
	memmove(leaf + 1, leaf, sizeof *leaf * (tree->bsize + 1 - in_tree.lf));
	leaf->data = key;

	branch = tree->branches + in_tree.br0;
	printf("branch[%u] memmove(%u, %u, %u)\n", tree->bsize, in_tree.br0+1, in_tree.br0, tree->bsize - in_tree.br0);
	if(in_tree.br0 != in_tree.br1) { /* Split `skip` with the existing branch. */
		assert(in_bit.b0 <= in_bit.b
			&& in_bit.b + !in_tree.br0 <= in_bit.b0 + branch->skip);
		printf("branch skip %u -> ", branch->skip);
		branch->skip -= in_bit.b - in_bit.b0 + !in_tree.br0;
		printf("%u\n", branch->skip);
	}
	memmove(branch + 1, branch, sizeof *branch * (tree->bsize - in_tree.br0));
	assert(in_tree.br1 - in_tree.br0 < 256
		&& in_bit.b >= in_bit.b0 + !!in_tree.br0
		&& in_bit.b - in_bit.b0 - !!in_tree.br0 < 256);
	branch->left = is_right ? (unsigned char)(in_tree.br1 - in_tree.br0) : 0;
	branch->skip = (unsigned char)(in_bit.b - in_bit.b0 - !!in_tree.br0);
	tree->bsize++;

	tree_print(tree, in_forest.idx);

	return 1;
}

/** @return If `key` is already in `t`, returns false, otherwise success.
 @throws[realloc, ERANGE] */
static int trie_add(struct trie *const trie, const char *const key)
	{ return trie_get(trie, key) ? 0 : trie_add_unique(trie, key); }

/** @return Whether `a` and `b` are equal up to the minimum. Used in
 <fn:trie_prefix>. */
/*static int trie_is_prefix(const char *a, const char *b) {
	for( ; ; a++, b++) {
		if(*a == '\0') return 1;
		if(*a != *b) return *b == '\0';
	}
}*/

static void trie_unused_coda(void);
static void trie_unused(void) {
	trie(0);
	trie_clear(0);
	trie_get(0, 0);
	trie_add(0, 0);
	trie_graph(0, 0);
	trie_unused_coda();
}
static void trie_unused_coda(void) { trie_unused(); }
