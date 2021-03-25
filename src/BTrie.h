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


#define TRIESTR_TEST(a, i) (a[i >> 3] & (128 >> (i & 7)))
#define TRIESTR_DIFF(a, b, i) ((a[i >> 3] ^ b[i >> 3]) & (128 >> (i & 7)))
#define TRIESTR_SET(a, i) (a[i >> 3] |= 128 >> (i & 7))
#define TRIESTR_CLEAR(a, i) (a[i >> 3] &= ~(128 >> (i & 7)))
#define TRIE_MAX_LEFT 3 /* Worst-case all-left cap. `[0,max(tree.left=255)]` */
#define TRIE_BRANCH (TRIE_MAX_LEFT + 1) /* Maximum branches. */
#define TRIE_ORDER (TRIE_BRANCH + 1) /* Maximum branching factor / leaves. */
#define TRIE_BITMAP ((TRIE_ORDER - 1) / 8 + 1) /* Bitmap size in bytes. */

/** Fixed-maximum-size, pre-order tree to go in the forest. These are
 semi-implicit in that `right` is all the remaining branches after `left`.
 @fixme Save space with less then 256 by making it variable-width. */
struct tree {
	unsigned short bsize; /* +1 is the rank. */
	union {
		struct { unsigned char left, right; } uc;
		unsigned short us;
	} link;
	struct branch { unsigned char left, skip; } branches[TRIE_BRANCH];
	union leaf { const char *data; /*size_t bigskip;*/ size_t link; }
		leaves[TRIE_ORDER];
};
MIN_ARRAY(tree, struct tree)
/** Trie-forest. We explicitly refer to leaves, which contain keys, and
 branches, as nodes in the binary-tree. Therefore, to resolve the conflicting
 'nodes' in B-Tree parlance, a group of contiguous data is a tree in a forest.
 These are all non-empty complete binary trees;
 `branches = (leaves \in [1, order]) - 1`. The forest, as a whole, is a
 complete binary tree except the links to different trees, having
 `\sum_{trees} branches = \sum_{trees} leaves - trees`. B-Trie is a
 variable-length encoding, so the B-Tree rules about balance are not
 maintained, (_ie_, every path through the forest doesn't have to have the
 same number of trees.) By design-choice, the root-tree is always first, and
 link-trees are on top. `empty and !links or links < forest.size`. */
struct trie { struct tree_array forest; };
#ifndef TRIE_IDLE /* <!-- !zero */
#define TRIE_IDLE { ARRAY_IDLE }
#endif /* !zero --> */

static void tree_print(const struct tree *const tree, const size_t label) {
	unsigned i, st = 0;
	struct { unsigned left, right, end; } stack[TRIE_ORDER];
	assert(tree);
	printf("tree %lu:\n"
		"\tskip[", (unsigned long)label);
	for(i = 0; i < tree->bsize; i++)
		printf("%s%u", i ? "," : "", tree->branches[i].skip);
	printf("],\n"
		"\tleft[");
	for(i = 0; i < tree->bsize; ) {
		printf("%u", tree->branches[i].left);
		stack[st].left = i + 1;
		stack[st].right = i + 1 + tree->branches[i].left;
		stack[st].end = st ? i < stack[st - 1].right ? stack[st - 1].right
			: stack[st - 1].end : tree->bsize;
		st++, i++;
edges:
		if(!st) { assert(i == tree->bsize); break; }
		if(i == stack[st-1].left) printf("(");
		if(i == stack[st-1].right) printf("|");
		if(i == stack[st-1].end) { printf(")"); st--; goto edges; }
	}
	assert(st == 0);
	printf("],\n"
		"\tleaf[");
	for(i = 0; i <= tree->bsize; i++) {
		printf("%s", i ? ", " : "");
		if(!i && tree->link.uc.left
			|| i == tree->bsize && tree->link.uc.right) {
			printf("<%lu>", tree->leaves[i].link);
		} else {
			printf("%s", tree->leaves[i].data);
		}
	}
	printf("].\n");
}

static void trie_print(const struct trie *const trie) {
	size_t t;
	if(!trie->forest.size) printf("Empty forest.\n");
	else for(t = 0; t < trie->forest.size; t++)
		tree_print(trie->forest.data + t, t);
}

static void tree_graph(const struct tree *const tree, const size_t t,
	FILE *const fp) {
	unsigned long tlu = t;
	unsigned i, st = 0, lf = 0;
	struct { unsigned from, left, right, end; } stack[TRIE_ORDER];
	assert(tree && fp);
	fprintf(fp, "\tsubgraph cluster_tree%lu {\n"
		"\t\tstyle = filled; fillcolor = lightgray; label = \"tree %lu\";\n",
		tlu, tlu);
	fprintf(fp, "\t\t// branches\n");
	for(i = 0; i < tree->bsize; ) {
		fprintf(fp, "\t\tbranch%lu_%u "
		"[label = \"%u\", shape = none, fillcolor = none];\n",
		tlu, i, tree->branches[i].skip);
		stack[st].from = i;
		stack[st].left = i + 1;
		stack[st].right = i + 1 + tree->branches[i].left;
		stack[st].end = st ? i < stack[st - 1].right ? stack[st - 1].right
			: stack[st - 1].end : tree->bsize;
		st++, i++;
edges:
		if(!st) { assert(i == tree->bsize); break; }
		if(i == stack[st-1].left) {
			if(i == stack[st-1].right) fprintf(fp,
				"\t\tbranch%lu_%u -> leaf%lu_%u "
				"[style = dashed, color = royalblue];\n",
				tlu, stack[st-1].from, tlu, lf++);
			else fprintf(fp,
				"\t\tbranch%lu_%u -> branch%lu_%u [style = dashed];\n",
				tlu, stack[st-1].from, tlu, i);
		}
		if(i == stack[st-1].right) {
			if(i == stack[st-1].end) fprintf(fp,
				"\t\tbranch%lu_%u -> leaf%lu_%u [color = royalblue];\n",
				tlu, stack[st-1].from, tlu, lf++);
			else fprintf(fp,
				"\t\tbranch%lu_%u -> branch%lu_%u;\n",
				tlu, stack[st-1].from, tlu, i);
		}
		if(i == stack[st-1].end) { st--; goto edges; }
	}
	assert(lf == 0 || lf == tree->bsize + 1);
	fprintf(fp, "\t\t// leaves\n");
	for(i = 0; i <= tree->bsize; i++) {
		fprintf(fp, "\t\tleaf%lu_%u [label = \"", tlu, i);
		if(!i && tree->link.uc.left
			|| i == tree->bsize && tree->link.uc.right) {
			fprintf(fp, "[%lu]", tree->leaves[i].link);
		} else {
			fprintf(fp, "%s", tree->leaves[i].data);
		}
		fprintf(fp, "\"];\n");
	}
	fprintf(fp, "\t}\n");
	/*fprintf(fp,
				"\t%s%u_%u -> %s%u_%u [ltail=cluster_tree%u, "
				"lhead=cluster_tree%u, color = firebrick, style = %s];\n",
				tree->bsize ? "branch" : "leaf", t, parent,
				link->bsize ? "branch" : "leaf", l, 0,
				t, l, is_left ? "dashed" : "solid"); */
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
		for(t = 0; t < trie->forest.size; t++)
			tree_graph(trie->forest.data + t, t, fp);
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
	for(byte.i = 0, bit = 0, t = 0; ; t = tree->leaves[in_tree.lf].link) {
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
		if(in_tree.lf == 0 && tree->link.uc.left
			|| in_tree.lf == tree->bsize && tree->link.uc.right) continue;
		break;
	}
	return tree->leaves[in_tree.lf].data;
}

/** @return `key` in `t` or null. @order \O(`key.length`) */
static const char *trie_get(const struct trie *const t, const char *const key) {
	const char *const leaf = trie_match(t, key);
	return leaf && !strcmp(leaf, key) ? leaf : 0;
}

/** @return Success splitting `tree_idx` of `forest`. @throws[malloc] */
static int trie_split(struct tree_array *const forest,
	const size_t forest_idx) {
	char fn[256];
	struct { struct tree *old, *new; } tree;
	struct { unsigned br0, br1, lf; } in_tree[2];
	struct { unsigned sub; int balance; } choice[2];
	unsigned i; /* Binary index in `in_tree`. */
	enum { RIGHT, LEFT } c, init_c; /* Binary index in `choice`. */
	struct branch *branch;
	tree.old = forest->data + forest_idx;
	assert(forest && forest_idx < forest->size
		&& tree.old->bsize == TRIE_BRANCH);
	if(!(tree.new = tree_array_new(forest))) return 0;

	/* This is just so that we can print it. */
	tree.new->bsize = 0, tree.new->link.us = 0, tree.new->leaves[0].data = 0;
	sprintf(fn, "graph/split-%lu-%u-1.gv", forest_idx, 1 + tree.old->bsize);
	trie_graph((const struct trie *)forest, fn);

	/* Pick the greedy optimum balance on the outside edge. */
	i = 0;
	in_tree[i].br0 = 0, in_tree[i].br1 = tree.old->bsize, in_tree[i].lf = 0;
	printf("init: in_tree br[%u/%u] %u\n", in_tree[i].br0, in_tree[i].br1, in_tree[i].lf);
	branch = tree.old->branches + in_tree[i].br0;
	/* Left edge coming from root. */
	choice[0].sub = branch->left;
	choice[0].balance = (int)((tree.old->bsize - choice[0].sub)  - choice[0].sub);
	/* Right edge coming from root. */
	choice[1].sub = in_tree[i].br1 - in_tree[i].br0 - 1 - branch->left;
	choice[1].balance = (int)((tree.old->bsize - choice[1].sub) - choice[1].sub);
	printf("tree bsize %u: branches %u/%u, balance %d/%d\n", tree.old->bsize, choice[0].sub, choice[1].sub, choice[0].balance, choice[1].balance);
	i = !i;
	if(c = init_c = (abs(choice[0].balance) < abs(choice[1].balance))) do {
		/* Go leftwards until it reaches the closest balance to zero. */
		in_tree[i].br1 = (in_tree[i].br0 = in_tree[!i].br0 + 1) + branch->left;
		in_tree[i].lf = in_tree[!i].lf;
		printf("in_tree left br[%u/%u] %u\n", in_tree[i].br0, in_tree[i].br1, in_tree[i].lf);
		branch = tree.old->branches + in_tree[i].br0;
		choice[c].sub = branch->left;
		choice[c].balance = (int)((tree.old->bsize - choice[c].sub) - choice[c].sub);
		printf("tree left bsize %u: branches %u, balance %d\n", tree.old->bsize, choice[c].sub, choice[c].balance);
		c = !c, i = !i;
		printf("%d < %d?\n", abs(choice[!i].balance), abs(choice[i].balance));
	} while(abs(choice[!i].balance) < abs(choice[i].balance));
	else do { /* Go rightwards until it reaches the closest balance to zero. */
		in_tree[i].br0 = in_tree[!i].br0 + branch->left + 1;
		in_tree[i].br1 = in_tree[!i].br1;
		in_tree[i].lf   = in_tree[!i].br0 + branch->left + 1;
		printf("in_tree right br[%u/%u] %u\n", in_tree[i].br0, in_tree[i].br1, in_tree[i].lf);
		branch = tree.old->branches + in_tree[i].br0;
		choice[c].sub = in_tree[i].br1 - in_tree[i].br0 - 1 - branch->left;
		choice[c].balance = (int)((tree.old->bsize - choice[c].sub) - choice[c].sub);
		printf("tree right bsize %u: branches %u, balance %d\n", tree.old->bsize, choice[c].sub, choice[c].balance);
		c = !c, i = !i;
		printf("%d < %d?\n", abs(choice[!i].balance), abs(choice[i].balance));
	} while(abs(choice[!i].balance) < abs(choice[i].balance));
	printf("final: in_tree %s br[%u/%u] %u\n", init_c ? "left" : "right", in_tree[i].br0, in_tree[i].br1, in_tree[i].lf);
	printf("final: choice sub %u balance %d\n", choice[c].sub, choice[c].balance);
	/* Split semi-balanced part of it up to the `new` tree. */
	branch = tree.old->branches + in_tree[i].br0;
	tree.new->bsize = (unsigned short)choice[c].sub, printf("new bsize %u\n", tree.new->bsize);
	if(init_c == LEFT) {
		assert(in_tree[i].lf == 0);
		tree.new->link.uc.left = tree.old->link.uc.left;
		tree.new->link.uc.right = 0;
		tree.old->link.uc.left = 0;
		{ /* Decrement the `left` counters. */
			unsigned j;
			printf("dec %u the first %u.\n", choice[c].sub, in_tree[!i].br0);
			for(j = 0; j < in_tree[!i].br0; j++)
				assert(tree.old->branches[j].left >= choice[c].sub),
				tree.old->branches[j].left -= choice[c].sub;
		}
	} else { /* `RIGHT` */
		assert(in_tree[i].lf + choice[c].sub == tree.old->bsize); /* Maybe? */
		tree.new->link.uc.left = 0;
		tree.new->link.uc.right = tree.old->link.uc.right;
		tree.old->link.uc.right = 0;
	}
	printf("memcpy new, %u, [0..%u) @%lu\n",
		in_tree[!i].br0, choice[c].sub, sizeof *tree.old->branches);
	memcpy(tree.new->branches, tree.old->branches + in_tree[!i].br0,
		sizeof *tree.old->branches * choice[c].sub);
	memmove(tree.old->branches + in_tree[!i].br0,
		tree.old->branches + in_tree[!i].br1,
		sizeof *tree.old->branches * (tree.old->bsize - in_tree[!i].br1));
	memcpy(tree.new->leaves, tree.old->leaves + in_tree[!i].lf,
		sizeof *tree.old->leaves * (choice[c].sub + 1));
	memmove(tree.old->leaves + in_tree[!i].lf,
		tree.old->leaves + in_tree[i].lf + choice[c].sub + 1,
		sizeof *tree.old->leaves * (tree.old->bsize - in_tree[!i].br1));
	tree.old->bsize -= choice[c].sub;

	sprintf(fn, "graph/split-%lu-%u-2.gv", forest_idx, 1 + tree.old->bsize);
	trie_graph((const struct trie *)forest, fn);
	assert(0);
	return 0;
}

/** @return The leftmost key of the `b` branch of tree `t` in `f`. */
static const char *key_sample(const struct tree_array *const ta,
	size_t tr, const unsigned br) {
	struct tree *tree = ta->data + tr;
	assert(ta && tr < ta->size && br <= tree->bsize);
	if(br || !tree->link.uc.left) return tree->leaves[br].data;
	tr = tree->leaves[br].link;
	for( ; ; ) {
		if(!(tree = ta->data + tr)->link.uc.left) return tree->leaves[0].data;
		tr = tree->leaves[0].link;
	}
}

/** @order \log{`f`} */
static int trie_add_unique(struct tree_array *const forest, const char *const key) {
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
		&& (tree->bsize = 0, tree->link.us = 0, tree->leaves[0].data = key, 1);

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
		if(!is_write && tree->bsize < TRIE_BRANCH && !tree->link.us)
			is_write = 1, printf("pre-select\n");
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
				in_tree.lf   += branch->left + 1;
				sample = key_sample(forest, in_forest.idx, in_tree.lf);
			}
			in_bit.b0 = in_bit.b1, in_bit.b++;
		}
		assert(in_tree.br0 == in_tree.br1 && in_tree.lf <= tree->bsize);
	} while((!in_tree.lf && tree->link.uc.left
		|| in_tree.lf == tree->bsize && tree->link.uc.right)
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
		&& !trie_split(forest, in_forest.idx)) return 0;
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
	{ return trie_get(trie, key) ? 0 : trie_add_unique(&trie->forest, key); }

#if 0 /* Unused yet. */
/** @return Whether `a` and `b` are equal up to the minimum. Used in
 <fn:trie_prefix>. */
static int trie_is_prefix(const char *a, const char *b) {
	for( ; ; a++, b++) {
		if(*a == '\0') return 1;
		if(*a != *b) return *b == '\0';
	}
}
#endif


#if 0
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
#endif


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
