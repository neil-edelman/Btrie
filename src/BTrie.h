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

 Say something about B-tree.

 @fixme Strings can not be more then 8 characters the same. Have a leaf value
 255->leaf.bigskip+255. May double the code.

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
#define TRIE_MAX_LEFT 255 /* Worst-case all-left cap. `[0,max(tree.left=255)]` */
#define TRIE_BRANCH (TRIE_MAX_LEFT + 1) /* Maximum branches. */
#define TRIE_ORDER (TRIE_BRANCH + 1) /* Maximum branching factor / leaves. */
#define TRIE_BITMAP ((TRIE_ORDER - 1) / 8 + 1) /* Bitmap size in bytes. */

/** Fixed-maximum-size, pre-order tree to go in the forest. These are
 semi-implicit in that `right` is all the remaining branches after `left`.
 @fixme Save space with less then 256 by making it variable-width. */
struct tree {
	unsigned short bsize, /* +1 is the rank. */
		is_link[TRIE_BITMAP]; /* Bitmap associated to leaf. */
	struct branch { unsigned char left, skip; } branches[TRIE_BRANCH];
	union leaf { const char *data; /*size_t bigskip;*/ size_t link; }
		leaves[TRIE_ORDER];
};
MIN_ARRAY(tree, struct tree)
/** Trie-forest. We explicitly refer to a key and any data associated therewith
 as nodes. In B-Tree parlance, a group of contiguous data, made up of what we
 call nodes, is itself a node. To resolve this conflict, a "B-Trie" is a forest
 of trees. Leaves, which contain keys, and branches are called nodes. These are
 all non-empty complete binary trees; `branches = (leaves \in [1, order]) - 1`.
 The forest, as a whole, is a complete binary tree except the links to
 different trees, having `\sum_{trees} branches = \sum_{trees} leaves - trees`.
 B-Trie is a variable-length encoding, so the B-Tree rules about balance are
 not maintained, (_ie_, every path through the forest doesn't have to have the
 same number of trees.) By design-choice, the root-tree is always first, and
 link-trees are on top. `empty and !links or links < forest.size`. */
struct trie { struct tree_array forest; };
#ifndef TRIE_IDLE /* <!-- !zero */
#define TRIE_IDLE { ARRAY_IDLE }
#endif /* !zero --> */


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
	struct { size_t br0, br1, i; } in_tree;
	struct tree *tree; /* `forest[t]`. */
	struct branch *branch;
	assert(trie && key);
	if(!trie->forest.size) return 0; /* Empty. */
	for(byte.i = 0, bit = 0, t = 0; ; t = tree->leaves[in_tree.i].link) {
		tree = trie->forest.data + t, assert(t < trie->forest.size);
		in_tree.br0 = 0, in_tree.br1 = tree->bsize, in_tree.i = 0;
		while(in_tree.br0 < in_tree.br1) { /* Tree branches. */
			branch = tree->branches + in_tree.br0;
			for(byte.next = (bit += branch->skip) >> 3; byte.i < byte.next;
				byte.i++) if(key[byte.i] == '\0') return 0;
			if(!TRIESTR_TEST(key, bit))
				in_tree.br1 = ++in_tree.br0 + branch->left;
			else
				in_tree.br0 += branch->left + 1, in_tree.i += branch->left + 1;
			bit++;
		}
		assert(in_tree.br0 == in_tree.br1); /* Leaf. */
		if(!TRIESTR_TEST(tree->is_link, in_tree.i))
			return tree->leaves[in_tree.i].data;
	}
}

/** @return `key` in `t` or null. @order \O(`key.length`) */
static const char *trie_get(const struct trie *const t, const char *const key) {
	const char *const leaf = trie_match(t, key);
	return leaf && !strcmp(leaf, key) ? leaf : 0;
}



/* Debug. */
static void print_tree(const struct tree *);
static int trie_graph(const struct trie *const t, const char *const fn);

/** @return Success splitting the `tree_idx` of `forest` where the added leaf
 is `tree_i`. */
static int trie_split(struct tree_array *const forest, const size_t forest_idx) {
	char fn[256];
	struct { struct tree *old, *new; } tree;
	struct { int edge; unsigned br0, br1, br2; int balance; } in_tree[2];
	unsigned i = 0;
	struct branch *branch;
	tree.old = forest->data + forest_idx;
	assert(forest && forest_idx < forest->size
		&& tree.old->bsize == TRIE_BRANCH);
	if(!(tree.new = tree_array_new(forest))) return 0;

	/* print */
	print_tree(tree.old);
	sprintf(fn, "graph/split-%lu-%u-1.gv", forest_idx, 1 + tree.old->bsize);
	trie_graph((const struct trie *)forest, fn);

	/* Pick the optimum balance along the exterior for edge splitting. */
	branch = tree.old->branches + 0;
	in_tree[i].edge  = 1, in_tree[!i].edge = -1;
	in_tree[i].br0 = in_tree[!i].br0 = 1;
	in_tree[i].br1 = in_tree[!i].br1 = 1 + branch->left;
	in_tree[i].br2 = in_tree[!i].br2 = tree.old->bsize;
	assert(in_tree[i].br1 <= in_tree[i].br2);
	in_tree[i].balance = (int)(in_tree[i].br2 - 2 * in_tree[i].br1);
	in_tree[!i].balance = (int)(in_tree[i].br2
		- 2 * (in_tree[i].br1 - in_tree[i].br0));
	{
		unsigned j;
		printf("egde %d: ", in_tree[i].edge);
		for(j = 0; j < in_tree[i].br0; j++) printf("%u ", branch[j].left);
		printf("[");
		for( ; j < in_tree[i].br1; j++) printf("%u ", branch[j].left);
		printf("|");
		for( ; j < in_tree[i].br2; j++) printf(" %u", branch[j].left);
		printf("]");
		for( ; j < tree.old->bsize; j++) printf(" %u", branch[j].left);
		printf(" balance %d; egde %d: ", in_tree[i].balance, in_tree[!i].edge);
		for(j = 0; j < in_tree[!i].br0; j++) printf("%u ", branch[j].left);
		printf("[");
		for( ; j < in_tree[!i].br1; j++) printf("%u ", branch[j].left);
		printf("|");
		for( ; j < in_tree[!i].br2; j++) printf(" %u", branch[j].left);
		printf("]");
		for( ; j < tree.old->bsize; j++) printf(" %u", branch[j].left);
		printf(" balance %d.\n", in_tree[!i].balance);
	}
	if(in_tree[i].balance < 0) { /* Should go left. */
		assert(branch->left);
		i = !i;
		do {
			{
				unsigned j;
				printf("egde %d: ", in_tree[i].edge);
				for(j = 0; j < in_tree[i].br0; j++) printf("%u ", branch[j].left);
				printf("[");
				for( ; j < in_tree[i].br1; j++) printf("%u ", branch[j].left);
				printf("|");
				for( ; j < in_tree[i].br2; j++) printf(" %u", branch[j].left);
				printf("]");
				for( ; j < tree.old->bsize; j++) printf(" %u", branch[j].left);
				printf(" balance %d; egde %d: ", in_tree[i].balance, in_tree[!i].edge);
				for(j = 0; j < in_tree[!i].br0; j++) printf("%u ", branch[j].left);
				printf("[");
				for( ; j < in_tree[!i].br1; j++) printf("%u ", branch[j].left);
				printf("|");
				for( ; j < in_tree[!i].br2; j++) printf(" %u", branch[j].left);
				printf("]");
				for( ; j < tree.old->bsize; j++) printf(" %u", branch[j].left);
				printf(" balance %d.\n", in_tree[!i].balance);
			}
			assert(in_tree[i].br0 <= in_tree[i].br1);
			if(in_tree[i].br0 == in_tree[i].br1) break;
			if(!(branch = tree.old->branches + in_tree[i].br0 + 1)->left)
				break;
			i = !i;
			in_tree[i].edge = in_tree[!i].edge - 1;
			in_tree[i].br0 = in_tree[!i].br0 + 1;
			in_tree[i].br1 = in_tree[i].br0 + branch->left;
			in_tree[i].br2 = in_tree[!i].br1;
			in_tree[i].balance = (int)(in_tree[i].br2 - 2 * (in_tree[i].br1 - in_tree[i].br0));
			if(in_tree[i].balance >= 0) { /* Crosses zero. */
				if(in_tree[i].balance == 0) {printf("found middle.\n");break;} /* Found the exact middle. */
				assert(0);
			}
		} while(1);
		/* ... */
	} else if(in_tree[i].balance > 0) { /* Should go right. */
		printf("Right selected.\n");
		i = !i;
		in_tree[i].edge = in_tree[!i].edge + 1;
		/* ... */
		assert(0);
	} else { /* Guessed 1-right correctly. */
		printf("Guessed correctly right, %d.\n", in_tree[i].edge);
	}
	printf("splitting at edge %d.\n", in_tree[i].edge);
	assert(0);
	return 0;
}

/** @return The leftmost key of the `b` branch of tree `t` in `f`. */
static const char *key_sample(const struct tree_array *const ta,
	size_t tr, const unsigned br) {
	struct tree *tree = ta->data + tr;
	assert(ta && tr < ta->size && br <= tree->bsize);
	if(!TRIESTR_TEST(tree->is_link, br)) return tree->leaves[br].data;
	tr = tree->leaves[br].link;
	for( ; ; ) {
		tree = ta->data + tr;
		if(!TRIESTR_TEST(tree->is_link, 0)) return tree->leaves[0].data;
		tr = tree->leaves[0].link;
	}
}

static int add_unique(struct tree_array *const forest, const char *const key) {
	static const char zero[TRIE_BITMAP]; /* For `memcmp`. */
	struct { size_t b, b0, b1; } in_bit;
	struct { size_t idx, tree_start_bit; } in_forest;
	struct { unsigned br0, br1, i; } in_tree;
	struct tree *tree;
	struct branch *branch;
	union leaf *leaf;
	const char *sample;
	int is_write, is_right;

	assert(forest && key);
	printf("___*** ADD \"%s\" ***\n", key);
	/* Empty case: make a new tree with one leaf. */
	if(!forest->size) return (tree = tree_array_new(forest))
		&& (tree->bsize = 0, memset(&tree->is_link, 0, TRIE_BITMAP),
		tree->leaves[0].data = key, 1);

	in_bit.b = 0, in_forest.idx = 0, is_write = 0;
	do {
		in_forest.tree_start_bit = in_bit.b;
tree:
		assert(in_forest.idx < forest->size);
		tree = forest->data + in_forest.idx;
		sample = key_sample(forest, in_forest.idx, 0);
		printf("At the top of tree %lu, bit %lu, sample %s:\n", in_forest.idx,
			in_bit.b, sample), print_tree(tree);
		/* Pre-select `is_write` if the tree is not full and has no links. */
		if(!is_write && tree->bsize < TRIE_BRANCH
			&& !memcmp(&tree->is_link, zero, TRIE_BITMAP)) is_write = 1,
			printf("pre-select\n");
		in_bit.b0 = in_bit.b;
		in_tree.br0 = 0, in_tree.br1 = tree->bsize, in_tree.i = 0;
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
				in_tree.i   += branch->left + 1;
				sample = key_sample(forest, in_forest.idx, in_tree.i);
			}
			in_bit.b0 = in_bit.b1, in_bit.b++;
		}
		assert(in_tree.br0 == in_tree.br1 && in_tree.i <= tree->bsize);
	} while(TRIESTR_TEST(tree->is_link, in_tree.i)
		&& (in_forest.idx = tree->leaves[in_tree.i].link, 1));
	/* Got to the leaves; uniqueness guarantees that this is safe. */
	while(!TRIESTR_DIFF(key, sample, in_bit.b)) in_bit.b++;

leaf:
	if(TRIESTR_TEST(key, in_bit.b))
		is_right = 1, in_tree.i += in_tree.br1 - in_tree.br0 + 1;
	else
		is_right = 0;
	printf("insert %s, at index %u bit %lu.\n", key, in_tree.i, in_bit.b);
	assert(in_tree.i <= tree->bsize + 1u);

	if(is_write) goto insert;
	/* If the tree is full, split it. */
	assert(tree->bsize <= TRIE_BRANCH);
	if(tree->bsize == TRIE_BRANCH
		&& !trie_split(forest, in_forest.idx)) return 0;
	/* Now we are sure that this tree is the one getting modified. */
	is_write = 1, in_bit.b = in_forest.tree_start_bit;
	goto tree;

insert:
	leaf = tree->leaves + in_tree.i;
	printf("leaf[%u] memmove(%u, %u, %u)\n", tree->bsize, in_tree.i+1, in_tree.i, tree->bsize + 1 - in_tree.i);
	memmove(leaf + 1, leaf, sizeof *leaf * (tree->bsize + 1 - in_tree.i));
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

	print_tree(tree);

	return 1;
}

/** @order \log{`f`} */
static int trie_add_unique(struct tree_array *const f, const char *const key) {
	struct { size_t b, b0, b1; } bit; /* `b \in [b0, b1]` next branch. */
	struct { struct tree *tree; size_t t; size_t bit; const char *key;
		unsigned b0, b1, i; /* Node branch range, next leaf accumulator. */
		int is_full;
		enum { TREE_LEFT, RIGHT, TOP, TOP_RIGHT } in; } t; /* `t \in f`. */
	struct { size_t t; size_t bit; unsigned i; } p; /* Parent valid if `t.t`. */
	const char *sample; /* String from trie to compare with `key`. */
	struct branch *branch;
	union leaf *leaf;
	unsigned lt;

	assert(f && key);
	printf("*** ADD \"%s\" ***\n", key);
	/* Empty case; make a new tree. */
	if(!f->size) return (t.tree = tree_array_new(f))
		&& (t.tree->bsize = 0, memset(&t.tree->is_link, 0, TRIE_BITMAP),
		t.tree->leaves[0].data = key, 1);

	/* Start at the beginning of the key and root of the forest. */
	bit.b = 0, t.t = 0;
	do {
		t.bit = bit.b; /* Cache bit value for backtracking. */
tree: /* Descend tree. */
		assert(t.t < f->size);
		t.b0 = 0, t.b1 = (t.tree = f->data + t.t)->bsize, t.i = 0;
		assert(t.tree->bsize <= TRIE_BRANCH);
		t.is_full = (t.tree->bsize == TRIE_BRANCH);
		printf("tree "), print_tree(t.tree);
		bit.b0 = bit.b;
		sample = key_sample(f, t.t, t.i);
		while(t.b0 < t.b1) { /* Branches. */
			branch = t.tree->branches + t.b0;
			for(bit.b1 = bit.b + branch->skip; bit.b < bit.b1; bit.b++)
				if(TRIESTR_DIFF(key, sample, bit.b)) goto insert;
			lt = branch->left + 1;
			if(!TRIESTR_TEST(key, bit.b)) {
				if(!t.is_full) branch->left =(unsigned char)lt,assert(lt < 256);
				t.b1 = t.b0++ + lt;
			} else {
				t.b0 += lt, t.i += lt;
				/*sample = (t.overflow & LINK) ? link_key(f,
					t.tree->leaves[t.i].link) : t.tree->leaves[t.i].data;*/
				sample = key_sample(f, t.t, t.i);
			}
			bit.b++, bit.b0 = bit.b1;
		}
		assert(t.b0 == t.b1 && t.i <= t.tree->bsize);
		/* If link-tree, `t.t` is updated and we continue down another tree. */
	} while(TRIESTR_TEST(t.tree->is_link, t.i) && (p.t = t.t, p.bit = t.bit,
		t.t = t.tree->leaves[p.i = t.i].link, 1));
	while(!TRIESTR_DIFF(key, sample, bit.b)) bit.b++; /* Got to the leaves. */
insert:
	/* Is it a right insertion? Is it above the root of the tree? */
	printf("diff %lu\n", bit.b);
	t.in = !!TRIESTR_TEST(key, bit.b) | ((!t.b0 && t.tree->bsize) << 1);
	printf("key is: %s, %s. leaf %u\n", t.in & RIGHT ? "right" : "left", t.in & TOP ? "top" : "tree", t.i);
	if(t.in & RIGHT) t.i += (lt = t.b1 - t.b0) + 1; else lt = 0;
	assert(t.i <= t.tree->bsize + 1u);

	/* Split and backtrack once on order boundary so the trie is not compact. */
	if(t.is_full) {
		assert(0);
		/* Split:
		 * Go down the tree until sign changes right - left. Make sure to
		 account for the future insert.
		 * Split it; make sure that the root is always [0]. */
		/* Fail-fast; single-point-of-failure before modification. */
		/*if(!tree_array_reserve(&f->forest,
			f->forest.size + 1 + !is_vacant_parent)) return 0;
		}*/
	}

	/* Insert a leaf into the vacant leaf tree. */
	leaf = t.tree->leaves + t.i;
	printf("leaf[%u] memmove(%u, %u, %u)\n", t.tree->bsize+1, t.i+1, t.i, t.tree->bsize + 1 -t.i);
	memmove(leaf + 1, leaf, sizeof *leaf * (t.tree->bsize + 1 - t.i));
	leaf->data = key;

	/* Insert a branch into the vacant branch tree; must be widened already. */
	branch = t.tree->branches + t.b0;
	printf("branch[%u] memmove(%u, %u, %u)\n", t.tree->bsize, t.b0+1, t.b0, t.tree->bsize - t.b0);
	if(t.b0 != t.b1) { /* Split `skip` with the existing branch. */
		assert(bit.b0 <= bit.b && bit.b + !t.b0 <= bit.b0 + branch->skip);
		printf("branch skip %u -> ", branch->skip);
		branch->skip -= bit.b - bit.b0 + !t.b0;
		printf("%u\n", branch->skip);
	}
	memmove(branch + 1, branch, sizeof *branch * (t.tree->bsize - t.b0));
	branch->left = lt;
	assert(bit.b >= bit.b0 + !!t.b0), branch->skip = bit.b - bit.b0 - !!t.b0;
	t.tree->bsize++;

	print_tree(t.tree);

	return 1;
}

/** @return If `key` is already in `t`, returns false, otherwise success.
 @throws[realloc, ERANGE] */
static int trie_add(struct trie *const trie, const char *const key)
	{ return trie_get(trie, key) ? 0 : /*trie_*/add_unique(&trie->forest, key); }



/** @return Whether `a` and `b` are equal up to the minimum. Used in
 <fn:trie_prefix>. */
/*static int trie_is_prefix(const char *a, const char *b) {
	for( ; ; a++, b++) {
		if(*a == '\0') return 1;
		if(*a != *b) return *b == '\0';
	}
}*/

static void print_tree(const struct tree *const tree) {
	unsigned i;
	assert(tree);
	printf("tree:skip[");
	for(i = 0; i < tree->bsize; i++)
		printf("%s%u", i ? "," : "", tree->branches[i].skip);
	printf("],left[");
	for(i = 0; i < tree->bsize; i++)
		printf("%s%u", i ? "," : "", tree->branches[i].left);
	printf("],leaf[");
	for(i = 0; i <= tree->bsize; i++) {
		printf("%s", i ? ", " : "");
		if(TRIESTR_TEST(tree->is_link, i)) {
			printf("%lu", tree->leaves[i].link);
		} else {
			printf("%s", tree->leaves[i].data);
		}
	}
	printf("].\n");
}

#if 0
static void print_trie(const struct trie *const t) {
	size_t i;
	assert(t);
	printf("forest {\n");
	for(i = 0; i < t->forest.size; i++)
		printf("\t"), print_tree(t, i);
	printf("}\n");
}
#endif

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
		} else if(!TRIESTR_TEST(tree->is_link, br) /*t >= f->links*/) {
			fprintf(fp, "\t\tbranch%u_%u -> leaf%u_%u "
				"[style = dashed, color = royalblue];\n",
				t, br, t, trie_left_leaf(tree, br));
		}
		if(right) {
			fprintf(fp, "\t\tbranch%u_%u -> branch%u_%u;\n",
				t, br, t, br + left + 1);
		} else if(!TRIESTR_TEST(tree->is_link, (br + left))/*t >= f->links*/) {
			fprintf(fp, "\t\tbranch%u_%u -> leaf%u_%u "
				"[color = royalblue];\n",
				t, br, t, trie_left_leaf(tree, br) + left + 1);
		}
	}
	fprintf(fp, "\t\t// leaves\n");
	for(lf = 0; lf <= tree->bsize; lf++) {
		if(TRIESTR_TEST(tree->is_link, lf)) {
		} else {
			fprintf(fp,
				"\t\tleaf%u_%u [label = \"%s\"];\n",
				t, lf, tree->leaves[lf].data);
		}
	}
	fprintf(fp, "\t}\n");

/*		for(lf = 0; lf <= tree->bsize; lf++) {
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
		}*/
	fprintf(fp, "\n");
}

static int trie_graph(const struct trie *const f, const char *const fn) {
	FILE *fp = 0;
	int success = 0;
	assert(f && fn);
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
		tree_graph(f, t, fp);
		/*fprintf(fp, "\t// the following are not reachable from the root\n"
			"\tnode [fillcolor = red];\n"
			"\n");*/
	}
	fprintf(fp, "}\n");
	success = 1;
finally:
	if(fp) fclose(fp);
	return success;
}
