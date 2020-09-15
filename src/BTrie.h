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
		if(min_capacity <= a->capacity) return 1; \
		c0 = a->capacity; \
		if(c0 < 3) c0 = 3; \
	} else { /* Idle. */ \
		if(!min_capacity) return 1; \
		c0 = 3; \
	} \
	if(min_capacity > max_size) return errno = ERANGE, 0; \
	/* `c_n = a1.625^n`, approximation golden ratio `\phi ~ 1.618`. */ \
	while(c0 < min_capacity) { \
		size_t c1 = c0 + (c0 >> 1) + (c0 >> 3); \
		if(c0 >= c1) { c0 = max_size; break; } \
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


/** Tries are isomophic to a single complete binary tree, but is split into a
 forest so that, a) we can always fit the `left` sub-branches into a single
 byte, and b) B-tree-like balancing to avoid array-insert. The forest is broken
 up into, also, complete binary trees, that have up to 256 internal nodes. */
struct tree {
	unsigned char branch_size; /* +1 for leaf size, (at least one leaf.) */
	unsigned char bmp[9]; /* Leaves { leaf | tree_idx }. */
	struct branch { unsigned char left, skip; } branches[256];
	union leaf { const char *leaf; size_t tree_idx; } leaves[257];
};
MIN_ARRAY(tree, struct tree)
struct trie { struct tree_array forest; };
#ifndef TRIE_IDLE /* <!-- !zero */
#define TRIE_IDLE { ARRAY_IDLE }
#endif /* !zero --> */


#define TRIESTR_TEST(a, i) (a[i >> 3] & (128 >> (i & 7)))
#define TRIESTR_DIFF(a, b, i) ((a[i >> 3] ^ b[i >> 3]) & (128 >> (i & 7)))
#define TRIESTR_SET(a, i) (a[i >> 3] |= 128 >> (i & 7))
#define TRIESTR_CLEAR(a, i) (a[i >> 3] &= ~(128 >> (i & 7)))

/** @return Whether `a` and `b` are equal up to the minimum. */
/*static int trie_is_prefix(const char *a, const char *b) {
	for( ; ; a++, b++) {
		if(*a == '\0') return 1;
		if(*a != *b) return *b == '\0';
	}
}*/
/* DEBUG */
static int level = 0;
static const char *lev(void) {
	static char str[32];
	int l = level;
	for(l = 0; l < level && l < (int)sizeof str - 1; l++) str[l] = '\t';
	str[l] = '\0';
	return str;
}


static void trie(struct trie *const t)
	{ assert(t), tree_array(&t->forest); }

static void trie_(struct trie *const t)
	{ assert(t), tree_array_(&t->forest), trie(t); }

static const char *trie_match(const struct trie *const t, const char *key) {
	struct tree *tree;
	size_t key_byte = 0, skip_byte, bit = 0; /* Check '\0' index; cursor. */
	assert(t && key);
	printf("%smatch %s {\n", lev(), key), level++;
	if(!t->forest.size) { printf("%sempty fail\n", lev()), level--, printf("%s}\n", lev()); return 0; } /* Empty. */
	for(tree = t->forest.data; ; ) {
		unsigned br0 = 0, br1 = tree->branch_size, i = 0;
		struct branch *branch;
		while(br0 < br1) {
			printf("%sindex br0 < br1, %u < %u\n", lev(), br0, br1);
			bit += (branch = tree->branches + br0)->skip;
			/* The key ends at an internal branch; '\0' is part of the key. */
			for(skip_byte = bit >> 3; key_byte < skip_byte; key_byte++)
				if(key[key_byte] == '\0') {
				printf("%sran out of key %s.\n", lev(), key), level--,
				printf("%s}\n", lev()); return 0;} else {
				printf("%sskipped byte\n", lev()); }
			/* Descend left or right based on bit of the key. */
			if(!TRIESTR_TEST(key, bit)) br1 = ++br0 + branch->left,
				printf("%sbit 0 at pos %lu\n", lev(), bit);
			else br0 += branch->left + 1, i += branch->left + 1, printf("%sbit 1 at pos %lu\n", lev(), bit);
			bit++;
		}
		printf("%sindex br0 = br1, %u = %u\n", lev(), br0, br1);
		assert(br0 == br1 && i <= tree->branch_size);
		if(!TRIESTR_TEST(tree->bmp, i)) return printf("%sgot %s at %u\n", lev(), key, i), level--, printf("%s}\n", lev()), tree->leaves[i].leaf;
		assert(tree->leaves[i].tree_idx < t->forest.size);
		tree = t->forest.data + tree->leaves[i].tree_idx;
		assert(0); /* not ready to test */
	}
}

static const char *trie_get(const struct trie *const t, const char *const key) {
	printf("%sget %s {\n", lev(), key), level++;
	{
	const char *const leaf = trie_match(t, key);
	printf("%s%s ?= %s\n", lev(), key, leaf), level--, printf("%s}\n", lev());
	return leaf && !strcmp(leaf, key) ? leaf : 0;
	}
}

/** Add `datum` to `trie`. Must not be the same as any key of `trie`; _ie_ it
 does not check for the end of the string. @return Success. @order \O(|`trie`|)
 @throws[realloc, ERANGE] */
static int trie_add_unique(struct trie *const t, const char *const key) {
	struct tree *tree;
	size_t bit = 0, bit0 = 0, bit1; /* `bit \in [bit0, bit1]` single branch. */
	assert(t && key);
	printf("%sunique %s {\n", lev(), key), level++;
	if(!t->forest.size) return (tree = tree_array_new(&t->forest))
		&& (tree->branch_size = 0, TRIESTR_CLEAR(tree->bmp, 0),
		tree->leaves[0].leaf = key, printf("%sfirst %u\n", lev(), tree->branch_size), level--, printf("%s}\n", lev()), 1);
	for(tree = t->forest.data; ; ) {
		unsigned br0 = 0, br1 = tree->branch_size, i = 0, left;
		struct branch *branch;
		const char **leaf;
		const char *br0_key;
		assert(br1 < 255); /* fail */
		/* Branch from internal node. */
		printf("%sinit branch [%u, %u]\n", lev(), br0, br1);
		while(branch = tree->branches + br0, br0_key = tree->leaves[i].leaf,
			br0 < br1) {
			assert(!TRIESTR_TEST(tree->bmp, i)); /* fail */
			for(bit1 = bit + branch->skip; bit < bit1; bit++)
				if(TRIESTR_DIFF(key, br0_key, bit)) {printf("%sbranch from branch %lu.\n", lev(), bit);goto insert;}
			bit0 = bit1;
			left = branch->left + 1; /* Leaves. */
			if(!TRIESTR_TEST(key, bit)) branch->left++, br1 = br0++ + left;
			else br0 += left, i += left;
			bit++;
			printf("%sbranch [%u, %u]\n", lev(), br0, br1);
		}
		/* Branch from leaf -- find the first difference. */
		while(!TRIESTR_DIFF(key, br0_key, bit)) bit++;
		printf("%sbranch from leaf, diff bw insert %s, and trie %s: %lu.\n",
			lev(), key, br0_key, bit);
insert:
		assert(br0 <= br1 && br1 <= tree->branch_size && br0_key
			&& i <= (unsigned)tree->branch_size + 1 && !br0 == !bit0
			&& TRIESTR_DIFF(key, br0_key, bit));
		/* This goes to a new sub-tree. */
		if(TRIESTR_TEST(tree->bmp, i)) { assert(0); /* fail */ continue; }
		/* Left or right leaf. */
		if(TRIESTR_TEST(key, bit)) i += (left = br1 - br0) + 1, printf("%s%s is after %s\n", lev(), key, br0_key);
		else left = 0, printf("%s%s is before %s\n", lev(), key, br0_key);
		printf("left");
		/* Insert leaf-and-branch pair. */
		leaf = &tree->leaves[i].leaf;
		memmove(leaf + 1, leaf, sizeof *leaf * (tree->branch_size + 1 - i));
		*leaf = key;
		branch = tree->branches + br0;
		if(br0 != br1) { /* Split the skip value with the existing branch. */
			assert(bit0 + branch->skip >= bit + !br0);
			branch->skip += bit0 - bit - !br0;
		}
		memmove(branch + 1, branch, sizeof *branch * (tree->branch_size - br0));
		branch->left = left;
		branch->skip = bit - bit0 - !!br0;
		tree->branch_size++;
		{
			unsigned q;
			printf("%sOrder: ", lev());
			for(q = 0; q < tree->branch_size + 1u; q++) {
				printf("%s%s", q ? ", " : "", tree->leaves[q].leaf);
			}
			printf(".\n");
			for(q = 0; q < tree->branch_size; q++)
				assert(strcmp(tree->leaves[q].leaf, tree->leaves[q + 1].leaf)<0);
		}
		level--, printf("%s}\n", lev());
		return 1;
	}
	assert(0);
	return 0;
}

static int trie_add(struct trie *const t, const char *const key) {
	int r;
	assert(t && key);
	printf("%sadd %s {\n", lev(), key), level++;
	r = trie_get(t, key) ? 0 : trie_add_unique(t, key);
	level--, printf("%s}\n", lev());
	return r;
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
		unsigned bl, lf;
		for(bl = 0; bl < t->forest.size; bl++) {
			struct tree *const tree = t->forest.data + bl;
			unsigned br;
			for(br = 0; br < tree->branch_size; br++) {
				struct branch *branch = tree->branches + br;
				const unsigned left = branch->left,
					right = trie_right(tree, br);
				fprintf(fp, "\tbranch%u [label = \"%u\"];\n"
					"\tbranch%u -> ", br, branch->skip, br);
				if(left) fprintf(fp, "branch%u [style = dashed]; // l branch\n",
					br + 1);
				else fprintf(fp, "leaf%u [style = dashed]; // l leaf\n",
					trie_left_leaf(tree, br));
				fprintf(fp, "\tbranch%u -> ", br);
				if(right) fprintf(fp, "branch%u; // right branch\n",
					br + left + 1);
				else fprintf(fp, "leaf%u; // right leaf\n",
					trie_left_leaf(tree, br) + left + 1);
			}
			/* This must be after the branches, or it will mix up the order. */
			for(lf = 0; lf <= tree->branch_size; lf++)
				fprintf(fp, "\tleaf%u [label = \"%s\", shape = box, "
				"fillcolor = lightsteelblue, style = filled];\n",
				lf, tree->leaves[lf].leaf /*fixme*/);
			fprintf(fp, "\tnode [color = red];\n"
				"}\n");	
		}
	}
	fprintf(fp, "\tnode [colour=red, style=filled];\n"
		"}\n");
	success = 1;
finally:
	if(fp) fclose(fp);
	return success;
}
