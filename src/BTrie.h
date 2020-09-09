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


/** Tries are a complete binary tree, broken up into a forest of trees that
 have up to 256 internal nodes, (so we can always fit the `left` sub-branches
 into a single byte.) */
struct block {
	unsigned char branch_size; /* +1 for leaf size. */
	unsigned char bmp[9]; /* Leaves leaf/block_idx (another tree in forest.) */
	struct branch { unsigned char left, skip; } branches[256];
	/* Not null up to `branch_size + 1`. */
	union leaf { const char *leaf; size_t block_idx; } leaves[257];
};
MIN_ARRAY(block, struct block)
struct trie { struct block_array blocks; };
#ifndef TRIE_IDLE /* <!-- !zero */
#define TRIE_IDLE { ARRAY_IDLE }
#endif /* !zero --> */


#define TRIESTR_IS_BIT(a, i) (a[i >> 3] & (128 >> (i & 7)))
#define TRIESTR_BIT_DIFF(a, b, i) ((a[i >> 3] ^ b[i >> 3]) & (128 >> (i & 7)))
#define TRIESTR_SET(a, i) (a[i >> 3] |= 128 >> (i & 7))
#define TRIESTR_CLEAR(a, i) (a[i >> 3] &= ~(128 >> (i & 7)))

/** @return Whether `a` and `b` are equal up to the minimum. */
/*static int trie_is_prefix(const char *a, const char *b) {
	for( ; ; a++, b++) {
		if(*a == '\0') return 1;
		if(*a != *b) return *b == '\0';
	}
}*/


static void trie(struct trie *const t)
	{ assert(t), block_array(&t->blocks); }

static void trie_(struct trie *const t)
	{ assert(t), block_array_(&t->blocks), trie(t); }

static const char *trie_match(const struct trie *const t, const char *key) {
	size_t key_byte, skip_bit, skip_byte;
	struct block *block;
	assert(t && key);
	if(!t->blocks.size) return 0;
	skip_bit = key_byte = 0;
	for(block = t->blocks.data; ; ) {
		unsigned n0 = 0, n1 = block->branch_size, i = 0;
		struct branch *branch;
		/* Block lookup. */
		while(n0 < n1) {
			/* The key ends at an internal branch; '\0' is part of the key. */
			for(skip_byte = (skip_bit += (branch = block->branches
				+ n0)->skip) >> 3; key_byte < skip_byte; key_byte++)
				if(key[key_byte] == '\0') return 0;
			/* Descend left or right based on bit of the key. */
			if(!TRIESTR_IS_BIT(key, skip_bit)) n1 = ++n0 + branch->left;
			else n0 += branch->left + 1, i += branch->left + 1;
		}
		assert(n0 == n1 && i <= block->branch_size);
		if(!TRIESTR_IS_BIT(block->bmp, i)) return block->leaves[i].leaf;
		assert(block->leaves[i].block_idx < t->blocks.size);
		block = t->blocks.data + block->leaves[i].block_idx;
	}
}

static const char *trie_get(const struct trie *const t, const char *const key) {
	const char *const leaf = trie_match(t, key);
	return leaf && !strcmp(leaf, key) ? leaf : 0;
}

/** Add `datum` to `trie`. Must not be the same as any key of `trie`; _ie_ it
 does not check for the end of the string. @return Success. @order \O(|`trie`|)
 @throws[realloc, ERANGE] */
static int trie_add_unique(struct trie *const t, const char *const key) {
	struct block *blk, *blk1;
	size_t bit = 0, bit0 = 0, bit1;
	assert(t && key);
	printf("add %s\n", key);
	if(!t->blocks.size) { /* [0]->[1] */
		if(!(blk = block_array_new(&t->blocks))) return 0;
		blk->branch_size = 0;
		return TRIESTR_CLEAR(blk->bmp, 0), blk->leaves[0].leaf = key, printf("first %u\n", blk->branch_size), 1;
	}
	/* [1,254]->[2,255] */
	for(blk = t->blocks.data, blk1 = blk + t->blocks.size; ; ) {
		struct branch *branch;
		unsigned br0 = 0, br1 = blk->branch_size, i = 0, left;
		const char **leaf;
		const char *br0_key;
		assert(br1 < 255); /* fail */
		/* Branch from internal node. */
		while(branch = blk->branches + br0, br0_key = blk->leaves[i].leaf,
			br0 < br1) {
			assert(!TRIESTR_IS_BIT(blk->bmp, i)); /* fail */
			for(bit1 = bit + branch->skip; bit < bit1; bit++)
				if(TRIESTR_BIT_DIFF(key, br0_key, bit)) goto insert;
			bit0 = bit1, bit++;
			if(TRIESTR_IS_BIT(key, bit))
				branch->left++, br1 = br0++ + branch->left + 1;
			else
				br0 += branch->left + 1, i += branch->left + 1;
		}
		/* Branch from leaf. */
		while(!TRIESTR_BIT_DIFF(key, br0_key, bit)) bit++;
insert:
		assert(br0 <= br1 && br1 <= blk->branch_size && br0_key
			&& i <= (unsigned)blk->branch_size + 1 && !br0 == !bit0
			&& TRIESTR_BIT_DIFF(key, br0_key, bit));
		/* This goes to a new sub-block. */
		if(TRIESTR_IS_BIT(blk->bmp, i)) { assert(0); /* fail */ continue; }
		/* How many left entries are there to move, before or after. */
		if(TRIESTR_IS_BIT(key, bit)) left = br1 - br0, i += left + 1, printf("%s is after %s\n", key, br0_key);
		else left = 0, printf("%s is before %s\n", key, br0_key);
		/* Insert leaf-and-branch pair. */
		leaf = &blk->leaves[i].leaf;
		memmove(leaf + 1, leaf, sizeof *leaf * (blk->branch_size + 1 - i));
		*leaf = key;
		branch = blk->branches + br0;
		if(br0 != br1) { /* Split the skip value with the existing branch. */
			assert(bit0 + branch->skip >= bit + !br0);
			branch->skip += bit0 - bit - !br0;
		}
		memmove(branch + 1, branch, sizeof *branch * (blk->branch_size - br0));
		branch->left = left;
		branch->skip = bit - bit0 - !!br0;
		blk->branch_size++;
		return 1;
	}
	assert(0);
	return 0;
}

static int trie_add(struct trie *const t, const char *const key) {
	assert(t && key);
	return trie_get(t, key) ? 0 : trie_add_unique(t, key);
}

/** Given branch index `b` in `block`, calculate (inefficiently) the right
 child branches. Used in <fn:trie_graph>. @order \O(log `size`) */
static unsigned trie_right(const struct block *const block, const unsigned b) {
	unsigned remaining = block->branch_size, n0 = 0, left, right;
	assert(block && b < remaining);
	for( ; ; ) {
		left = block->branches[n0].left;
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
 `n` in `block`. Used in <fn:trie_graph>. */
static unsigned trie_left_leaf(const struct block *const block,
	const size_t n) {
	unsigned remaining = block->branch_size, n0 = 0, left, right, i = 0;
	assert(block && n < remaining);
	for( ; ; ) {
		left = block->branches[n0].left;
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
	if(!(fp = fopen(fn, "w"))) goto finally;
	fprintf(fp, "digraph {\n"
		"\trankdir=TB;\n"
		/*"\tedge [color=royalblue];\n"
		"\tnode [shape=box, style=filled, fillcolor=pink];\n"*/
		"\tnode [shape = none, fillcolor = none];\n");
	if(!t->blocks.size) {
		fprintf(fp, "\tlabel=\"empty\";\n");
	} else {
		unsigned bl, lf;
		for(bl = 0; bl < t->blocks.size; bl++) {
			struct block *const block = t->blocks.data + bl;
			unsigned br;
			for(br = 0; br < block->branch_size; br++) {
				struct branch *branch = block->branches + br;
				const unsigned left = branch->left,
					right = trie_right(block, br);
				fprintf(fp, "\tbranch%u [label = \"%u\"];\n"
					"\tbranch%u -> ", br, branch->skip, br);
				if(left) fprintf(fp, "branch%u [style = dashed]; // l branch\n",
					br + 1);
				else fprintf(fp, "leaf%u [style = dashed]; // l leaf\n",
					trie_left_leaf(block, br));
				fprintf(fp, "\tbranch%u -> ", br);
				if(right) fprintf(fp, "branch%u; // right branch\n",
					br + left + 1);
				else fprintf(fp, "leaf%u; // right leaf\n",
					trie_left_leaf(block, br) + left + 1);
			}
			/* This must be after the branches, or it will mix up the order.
			 Since they have been referenced, one needs explicit formatting? */
			/*FIXME*/
			for(lf = 0; lf <= block->branch_size; lf++)
				fprintf(fp, "\tleaf%u [label = \"%s\", shape = box, "
				"fillcolor = lightsteelblue, style = filled];\n",
				lf, block->leaves[lf].leaf);
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
