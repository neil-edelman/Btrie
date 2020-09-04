/** @license 2020 Neil Edelman, distributed under the terms of the
 [MIT License](https://opensource.org/licenses/MIT).

 Test Trie.

 @std C89/90 */

#include <stdlib.h> /* EXIT malloc free rand */
#include <stdio.h>  /* *printf */
#include <assert.h> /* assert */
#include <errno.h>  /* errno */
#include <string.h> /* strncpy */
#include <time.h>   /* clock time */
#include <math.h>   /* sqrt NAN? for stddev */


/*#define TRIE_NAME str*/
#include "../src/BTrie.h"

/** Specific test for str. */
static void test_basic_trie_str(void) {
	extern const char *const parole[];
	extern const size_t parole_size;
	struct trie t = TRIE_IDLE;
	const char *words[] = { "aaaa", "aaab", "a", "foo", "bar", "baz", "qux",
		"quux", "foos", "f" }, *w, *s;
	const size_t words_size = sizeof words / sizeof *words;
	size_t i;
	char fn[64];
	int r;

#if 0
	const char *alph[] = { "m", "n", "o", "u", "v", "x", "y", "z", "p", "q",
		"r", "", "å", "a", "b", "g", "h", "i", "j", "k", "l", "c", "d", "e",
		"f", "s", "t", "w" };
	const size_t alph_size = sizeof alph / sizeof *alph;
	size_t i;
#endif

	for(i = 0; i < /*words_size*/3; i++) {
		w = parole[i];
		s = trie_get(&t, w), assert(!s);
		r = trie_add(&t, w), assert(r);
		sprintf(fn, "graph/%lu.gv", (unsigned long)i + 1);
		r = trie_graph(&t, fn), assert(r);
		s = trie_get(&t, w), assert(s == w);
	}

#if 0
	trie_str_print(&trie);
	trie_str_graph(&trie, "graph/trie0.gv");
	/*printf("Trie0: %s.\n\n", str_trie_to_string(&trie));*/

	if(!str_trie_add(&trie, "foo")) goto catch;
	/*trie_str_print(&trie);*/
	trie_str_graph(&trie, "graph/trie1.gv");
	/*printf("Trie1: %s.\n\n", str_trie_to_string(&trie));*/

	if(!str_trie_add(&trie, "bar")) goto catch;
	/*trie_str_print(&trie);*/
	trie_str_graph(&trie, "graph/trie2.gv");
	/*printf("Trie2: %s.\n\n", str_trie_to_string(&trie));*/

	if(!str_trie_add(&trie, "baz")) goto catch;
	/*trie_str_print(&trie);*/
	trie_str_graph(&trie, "graph/trie3.gv");
	/*printf("Trie3: %s.\n\n", str_trie_to_string(&trie));*/

	if(!str_trie_add(&trie, "qux")) goto catch;
	/*trie_str_print(&trie);*/
	trie_str_graph(&trie, "graph/trie4.gv");
	/*printf("Trie4: %s.\n\n", str_trie_to_string(&trie));*/

	if(!str_trie_add(&trie, "quxx")) goto catch;
	/*trie_str_print(&trie);*/
	trie_str_graph(&trie, "graph/trie5.gv");
	/*printf("Trie5: %s.\n\n", str_trie_to_string(&trie));*/

	if(!str_trie_add(&trie, "quxxx")) goto catch;
	/*trie_str_print(&trie);*/
	trie_str_graph(&trie, "graph/trie6.gv");
	/*printf("Trie6: %s.\n\n", str_trie_to_string(&trie));*/

	assert(str_trie_size(&trie) == 6);

	if(!str_trie_add(&trie, "a")) goto catch;
	trie_str_graph(&trie, "graph/trie_a.gv");
	if(!str_trie_add(&trie, "b")) goto catch;
	trie_str_graph(&trie, "graph/trie_b.gv");
	/*trie_str_print(&trie);*/
	if(!str_trie_add(&trie, "c")) goto catch;
	trie_str_print(&trie);
	trie_str_graph(&trie, "graph/trie_c.gv");
	if(!str_trie_add(&trie, "d")
	   || !str_trie_add(&trie, "e")
	   || !str_trie_add(&trie, "f")
	   || !str_trie_add(&trie, "g")
	   || !str_trie_add(&trie, "h")
	   || !str_trie_add(&trie, "i")
	   || !str_trie_add(&trie, "j")
	   || !str_trie_add(&trie, "k")
	   || !str_trie_add(&trie, "l")
	   || !str_trie_add(&trie, "m")
	   || !str_trie_add(&trie, "n")
	   || !str_trie_add(&trie, "o")
	   || !str_trie_add(&trie, "p")
	   || !str_trie_add(&trie, "q")
	   || !str_trie_add(&trie, "r")
	   || !str_trie_add(&trie, "s")
	   || !str_trie_add(&trie, "t")
	   || !str_trie_add(&trie, "u")
	   || !str_trie_add(&trie, "v")
	   || !str_trie_add(&trie, "w")
	   || !str_trie_add(&trie, "x")
	   || !str_trie_add(&trie, "y")
	   || !str_trie_add(&trie, "z")) goto catch;
	trie_str_print(&trie);
	trie_str_graph(&trie, "graph/trie_z.gv");
	printf("TrieZ: %s.\n\n", str_trie_to_string(&trie));
	assert(str_trie_size(&trie) == 26 + 6);
	if(!str_trie_remove(&trie, "x")
		|| !str_trie_remove(&trie, "z")
		|| !str_trie_remove(&trie, "y")
		|| !str_trie_remove(&trie, "d")
		|| !str_trie_remove(&trie, "c")
		|| !str_trie_remove(&trie, "b")
		|| !str_trie_remove(&trie, "a")
		|| !str_trie_remove(&trie, "f")
		|| !str_trie_remove(&trie, "g")
		|| !str_trie_remove(&trie, "h")
		|| !str_trie_remove(&trie, "i")
		|| !str_trie_remove(&trie, "j")
		|| !str_trie_remove(&trie, "k")
		|| !str_trie_remove(&trie, "l")
		|| !str_trie_remove(&trie, "m")
		|| !str_trie_remove(&trie, "n")
		|| !str_trie_remove(&trie, "o")
		|| !str_trie_remove(&trie, "p")
		|| !str_trie_remove(&trie, "q")
		|| !str_trie_remove(&trie, "r")
		|| !str_trie_remove(&trie, "s")
		|| !str_trie_remove(&trie, "t")
		|| !str_trie_remove(&trie, "u")
		|| !str_trie_remove(&trie, "v")
		|| !str_trie_remove(&trie, "w")
		|| !str_trie_remove(&trie, "e")) goto catch;
	trie_str_graph(&trie, "graph/trie_a-z-delete.gv");
	assert(str_trie_size(&trie) == 6);
	for(i = 0; i < words_size; i++)
		printf("\"%s\": %s\n", words[i], str_trie_index_get(&trie, words[i]));
	str_trie_(&trie);

	printf("Trie from array.\n");
	if(!str_trie_from_array(&trie, words, words_size)) goto catch;
	trie_str_graph(&trie, "graph/trie_all_at_once.gv");
	str_trie_(&trie);
	if(!str_trie_from_array(&trie, alph, alph_size)) goto catch;
	trie_str_graph(&trie, "graph/alph_all_at_once.gv");
	if(!str_trie_from_array(&trie, wordsr, wordsr_size)) goto catch;
	trie_str_graph(&trie, "graph/trie_r_all_at_once.gv");

	goto finally;
catch:
	printf("Test failed.\n"), assert(0);
finally:
#endif
	trie_(&t);
}

#if 0
/** Given `n` in `t` branches, calculate the right child branches. Used in
 <fn:trie_graph>. @order \O(log `size`) */
static size_t trie_right(const struct block *const b, const size_t n) {
	size_t remaining = b->branches.size, n0 = 0, left, right;
	assert(b && n < remaining);
	for( ; ; ) {
		left = trie_left(b->branches.data[n0]);
		right = remaining - left - 1;
		assert(left < remaining && right < remaining);
		if(n0 >= n) break;
		if(n <= n0 + left) remaining = left, n0++;
		else remaining = right, n0 += left + 1;
	}
	assert(n0 == n);
	return right;
}

/** @return Given `n` in `t` branches, follows the internal nodes left until
 it hits a branch. Used in <fn:trie_graph>. */
static size_t trie_left_leaf(const struct Trie *const t, const size_t n) {
	size_t remaining = t->branches.size, n0 = 0, left, right, i = 0;
	assert(t && n < remaining);
	for( ; ; ) {
		left = trie_left(t->branches.data[n0]);
		right = remaining - left - 1;
		assert(left < remaining && right < remaining);
		if(n0 >= n) break;
		if(n <= n0 + left) remaining = left, n0++;
		else remaining = right, n0 += left + 1, i += left + 1;
	}
	assert(n0 == n);
	return i;
}

/** Draw a graph of `t` to `fn` in Graphviz format. */
static void trie_graph_fp(const struct Trie *const t, FILE *fp) {
	size_t i, n;
	assert(t && fp);
	fprintf(fp, "digraph {\n"
			"\trankdir = TB;\n"
			"\tnode [shape = record, style = filled];\n"
			"\tTrie [label = \"{\\Trie"
			"\\l|size: %lu\\l}\"];\n", (unsigned long)t->leaves.size);
	fprintf(fp, "\tnode [shape = none, fillcolor = none];\n");
	for(n = 0; n < t->branches.size; n++) {
		const size_t branch = t->branches.data[n];
		const size_t left = trie_left(branch), right = trie_right(t, n);
		fprintf(fp, "\tbranch%lu [label = \"%lu\"];\n"
				"\tbranch%lu -> ", (unsigned long)n, trie_skip(branch),
				(unsigned long)n);
		if(left) fprintf(fp, "branch%lu [style = dashed]; // left branch\n",
						 (unsigned long)n + 1);
		else fprintf(fp, "leaf%lu [style = dashed]; // left leaf\n",
					 (unsigned long)trie_left_leaf(t, n));
		fprintf(fp, "\tbranch%lu -> ", (unsigned long)n);
		if(right) fprintf(fp, "branch%lu; // right branch\n",
						  (unsigned long)n + left + 1);
		else fprintf(fp, "leaf%lu; // right leaf\n",
					 (unsigned long)trie_left_leaf(t, n) + left + 1);
	}
	/* This must be after the branches, or it will mix up the order. Since they
	 have been referenced, one needs explicit formatting? */
	for(i = 0; i < t->leaves.size; i++)
		fprintf(fp, "\tleaf%lu [label = \"%s\", shape = box, "
				"fillcolor = lightsteelblue, style = filled];\n", (unsigned long)i,
				t->leaves.data[i]);
	fprintf(fp, "\tnode [color = red];\n"
			"}\n");
}

/** Graphs `t` in `Graphviz` format in the file `fn`.
 @return Success. @throws[fopen, EDOM] */
static int trie_graph(const struct Trie *const t, const char *const fn) {
	FILE *fp;
	assert(t && fn);
	if(!(fp = fopen(fn, "w"))) return 0;
	trie_graph_fp(t, fp);
	return fclose(fp) ? errno ? 0 : (errno = EDOM, 0) : 1;
}
#endif

int main(void) {
	unsigned seed = (unsigned)clock();
	srand(seed), rand(), printf("Seed %u.\n", seed);
	test_basic_trie_str();
	return EXIT_SUCCESS;
}
