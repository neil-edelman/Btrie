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
static void test_basic(void) {
	extern const char *const parole[];
	/*extern const size_t parole_size;*/
	const char *words[] = { "f", "o", "u", "m", "n", "v", "x", "y", "z", "p",
		"q", "r", "", "å", "a", "b", "g", "h", "i", "j", "k", "l", "c", "d",
		"e", "f", "s", "t", "w", "aaaa", "aaab", "foo", "bar", "baz", "qux",
		"quux", "foos", "f" };
	const size_t words_size = sizeof words / sizeof *words;
	struct trie t = TRIE_IDLE;
	const char *w, *s;
	size_t i, j;
	char fn[64];
	int r;

	for(i = 0; i < words_size; i++) {
		w = words[i];
		s = trie_get(&t, w), assert(!s);
		r = trie_add(&t, w), assert(r);
		sprintf(fn, "graph/word-%lu.gv", (unsigned long)i + 1);
		r = trie_graph(&t, fn), assert(r);
		s = trie_get(&t, w), assert(s == w);
		/*printf("\"%s\": %s\n", w, s);*/
		for(j = 0; j < i; j++)
			w = words[j], s = trie_get(&t, w), assert(s == w);
	}
	trie_clear(&t);

	for(i = 0; i < /*parole_size*/30; i++) {
		w = parole[i];
		s = trie_get(&t, w), assert(!s);
		r = trie_add(&t, w), assert(r);
		sprintf(fn, "graph/parole-%lu.gv", (unsigned long)i + words_size);
		r = trie_graph(&t, fn), assert(r);
		s = trie_get(&t, w), assert(s == w);
	}

	/*printf("Trie from array.\n");
	if(!str_trie_from_array(&trie, words, words_size)) goto catch;
	trie_str_graph(&trie, "graph/trie_all_at_once.gv");
	str_trie_(&trie);
	if(!str_trie_from_array(&trie, alph, alph_size)) goto catch;
	trie_str_graph(&trie, "graph/alph_all_at_once.gv");
	if(!str_trie_from_array(&trie, wordsr, wordsr_size)) goto catch;
	trie_str_graph(&trie, "graph/trie_r_all_at_once.gv");*/

	goto finally;
/*catch:
	printf("Test failed.\n"), assert(0);*/
finally:
	trie_(&t);
}

static void test_thing(void) {
	const char *words[] = { "x", "y", "z",  "a" };
	const size_t words_size = sizeof words / sizeof *words;
	const char *w, *s;
	size_t i, j;
	char fn[64];
	int r;
	struct trie t = TRIE_IDLE;
	assert(!errno);
	for(i = 0; i < words_size; i++) {
		w = words[i];
		s = trie_get(&t, w), assert(!s);
		r = trie_add(&t, w), assert(r);
		sprintf(fn, "graph/thing-%lu.gv", (unsigned long)i + 1);
		r = trie_graph(&t, fn);
		if(!r) perror(fn), errno = 0; /* Ignore. */
		s = trie_get(&t, w), assert(s == w);
		for(j = 0; j < i; j++)
			w = words[j], s = trie_get(&t, w), assert(s == w);
	}
	trie_(&t);
}

int main(void) {
	unsigned seed = (unsigned)clock();
	srand(seed), rand(), printf("Seed %u.\n", seed);
	errno = 0;
	test_thing();
	test_basic();
	return EXIT_SUCCESS;
}
