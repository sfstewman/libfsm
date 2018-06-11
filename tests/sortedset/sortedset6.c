/*
 * Copyright 2018 Shannon Stewman
 * Copyright 2017 Ed Kellett
 *
 * See LICENCE for the full copyright terms.
 */

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <adt/hashset.h>

int cmp_int(const void *a_, const void *b_) {
	int a = *(const int *)a_, b = *(const int *)b_;
	return (a>b) - (a<b);
}

unsigned long hash_int(const void *a_)
{
	const int *a = a_;
	return hashrec(a, sizeof *a);
}

int *next_int(void) {
	static int n = 0;
	int *p = malloc(sizeof *p);
	if (p == NULL) abort();
	*p = n++;
	return p;
}

int main(void) {
	struct sortedset *s = sortedset_create(hash_int,cmp_int);
	struct sortedset_iter iter;
	size_t i;
	int *p;

	for (i = 0; i < 5000; i++) {
		assert(sortedset_add(s, next_int()));
	}

	for (i = 0, p = sortedset_first(s, &iter); i < 5000; i++, sortedset_next(&iter)) {
		assert(p);
		if (i < 4999) {
			assert(sortedset_hasnext(&iter));
		} else {
			assert(!sortedset_hasnext(&iter));
		}
	}

	assert(sortedset_freeze(s));

	for (i = 0, p = sortedset_first(s, &iter); i < 5000; i++, sortedset_next(&iter)) {
		assert(p);
		int nxt = sortedset_hasnext(&iter);
		fprintf(stderr, "[%5zu] %p %d\n", i,(void *)p,nxt);
		if (i < 4999) {
			assert(nxt);
		} else {
			assert(!nxt);
		}
	}

	return 0;
}

