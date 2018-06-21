/*
 * Copyright 2017 Ed Kellett
 *
 * See LICENCE for the full copyright terms.
 */

#include <assert.h>
#include <stdlib.h>
#include <adt/hashset.h>

int cmp_int(const void *a_, const void *b_) {
	int a = *(const int *)a_, b = *(const int *)b_;
	if (a > b)      return 1;
	else if (a < b) return -1;
	else            return 0;
}

unsigned long hash_int(const void *a_)
{
	const int *a = a_;
	return hashrec(a, sizeof *a);
}

int *next_int(int reset) {
	static int n = 0;
	int *p;

	if (reset) {
		n = 0;
		return NULL;
	}

	p = malloc(sizeof *p);
	if (p == NULL) abort();
	*p = n++;
	return p;
}

int main(void) {
	struct sortedset *s;
	size_t i;

	s = sortedset_create(hash_int,cmp_int);

	for (i = 0; i < 5000; i++) {
		assert(sortedset_add(s, next_int(0)));
	}
	assert(sortedset_count(s) == 5000);

	next_int(1);

	for (i = 0; i < 5000; i++) {
		assert(sortedset_add(s, next_int(0)));
	}
	assert(sortedset_count(s) == 5000);

	return 0;
}
