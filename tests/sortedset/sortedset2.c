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

int main(void) {
	struct sortedset *s = sortedset_create(hash_int,cmp_int);
	int a = 1;
	assert(sortedset_add(s, &a));
	assert(sortedset_add(s, &a));
	assert(sortedset_add(s, &a));

	assert(sortedset_freeze(s));
	assert(sortedset_ordered(s));
	assert(s->len == 1);

	sortedset_remove(s, &a);

	assert(!sortedset_ordered(s));
	assert(!sortedset_contains(s, &a));

	assert(sortedset_freeze(s));
	assert(sortedset_ordered(s));
	assert(s->len == 0);

	return 0;
}

