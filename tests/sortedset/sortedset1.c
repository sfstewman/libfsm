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
	/* ensure that a has enough elements that the table has to be
	 * rehashed a few times
	 */
	int a[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16};

	/* add 'em in */
	assert(sortedset_add(s, &a[0]));
	assert(sortedset_add(s, &a[1]));
	assert(sortedset_add(s, &a[2]));
	assert(sortedset_add(s, &a[3]));

	assert(sortedset_add(s, &a[4]));
	assert(sortedset_add(s, &a[5]));
	assert(sortedset_add(s, &a[6]));
	assert(sortedset_add(s, &a[7]));

	assert(sortedset_add(s, &a[8]));
	assert(sortedset_add(s, &a[9]));
	assert(sortedset_add(s, &a[10]));
	assert(sortedset_add(s, &a[11]));

	assert(sortedset_add(s, &a[12]));
	assert(sortedset_add(s, &a[13]));
	assert(sortedset_add(s, &a[14]));
	assert(sortedset_add(s, &a[15]));

	/* check that they're in */
	assert(sortedset_contains(s, &a[0]));
	assert(sortedset_contains(s, &a[1]));
	assert(sortedset_contains(s, &a[2]));
	assert(sortedset_contains(s, &a[3]));

	assert(sortedset_contains(s, &a[4]));
	assert(sortedset_contains(s, &a[5]));
	assert(sortedset_contains(s, &a[6]));
	assert(sortedset_contains(s, &a[7]));

	assert(sortedset_contains(s, &a[8]));
	assert(sortedset_contains(s, &a[9]));
	assert(sortedset_contains(s, &a[10]));
	assert(sortedset_contains(s, &a[11]));

	assert(sortedset_contains(s, &a[12]));
	assert(sortedset_contains(s, &a[13]));
	assert(sortedset_contains(s, &a[14]));
	assert(sortedset_contains(s, &a[15]));

	assert(sortedset_freeze(s));
	assert(sortedset_ordered(s));
	assert(s->len == 16);

	{
		size_t i;
		for (i=1; i < s->len; i++) {
			assert(cmp_int(s->sorted[i], s->sorted[i-1]) >= 0);
		}
	}

	return 0;
}

