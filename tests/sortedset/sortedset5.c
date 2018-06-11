/*
 * Copyright 2017 Ed Kellett
 *
 * See LICENCE for the full copyright terms.
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <adt/hashset.h>

int cmp_int(const void *a_, const void *b_) {
	int a = *(const int *)(a_), b = *(const int *)(b_);
	return (a>b) - (b>a);
	/*
	if (a > b)      return  1;
	else if (a < b) return -1;
	else            return 0;
	*/
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
	/* fprintf(stderr, "alloc> %d @ %p\n", *p, (void *)p); */
	return p;
}

#define NVALUES 5000
#define NREMOVE 3
int main(void) {
	struct sortedset *s = sortedset_create(hash_int,cmp_int);
	int a[NREMOVE] = {1200,2400,3600};
	/* int a[3] = {5,2,19}; */
	size_t i,i0;

	for (i = 0; i < NVALUES; i++) {
		assert(sortedset_add(s, next_int()));
	}

	assert(sortedset_freeze(s));
	assert(sortedset_ordered(s));
	assert(s->len == NVALUES);

	for (i=0; i < NVALUES; i++) {
		int *ip;

		ip = s->sorted[i];
		assert(*ip == (int)i);
	}

	for (i = 0; i < sizeof a/sizeof a[0]; i++) {
		assert(sortedset_contains(s, &a[i]));
		sortedset_remove(s, &a[i]);
	}
	assert(sortedset_count(s) == NVALUES-NREMOVE);
	assert(!sortedset_ordered(s));

	assert(sortedset_freeze(s));
	assert(s->len == NVALUES-NREMOVE);

	/* make sure that they're sorted */
	for (i = 1; i < s->len; i++) {
		assert(cmp_int(s->sorted[i],s->sorted[i-1]) >= 0);
	}

	i0=0;
	for (i=0; i < NVALUES; i++) {
		int *ip;
		int j, removed;

		removed=0;
		for(j=0; j < NREMOVE; j++) {
			if ((int)i == a[j]) {
				removed=1;
				break;
			}
		}

		if (!removed) {
			ip = s->sorted[i0++];
			assert(*ip == (int)i);
		}
	}

	return 0;
}
