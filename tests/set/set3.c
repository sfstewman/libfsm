/*
 * Copyright 2017 Ed Kellett
 *
 * See LICENCE for the full copyright terms.
 */

#include <assert.h>
#include <stdlib.h>
#include <adt/set.h>

int cmp_int(const void *a_, const void *b_) {
	int a = *(const int *)a_, b = *(const int *)b_;
	if (a > b)      return 1;
	else if (a < b) return -1;
	else            return 0;
}

int bulkcmp_int(const void **a_, const void **b_) {
	return cmp_int(*a_, *b_);
}

int main(void) {
	struct set *s = set_create(NULL, cmp_int, bulkcmp_int);
	struct set_iter iter;
	int *p;
	int a[3] = {1, 2, 3};
	int seen[3] = {0, 0, 0};
	int i;
	assert(set_add(s, &a[0]));
	assert(set_add(s, &a[1]));
	assert(set_add(s, &a[2]));
	for (p = set_first(s, &iter); p != NULL; p = set_next(&iter)) {
		assert(*p == 1 || *p == 2 || *p == 3);
		seen[*p - 1] = 1;
	}
	for (i = 0; i < 3; i++) {
		assert(seen[i]);
	}
	return 0;
}
