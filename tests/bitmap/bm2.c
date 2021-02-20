/*
 * Copyright 2021 Shannon F. Stewman
 * 
 * See LICENCE for the full copyright terms.
 */

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <limits.h>

#include <print/esc.h>
#include <adt/bitmap.h>

int main(void)
{
	struct bm bm;
	int i;

	bm_clear(&bm);
	assert(bm_count(&bm) == 0);

	bm_set(&bm,   5);
	bm_set(&bm,   8);
	bm_set(&bm,  63);
	bm_set(&bm,  65);
	bm_set(&bm, 200);

	for (i=0; i < UCHAR_MAX+1; i++) {
		int expect_set = (i == 5) || (i == 8) || (i==63) || (i==65) || (i == 200);
		int is_set = (bm_get(&bm, i) != 0);
		assert( expect_set == is_set );
	}

	i = -1;

	i = bm_next(&bm, i, 1);
	assert(i == 5);

	i = bm_next(&bm, i, 1);
	assert(i == 8);

	i = bm_next(&bm, i, 1);
	assert(i == 63);

	i = bm_next(&bm, i, 1);
	assert(i == 65);

	i = bm_next(&bm, i, 1);
	assert(i == 200);

	i = bm_next(&bm, i, 1);
	assert(i == UCHAR_MAX+1);

	return 0;
}


