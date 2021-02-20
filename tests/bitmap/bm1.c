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
	size_t i;

	bm_clear(&bm);
	assert(bm_count(&bm) == 0);

	assert(bm_isallset(&bm) == 0);
	assert(bm_isanyset(&bm) == 0);

	bm_set(&bm,   3);
	bm_set(&bm,   5);
	bm_set(&bm, 200);

	assert(bm_get(&bm,   3) != 0);
	assert(bm_get(&bm,   5) != 0);
	assert(bm_get(&bm, 200) != 0);

	assert(bm_count(&bm) == 3);

	assert(bm_isallset(&bm) == 0);
	assert(bm_isanyset(&bm) == 1);


	for (i=0; i < UCHAR_MAX+1; i++) {
		int expect_set = (i == 3) || (i == 5) || (i == 200);
		int is_set = (bm_get(&bm, i) != 0);
		assert( expect_set == is_set );
	}

	bm_set(&bm, 2);
	bm_set(&bm, 4);

	assert(bm_count(&bm) == 5);

	assert(bm_isallset(&bm) == 0);
	assert(bm_isanyset(&bm) == 1);


	bm_clearbit(&bm, 3);

	assert(bm_count(&bm) == 4);

	assert(bm_isallset(&bm) == 0);
	assert(bm_isanyset(&bm) == 1);


	assert(bm_get(&bm,   2) != 0);
	assert(bm_get(&bm,   3) == 0);
	assert(bm_get(&bm,   4) != 0);
	assert(bm_get(&bm,   5) != 0);
	assert(bm_get(&bm, 200) != 0);

	bm_setrange(&bm, 2,9);
	assert(bm_count(&bm) == 9);

	assert(bm_isallset(&bm) == 0);
	assert(bm_isanyset(&bm) == 1);


	assert(bm_get(&bm,   2) != 0);
	assert(bm_get(&bm,   3) != 0);
	assert(bm_get(&bm,   4) != 0);
	assert(bm_get(&bm,   5) != 0);
	assert(bm_get(&bm,   6) != 0);
	assert(bm_get(&bm,   7) != 0);
	assert(bm_get(&bm,   8) != 0);
	assert(bm_get(&bm,   9) != 0);
	assert(bm_get(&bm, 200) != 0);

	for (i=0; i < UCHAR_MAX+1; i++) {
		int expect_set = ((i >= 2) && (i <= 9)) || (i == 200);
		int is_set = (bm_get(&bm, i) != 0);
		assert( expect_set == is_set );
	}

	bm_clearrange(&bm, 5,20);
	assert(bm_count(&bm) == 4);

	assert(bm_isallset(&bm) == 0);
	assert(bm_isanyset(&bm) == 1);


	assert(bm_get(&bm,   2) != 0);
	assert(bm_get(&bm,   3) != 0);
	assert(bm_get(&bm,   4) != 0);
	assert(bm_get(&bm,   5) == 0);
	assert(bm_get(&bm,   6) == 0);
	assert(bm_get(&bm,   7) == 0);
	assert(bm_get(&bm,   8) == 0);
	assert(bm_get(&bm,   9) == 0);
	assert(bm_get(&bm, 200) != 0);

	for (i=0; i < UCHAR_MAX+1; i++) {
		int expect_set = ((i >= 2) && (i <= 4)) || (i == 200);
		int is_set = (bm_get(&bm, i) != 0);
		assert( expect_set == is_set );
	}

	bm_invert(&bm);

	assert(bm_count(&bm) == 252);

	assert(bm_get(&bm,   2) == 0);
	assert(bm_get(&bm,   3) == 0);
	assert(bm_get(&bm,   4) == 0);
	assert(bm_get(&bm,   5) != 0);
	assert(bm_get(&bm,   6) != 0);
	assert(bm_get(&bm,   7) != 0);
	assert(bm_get(&bm,   8) != 0);
	assert(bm_get(&bm,   9) != 0);
	assert(bm_get(&bm, 200) == 0);

	for (i=0; i < UCHAR_MAX+1; i++) {
		int expect_not_set = ((i >= 2) && (i <= 4)) || (i == 200);
		int expect_set = !expect_not_set;
		int is_set = (bm_get(&bm, i) != 0);
		assert( expect_set == is_set );
	}

	assert(bm_isallset(&bm) == 0);
	assert(bm_isanyset(&bm) == 1);

	bm_set(&bm,   2);
	bm_set(&bm,   3);
	bm_set(&bm,   4);

	assert(bm_count(&bm) == 255);
	assert(bm_isallset(&bm) == 0);
	assert(bm_isanyset(&bm) == 1);


	bm_set(&bm, 200);
	assert(bm_count(&bm) == 256);
	assert(bm_isallset(&bm) == 1);
	assert(bm_isanyset(&bm) == 1);


	bm_invert(&bm);
	assert(bm_isallset(&bm) == 0);
	assert(bm_isanyset(&bm) == 0);


	return 0;
}

