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
	struct bm bm0, bm1, bm2, bm3;
	int any;

	bm_clear(&bm0);
	bm_clear(&bm1);
	bm_clear(&bm2);

	assert(bm_count(&bm0) == 0);
	assert(bm_count(&bm1) == 0);
	assert(bm_count(&bm2) == 0);

	bm_set(&bm0,   5);
	bm_set(&bm0,   8);
	bm_set(&bm1,  63);
	bm_set(&bm1,  65);
	bm_set(&bm2, 200);

	assert(bm_count(&bm0) == 2);
	assert(bm_get(&bm0, 5) != 0);
	assert(bm_get(&bm0, 8) != 0);

	assert(bm_count(&bm1) == 2);
	assert(bm_get(&bm1, 63) != 0);
	assert(bm_get(&bm1, 65) != 0);

	assert(bm_count(&bm2) == 1);
	assert(bm_get(&bm2, 200) != 0);


	bm3 = bm2;
	any = bm_and(&bm3, &bm0);
	assert(any == 0);

	bm3 = bm2;
	any = bm_and(&bm3, &bm1);
	assert(any == 0);

	bm3 = bm2;
	any = bm_and(&bm3, &bm2);
	assert(any != 0);



	bm_or(&bm2, &bm0);
	bm_or(&bm2, &bm1);

	assert(bm_count(&bm0) == 2);
	assert(bm_get(&bm0, 5) != 0);
	assert(bm_get(&bm0, 8) != 0);

	assert(bm_count(&bm1) == 2);
	assert(bm_get(&bm1, 63) != 0);
	assert(bm_get(&bm1, 65) != 0);

	assert(bm_count(&bm2) == 5);
	assert(bm_get(&bm2,   5) != 0);
	assert(bm_get(&bm2,   8) != 0);
	assert(bm_get(&bm2,  63) != 0);
	assert(bm_get(&bm2,  65) != 0);
	assert(bm_get(&bm2, 200) != 0);


	bm3 = bm2;
	any = bm_and(&bm3, &bm0);
	assert(any != 0);

	bm3 = bm2;
	any = bm_and(&bm3, &bm1);
	assert(any != 0);

	bm3 = bm2;
	any = bm_and(&bm3, &bm2);
	assert(any != 0);

	return 0;
}



