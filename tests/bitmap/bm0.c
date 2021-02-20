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

	bm_clear(&bm);
	assert(bm_count(&bm) == 0);

	bm_setall(&bm);
	assert(bm_count(&bm) == UCHAR_MAX+1);

	return 0;
}
