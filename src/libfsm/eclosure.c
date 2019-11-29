/*
 * Copyright 2008-2017 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#include <assert.h>
#include <limits.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <fsm/fsm.h>
#include <fsm/pred.h>
#include <fsm/walk.h>
#include <fsm/options.h>

#include <adt/set.h>
#include <adt/stateset.h>

#include "internal.h"

static int
hasbit(const unsigned char *bmap, unsigned int b) {
	const unsigned char bmask = 1 << (b % 8);
	const unsigned int  boff  = b / 8;

	return !!(bmap[boff] & bmask);
}

static void
setbit(unsigned char *bmap, const unsigned int b) {
	const unsigned char bmask = 1 << (b % 8);
	const unsigned int  boff  = b / 8;

	bmap[boff] |= bmask;

	assert(hasbit(bmap,b));
}

/*
 * Return a set of each state in the epsilon closure of the given state.
 * These are all the states reachable through epsilon transitions (that is,
 * without consuming any input by traversing a labelled edge), including the
 * given state itself.
 *
 * Intermediate states consisting entirely of epsilon transitions are
 * considered part of the closure.
 *
 * Returns closure on success, NULL on error.
 */
static void
epsilon_closure_inner(const struct fsm *fsm, fsm_state_t state, unsigned char *bitmap, unsigned int *closure_size_ptr, unsigned int *closure_first_ptr)
{
	struct state_iter it;
	fsm_state_t s;

	assert(fsm != NULL);
	assert(state < fsm->statecount);
	assert(bitmap != NULL);

	/* Find if the given state is already in the closure */
	if (hasbit(bitmap, state)) {
		/* fprintf(stderr, "EPS(0x%02x, state=%u) already set\n", *bitmap, state); */
		return;
	}

	/* fprintf(stderr, "EPS(0x%02x, state=%u) setting bit\n", *bitmap, state); */
	setbit(bitmap,state);
	*closure_size_ptr += 1;

	if (state < *closure_first_ptr) {
		*closure_first_ptr = state;
	}

	/* Follow each epsilon transition */
	for (state_set_reset(fsm->states[state].epsilons, &it); state_set_next(&it, &s); ) {
		epsilon_closure_inner(fsm, s, bitmap, closure_size_ptr, closure_first_ptr);
	}
}

struct state_set *
epsilon_closure(const struct fsm *fsm, fsm_state_t state, struct state_set *closure, struct epsilon_closure_table *tbl)
{
	unsigned char *bitmap;
	unsigned int nstates, nelts, closure_size, closure_first;
	unsigned int b, bcount;
	struct state_iter it;
	fsm_state_t s;

	const unsigned nbits = CHAR_BIT * sizeof *bitmap;

	assert(fsm != NULL);
	assert(closure != NULL);

	/* fprintf(stderr, "ECL of state %u\n", state); */
       	nstates = fsm_countstates(fsm);

	nelts = nstates / nbits + ((nstates % nbits ) != 0);

	bitmap = calloc(nelts, sizeof (*bitmap));
	if (bitmap == NULL) {
		return NULL;
	}

	for (state_set_reset(closure, &it); state_set_next(&it, &s); ) {
		setbit(bitmap,s);
	}

	closure_size = 0;
	closure_first = UINT_MAX;
	epsilon_closure_inner(fsm, state, bitmap, &closure_size, &closure_first);

	/* fprintf(stderr, "closure_first = %u, closure_size = %u\n", closure_first, closure_size); */

	/* convert bitmap to state_set */
	bcount = 0;
	for (b=closure_first; b < nstates && bcount < closure_size; b++) {
		if (hasbit(bitmap, b)) {
			/* fprintf(stderr, "  - ECL includes state %u\n", b); */
			if (!state_set_add(closure, b)) {
				free(bitmap);
				return NULL;
			}

			bcount++;
		}
	}

	free(bitmap);
	/* fprintf(stderr, "-- ECL found!\n"); */
	return closure;
}

