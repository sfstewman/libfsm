/*
 * Copyright 2008-2017 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#include "walk2.h"

struct fsm;

struct fsm *
fsm_subtract(struct fsm *a, struct fsm *b)
{
	return fsm_walk2(a,b, FSM_WALK2_EDGE_SUBTRACT, FSM_WALK2_END_SUBTRACT);
}

