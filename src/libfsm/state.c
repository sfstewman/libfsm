/*
 * Copyright 2008-2017 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#include <assert.h>
#include <stdlib.h>

#include <adt/set.h>

#include <fsm/fsm.h>

#include "internal.h"

static int
fsm_state_cmpedges(const void *a, const void *b)
{
	const struct fsm_edge *ea, *eb;

	assert(a != NULL);
	assert(b != NULL);

	ea = a;
	eb = b;

	/* N.B. various edge iterations rely on the ordering of edges to be in
	 * ascending order.
	 */
	return (ea->symbol > eb->symbol) - (ea->symbol < eb->symbol);
}


static struct edge_set *
edge_set_create(struct fsm *fsm)
{
	static const struct edge_set init;

	struct edge_set *set;
	set = f_malloc(fsm, sizeof *set);
	*set = init;
	set->set = set0_create(fsm_state_cmpedges);
	return set;
}

struct fsm_state *
fsm_addstate(struct fsm *fsm)
{
	struct fsm_state *new;

	assert(fsm != NULL);

	new = f_malloc(fsm, sizeof *new);
	if (new == NULL) {
		return NULL;
	}

	new->end = 0;
	new->edges = edge_set_create(fsm);
	new->opaque = NULL;

#ifdef DEBUG_TODFA
	new->nfasl = NULL;
#endif

	*fsm->tail = new;
	new->next = NULL;
	fsm->tail  = &new->next;

	return new;
}

void
fsm_removestate(struct fsm *fsm, struct fsm_state *state)
{
	struct fsm_state *s;
	struct fsm_edge *e;
	struct edge_iter it;

	assert(fsm != NULL);
	assert(state != NULL);

	/* for endcount accounting */
	fsm_setend(fsm, state, 0);

	for (s = fsm->sl; s != NULL; s = s->next) {
		for (e = edge_set_first(s->edges, &it); e != NULL; e = edge_set_next(&it)) {
			state_set_remove(e->sl, state);
		}
	}

	for (e = edge_set_first(state->edges, &it); e != NULL; e = edge_set_next(&it)) {
		state_set_free(e->sl);
		f_free(fsm, e);
	}
	edge_set_free(state->edges);

	if (fsm->start == state) {
		fsm->start = NULL;
	}

	{
		struct fsm_state **p;
		struct fsm_state **tail;

		tail = &fsm->sl;

		for (p = &fsm->sl; *p != NULL; p = &(*p)->next) {
			if (*p == state) {
				struct fsm_state *next;

				if (fsm->tail == &(*p)->next) {
					fsm->tail = tail;
				}

				next = (*p)->next;
				f_free(fsm, *p);
				*p = next;
				break;
			}

			tail = &(*p)->next;
		}
	}
}
