/*
 * Copyright 2019 Scott Vokes
 *
 * See LICENCE for the full copyright terms.
 */

#include <assert.h>
#include <stdlib.h>
#include <errno.h>

#include <adt/queue.h>
#include <adt/set.h>
#include <adt/edgeset.h>
#include <adt/stateset.h>

#include "internal.h"

static void
clear_states(struct fsm_state *s)
{
	for (; s != NULL; s = s->next) { s->reachable = 0; }
}

static int
mark_states(struct fsm *fsm)
{
	const unsigned state_count = fsm_countstates(fsm);
	struct queue *q = queue_new(state_count);
	int res = 0;
	if (q == NULL) { return 1; }

	if (!queue_push(q, fsm->start)) {
		goto cleanup;
	}
	fsm->start->reachable = 1;
	
	for (;;) {
		const struct fsm_edge *e;
		struct edge_iter edge_iter;
		struct fsm_state *s;

		/* pop off queue; break if empty */
		if (!queue_pop(q, (void *)&s)) { break; }

		/* enqueue all directly reachable and unmarked, and mark them */
		{
			struct state_iter state_iter;
			struct fsm_state *es;
			for (es = state_set_first(s->epsilons, &state_iter);
			     es != NULL;
			     es = state_set_next(&state_iter)) {
				if (es->reachable) { continue; }
				if (!queue_push(q, es)) {
					goto cleanup;
				}
				es->reachable = 1;
			}
		}
		for (e = edge_set_first(s->edges, &edge_iter);
		     e != NULL;
		     e = edge_set_next(&edge_iter)) {
			struct state_iter state_iter;
			struct fsm_state *es;
			for (es = state_set_first(e->sl, &state_iter);
			     es != NULL;
			     es = state_set_next(&state_iter)) {
				if (es->reachable) { continue; }
				if (!queue_push(q, es)) {
					goto cleanup;
				}
				es->reachable = 1;
			}
		}
	}

	res = 1;

cleanup:
	if (q != NULL) { free(q); }
	return res;
}

int
sweep_states(struct fsm *fsm)
{
	int swept = 0;
	struct fsm_state **tail;

	/* This doesn't use fsm_removestate because it would be modifying the
	 * state graph while traversing it, and any state being removed here
	 * should (by definition) not be the start, or have any other reachable
	 * edges referring to it.
	 *
	 * There may temporarily be other states in the graph with other
	 * to it, because the states aren't topologically sorted, but
	 * they'll be collected soon as well. */

	for (tail = &fsm->sl; *tail != NULL;) {
		struct fsm_state *tmp;

		tmp = *tail;
		if (tmp->reachable) {
			/* reachable, advance tail to next state */
			tail = &(*tail)->next;
		} else {
			/* unreachable state */

			assert(*tail != fsm->start);

			/* for endcount accounting */
			fsm_setend(fsm, tmp, 0);

			/* remove *tail, don't advance tail */
			*tail = tmp->next;         /* remove link */

			/* clean up */
			edge_set_free(tmp->edges); /* free edges  */
			free(tmp);                 /* free state  */

			swept++;
		}
	}

	fsm->tail = tail;

	return swept;
}

int
fsm_collect_unreachable_states(struct fsm *fsm)
{
	clear_states(fsm->sl);
	if (!mark_states(fsm)) { return -1; }
	return sweep_states(fsm);
}
