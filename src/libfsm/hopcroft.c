#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

#include <fsm/fsm.h>
#include <fsm/pred.h>
#include <fsm/walk.h>

#include <adt/edgeset.h>

#include "internal.h"

int fsm_minimize_brz(struct fsm *);

struct hopcroft {
	fsm_state_t *pstates; /* list of items in each partition.  fsm->statecount elements */
	unsigned    *pstart;  /* index in pstates where each partition starts.  fsm->statecount elements */
	unsigned    *pend;    /* index in pstates where each partition starts.  fsm->statecount elements */

	unsigned    *plookup; /* reverse lookup: plookup[state] = partition of state */

	unsigned    np;       /* number of current partitions */

	/* (src,dst) edge list, ordered by symbol */
	struct {
		fsm_state_t src;
		fsm_state_t dst;
	} *edges;

	/* offsets into edges where each symbol begins */
	unsigned sym_offs[FSM_SIGMA_COUNT+1];

	/* worklist queue.  max size is fsm->statecount */
	struct {
		unsigned *q;  /* partitions in work list */
		unsigned n;   /* current size of work list */
	} worklist;

	/*** work arrays, each with fsm->statecount elements ***/
	fsm_state_t *scratch;   /* holds states while partitions are divided */
	int         *ismemb;    /* indicates if a state has a transition into the current partition */
	fsm_state_t *members;   /* list of states with transition into current partition */
};

static void
hopcroft_finalize(struct fsm *fsm, struct hopcroft *hop)
{
	const struct fsm_alloc *A = fsm->opt->alloc;
	assert(fsm != NULL);
	assert(hop != NULL);

	f_free(A, hop->pstates);
	f_free(A, hop->pstart);
	f_free(A, hop->pend);
	f_free(A, hop->worklist.q);
	f_free(A, hop->scratch);
	f_free(A, hop->ismemb);
	f_free(A, hop->members);
	f_free(A, hop->edges);
}

static struct hopcroft *
hopcroft_initialize(struct fsm *fsm, struct hopcroft *hop)
{
	static const struct hopcroft zero;
	const unsigned n = fsm->statecount;
	const struct fsm_alloc *A = fsm->opt->alloc;
	int errsv;

	if (n == 0) {
		errno = EINVAL;
		return NULL;
	}

	*hop = zero;

	if (hop->pstates = f_calloc(A, n, sizeof hop->pstates[0]), hop->pstates == NULL) {
		goto error;
	}

	if (hop->plookup = f_calloc(A, n, sizeof hop->plookup[0]), hop->plookup == NULL) {
		goto error;
	}

	if (hop->pstart = f_calloc(A, n, sizeof hop->pstart[0]), hop->pstart == NULL) {
		goto error;
	}

	if (hop->pend = f_calloc(A, n, sizeof hop->pend[0]), hop->pend == NULL) {
		goto error;
	}

	if (hop->worklist.q = f_calloc(A, n, sizeof hop->worklist.q), hop->worklist.q == NULL) {
		goto error;
	}

	if (hop->scratch = f_calloc(A, n, sizeof hop->scratch[0]), hop->scratch == NULL) {
		goto error;
	}

	if (hop->ismemb = f_calloc(A, n, sizeof hop->ismemb[0]), hop->ismemb == NULL) {
		goto error;
	}

	if (hop->members = f_calloc(A, n, sizeof hop->members[0]), hop->members == NULL) {
		goto error;
	}

	/* build edge list */
	{
		unsigned st;
		int i;
		unsigned sym_counts[FSM_SIGMA_COUNT];
		unsigned nedges;


		/* first count edges for each symbol and total number of edges */
		memset(sym_counts, 0, sizeof sym_counts);
		nedges = 0;
		for (st=0; st < fsm->statecount; st++) {
			struct edge_iter it;
			struct fsm_edge e;

			for (edge_set_reset(fsm->states[st].edges, &it); edge_set_next(&it, &e); ) {
				sym_counts[e.symbol]++;
				nedges++;
			}
		}

		/* Offsets are the cumulative sum of the counts */
		hop->sym_offs[0] = 0;
		for (i=0; i < FSM_SIGMA_COUNT; i++) {
			hop->sym_offs[i+1] = hop->sym_offs[i] + sym_counts[i];

			/* reuse count to keep track of where to put next edge
			 * in the table
			 */
			sym_counts[i] = 0;
		}

		if (hop->edges = f_calloc(A, nedges, sizeof hop->edges[0]), hop->edges == NULL) {
			goto error;
		}

		/* Now collect the actual edges... */
		/* first count edges for each symbol */
		for (st=0; st < fsm->statecount; st++) {
			struct edge_iter it;
			struct fsm_edge e;

			for (edge_set_reset(fsm->states[st].edges, &it); edge_set_next(&it, &e); ) {
				unsigned off = hop->sym_offs[e.symbol]+sym_counts[e.symbol];

				assert(off < hop->sym_offs[e.symbol+1]);

				sym_counts[e.symbol]++;

				hop->edges[off].src = st;
				hop->edges[off].dst = e.state;
			}
		}
	}

	return hop;

error:
	errsv = errno;
	hopcroft_finalize(fsm, hop);
	errno = errsv;
	return NULL;
}

static int
hopcroft_inner(struct fsm *fsm, struct hopcroft *hop)
{
	unsigned nstates;

	assert(fsm != NULL);
	assert(hop != NULL);

	nstates = fsm->statecount;

	if (fsm->endcount == 0) {
		/* trim should be run first! */
		return 1;
	}

	/* start with two partions: end states and non-end states */
	{
		unsigned st;

		hop->pstart[0] = 0;
		hop->pend[0]   = 0;

		hop->pstart[1] = fsm->endcount;
		hop->pend[1]   = fsm->endcount;

		for (st=0; st < nstates; st++) {
			if (fsm->states[st].end) {
				assert(hop->pend[0] < fsm->endcount);

				hop->pstates[hop->pend[0]++] = st;
				hop->plookup[st] = 0;
			} else {
				assert(hop->pend[1] < nstates);

				hop->pstates[hop->pend[1]++] = st;
				hop->plookup[st] = 1;
			}
		}

		hop->worklist.q[0] = 0;
		if (hop->pstart[1] < hop->pend[1]) {
			hop->np = 2;

			hop->worklist.q[1] = 1;
			hop->worklist.n = 2;
		} else {
			hop->np = 1;
			hop->worklist.n = 1;
		}
	}

	while (hop->worklist.n > 0) {
		unsigned part;
		int ch;

		assert(hop->worklist.n > 0);

		part = hop->worklist.q[--hop->worklist.n];

		assert(part < hop->np);

		for (ch=0; ch < FSM_SIGMA_COUNT; ch++) {
			/* range of edges that involve symbol 'ch' */
			const unsigned e0 = hop->sym_offs[ch];
			const unsigned e1 = hop->sym_offs[ch+1];

			unsigned nmembers = 0;

			unsigned ei, p;

			/* build X: set of states that have a transition into partition 'part' */
			for (ei = e0; ei < e1; ei++) {
				const unsigned src = hop->edges[ei].src;
				const unsigned dst = hop->edges[ei].dst;
				if (hop->plookup[dst] == part) {
					hop->members[nmembers++] = src;
					hop->ismemb[src] = 1;
				}
			}

			/* iterate over current partitions */
			p=0;
			while (p < hop->np) {
				const unsigned p0 = hop->pstart[p];
				const unsigned pnum = hop->pend[p] - p0;
				fsm_state_t *pstates = &hop->pstates[p0];
				unsigned num_in = 0, num_out = 0, ind;

				assert(hop->pstart[p] < hop->pend[p]);
				assert(hop->pend[p] <= fsm->statecount);

				for (ind=0; ind < pnum; ind++) {
					const fsm_state_t st = pstates[ind];

					assert(st < fsm->statecount);
					assert(ind >= num_in);

					if (hop->ismemb[st]) {
						/* state is in intersection of partition with set X */
						if (ind > num_in) {
							pstates[num_in] = st;
						}
						num_in++;
					} else {
						hop->scratch[num_out++] = st;
					}
				}

				assert(num_in  <= pnum);
				assert(num_out <= pnum);
				assert(num_in + num_out == pnum);

				if (num_in > 0 && num_out > 0) {
					/* partitions changed, need to update partitions and the work list */

					const unsigned new_p = hop->np++;  /* new partition for items in no-intersection states */
					unsigned out_ind;
					unsigned wi;

					/* intersection    partition (p)     is present in pstates[0] ... pstates[num_in],
					 * no-intersection partition (new_p) should be copied to pstates[num_in] ... pstates[pnum]
					 *
					 * update hop->pstart and hop->pend to reflect this...
					 */
					hop->pend[new_p] = hop->pend[p];
					hop->pend[p] = hop->pstart[new_p] = hop->pstart[p] + num_in;

					/* copy new partition states from scratch[0] ... scratch[num_out] to the remaining space
					 * pstates[num_in] ... pstates[pnum]
					 *
					 * also update hop->plookup
					 */
					for (out_ind = 0; out_ind < num_out; out_ind++) {
						const fsm_state_t st = hop->scratch[out_ind];
						pstates[num_in + out_ind] = st;

						hop->plookup[st] = new_p;
					}

					{
						/* update work lists
						 * XXX - can we avoid this linear scan?
						 */
						bool in_worklist = false;
						for (wi = 0; wi < hop->worklist.n; wi++) {
							if (hop->worklist.q[wi] == p) {
								in_worklist = true;
								break;
							}
						}

						if (in_worklist || num_in > num_out) {
							hop->worklist.q[hop->worklist.n++] = new_p;
						} else {
							hop->worklist.q[hop->worklist.n++] = p;
						}
					}

					/* Important! don't advance p here because it has changed */
				} else {
					/* partition did not change, no need to update the work list.
					 *
					 * also, there's no need to copy states: if all states ended
					 * up in the intersection partition, then the partition list
					 * was not changed.
					 *
					 * if they ended up in the no-intersection partition, then
					 * partition list is still not changed.
					 */

					p++; /* onward to the next partition! */
				}
			}

			{
				/* reset member set */
				unsigned mi;

				for (mi=0; mi < nmembers; mi++) {
					fsm_state_t st = hop->members[mi];
					hop->ismemb[st] = 0;
				}
			}
		}
	}

	/* states should be divided into partitions.  states within the same
	 * partition should be equivalent.
	 *
	 * Now that the excitement is done, we're left with the necessary but mundane task of 
	 * turning the original graph + partitions into a new graph.
	 */

	assert(hop->np <= fsm->statecount);

	if (hop->np == fsm->statecount) {
		/* special case: number of partitions is equal to the number of original states.  This means that each state has its own
		 * partition, so there are states equivalent to each other.
		 *
		 * In this case, we return the original graph, unaltered.
		 */

		return 1;
	} else {
		/* At least two states are equivalent.
		 *
		 * Generate a new graph and move it into fsm.  There's probably a way to do this in-place, but that's a refinement for
		 * later.
		 */
		struct fsm *min_fsm;
		fsm_state_t p;

		min_fsm = fsm_new(fsm->opt);
		if (min_fsm == NULL) {
			return 0;
		}

		if (!fsm_addstate_bulk(min_fsm, hop->np)) {
			return 0;
		}

		/* mark start state */
		fsm_setstart(min_fsm, hop->plookup[fsm->start]);

		/* now mark end states and add edges! */
		for (p = 0; p < hop->np; p++) {
			fsm_state_t st;
			struct edge_iter it;
			struct fsm_edge e;

			/* we only need to process the first state in each partition.  All other states are equivalent, so the
			 * first state will capture all of the behavior
			 */

			assert(hop->pend[p] > hop->pstart[p]);
			assert(hop->pend[p] <= fsm->statecount);

			st = hop->pstates[hop->pstart[p]];

			assert(st < fsm->statecount);

			/* end states can only share a partition with other end states, so if the first state is an end state,
			 * then all states in the partition are end states, and if the first state is not, then no state in
			 * the partition is an end state.
			 *
			 * So, the 'end' status of the partition is equal to the end status of the first state in the partition.
			 */

			fsm_setend(min_fsm, p, fsm->states[st].end);

			/* now add edges! */
			for (edge_set_reset(fsm->states[st].edges, &it); edge_set_next(&it, &e); ) {
				fsm_state_t p_dst = hop->plookup[e.state];
				if (!fsm_addedge_literal(min_fsm, p, p_dst, e.symbol)) {
					return 0;
				}
			}
		}

		fsm_move(fsm, min_fsm);

		return 1;
	}
}

int
fsm_minimise_hop(struct fsm *fsm)
{
	struct hopcroft hop;
	int errsv, ret;

	if (fsm->statecount < 2) {
		return 1;
	}

	if (hopcroft_initialize(fsm,&hop) == NULL) {
		return 0;
	}

	ret = hopcroft_inner(fsm,&hop);
	errsv = errno;
	hopcroft_finalize(fsm,&hop);
	errno = errsv;

	return ret;
}

#if 0
is_memb = [ False ] * nstates
worklist = [ 0, 1 ]
while len(worklist) > 0:
    pdiv = worklist.pop()
    # print('!-- pdiv:', pdiv)
    # print('!-- wlst:', worklist)
    # print('!-- part:',partitions)
    for ch in range(256):
        states = []
        for st in range(nstates):
            dst = forward_transitions[st].get(ch)
            if dst is not None and partition_lookup[dst] == pdiv:
                states.append(st)
                is_memb[st] = True

        pi = 0
        while pi < len(partitions):
            # print('!   >>', pi, partitions[pi])
            p_0 = [ st for st in partitions[pi] if is_memb[st] ]
            p_1 = [ st for st in partitions[pi] if not is_memb[st] ]

            if len(p_0) > 0 and len(p_1) > 0:
                partitions[pi] = p_0
                pi_new = len(partitions)
                partitions.append(p_1)

                for st in p_1:
                    partition_lookup[st] = pi_new

                # XXX - linear scan!  fix this!
                if pi in worklist:
                    worklist.append(pi_new)
                elif len(p_0) <= len(p_1):
                    worklist.append(pi)
                else:
                    worklist.append(pi_new)
            else:
                pi += 1

        for st in states:
            is_memb[st] = False
#endif

