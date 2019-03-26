/*
 * Copyright 2008-2017 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <adt/set.h>
#include <adt/hashset.h>
#include <adt/mappingset.h>
#include <adt/transset.h>
#include <adt/stateset.h>
#include <adt/edgeset.h>

#include <fsm/fsm.h>
#include <fsm/pred.h>
#include <fsm/walk.h>
#include <fsm/options.h>

#include "internal.h"

/* hash function for a set of sorted states */
static unsigned long
hash_states(const struct state_set *s)
{
	const struct fsm_state **states = state_set_array(s);
	size_t nstates = state_set_count(s);

	return hashrec(states, nstates * sizeof states[0]);
}


/*
 * A set of states in an NFA.
 *
 * These have labels naming a transition which was followed to reach the state.
 * This is used for finding which states are reachable by a given label, given
 * a set of several states.
 */
struct trans {
	const struct fsm_state *state;
	char c;
};

/*
 * This maps a DFA state onto its associated NFA epsilon closure, such that an
 * existing DFA state may be found given any particular set of NFA states
 * forming an epsilon closure.
 *
 * These mappings are kept in a list; order does not matter.
 */

struct mapping {
	/* The set of NFA states forming the epsilon closure for this DFA state */
	struct state_set *closure;

	/* The DFA state associated with this epsilon closure of NFA states */
	struct fsm_state *dfastate;

	/* boolean: are the outgoing edges for dfastate all created? */
	unsigned int done:1;
};

struct fsm_determinise_cache {
	struct mapping_set *mappings;
	struct trans_set *trans;
};

static void
clear_trans(const struct fsm *fsm, struct trans_set *trans)
{
	struct trans_iter it;
	struct trans *t;

	for (t = trans_set_first(trans, &it); t != NULL; t = trans_set_next(&it)) {
		f_free(fsm, t);
	}

	trans_set_clear(trans);
}

static void
clear_mappings(const struct fsm *fsm, struct mapping_set *mappings)
{
	struct mapping_iter it;
	struct mapping *m;

	for (m = mapping_set_first(mappings, &it); m != NULL; m = mapping_set_next(&it)) {
		state_set_free(m->closure);
		f_free(fsm, m);
	}

	mapping_set_clear(mappings);
}

static int
cmp_trans(const void *a, const void *b)
{
	const struct trans *ta, *tb;

	assert(a != NULL);
	assert(b != NULL);

	ta = a;
	tb = b;

	return (ta->c > tb->c) - (ta->c < tb->c);
}

static int
cmp_mapping(const void *a, const void *b)
{
	const struct mapping *ma, *mb;

	assert(a != NULL);
	assert(b != NULL);

	ma = a;
	mb = b;

	return state_set_cmp(ma->closure, mb->closure);
}

static unsigned long
hash_mapping(const void *a)
{
	const struct mapping *m = a;
	return hash_states(m->closure);
}

/*
 * Find the DFA state associated with a given epsilon closure of NFA states.
 * A new DFA state is created if none exists.
 *
 * The association of DFA states to epsilon closures in the NFA is stored in
 * the mapping set for future reference.
 */
static struct mapping *
addtomappings(struct mapping_set *mappings, struct fsm *dfa, struct state_set *closure)
{
	struct mapping *m, search;

	/* Use an existing mapping if present */
	search.closure = closure;
	if ((m = mapping_set_contains(mappings, &search))) {
		state_set_free(closure);
		return m;
	}

	/* else add new DFA state */
	m = f_malloc(dfa, sizeof *m);
	if (m == NULL) {
		return NULL;
	}

	assert(closure != NULL);
	m->closure  = closure;
	m->dfastate = fsm_addstate(dfa);
	if (m->dfastate == NULL) {
		f_free(dfa, m);
		return NULL;
	}

	m->done = 0;

	if (!mapping_set_add(mappings, m)) {
		f_free(dfa, m);
		return NULL;
	}

	return m;
}

struct epsilon_state {
	/* original state */
	struct fsm_state *st;

	/* counter for identifying whether state is in the current closure */
	unsigned int closure_id;

	/* first edge */
	unsigned int edge0;
};

struct epsilon_edge {
	unsigned int src;
	unsigned int dst;
};

struct epsilon_memo {
	struct state_set *in_set;
	struct state_set *closure;
};

struct epsilon_table {
	size_t nstates;

	struct epsilon_state *states;
	struct epsilon_edge *edges;
	struct hashset rev_map;
	struct hashset memoize;

	unsigned int last_closure_id;
};

/* maps struct fsm_state * to index to struct epsilon_state * */
struct epsilon_map_entry {
	struct fsm_state *st;
	struct epsilon_state *est;
};

static int epsilon_state_compare(const void *a, const void *b)
{
	const struct epsilon_state *ea = a, *eb = b;
	return (ea->st > eb->st) - (ea->st < eb->st);
}

static unsigned long epsilon_state_hash(const void *a)
{
	const struct epsilon_state *ent = a;
	return hashrec(ent->st, sizeof *(ent->st));
}

static int epsilon_memo_cmp(const void *a, const void *b)
{
	const struct epsilon_memo *ma = a, *mb = b;
	return state_set_cmp(ma->in_set, mb->in_set);
}

static unsigned long epsilon_memo_hash(const void *a)
{
	const struct epsilon_memo *ma = a;
	return hash_states(ma->in_set);
}

static struct epsilon_state *
epsilon_table_lookup(struct epsilon_table *tbl, const struct fsm_state *st)
{
	(void)tbl;

	return st->tmp.eps;

	/*
	const static struct epsilon_state zero;
	st->equiv = (struct fsm_state *)&tbl->states[state_ind];

	struct epsilon_state tmp = zero;
	tmp.st = st;
	return hashset_contains(&tbl->rev_map, &tmp);
	*/
}

static struct state_set *
epsilon_memo_lookup(struct epsilon_table *tbl, struct state_set *s)
{
	struct epsilon_memo memo, *lkup;
	memo.in_set = s;

	lkup = hashset_contains(&tbl->memoize, &memo);
	if (lkup == NULL) {
		return NULL;
	}

	return lkup->closure;
}

static void
epsilon_memo_free(struct epsilon_memo *memo)
{
	if (memo == NULL) {
		return;
	}

	if (memo->in_set != NULL) {
		state_set_free(memo->in_set);
	}

	if (memo->closure != NULL) {
		state_set_free(memo->closure);
	}

	free(memo);
}

static struct epsilon_memo *
epsilon_memo_remember(struct epsilon_table *tbl, struct state_set *s, struct state_set *closure)
{
	static const struct epsilon_memo zero;

	struct epsilon_memo *memo;

	memo = malloc(sizeof *memo);
	if (memo == NULL) {
		goto error;
	}

	*memo = zero;

	memo->in_set = state_set_copy(s);
	if (memo->in_set == NULL) {
		goto error;
	}

	memo->closure = state_set_copy(closure);
	if (memo->closure == NULL) {
		goto error;
	}

	if (hashset_add(&tbl->memoize, memo) == NULL) {
		goto error;
	}

	return memo;

error:
	epsilon_memo_free(memo);
	return NULL;
}

static int epsilon_table_initialize(struct epsilon_table *tbl, const struct fsm *fsm)
{
	static const struct epsilon_table init;
	size_t nstates, nedges;
	struct fsm_state *st;
	size_t revmap_nbuckets;
	size_t state_ind, edge_ind;

	*tbl = init;

	/* count states */
	nstates = nedges = 0;
	for (st = fsm->sl; st != NULL; st = st->next) {
		const struct fsm_edge *e;

		nstates++;

		e = fsm_hasedge(st, FSM_EDGE_EPSILON);
		if (e != NULL) {
			nedges += state_set_count(e->sl);
		}
	}

	/* fprintf(stderr, "\n--[ nstates = %zu, nedges = %zu ]--\n\n", nstates,nedges); */

	/* initialize reverse map */
	revmap_nbuckets = nstates * (int)(1+1.0/DEFAULT_LOAD);
	if (!hashset_initialize(&tbl->rev_map, revmap_nbuckets, DEFAULT_LOAD, epsilon_state_hash, epsilon_state_compare)) {
		goto error;
	}

	if (!hashset_initialize(&tbl->memoize, DEFAULT_NBUCKETS, DEFAULT_LOAD, epsilon_memo_hash, epsilon_memo_cmp)) {
		goto error;
	}

	/* allocate state and edge arrays */
	tbl->states = f_malloc(fsm, (nstates+1) * sizeof *tbl->states);
	if (tbl->states == NULL) {
		goto error;
	}

	if (nedges > 0) {
		tbl->edges = f_malloc(fsm, nedges * sizeof *tbl->edges);
		if (tbl->edges == NULL) {
			goto error;
		}
	}

	/* iterate through states, filling in the state array and the index
	 * lookup
	 */
	state_ind = 0;
	for (st = fsm->sl; st != NULL; st = st->next) {
		tbl->states[state_ind].st = st;
		tbl->states[state_ind].closure_id = 0;
		tbl->states[state_ind].edge0 = 0;

		if (hashset_add(&tbl->rev_map, &tbl->states[state_ind]) == NULL) {
			goto error;
		}

		/* hijack equiv field to speed things up... */
		st->tmp.eps = &tbl->states[state_ind];

		state_ind++;
	}

	/* next iterate through edges, filling in edge table and
	 * updating the edge0 entries in the state table
	 */
	edge_ind  = 0;
	for (state_ind = 0; state_ind < nstates; state_ind++) {
		const struct fsm_state *st0;
		const struct fsm_state *st1;
		const struct fsm_edge *e;
		struct state_iter it;

		st0 = tbl->states[state_ind].st;
		tbl->states[state_ind].edge0 = edge_ind;

		e = fsm_hasedge(st0, FSM_EDGE_EPSILON);
		if (e == NULL) {
			continue;
		}

		for (st1 = state_set_first(e->sl, &it); st1 != NULL; st1 = state_set_next(&it)) {
			struct epsilon_state *est;

			assert(edge_ind < nedges);

			est = epsilon_table_lookup(tbl, st1);
			assert(est != NULL);

			if (est == NULL) {
				/* something went wrong */
				/* XXX - provide better feedback? */
				goto error;
			}

			tbl->edges[edge_ind].src = state_ind;
			tbl->edges[edge_ind].dst = est - &tbl->states[0];

			edge_ind++;
		}
	}

	assert(edge_ind == nedges);

	/* last extra state holds the edge count */
	tbl->states[nstates].st = NULL;
	tbl->states[nstates].closure_id = 0;
	tbl->states[nstates].edge0 = edge_ind;

	tbl->nstates = nstates;

	return 1;

error:
	hashset_finalize(&tbl->rev_map);
	hashset_finalize(&tbl->memoize);
	f_free(fsm, tbl->states);
	f_free(fsm, tbl->edges);

	return 0;
}

static void epsilon_table_finalize(const struct fsm *fsm, struct epsilon_table *tbl)
{
	if (tbl == NULL) {
		return;
	}

	hashset_finalize(&tbl->rev_map);

	if (tbl->memoize.buckets != NULL) {
		struct hashset_iter it;
		struct epsilon_memo *m;
		for (m = hashset_first(&tbl->memoize,&it); m != NULL; m = hashset_next(&it)) {
			epsilon_memo_free(m);
		}
	}

	hashset_finalize(&tbl->memoize);

	f_free(fsm, tbl->states);
	f_free(fsm, tbl->edges);

	tbl->states = NULL;
	tbl->edges  = NULL;
}

/* data for Tarjan's strongly connected components alg */
struct scc_data {
	unsigned int *stack;
	unsigned int *indexes;
	unsigned int *lowest;
	unsigned int *labels;
	unsigned char *on_stack;

	unsigned int top; /* holds stack top */
	unsigned int lbl; /* holds current scc label */
	unsigned int idx; /* holds current index */
};

static void scc_dfs(struct epsilon_table *tbl, struct scc_data *data, unsigned int st)
{
	unsigned int e0,e1, e, lbl;

	/* invariants:
	 * 1. beginning this search, nodes must have been visited (index == 0)
	 * 2. nodes should not be on the node stack (should follow from 1)
	 */
	assert(data->indexes[st] == 0);
	assert(data->on_stack[st] == 0);

	if (data->labels[st] != 0) {
		/* already part of an SCC */
		fprintf(stderr, "--> state %u already labeled: %u\n", st, data->labels[st]);
		return;
	}

	data->stack[data->top++] = st; /* data->indexes[st]; */

	data->indexes[st] = ++data->idx;
	assert(data->idx > 0);

	data->lowest[st] = data->indexes[st];
	data->on_stack[st] = 1;

	fprintf(stderr, "--push--\n[%4u] %u [ind=%u : lo=%u : stk=%d]\n", data->top, st, data->indexes[st], data->lowest[st], data->on_stack[st]);
	fprintf(stderr, "--stack--\n");
	{
		unsigned int i;
		for(i=data->top; i > 0; i--) {
			unsigned int st1 = data->stack[i-1];
			fprintf(stderr, "[%4u] %u [ind=%u : lo=%u : stk=%d]\n", i, st1, data->indexes[st1], data->lowest[st1], data->on_stack[st1]);
		}
	}

	e0 = tbl->states[st].edge0;
	e1 = tbl->states[st+1].edge0;
	for (e=e0; e < e1; e++) {
		unsigned int st1;

		assert(tbl->edges[e].src == st);

		st1 = tbl->edges[e].dst;

		if (data->indexes[st1] == 0) {
			scc_dfs(tbl, data, st1);
			if (data->lowest[st] > data->lowest[st1]) {
				data->lowest[st] = data->lowest[st1];
			}
		} else if (data->on_stack[st1] && data->lowest[st] > data->indexes[st1]) {
			data->lowest[st] = data->lowest[st1];
		}
	}

	if (data->indexes[st] != data->lowest[st]) {
		/* not the root of a strongly connected component */
		assert(data->lowest[st] < data->indexes[st]);
		return;
	}

	/* the root of a strongly connected component */
	lbl = ++data->lbl;
	assert(lbl > 0);
	fprintf(stderr, "--scc %u--\n", lbl);
	for (;;) {
		unsigned int st1;

		assert(data->top > 0);
		st1 = data->stack[--data->top];

		fprintf(stderr, "[%4u] lbl=%4u st0=%u[ind=%u : lo=%u : stk=%d] st1=%u[ind=%u : lo=%u : stk=%d]\n",
			data->top+1, lbl,
			st,  data->indexes[st],  data->lowest[st],  data->on_stack[st],
			st1, data->indexes[st1], data->lowest[st1], data->on_stack[st1]);

		assert(data->on_stack[st1] != 0);
		data->on_stack[st1] = 0;

		assert(data->labels[st1] == 0);
		data->labels[st1] = lbl;

		if (st == st1) {
			break;
		}
	}
}

static int find_strongly_connected_components(struct epsilon_table *tbl, unsigned int **scc_states, unsigned int **scc_offsets)
{
	static const struct scc_data zero;
	struct scc_data data;
	char *block;
	size_t sz;
	unsigned i, minindexed = 0;
	int ret = -1;

	/* allocate one block, all at once */
	sz  = 4*tbl->nstates * sizeof data.stack[0]; /* stack, indexes, lowest, labels */
	sz += tbl->nstates * sizeof data.on_stack[0];

	block = malloc(sz);
	if (block == NULL) {
		goto finish;
	}

	data = zero;

	data.stack    = malloc(tbl->nstates * sizeof data.stack[0]);
	data.indexes  = malloc(tbl->nstates * sizeof data.indexes[0]);
	data.lowest   = malloc(tbl->nstates * sizeof data.lowest[0]);
	data.labels   = malloc(tbl->nstates * sizeof data.labels[0]);
	data.on_stack = malloc(tbl->nstates * sizeof data.on_stack[0]);

	if (data.stack == NULL || data.indexes == NULL || data.lowest == NULL || data.labels == NULL || data.on_stack == NULL) {
		goto finish;
	}

	for (i=0; i < tbl->nstates; i++) {
		data.stack[i]    = 0;
		data.indexes[i]  = 0;
		data.lowest[i]   = 0;
		data.labels[i]   = 0;
		data.on_stack[i] = 0;
	}

	for (;;) {
		unsigned int st;

		/* scan for states that have not been labeled as part of a connected component... */
		for (st=minindexed; st < tbl->nstates; st++) {
			if (data.indexes[st] > 0) {
				continue;
			}

			if (tbl->states[st].edge0 == tbl->states[st+1].edge0) {
				/* no epsilon edges, no need for a DFS */
				data.indexes[st] = ++data.idx;
				data.labels[st]  = ++data.lbl;
				continue;
			}

			/* found a label==0 where there are epsilon edges */
			break;
		}

		/* stop when we can't find any more unlabeled states */
		if (st == tbl->nstates) {
			break;
		}

		minindexed = st; /* don't repeatedly search through things already given an index... */

		fprintf(stderr, "=== search starting at %u ===\n", st);
		scc_dfs(tbl, &data, st);

		/* state should be labeled after scc_dfs */
		assert(data.labels[st] > 0);
	}

	/* set the labels on the fsm_state nodes */
	{ 
		unsigned int st;
		for (st=0; st < tbl->nstates; st++) {
			struct fsm_state *s = tbl->states[st].st;
			s->eps_scc = data.labels[st];
		}
	}

	/* Build a list of states associated with each SCC so we can generate
	 * the epsilon closure for each SCC in reverse-topological order.
	 *
	 * Need to return:
	 * 1) list of states ordered by scc
	 * 2) offsets into the list for each scc
	 *
	 * To avoid unnecessary allocations, reuse the stack, indexes, and
	 * lowest arrays.
	 */
	{
		unsigned int *max_off, *scc_list, *lbl_inds;
		unsigned int i, maxlbl;

		max_off  = data.stack;   data.stack   = NULL;  /* we want to retain max_off and scc_list */
		scc_list = data.indexes; data.indexes = NULL;
		lbl_inds = data.lowest;  /* temporary counters, no need to retain */

		maxlbl = data.lbl;

		for (i=0; i < tbl->nstates; i++) {
			max_off[i] = scc_list[i] = lbl_inds[i] = 0;
		}

		/* count number of states per label */
		for (i=0; i < tbl->nstates; i++) {
			unsigned int lbl = data.labels[i];
			assert(lbl > 0 && lbl <= maxlbl);

			max_off[lbl-1]++;
		}

		/* convert max_off to cumulative sum */
		for (i=1; i < maxlbl; i++) {
			max_off[i] += max_off[i-1];
			lbl_inds[i] = max_off[i-1]; /* first offset of lbl[i] starts at max_off[i-1] */
		}

		/* build lists of states */
		for (i=0; i < tbl->nstates; i++) {
			unsigned int lbl = data.labels[i];
			unsigned int off;

			assert(lbl > 0 && lbl <= maxlbl);

			off = lbl_inds[lbl-1]++;
			assert(off < max_off[lbl-1]);
			scc_list[off] = i;
		}

		if (scc_states) {
			*scc_states = scc_list;
		} else {
			free(scc_list);
		}

		if (scc_offsets) {
			*scc_offsets = max_off;
		} else {
			free(max_off);
		}
	}

	ret = 0;

finish:
	free(data.stack);
	free(data.indexes);
	free(data.lowest);
	free(data.labels);
	free(data.on_stack);

	return ret;
}

static struct state_array *
epsilon_closure_tbl(struct epsilon_table *tbl, size_t s0, unsigned int closure_id, struct state_array *states)
{
	unsigned int ei,e0,e1;

	assert(s0 < tbl->nstates);
	assert(closure_id > 0);

	if (tbl->states[s0].closure_id == closure_id) {
		return states;
	}

	if (state_array_add(states, tbl->states[s0].st) == NULL) {
		return NULL;
	}

	tbl->states[s0].closure_id = closure_id;

	e0 = tbl->states[s0].edge0;
	e1 = tbl->states[s0+1].edge0;

	for (ei = e0; ei < e1; ei++) {
		assert(tbl->edges[ei].src == s0);
		if (epsilon_closure_tbl(tbl, tbl->edges[ei].dst, closure_id, states) == NULL) {
			return NULL;
		}
	}

	return states;
}

static struct state_set *
epsilon_closure_usetbl(const struct fsm *fsm, struct epsilon_table *tbl, const struct fsm_state *state)
{
	const static struct state_array arr_init;
	struct state_array arr = arr_init;
	struct epsilon_state *est;
	unsigned int closure_id;

	est = epsilon_table_lookup(tbl, state);
	if (est == NULL) {
		return NULL;
	}

	closure_id = ++tbl->last_closure_id;
	if (epsilon_closure_tbl(tbl,est - &tbl->states[0],closure_id,&arr) == NULL) {
		f_free(fsm, arr.states);
		return NULL;
	}

	/* convert states to set */
	/* fprintf(stderr, "%s: %zd, %u\n", __func__, est-&tbl->states[0],closure_id); */
	return state_set_create_from_array((struct fsm_state **)arr.states, arr.len);
}

static struct state_set *
epsilon_closure_states(const struct fsm *fsm, struct epsilon_table *tbl, struct state_set *states)
{
	const static struct state_array arr_init;
	struct state_array arr = arr_init;
	struct epsilon_state *est;
	unsigned int closure_id;
	struct state_iter it;
	struct fsm_state *s;

	closure_id = ++tbl->last_closure_id;
	/* fprintf(stderr, "%s: --[ %lu states, closure_id = %u ]--\n", __func__, (unsigned long)state_set_count(states), closure_id); */
	for (s = state_set_first(states,&it); s != NULL; s = state_set_next(&it)) {
		est = epsilon_table_lookup(tbl, s);
		if (est == NULL) {
			goto error;
		}

		/* fprintf(stderr, "%s: %zd, %u\n", __func__, est-&tbl->states[0],closure_id); */
		if (epsilon_closure_tbl(tbl,est - &tbl->states[0],closure_id,&arr) == NULL) {
			goto error;
		}
	}
	/* fprintf(stderr, "%s: ---\n", __func__); */

	/* convert states to set */
	return state_set_create_from_array((struct fsm_state **)arr.states, arr.len);

error:
	f_free(fsm, arr.states);
	return NULL;
}

int fsm_label_epsilon_scc(struct fsm *fsm)
{
	const static struct epsilon_table epstbl_init;
	struct epsilon_table epstbl = epstbl_init;
	int ret = -1;

	if (!epsilon_table_initialize(&epstbl,fsm)) {
		goto finish;
	}

	ret = find_strongly_connected_components(&epstbl, NULL, NULL);

finish:
	epsilon_table_finalize(fsm,&epstbl);
	return ret;
}

/*
 * Return the DFA state associated with the closure of a given NFA state.
 * Create the DFA state if neccessary.
 */
static struct fsm_state *
state_closure(const struct fsm *nfa, struct epsilon_table *tbl, struct mapping_set *mappings, struct fsm *dfa, const struct fsm_state *nfastate,
	int includeself)
{
	struct mapping *m;
	struct state_set *ec;

	assert(dfa != NULL);
	assert(nfastate != NULL);
	assert(mappings != NULL);

	ec = epsilon_closure_usetbl(nfa, tbl, nfastate);
	if (ec == NULL) {
		return NULL;
	}

	if (!includeself) {
		state_set_remove(ec, (void *) nfastate);
	}

	if (state_set_count(ec) == 0) {
		state_set_free(ec);
		return NULL;
	}

	m = addtomappings(mappings, dfa, ec);
	if (m == NULL) {
		return NULL;
	}

	return m->dfastate;
}

/*
 * Return the DFA state associated with the closure of a set of given NFA
 * states. Create the DFA state if neccessary.
 */
static struct fsm_state *
set_closure(const struct fsm *nfa, struct epsilon_table *tbl, struct mapping_set *mappings, struct fsm *dfa, struct state_set *set)
{
	struct state_set *ec;
	struct mapping *m;

	assert(set != NULL);
	assert(mappings != NULL);

	ec = epsilon_memo_lookup(tbl, set);
	if (ec != NULL) {
		ec = state_set_copy(ec);
		if (ec == NULL) {
			return NULL;
		}
	} else {
		ec = epsilon_closure_states(nfa, tbl, set);
		if (ec == NULL) {
			return NULL;
		}

		epsilon_memo_remember(tbl, set, ec);
	}

	m = addtomappings(mappings, dfa, ec);
	if (m == NULL) {
		/* XXX - cleanup? */
		return NULL;
	}

	return m->dfastate;
}

struct mapping_iter_save {
	struct mapping_iter iter;
	int saved;
};

/*
 * Return an arbitary mapping which isn't marked "done" yet.
 */
static struct mapping *
nextnotdone(struct mapping_set *mappings, struct mapping_iter_save *sv)
{
	struct mapping_iter it;
	struct mapping *m;
	int do_rescan = sv->saved;

	assert(sv != NULL);

	if (sv->saved) {
		it = sv->iter;
		m = mapping_set_next(&it);
	} else {
		m = mapping_set_first(mappings, &it);
	}

rescan:
	for (; m != NULL; m = mapping_set_next(&it)) {
		if (!m->done) {
			sv->saved = 1;
			sv->iter = it;
			return m;
		}
	}

	if (do_rescan) {
		m = mapping_set_first(mappings, &it);
		do_rescan = 0;
		goto rescan;
	}

	return NULL;
}

/*
 * List all states within a set which are reachable via non-epsilon
 * transitions (that is, have a label associated with them).
 *
 * TODO: maybe simpler to just return the set, rather than take a double pointer
 */
static int
listnonepsilonstates(const struct fsm *fsm, struct trans_set *trans, struct state_set *set)
{
	struct fsm_state *s;
	struct state_iter it;

	assert(set != NULL);
	assert(trans != NULL);

	for (s = state_set_first(set, &it); s != NULL; s = state_set_next(&it)) {
		struct fsm_edge *e;
		struct edge_iter jt;

		for (e = edge_set_first(s->edges, &jt); e != NULL; e = edge_set_next(&jt)) {
			struct fsm_state *st;
			struct state_iter kt;

			if (e->symbol > UCHAR_MAX) {
				break;
			}

			for (st = state_set_first(e->sl, &kt); st != NULL; st = state_set_next(&kt)) {
				struct trans *p, search;

				assert(st != NULL);

				/* Skip transitions we've already got */
				search.c = e->symbol;
				if ((p = trans_set_contains(trans, &search))) {
					continue;
				}

				p = f_malloc(fsm, sizeof *p);
				if (p == NULL) {
					clear_trans(fsm ,trans);
					return 0;
				}

				p->c = e->symbol;
				p->state = st;

				if (!trans_set_add(trans, p)) {
					f_free(fsm, p);
					clear_trans(fsm, trans);
					return 0;
				}
			}
		}
	}

	return 1;
}

/*
 * Return a list of all states reachable from set via the given transition.
 */
static int
allstatesreachableby(struct state_set *set, char c, struct state_set *sl)
{
	struct fsm_state *s;
	struct state_iter it;

	assert(set != NULL);

	for (s = state_set_first(set, &it); s != NULL; s = state_set_next(&it)) {
		struct fsm_state *es;
		struct fsm_edge *to;

		if ((to = fsm_hasedge(s, (unsigned char) c)) != NULL) {
			struct state_iter jt;

			for (es = state_set_first(to->sl, &jt); es != NULL; es = state_set_next(&jt)) {
				assert(es != NULL);

				if (!state_set_add(sl, es)) {
					return 0;
				}
			}
		}
	}

	return 1;
}

static void
carryend(struct state_set *set, struct fsm *fsm, struct fsm_state *state)
{
	struct state_iter it;
	struct fsm_state *s;

	assert(set != NULL); /* TODO: right? */
	assert(fsm != NULL);
	assert(state != NULL);

	for (s = state_set_first(set, &it); s != NULL; s = state_set_next(&it)) {
		if (fsm_isend(fsm, s)) {
			fsm_setend(fsm, state, 1);
		}
	}
}

/*
 * Convert an NFA to a DFA. This is the guts of conversion; it is an
 * implementation of the well-known multiple-states method. This produces a DFA
 * which simulates the given NFA by collating all reachable NFA states
 * simultaneously. The basic principle behind this is a closure on epsilon
 * transitions, which produces the set of all reachable NFA states without
 * consuming any input. This set of NFA states becomes a single state in the
 * newly-created DFA.
 *
 * For a more in-depth discussion, see (for example) chapter 2 of Appel's
 * "Modern compiler implementation", which has a detailed description of this
 * process.
 *
 * As all DFA are NFA; for a DFA this has no semantic effect (other than
 * renumbering states as a side-effect of constructing the new FSM).
 */
static struct fsm *
determinise(struct fsm *nfa,
	struct fsm_determinise_cache *dcache)
{
	static const struct mapping_iter_save sv_init;
	static const struct epsilon_table epstbl_init;

	struct epsilon_table epstbl = epstbl_init;

	struct mapping *curr;
	struct mapping_set *mappings;
	struct mapping_iter it;
	struct trans_set *trans;
	struct fsm *dfa;

	struct mapping_iter_save sv;

	assert(nfa != NULL);
	assert(nfa->opt != NULL);
	assert(dcache != NULL);

	dfa = fsm_new(nfa->opt);
	if (dfa == NULL) {
		return NULL;
	}

#ifdef DEBUG_TODFA
	dfa->nfa = nfa;
#endif

	if (nfa->endcount == 0) {
		dfa->start = fsm_addstate(dfa);
		if (dfa->start == NULL) {
			fsm_free(dfa);
			return NULL;
		}

		return dfa;
	}

	if (dcache->mappings == NULL) {
		dcache->mappings = mapping_set_create(hash_mapping, cmp_mapping);
		if (dcache->mappings == NULL) {
			fsm_free(dfa);
			return NULL;
		}
	}
	mappings = dcache->mappings;

	if (dcache->trans == NULL) {
		dcache->trans = trans_set_create(cmp_trans);
		if (dcache->trans == NULL) {
			fsm_free(dfa);
			mapping_set_free(mappings);
			return NULL;
		}
	}
	trans = dcache->trans;
	assert(trans != NULL);

	if (!epsilon_table_initialize(&epstbl,nfa)) {
		goto error;
	}

	/*
	 * The epsilon closure of the NFA's start state is the DFA's start state.
	 * This is not yet "done"; it starts off the loop below.
	 */
	{
		const struct fsm_state *nfastart;
		struct fsm_state *dfastart;
		int includeself = 1;

		nfastart = fsm_getstart(nfa);

		/*
		 * As a special case for Brzozowski's algorithm, fsm_determinise() is
		 * expected to produce a minimal DFA for its invocation after the second
		 * reversal. Since we do not provide multiple start states, fsm_reverse()
		 * may introduce a new start state which transitions to several states.
		 * This is the situation we detect here.
		 *
		 * This fabricated start state is then excluded from its epsilon closure,
		 * so that the closures for its destination states are found equivalent,
		 * because they also do not include the start state.
		 *
		 * If you pass an equivalent NFA where this is not the case (for example,
		 * with the start state containing an epsilon edge to itself), we regard
		 * this as any other DFA, and minimal output is not guaranteed.
		 */
		if (!fsm_isend(nfa, nfastart)
			&& fsm_epsilonsonly(nfa, nfastart) && !fsm_hasincoming(nfa, nfastart))
		{
			includeself = 0;
		}

		dfastart = state_closure(nfa, &epstbl, mappings, dfa, nfastart, includeself);
		if (dfastart == NULL) {
			/* TODO: error */
			goto error;
		}

		fsm_setstart(dfa, dfastart);
	}

	/*
	 * While there are still DFA states remaining to be "done", process each.
	 */
	sv = sv_init;
	for (curr = mapping_set_first(mappings, &it); (curr = nextnotdone(mappings, &sv)) != NULL; curr->done = 1) {
		struct trans_iter jt;
		struct trans *t;

		/*
		 * Loop over every unique non-epsilon transition out of curr's epsilon
		 * closure.
		 *
		 * This is a set of labels. Since curr->closure is already a closure
		 * (computed on insertion to mappings), these labels directly reach the
		 * next states in the NFA.
		 */
		/* TODO: document that nes contains only entries with labels set */
		if (!listnonepsilonstates(dfa, trans, curr->closure)) {
			goto error;
		}

		for (t = trans_set_first(trans, &jt); t != NULL; t = trans_set_next(&jt)) {
			struct fsm_state *new;
			struct fsm_edge *e;
			struct state_set *reachable;

			assert(t->state != NULL);

			reachable = state_set_create();
			if (reachable == NULL) {
				goto error;
			}

			/*
			 * Find the closure of the set of all NFA states which are reachable
			 * through this label, starting from the set of states forming curr's
			 * closure.
			 */
			if (!allstatesreachableby(curr->closure, t->c, reachable)) {
				state_set_free(reachable);
				goto error;
			}

			new = set_closure(nfa, &epstbl, mappings, dfa, reachable);
			state_set_free(reachable);
			if (new == NULL) {
				clear_trans(dfa, trans);
				goto error;
			}

			e = fsm_addedge_literal(dfa, curr->dfastate, new, t->c);
			if (e == NULL) {
				clear_trans(dfa, trans);
				goto error;
			}
		}

		clear_trans(dfa, trans);

#ifdef DEBUG_TODFA
		{
			struct state_set *q;

			for (q = state_set_first(curr->closure, &jt); q != NULL; q = state_set_next(&jt)) {
				if (!set_add(&curr->dfastate->nfasl, q)) {
					goto error;
				}
			}
		}
#endif

		/*
		 * The current DFA state is an end state if any of its associated NFA
		 * states are end states.
		 */
		carryend(curr->closure, dfa, curr->dfastate);

		/*
		 * Carry through opaque values, if present. This isn't anything to do
		 * with the DFA conversion; it's meaningful only to the caller.
		 */
		fsm_carryopaque(dfa, curr->closure, dfa, curr->dfastate);
	}

	clear_mappings(dfa, mappings);

	/* TODO: can assert a whole bunch of things about the dfa, here */
	assert(fsm_all(dfa, fsm_isdfa));

	return dfa;

error:
	epsilon_table_finalize(nfa,&epstbl);
	clear_mappings(dfa, mappings);
	fsm_free(dfa);

	return NULL;
}

int
fsm_determinise_cache(struct fsm *fsm,
	struct fsm_determinise_cache **dcache)
{
	struct fsm *dfa;

	assert(fsm != NULL);
	assert(fsm->opt != NULL);
	assert(dcache != NULL);

	if (*dcache == NULL) {
		*dcache = f_malloc(fsm, sizeof **dcache);
		if (*dcache == NULL) {
			return 0;
		}

		(*dcache)->mappings = mapping_set_create(hash_mapping, cmp_mapping);
		if ((*dcache)->mappings == NULL) {
			f_free(fsm, *dcache);
			return 0;
		}

		(*dcache)->trans    = trans_set_create(cmp_trans);
		if ((*dcache)->trans == NULL) {
			mapping_set_free((*dcache)->mappings);
			f_free(fsm, *dcache);
			return 0;
		}
	}

	dfa = determinise(fsm, *dcache);
	if (dfa == NULL) {
		return 0;
	}

#ifdef DEBUG_TODFA
	fsm->nfa = fsm_new(fsm->opt);
	if (fsm->nfa == NULL) {
		return 0;
	}

	assert(dfa->nfa == fsm);

	fsm->nfa->sl    = fsm->sl;
	fsm->nfa->tail  = fsm->tail;
	fsm->nfa->start = fsm->start;

	/* for fsm_move's free contents */
	fsm->sl    = NULL;
	fsm->tail  = NULL;
	fsm->start = NULL;
#endif

	fsm_move(fsm, dfa);

	return 1;
}

void
fsm_determinise_freecache(struct fsm *fsm, struct fsm_determinise_cache *dcache)
{
	(void) fsm;

	if (dcache == NULL) {
		return;
	}

	clear_mappings(fsm, dcache->mappings);
	clear_trans(fsm, dcache->trans);

	if (dcache->mappings != NULL) {
		mapping_set_free(dcache->mappings);
	}

	if (dcache->trans != NULL) {
		trans_set_free(dcache->trans);
	}

	f_free(fsm, dcache);
}

int
fsm_determinise(struct fsm *fsm)
{
	struct fsm_determinise_cache *dcache;
	int r;

	dcache = NULL;

	r = fsm_determinise_cache(fsm, &dcache);

	fsm_determinise_freecache(fsm, dcache);

	return r;
}

