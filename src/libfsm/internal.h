/*
 * Copyright 2008-2017 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#ifndef FSM_INTERNAL_H
#define FSM_INTERNAL_H

#include <limits.h>
#include <stdlib.h>

#include <fsm/fsm.h>
#include <fsm/options.h>

#include <adt/hashset.h>

struct set;
struct edge_set;
struct state_set;

/*
 * The alphabet (Sigma) for libfsm's FSM is arbitrary octets.
 * These octets may or may not spell out UTF-8 sequences,
 * depending on the context in which the FSM is used.
 *
 * Octets are implemented here as (unsigned char) values in C.
 * As an implementation detail, we extend this range from 0..UCHAR_MAX
 * to include "special" edge types after the last valid octet.
 *
 * Currently the only special edge type is the epsilon transition,
 * for Thompson NFA.
 */

/*
 * The number of non-special symbols in the alphabet.
 * This is the number of symbols with the value <= UCHAR_MAX.
 */
#define FSM_SIGMA_COUNT (UCHAR_MAX + 1)

enum fsm_edge_type {
	FSM_EDGE_EPSILON = UCHAR_MAX + 1
};

/*
 * The highest value of an symbol, including special symbols.
 */
#define FSM_EDGE_MAX FSM_EDGE_EPSILON

#define FSM_ENDCOUNT_MAX ULONG_MAX

struct fsm_edge {
	struct state_set *sl;
	enum fsm_edge_type symbol;
};

struct epsilon_state;

struct fsm_state {
	unsigned int end:1;
	unsigned int reachable:1;

	struct edge_set *edges; /* containing `struct fsm_edge *` */

	void *opaque;

	/* these are only valid within one particular transformation.
	 * expected to be NULL at start and set back to NULL after. */
	union {
		/* temporary relation between one FSM and another */
		struct fsm_state *equiv;
		/* tracks which states have been visited in walk2 */
		struct fsm_state *visited;

		/* used by scc epsilon closure algorithm */
		struct epsilon_state *eps;
	} tmp;

#ifdef DEBUG_TODFA
	struct set *nfasl;
#endif

	struct fsm_state *next;

	unsigned int eps_scc;
};

struct fsm {
	struct fsm_state *sl;
	struct fsm_state **tail; /* tail of .sl */
	struct fsm_state *start;

	unsigned long endcount;

	const struct fsm_options *opt;

#ifdef DEBUG_TODFA
	struct fsm *nfa;
#endif
};

struct fsm_edge *
fsm_hasedge(const struct fsm_state *s, int c);

struct fsm_edge *
fsm_addedge(struct fsm_state *from, struct fsm_state *to, enum fsm_edge_type type);

void
fsm_carryopaque(struct fsm *fsm, const struct state_set *set,
	struct fsm *new, struct fsm_state *state);

void
fsm_clear_tmp(struct fsm *fsm);

void
fsm_state_clear_tmp(struct fsm_state *state);

struct state_set *
epsilon_closure(const struct fsm_state *state, struct state_set *closure);

struct state_array {
	struct fsm_state **states;
	size_t len;
	size_t cap;
};

void
state_array_clear(struct state_array *arr);

struct state_array *
state_array_add(struct state_array *arr, struct fsm_state *st);

struct state_array *
state_array_copy(struct state_array *dst, const struct state_array *src);

/* a set of uints */
struct uintset {
	struct hashset set;
};

int
uintset_initialize(struct uintset *s, size_t nbuckets);

void
uintset_finalize(struct uintset *s);

void *
uintset_add(struct uintset *s, unsigned int i);

size_t
uintset_count(const struct uintset *s);

void
uintset_clear(struct uintset *s);

int
uintset_contains(const struct uintset *s, unsigned int i);

enum { EDGE_BMAP_NBITS         = 256 };
enum { EDGE_BMAP_NBUCKETS      =  32 };
enum { EDGE_BMAP_BITSPERBUCKET =   8 };

struct edge_bmap {
	unsigned char bits[EDGE_BMAP_NBUCKETS];  /* bitmap of edges.  XXX - better as uint64_t? */
};

struct edge_bmap_iter {
	int bit;
};

void
edge_bmap_set(struct edge_bmap *bmap, unsigned char sym);

/* a |= b */
void
edge_bmap_or_eq(struct edge_bmap *a, const struct edge_bmap *b);

/* test that edges has bit 'sym' set */
int
edge_bmap_test(const struct edge_bmap *bmap, unsigned char sym);

void
edge_bmap_zero(struct edge_bmap *bmap);

int
edge_bmap_next(const struct edge_bmap *bmap, struct edge_bmap_iter *it);

int
edge_bmap_first(const struct edge_bmap *bmap, struct edge_bmap_iter *it);

#endif

