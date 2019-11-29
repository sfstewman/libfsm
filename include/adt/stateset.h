/*
 * Copyright 2019 Shannon F. Stewman
 *
 * See LICENCE for the full copyright terms.
 */

#ifndef ADT_STATESET_H
#define ADT_STATESET_H

struct set;
struct fsm_alloc;
struct state_set;

struct state_set {
	const struct fsm_alloc *alloc;
	fsm_state_t *a;
	size_t i;
	size_t n;
};

struct state_iter {
	size_t i;
	const struct state_set *set;
};

struct state_set *
state_set_create(const struct fsm_alloc *a);

void
state_set_free(struct state_set *set);

int
state_set_add(struct state_set *set, fsm_state_t state);

int
state_set_add_bulk(struct state_set *set, fsm_state_t *a, size_t n);

void
state_set_remove(struct state_set *set, fsm_state_t state);

int
state_set_empty(const struct state_set *s);

fsm_state_t
state_set_only(const struct state_set *s);

int
state_set_contains(const struct state_set *set, fsm_state_t state);

size_t
state_set_count(const struct state_set *set);

void
state_set_reset(struct state_set *set, struct state_iter *it);

/*
int
state_set_next(struct state_iter *it, fsm_state_t *state);

int
state_set_hasnext(struct state_iter *it);
*/

int
state_set_cmp(const struct state_set *a, const struct state_set *b);

const fsm_state_t *
state_set_array(const struct state_set *set);

void
state_set_rebase(struct state_set *set, fsm_state_t base);

void
state_set_replace(struct state_set *set, fsm_state_t old, fsm_state_t new);

unsigned long
state_set_hash(const struct state_set *set);

static __inline__ int
state_set_next(struct state_iter *it, fsm_state_t *state)
{
	assert(it != NULL);
	assert(state != NULL);

	if (it->set == NULL) {
		return 0;
	}

	if (it->i >= it->set->i) {
		return 0;
	}

	*state = it->set->a[it->i];

	it->i++;

	return 1;
}

static __inline__ int
state_set_hasnext(struct state_iter *it)
{
	assert(it != NULL);

	return it->set && it->i + 1 < it->set->i;
}

#endif

