/*
 * Copyright 2019 Shannon F. Stewman
 *
 * See LICENCE for the full copyright terms.
 */

#include <stddef.h>
#include <stdlib.h>
#include <assert.h>

#include <adt/set.h>
#include <adt/stateset.h>

struct state_set {
	struct set *set;
};

static int
cmp_states(const void *a, const void *b)
{
	return (a > b) - (a < b);
}

static int
cmp_states_bulk(const void *a, const void *b)
{
	const void *pa = ((void **)a)[0], *pb = ((void **)b)[0];
	return (pa > pb) - (pa < pb);
}

struct state_set *
state_set_create(void)
{
	struct state_set *set;

	set = malloc(sizeof *set);
	if (set == NULL) {
		return NULL;
	}

	set->set = NULL;

	return set;
}

struct state_set *
state_set_create_from_array(struct fsm_state **states, size_t n)
{
	struct state_set *set;

	set = state_set_create();

	set->set = set_create_from_array((void **)states, n, cmp_states, cmp_states_bulk);

	if (set->set == NULL) {
		state_set_free(set);
		return NULL;
	}

	return set;
}

struct state_set *
state_set_create_singleton(struct fsm_state *state)
{
	struct state_set *set = state_set_create();
	set->set = set_create_singleton(cmp_states, state);
	if (set->set == NULL) {
		state_set_free(set);
		return NULL;
	}

	return set;
}

void
state_set_free(struct state_set *set)
{
	if (set == NULL) {
		return;
	}

	set_free(set->set);
	free(set);
}

struct fsm_state *
state_set_add(struct state_set *set, struct fsm_state *st)
{
	return set_add(&set->set, st);
}

void
state_set_remove(struct state_set *set, const struct fsm_state *st)
{
	set_remove(&set->set, (void *)st);
}

int
state_set_empty(const struct state_set *s)
{
	return set_empty(s->set);
}

struct fsm_state *
state_set_only(const struct state_set *s)
{
	return set_only(s->set);
}

struct fsm_state *
state_set_contains(const struct state_set *set, const struct fsm_state *st)
{
	return set_contains(set->set, st);
}

size_t
state_set_count(const struct state_set *set)
{
	return set_count(set->set);
}

struct fsm_state *
state_set_first(struct state_set *set, struct state_iter *it)
{
	return set_first(set->set, &it->iter);
}

struct fsm_state *
state_set_next(struct state_iter *it)
{
	return set_next(&it->iter);
}

struct state_set *
state_set_copy(const struct state_set *src)
{
	struct state_set *dst;

	assert(src != NULL);

	dst = state_set_create();
	if (dst == NULL) {
		return NULL;
	}

	if (state_set_copy_into(dst,src) == NULL) {
		state_set_free(dst);
		return NULL;
	}

	return dst;
}

struct state_set *
state_set_copy_into(struct state_set *dst, const struct state_set *src)
{
	assert(src != NULL);
	if (src->set == NULL) {
		return dst;
	}

	dst->set = set_copy(src->set);
	if (dst->set == NULL) {
		return NULL;
	}

	return dst;
}

int
state_set_hasnext(struct state_iter *it)
{
	return set_hasnext(&it->iter);
}

const struct fsm_state **
state_set_array(const struct state_set *set)
{
	return (const struct fsm_state **)set_array(set->set);
}

int
state_set_cmp(const struct state_set *a, const struct state_set *b)
{
	return set_cmp(a->set, b->set);
}


