/*
 * Copyright 2008-2017 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#ifndef SET_H
#define SET_H

struct set0;

struct set0_iter {
	size_t i;
	const struct set0 *set;
};

struct set0 *
set0_create(int (*cmp)(const void *a, const void *b));

void *
set0_add(struct set0 **set0, void *item);

void
set0_remove(struct set0 **set0, void *item);

void
set0_free(struct set0 *set0);

size_t
set0_count(const struct set0 *set0);

void
set0_clear(struct set0 *set);

/*
 * Find if an item is in a set, and return it.
 */
void *
set0_contains(const struct set0 *set, const void *item);

/*
 * Compare two sets like memcmp
 */
int
set0_cmp(const struct set0 *a, const struct set0 *b);

/*
 * Compare two sets for equality.
 */
int
set0_equal(const struct set0 *a, const struct set0 *b);

int
set0_empty(const struct set0 *set);

void *
set0_first(const struct set0 *set, struct set0_iter *it);

void *
set0_firstafter(const struct set0 *set, struct set0_iter *it, void *item);

void *
set0_next(struct set0_iter *it);

/*
 * Return the sole item for a singleton set.
 */
void *
set0_only(const struct set0 *set);

int
set0_hasnext(const struct set0_iter *it);

const void **
set0_array(const struct set0 *set);

#endif

