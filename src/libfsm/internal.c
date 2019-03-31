#include "internal.h"

#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

void
state_array_clear(struct state_array *arr)
{
	arr->len = 0;
}

struct state_array *
state_array_add(struct state_array *arr, struct fsm_state *st)
{
	if (arr->len >= arr->cap) {
		struct fsm_state **new;
		size_t new_cap;

		if (arr->cap < 16) {
			new_cap = 16;
		} else if (arr->cap < 2048) {
			new_cap = arr->cap * 2;
		} else {
			new_cap = arr->cap + arr->cap/4;
		}

		new = realloc(arr->states, new_cap * sizeof arr->states[0]);
		if (new == NULL) {
			return NULL;
		}

		arr->states = new;
		arr->cap = new_cap;
	}

	assert(arr->len < arr->cap);
	assert(arr->states != NULL);

	arr->states[arr->len] = st;
	arr->len++;
	return arr;
}

struct state_array *
state_array_copy(struct state_array *dst, const struct state_array *src)
{
	if (src->len == 0) {
		dst->states = NULL;
		dst->len = dst->cap = 0;
		return dst;
	}

	dst->states = malloc(src->len * sizeof src->states[0]);
	if (dst->states == NULL) {
		return NULL;
	}

	dst->len = dst->cap = src->len;
	memcpy(dst->states, src->states, src->len * sizeof src->states[0]);

	return dst;
}

static int
cmp_voidp_as_ulong(const void *a, const void *b)
{
	unsigned long va,vb;

	assert(a != NULL);
	assert(b != NULL);

	va = (unsigned long)a;
	vb = (unsigned long)b;

	return (va > vb) - (va < vb);
}

uint32_t jenkins_u32_hash(uint32_t a)
{
	a = (a+0x7ed55d16) + (a<<12);
	a = (a^0xc761c23c) ^ (a>>19);
	a = (a+0x165667b1) + (a<<5);
	a = (a+0xd3a2646c) ^ (a<<9);
	a = (a+0xfd7046c5) + (a<<3);
	a = (a^0xb55a4f09) ^ (a>>16);
	return a;
}


static unsigned long
hash_voidp_as_ulong(const void *a)
{
	const unsigned long va = (unsigned long)a;
	assert(a != NULL);

	return jenkins_u32_hash(va-1);
}

int
uintset_initialize(struct uintset *s, size_t nbuckets)
{
	return hashset_initialize(&s->set, nbuckets, DEFAULT_LOAD, hash_voidp_as_ulong, cmp_voidp_as_ulong);
}

void
uintset_finalize(struct uintset *s)
{
	hashset_finalize(&s->set);
}

void *
uintset_add(struct uintset *s, unsigned int i)
{
	unsigned long l = i + 1;
	return hashset_add(&s->set, (void *)l);
}

size_t
uintset_count(const struct uintset *s)
{
	return hashset_count(&s->set);
}

void
uintset_clear(struct uintset *s)
{
	hashset_clear(&s->set);
}

int
uintset_contains(const struct uintset *s, unsigned int i)
{
	unsigned long l = i + 1;
	return hashset_contains(&s->set, (void *)l) != NULL;
}

void
edge_bmap_set(struct edge_bmap *bmap, unsigned char sym)
{
	int ind = sym/EDGE_BMAP_BITSPERBUCKET, shift = sym%EDGE_BMAP_BITSPERBUCKET;
	assert(ind >= 0 && ind < EDGE_BMAP_NBUCKETS);
	assert(shift >= 0 && shift < EDGE_BMAP_BITSPERBUCKET );

	bmap->bits[ind] |= (1 << shift);
}

void
edge_bmap_or_eq(struct edge_bmap *a, const struct edge_bmap *b)
{
	int i;
	for (i=0; i < EDGE_BMAP_NBUCKETS; i++) {
		a->bits[i] |= b->bits[i];
	}
}

int
edge_bmap_test(const struct edge_bmap *bmap, unsigned char sym)
{
	int ind = sym/EDGE_BMAP_BITSPERBUCKET, shift = sym%EDGE_BMAP_BITSPERBUCKET;
	assert(ind >= 0 && ind < EDGE_BMAP_NBUCKETS);
	assert(shift >= 0 && shift < EDGE_BMAP_BITSPERBUCKET );

	return bmap->bits[ind] & (1<<shift);
}

void
edge_bmap_zero(struct edge_bmap *bmap)
{
	assert(bmap != NULL);

	memset(bmap->bits,0,sizeof bmap->bits);
}

int
edge_bmap_next(const struct edge_bmap *bmap, struct edge_bmap_iter *it)
{
	int bit = it->bit+1;

	assert(bmap != NULL);
	assert(it   != NULL);

	while (bit < EDGE_BMAP_NBITS) {
		int bkt,ind;

		bkt = bit/EDGE_BMAP_BITSPERBUCKET;
		ind = bit%EDGE_BMAP_BITSPERBUCKET;

		if (bmap->bits[bkt] == 0) {
			bit = EDGE_BMAP_BITSPERBUCKET*(bkt+1);
			continue;
		}

		if (bmap->bits[bkt] & (1<<ind)) {
			break;
		}

		bit++;
	}

	it->bit = bit;
	return (bit < EDGE_BMAP_NBITS) ? bit : -1;
}

int
edge_bmap_first(const struct edge_bmap *bmap, struct edge_bmap_iter *it)
{
	assert(bmap != NULL);
	assert(it   != NULL);

	it->bit = -1;
	return edge_bmap_next(bmap,it);
}

