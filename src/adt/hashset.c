/*
 * Copyright 2018- Shannon Stewman
 *
 * See LICENCE for the full copyright terms.
 */

#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#include <adt/hashset.h>

/* XXX: explore whether we should split the bucket or not */

struct bucket {
	unsigned long hash;
	void *item;
};

#define TOMBSTONE_HASH (~(0UL))
#define UNSET_HASH     (0UL)

static int
is_pow2(size_t n) {
	return (n & (n-1)) == 0;
}

static int
finditem(const struct hashset *s, unsigned long hash, const void *item, size_t *bp)
{
	size_t b,c,nb;

	if (s->nbuckets == 0) {
		return 0;
	}

	b = is_pow2(s->nbuckets) ? (hash & (s->nbuckets-1)) : (hash % s->nbuckets);
	nb = s->nbuckets;
	for (c=0; c < nb; c++) {
		if (s->buckets[b].hash == hash) {
			if (item == s->buckets[b].item || s->cmp(item, s->buckets[b].item) == 0) {
				*bp = b;
				return 1;
			}
		} else if (s->buckets[b].item == NULL && s->buckets[b].hash == UNSET_HASH) {
			*bp = b;
			return 0;
		}

		if (++b == nb) {
			b = 0;
		}
	}

	*bp = nb;
	return 0;
}

int
hashset_initialize(struct hashset *s, size_t nb, float load,
	unsigned long (*hash)(const void *a),int (*cmp)(const void *a, const void *b))
{
	static const struct hashset init;
	*s = init;
	s->hash = hash;
	s->cmp = cmp;
	s->load = load;
	if (nb == 0) {
		return 1;
	}

	s->buckets = calloc(nb, sizeof s->buckets[0]);
	s->maxload = load * nb;
	return (s->buckets != NULL);
}

struct hashset *
hashset_create(unsigned long (*hash)(const void *a),int (*cmp)(const void *a, const void *b))
{
	struct hashset *s = malloc(sizeof *s);
	hashset_initialize(s, 0,DEFAULT_LOAD, hash,cmp);
	return s;
}

static int
rehash(struct hashset *s)
{
	const static struct hashset hs_init;

	size_t i,nb,newsz;
	struct hashset ns;
	struct bucket *b;

	ns = hs_init;

	/* check resizing logic */
	newsz = (s->nbuckets > 0) ? 2*s->nbuckets : DEFAULT_NBUCKETS;
	ns.buckets = calloc(newsz, sizeof ns.buckets[0]);
	if (ns.buckets == NULL) {
		return 0;
	}

	ns.nbuckets = newsz;
	ns.maxload = s->load * newsz;
	ns.hash = s->hash;
	ns.cmp  = s->cmp;

	nb = s->nbuckets;
	b = s->buckets;
	for (i=0; i < nb; i++) {
		size_t bi = 0;

		if (b[i].item == NULL) {
			continue;
		}

		/* XXX: replace finditem with something that doesn't
		 * call cmp() since all items should be unique */
		finditem(&ns, b[i].hash, b[i].item, &bi);
		ns.buckets[bi] = b[i];
	}

	free(s->buckets);
	s->nbuckets = ns.nbuckets;
	s->buckets  = ns.buckets;
	s->maxload  = ns.maxload;
	return 1;
}

void *
hashset_add(struct hashset *s, void *item)
{
	size_t b=0;
	unsigned long hash = s->hash(item);

	if (s->buckets == NULL) {
		if (!rehash(s)) {
			return NULL;
		}
	}

	if (finditem(s,hash,item,&b)) {
		/* found, return item */
		return s->buckets[b].item;
	}

	/* not found, so add it */

	/* check if we need a rehash */
	if (s->nitems >= s->maxload) {
		if (!rehash(s)) {
			return NULL;
		}

		/* re-find the first available bucket */
		finditem(s,hash,item,&b);
	}

	s->buckets[b].hash = hash;
	s->buckets[b].item = item;

	s->nitems++;

	return item;
}

int
hashset_remove(struct hashset *s, void *item)
{
	size_t b;
	unsigned long h = s->hash(item);
	b = 0;
	if (s->nitems == 0 || !finditem(s,h,item,&b)) {
		return 0;
	}

	s->buckets[b].item = NULL;
	s->buckets[b].hash = TOMBSTONE_HASH;
	s->nitems--;

	return 1;
}

void
hashset_finalize(struct hashset *s)
{
	free(s->buckets);
}

void
hashset_free(struct hashset *s)
{
	hashset_finalize(s);
	free(s);
}

size_t
hashset_count(const struct hashset *s)
{
	return s->nitems;
}

void
hashset_clear(struct hashset *s)
{
	s->nitems = 0;
	if (s->buckets != NULL) {
		memset(s->buckets, 0, s->nbuckets * sizeof s->buckets[0]);
	}
}

/*
 * Find if an item is in a set, and return it.
 */
void *
hashset_contains(const struct hashset *s, const void *item)
{
	unsigned long h = s->hash(item);
	size_t b = 0;
	if (finditem(s,h,item,&b)) {
		return s->buckets[b].item;
	}

	return NULL;
}

/*
 * Compare two sets for equality.
 */
int
hashset_equal(const struct hashset *a, const struct hashset *b)
{
	size_t i,n;
	struct bucket *ab;

	if (a->nitems != b->nitems) {
		return 0;
	}

	n = a->nbuckets;
	ab = a->buckets;
	for (i=0; i < n; i++) {
		if (ab[i].item != NULL && !hashset_contains(b,ab[i].item)) {
			return 0;
		}
	}

	return 1;
}

int
hashset_empty(const struct hashset *s)
{
	return s->nitems == 0;
}

static void *
hs_next(const struct hashset *s, size_t *ip)
{
	size_t i = *ip, nb = s->nbuckets;
	for (; i < nb; i++) {
		if (s->buckets[i].item != NULL) {
			*ip = i+1;
			return s->buckets[i].item;
		}
	}

	*ip = nb;
	return NULL;
}

void *
hashset_first(const struct hashset *s, struct hashset_iter *it)
{
	it->set = s;
	it->i = 0;
	return hs_next(s, &it->i);
}

void *
hashset_next(struct hashset_iter *it)
{
	return hs_next(it->set, &it->i);
}

/*
 * Return the sole item for a singleton set.
 */
void *
hashset_only(const struct hashset *s)
{
	size_t i,n;
	struct bucket *b;

	if (s->nitems == 0) {
		return NULL;
	}

	n = s->nbuckets;
	b=s->buckets;
	for (i=0; i < n; i++) {
		if (b[i].item != NULL) {
			return b[i].item;
		}
	}

	/* should not reach */
	abort();
}

static int
hs_hasnext(const struct hashset *s, size_t *ip)
{
	size_t i = *ip, nb = s->nbuckets;
	for (; i < nb; i++) {
		if (s->buckets[i].item != NULL) {
			*ip = i;
			return 1;
		}
	}

	*ip = nb;
	return 0;
}

int
hashset_hasnext(struct hashset_iter *it)
{
	return hs_hasnext(it->set, &it->i);
}

extern int
siphash(const uint8_t *in, const size_t inlen, const uint8_t *k,
            uint8_t *out, const size_t outlen);

/* random key read from /dev/random */
/* XXX: replace with a seed read from /dev/random at startup... */
static const unsigned char hashk[] = {
	0x14, 0xa8, 0xff, 0x36, 0x15, 0x16, 0x2c, 0xf7, 0xf4, 0xce, 0xb8, 0x66, 0x74, 0xf4, 0x3d, 0x64,
};

unsigned long
hashptr(const void *p) {
	unsigned char v[sizeof p];
	unsigned long h;
	unsigned char ha[sizeof h];

	memcpy(&v[0], &p, sizeof p);

	siphash(v, sizeof v, hashk, &ha[0], sizeof ha);
	memcpy(&h, &ha[0], sizeof h);

	return h;
}

unsigned long
hashrec(const void *p, size_t n) {
	const unsigned char *s = p;
	unsigned long h = 0;
	unsigned char ha[sizeof h];

	siphash(s, n, hashk, &ha[0], sizeof ha);
	memcpy(&h, &ha[0], sizeof h);

	return h;
}

struct sortedset *
sortedset_create(unsigned long (*hash)(const void *a),int (*cmp)(const void *a, const void *b))
{
	static const struct sortedset init;
	struct sortedset *s;
	s = malloc(sizeof *s);
	*s = init;

	hashset_initialize(&s->hs, 0,DEFAULT_LOAD, hash,cmp);

	return s;
}

static void
sortedset_markdirty(struct sortedset *s)
{
	if (s->hs.flags & SORTEDSET_FROZEN) {
		s->hs.flags ^= SORTEDSET_FROZEN;
	}
}

void *
sortedset_add(struct sortedset *s, void *item)
{
	void *ret = hashset_add(&s->hs, item);
	sortedset_markdirty(s);
	return ret;
}

int
sortedset_remove(struct sortedset *s, void *item)
{
	int ret = hashset_remove(&s->hs,item);
	if (ret) {
		sortedset_markdirty(s);
	}
	return ret;
}

void
sortedset_free(struct sortedset *s)
{
	hashset_finalize(&s->hs);
	free(s->sorted);
	free(s);
}

size_t
sortedset_count(const struct sortedset *s)
{
	return hashset_count(&s->hs);
}

void
sortedset_clear(struct sortedset *s)
{
	hashset_clear(&s->hs);
	s->len = 0;
}

/*
 * Find if an item is in a set, and return it.
 */
void *
sortedset_contains(const struct sortedset *s, const void *item)
{
	return hashset_contains(&s->hs, item);
}

/*
 * Compare two sets for equality.
 */
int
sortedset_equal(const struct sortedset *a, const struct sortedset *b)
{
	if (sortedset_ordered(a) && sortedset_ordered(b)) {
		return sortedset_full_cmp(a,b);
	}

	return hashset_equal(&a->hs, &b->hs);
}

int
sortedset_full_cmp(const struct sortedset *a, const struct sortedset *b)
{
	size_t i,n;
	int (*cmp)(const void *, const void *);

	n = a->len;
	if (n != b->len) {
		return (b->len > n) - (n > b->len);
	}

	cmp = a->hs.cmp;
	if (cmp != b->hs.cmp) {
		abort();
	}

	for (i=0; i < n; i++) {
		int c = cmp(a->sorted[i], b->sorted[i]);
		if (c != 0) {
			return c;
		}
	}

	return 0;
}

int
sortedset_empty(const struct sortedset *s)
{
	return hashset_empty(&s->hs);
}

void *
sortedset_first(const struct sortedset *s, struct sortedset_iter *it)
{
	it->set = s;
	it->i=0;

	if (sortedset_ordered(s)) {
		return s->len > 0 ? s->sorted[it->i++] : NULL;
	}

	return hs_next(&s->hs, &it->i);
}

void *
sortedset_next(struct sortedset_iter *it)
{
	const struct sortedset *s = it->set;
	if (sortedset_ordered(s)) {
		return it->i < s->len ? s->sorted[it->i++] : NULL;
	}

	return hs_next(&s->hs, &it->i);
}

/*
 * Return the sole item for a singleton set.
 */
void *
sortedset_only(const struct sortedset *s)
{
	if (sortedset_ordered(s)) {
		return (s->len > 0) ? s->sorted[0] : NULL;
	}

	return hashset_only(&s->hs);
}

int
sortedset_hasnext(struct sortedset_iter *it)
{
	const struct sortedset *s = it->set;
	if (sortedset_ordered(s)) {
		return it->i < s->len;
	}

	return hs_hasnext(&s->hs, &it->i);
}

static void
insertion_sort_elements(void **base, size_t nelts, int (*cmp)(const void *,const void *))
{
	size_t i;

	for (i=1; i < nelts; i++) {
		void *x = base[i];
		size_t j = i;

		while (j > 0 && cmp(x,base[j-1]) < 0) {
			base[j] = base[j-1];
			j--;
		}

		base[j] = x;
	}
}

#define TOO_SMALL_FOR_QUICK_SORT 8

#define SWAP(i,j) do { size_t i_ = (i); size_t j_ = (j);\
	void *tmp = base[i_]; base[i_] = base[j_]; base[j_] = tmp; \
} while(0)
#define CMP(i,j) (cmp(base[(i)],base[(j)]))

static void
quick_sort_elements(void** base, size_t nelts, int (*cmp)(const void *,const void *))
{
	size_t i, pivot, end;

	if (nelts <= TOO_SMALL_FOR_QUICK_SORT) {
		insertion_sort_elements(base,nelts,cmp);
		return;
	}

	/* choose pivot
	 *
	 * XXX - should change to something more robust like
	 * median-of-medians
	 */
	pivot = nelts/2;
	end = nelts-1;

	SWAP(pivot,end);

	pivot = 0;
	for (i=0; i < end; i++) {
		if ( CMP(i,end) <= 0 ) {
			SWAP(i,pivot);
			pivot++;
		}
	}

	SWAP(pivot,end);

	if (pivot > 0) {
		quick_sort_elements(&base[0], pivot, cmp);
	}

	if (pivot < nelts-1) {
		quick_sort_elements(&base[pivot+1], nelts-pivot-1, cmp);
	}
}

#undef SWAP
#undef CMP


int
sortedset_freeze(struct sortedset *set)
{
	size_t i,n,nb;
	void **p;

	nb = set->hs.nbuckets;
	n = set->hs.nitems;

	p = set->sorted;
	if (set->max < n) {
		p = realloc(set->sorted, n * sizeof *p);

		if (p == NULL) {
			return 0;
		}

		set->sorted = p;
		set->max = n;
	}

	set->len = 0;
	memset(&p[0], 0, set->max * sizeof p[0]);
	for (i=0; i < nb; i++) {
		void *item = set->hs.buckets[i].item;
		if (item != NULL) {
			assert(set->len < n);
			p[set->len++] = item;
		}
	}

	/* sort elements */
	/* XXX: replace this with something better */
	qsort((void *)(&p[0]), set->len, sizeof p[0], set->hs.cmp);
	quick_sort_elements(&p[0], set->len, set->hs.cmp);

	set->hs.flags |= SORTEDSET_FROZEN;
	return 1;
}

