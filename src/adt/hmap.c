#include <adt/hmap.h>

#include <assert.h>
#include <stdlib.h>
#include <string.h>

/* I'd prefer using something like Murmur3 or SipHash, but the reference
 * implementations tend to require C99's optional uintN_t types.
 *
 * XXX - Replace with something better
 *
 * Adapted from http://www.cse.yorku.ca/~oz/hash.html
 */
static unsigned long
sdbm(const unsigned char *str, size_t n)
{
	unsigned long hash = 0;
	size_t i;
	int c;

	for (i=0; i < n; i++) {
		c = *str++;
		hash = c + (hash << 6) + (hash << 16) - hash;
	}

	return hash;
}

unsigned long
djb2(const char *str)
{
	unsigned long hash = 5381;
	int c;

	while (c = (unsigned char)(*str++), c != 0) {
		hash = ((hash << 5) + hash) + c; /* hash * 33 + c */
	}

	return hash;
}

struct hmap_khb {
	unsigned long hash;
	void *key;
};

static int
hmap_set_inner(struct hmap *m, unsigned long h, void *k, union hmap_value v)
{
	size_t i,n, b;
	void *opaque;
	int (*cmp)(void *, const void *, const void *);

	assert(m != NULL);

	n      = m->nbuckets;
	opaque = m->opaque;
	cmp    = m->cmp;

	b = h % n;
	for (i=0; i < n; i++) {
		if (m->khb[b].hash == 0 && m->khb[b].key == NULL) {
			goto set_item;
		}

		if (m->khb[b].hash == h && cmp(opaque, m->khb[b].key, k) == 0) {
			goto set_item;
		}

		if (++b >= n) {
			b = 0;
		}

	}

	assert(!"unreachable");
	return 0;

set_item:
	m->khb[b].hash = h;
	m->khb[b].key = k;
	m->vb[b] = v;
	m->nitems++;

	return 1;
}

static int
hmap_rehash(struct hmap *m)
{
	size_t i, n, ni, nbuckets, old_nbuckets;
	struct hmap_khb *khb;
	union hmap_value *vb, *old_vb;
	struct hmap_khb *old_khb;

	khb = NULL;
	vb  = NULL;

	nbuckets = (m->khb == NULL) ? m->nbuckets : 2*m->nbuckets;
	khb = malloc(nbuckets * sizeof khb[0]);
	if (khb == NULL) {
		goto error;
	}

	vb = malloc(nbuckets * sizeof vb[0]);
	if (vb == NULL) {
		goto error;
	}

	for (i=0; i < nbuckets; i++) {
		khb[i].hash = 0;
		khb[i].key  = NULL;
		vb[i].p = NULL;
	}

	old_khb = m->khb;
	old_vb  = m->vb;
	ni      = m->nitems;
        old_nbuckets = m->nbuckets;

	m->khb      = khb;
	m->vb       = vb;
	m->nbuckets = nbuckets;
	m->nitems   = 0;
	m->nthresh  = nbuckets * m->maxload;

	assert(m->nthresh > ni);

	if (!old_khb) {
		goto finish;
	}

	for (n=old_nbuckets, i=0; i < n; i++) {
		if (old_khb[i].key == NULL) {
			continue;
		}

		hmap_set_inner(m, old_khb[i].hash, old_khb[i].key, old_vb[i]);
	}

	assert(m->nitems == ni);

finish:
	free(old_khb);
	free(old_vb);

	return 1;

error:
	free(khb);
	free(vb);
	return 0;
}

int
hmap_set(struct hmap *m, void *k, union hmap_value v)
{
	unsigned long h;

	assert(m != NULL);

	if (m->nitems >= m->nthresh) {
		if (!hmap_rehash(m)) {
			return 0;
		}
	}

	h = m->hash(m->opaque, k);
	return hmap_set_inner(m, h, k, v);
}

int
hmap_setptr(struct hmap *m, void *k, void *v)
{
	union hmap_value vt;
	vt.p = v;
	return hmap_set(m, k, vt);
}

hmap_setint(struct hmap *m, void *k, long i)
{
	union hmap_value vt;
	vt.i = i;
	return hmap_set(m, k, vt);
}

int
hmap_setuint(struct hmap *m, void *k, unsigned long u)
{
	union hmap_value vt;
	vt.u = u;
	return hmap_set(m, k, vt);
}

struct hmap *
hmap_create(size_t nbuckets, float maxload, void *opaque,
	unsigned long (*hash)(void *, const void *),
	int (*cmp)(void *opaque, const void *k1, const void *k2))
{
	struct hmap *m;
	size_t i;

	m = malloc(sizeof *m);
	if (m == NULL) {
		goto error;
		return NULL;
	}

	m->khb = NULL;
	m->vb  = NULL;

	m->khb = malloc(nbuckets * sizeof m->khb[0]);
	if (m->khb == NULL) {
		goto error;
	}

	m->vb = malloc(nbuckets * sizeof m->vb[0]);
	if (m->vb == NULL) {
		goto error;
	}

	for (i=0; i < nbuckets; i++) {
		m->khb[i].hash = 0;
		m->khb[i].key  = NULL;

		m->vb[i].p = NULL;
	}

	m->nitems   = 0;
	m->nbuckets = nbuckets;
	m->nthresh  = nbuckets * maxload;
	m->maxload  = maxload;

	m->opaque = opaque;
	m->hash   = hash;
	m->cmp    = cmp;

	return m;

error:
	hmap_free(m);
	return NULL;
}

void
hmap_free(struct hmap *m)
{
	if (m == NULL) {
		return;
	}

	free(m->khb);
	free(m->vb);
	free(m);
}

union hmap_value *
hmap_get(const struct hmap *m, const void *k)
{
	unsigned long h = m->hash(m->opaque, k);
	size_t b = h % m->nbuckets;
	for (;;) {
		if (m->khb[b].hash == 0 && m->khb[b].key == NULL) {
			/* empty bucket... cannot find value */
			return NULL;
		}

		if (m->khb[b].hash == h) {
			if (m->cmp(m->opaque, m->khb[b].key, k) == 0) {
				return &m->vb[b];
			}
		}

		if (++b >= m->nbuckets) {
			b = 0;
		}
	}
}

void *
hmap_getptr(const struct hmap *m, const void *k)
{
	union hmap_value *v;

	v = hmap_get(m,k);
	return (v != NULL) ? v->p : NULL;
}

long
hmap_getint(const struct hmap *m, const void *k)
{
	union hmap_value *v;

	v = hmap_get(m,k);
	return (v != NULL) ? v->i : 0;
}

unsigned long
hmap_getuint(const struct hmap *m, const void *k)
{
	union hmap_value *v;

	v = hmap_get(m,k);
	return (v != NULL) ? v->u : 0;
}

int
hmap_foreach(const struct hmap *m, void *opaque, int (*callback)(const void *k, union hmap_value v, void *opaque))
{
	size_t i,n;

	for (n=m->nbuckets, i=0; i < n; i++) {
		if (m->khb[i].key == NULL) {
			continue;
		}
		if (!callback(m->khb[i].key, m->vb[i], opaque)) {
			return 0;
		}
	}

	return 1;
}

static void *
next_bucket(struct hmap_iter *it)
{
	size_t i,n;
	const struct hmap *m;

	m = it->m;
	n = m->nbuckets;
	for(i = it->i; i < n; i++) {
		if (m->khb[i].key == NULL) {
			continue;
		}

		it->i = i+1;
		it->k = m->khb[i].key;
		it->v = m->vb[i];

		return it->k;
	}

	it->k = NULL;
	it->v.p = NULL;
	return NULL;
}

void *
hmap_iter_first(const struct hmap *m, struct hmap_iter *it)
{
	it->m = m;
	it->i = 0;
	it->k = NULL;
	it->v.p = NULL;

	return next_bucket(it);
}

void *
hmap_iter_next(struct hmap_iter *it)
{
	return next_bucket(it);
}

unsigned long
hash_string(void *opaque, const void *key)
{
	(void)opaque;
	return djb2(key);

}

unsigned long
hash_pointer(void *opaque, const void *key)
{
	unsigned char v[sizeof key];

	(void)opaque;
	memcpy(v, &key, sizeof key);
	return sdbm(v, sizeof key);
}

static int
cmp_string(void *dummy, const void *a, const void *b)
{
	(void)dummy;
	assert(a != NULL);
	assert(b != NULL);

	return strcmp(a,b);
}

struct hmap *
hmap_create_string(size_t nbuckets, float maxload)
{
	return hmap_create(nbuckets, maxload, NULL,
		hash_string, cmp_string);
}

static int
cmp_pointer(void *dummy, const void *a, const void *b)
{
	(void)dummy;

	return a != b;
}

struct hmap *
hmap_create_pointer(size_t nbuckets, float maxload)
{
	return hmap_create(nbuckets, maxload, NULL,
		hash_pointer, cmp_pointer);
}
