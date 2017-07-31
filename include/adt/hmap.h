#ifndef ADT_HMAP_H
#define ADT_HMAP_H

#include <stdlib.h>

struct hmap_khb;

union hmap_value {
	void *p;
	long i;
	unsigned long u;
};

/* Simple open-addressing linear probing hash table */
struct hmap {
	size_t nbuckets;
	size_t nitems;
	size_t nthresh;

	struct hmap_khb *khb;
	union hmap_value *vb;

	void *opaque;
	unsigned long (*hash)(void *opaque, const void *key);
	int (*cmp)(void *opaque, const void *k1, const void *k2);
	float maxload;
};

struct hmap_iter {
	const struct hmap *m;
	size_t i;
	void *k;
	union hmap_value v;
};

struct hmap *
hmap_create(size_t nbuckets, float maxload, void *opaque,
	unsigned long (*hashfunc)(void *, const void *),
	int (*eqfunc)(void *opaque, const void *k1, const void *k2));

/* creates an hmap suitable for storing strings as keys */
struct hmap *
hmap_create_string(size_t nbuckets, float maxload);

/* creates an hmap suitable for storing void * pointers as keys */
struct hmap *
hmap_create_pointer(size_t nbuckets, float maxload);

void
hmap_free(struct hmap *m);

union hmap_value *
hmap_get(const struct hmap *m, const void *k);

void *
hmap_getptr(const struct hmap *m, const void *k);

long
hmap_getint(const struct hmap *m, const void *k);

unsigned long
hmap_getuint(const struct hmap *m, const void *k);

int
hmap_set(struct hmap *m, void *k, union hmap_value v);

int
hmap_setptr(struct hmap *m, void *k, void *v);

int
hmap_setint(struct hmap *m, void *k, long i);

int
hmap_setuint(struct hmap *m, void *k, unsigned long u);

int
hmap_foreach(const struct hmap *m, void *opaque, int (*callback)(const void *k, union hmap_value v, void *opaque));

void *
hmap_iter_first(const struct hmap *m, struct hmap_iter *it);

void *
hmap_iter_next(struct hmap_iter *it);

unsigned long
hash_string(void *hopaque, const void *key);

unsigned long
hash_pointer(void *hopaque, const void *key);

#endif /* ADT_HMAP_H */

