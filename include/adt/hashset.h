#ifndef HASHSET_H
#define HASHSET_H

#define DEFAULT_LOAD 0.66
#define DEFAULT_NBUCKETS 4

struct bucket;

enum {
	SORTEDSET_FROZEN = 0x0001
};

struct hashset {
	size_t nbuckets;
	size_t nitems;
	struct bucket *buckets;
	size_t maxload;
	int (*cmp)(const void *,const void *);
	unsigned long (*hash)(const void *);
	float load;
	uint32_t flags;
};

struct hashset_iter {
	size_t i;
	const struct hashset *set;
};

struct hashset *
hashset_create(unsigned long (*hash)(const void *a),int (*cmp)(const void *a, const void *b));

int
hashset_initialize(struct hashset *s, size_t nb, float load,
	unsigned long (*hash)(const void *a),int (*cmp)(const void *a, const void *b));

void
hashset_finalize(struct hashset *s);

void *
hashset_add(struct hashset *s, void *item);

int
hashset_remove(struct hashset *s, void *item);

void
hashset_free(struct hashset *s);

size_t
hashset_count(const struct hashset *s);

void
hashset_clear(struct hashset *s);

/*
 * Find if an item is in a set, and return it.
 */
void *
hashset_contains(const struct hashset *s, const void *item);

/*
 * Compare two sets for equality.
 */
int
hashset_equal(const struct hashset *a, const struct hashset *b);

int
hashset_empty(const struct hashset *s);

void *
hashset_first(const struct hashset *s, struct hashset_iter *it);

void *
hashset_next(struct hashset_iter *it);

/*
 * Return the sole item for a singleton set.
 */
void *
hashset_only(const struct hashset *set);

int
hashset_hasnext(struct hashset_iter *it);

/* Common hash functions */

/* hashes pointer value */
unsigned long
hashptr(const void *p);

/* hashes record pointed to by `p` with length n.
 * this includes padding bytes, so treat with care. */
unsigned long
hashrec(const void *p, size_t n);


/* sorted hashset extension
 *
 * provides a hashset that you can freeze.  after freezing, provides
 * sorted iteration.
 */

struct sortedset {
	struct hashset hs;
	void **sorted;
	size_t len;
	size_t max;
};

struct sortedset_iter {
	size_t i;
	const struct sortedset *set;
};

struct sortedset *
sortedset_create(unsigned long (*hash)(const void *a),int (*cmp)(const void *a, const void *b));

void *
sortedset_add(struct sortedset *s, void *item);

int
sortedset_remove(struct sortedset *s, void *item);

void
sortedset_free(struct sortedset *s);

size_t
sortedset_count(const struct sortedset *s);

void
sortedset_clear(struct sortedset *s);

/*
 * Find if an item is in a set, and return it.
 */
void *
sortedset_contains(const struct sortedset *s, const void *item);

/*
 * Compare two sets for equality.
 */
int
sortedset_equal(const struct sortedset *a, const struct sortedset *b);

int
sortedset_empty(const struct sortedset *s);

void *
sortedset_first(const struct sortedset *s, struct sortedset_iter *it);

void *
sortedset_next(struct sortedset_iter *it);

/*
 * Return the sole item for a singleton set.
 */
void *
sortedset_only(const struct sortedset *set);

int
sortedset_hasnext(struct sortedset_iter *it);

#define sortedset_ordered(s) (!!(s->hs.flags & SORTEDSET_FROZEN))

int
sortedset_full_cmp(const struct sortedset *a, const struct sortedset *b);

/* "freezes" the set, ordering all elements */
int
sortedset_freeze(struct sortedset *set);

#endif /* HASHSET_H */

