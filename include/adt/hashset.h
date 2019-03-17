#ifndef HASHSET_H
#define HASHSET_H

#define DEFAULT_LOAD 0.66
#define DEFAULT_NBUCKETS 4

struct bucket;

struct hashset {
	size_t nbuckets;
	size_t nitems;
	struct bucket *buckets;
	size_t maxload;
	int (*cmp)(const void *,const void *);
	unsigned long (*hash)(const void *);
	float load;
};

struct hashset_iter {
	size_t i;
	const struct hashset *set;
};

struct hashset *
hashset_create(unsigned long (*hash)(const void *a),int (*cmp)(const void *a, const void *b));

void *
hashset_add(struct hashset *s, void *item);

void
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

#endif /* HASHSET_H */

