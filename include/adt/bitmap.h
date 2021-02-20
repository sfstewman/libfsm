/*
 * Copyright 2008-2017 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#ifndef ADT_BITMAP_H
#define ADT_BITMAP_H

struct fsm_state;
struct fsm_options;

struct bm {
	unsigned char map[UCHAR_MAX / CHAR_BIT + 1];
};

int
bm_get(const struct bm *bm, size_t i);

void
bm_set(struct bm *bm, size_t i);

void
bm_setrange(struct bm *bm, size_t imin, size_t imax);

void
bm_clearbit(struct bm *bm, size_t i);

void
bm_clearrange(struct bm *bm, size_t imin, size_t imax);

size_t
bm_next(const struct bm *bm, int i, int value);

unsigned int
bm_count(const struct bm *bm);

void
bm_setall(struct bm *bm);

void
bm_clear(struct bm *bm);

void
bm_invert(struct bm *bm);

int
bm_isallset(const struct bm *bm);

int
bm_isanyset(const struct bm *bm);

/* bm = bm | bm0 */
void
bm_or(struct bm *bm, const struct bm *bm0);

/* bm = bm & bm0, returns if bm has any bits set after the & */
int
bm_and(struct bm *bm, const struct bm *bm0);

int
bm_print(FILE *f, const struct fsm_options *opt, const struct bm *bm,
	int boxed,
	escputc *escputc);

int
bm_snprint(const struct bm *bm, const struct fsm_options *opt,
	char *s, size_t sz,
	int boxed,
	escputc *escputc);

#endif

