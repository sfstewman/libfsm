/*
 * Copyright 2008-2017 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#include <ctype.h>
#include <assert.h>
#include <limits.h>
#include <stdio.h>

#include <adt/set.h>
#include <adt/bitmap.h>

#include <fsm/fsm.h>
#include <fsm/pred.h>
#include <fsm/out.h>
#include <fsm/options.h>

#include "libfsm/internal.h"

#include "libfsm/out.h"

static unsigned int
indexof(const struct fsm *fsm, const struct fsm_state *state)
{
	struct fsm_state *s;
	unsigned int i;

	assert(fsm != NULL);
	assert(state != NULL);

	for (s = fsm->sl, i = 0; s != NULL; s = s->next, i++) {
		if (s == state) {
			return i;
		}
	}

	assert(!"unreached");
	return 0;
}

static int
escputc(const struct fsm_options *opt, int c, FILE *f)
{
	size_t i;

	const struct {
		int c;
		const char *s;
	} a[] = {
		{ '\\', "\\\\" },
		{ '\"', "\\\"" },

		{ '\f', "\\f"  },
		{ '\n', "\\n"  },
		{ '\r', "\\r"  },
		{ '\t', "\\t"  },
		{ '\v', "\\v"  }
	};

	assert(opt != NULL);
	assert(c != FSM_EDGE_EPSILON);
	assert(f != NULL);

	if (opt->always_hex) {
		return fprintf(f, "\\x%02x", (unsigned char) c);
	}

	for (i = 0; i < sizeof a / sizeof *a; i++) {
		if (a[i].c == c) {
			return fputs(a[i].s, f);
		}
	}

	if (!isprint((unsigned char) c)) {
		return fprintf(f, "\\x%02x", (unsigned char) c);
	}

	return fprintf(f, "%c", c);
}

/* TODO: centralise, maybe with callback */
static int
escputs(const struct fsm_options *opt, FILE *f, const char *s)
{
	const char *p;
	int r, n;

	assert(opt != NULL);
	assert(f != NULL);
	assert(s != NULL);

	n = 0;

	for (p = s; *p != '\0'; p++) {
		r = escputc(opt, *p, f);
		if (r == -1) {
			return -1;
		}

		n += r;
	}

	return n;
}

/* TODO: centralise */
static const struct fsm_state *
findany(const struct fsm_state *state)
{
	struct fsm_state *f, *s;
	struct fsm_edge *e;
	struct edge_iter it;
	struct state_iter jt;
	struct bm bm;

	assert(state != NULL);

	bm_clear(&bm);

	e = edge_set_first(state->edges, &it);
	if (e == NULL) {
		return NULL;
	}

	/* if the first edge is not the first character,
	 * then we can't possibly have an "any" transition */
	if (e->symbol != '\0') {
		return NULL;
	}

	f = state_set_first(e->sl, &jt);
	if (f == NULL) {
		return NULL;
	}

	for (e = edge_set_first(state->edges, &it); e != NULL; e = edge_set_next(&it)) {
		if (e->symbol > UCHAR_MAX) {
			return NULL;
		}

		if (state_set_count(e->sl) != 1) {
			return NULL;
		}

		s = state_set_only(e->sl);
		if (f != s) {
			return NULL;
		}

		bm_set(&bm, e->symbol);
	}

	if (bm_count(&bm) != UCHAR_MAX + 1U) {
		return NULL;
	}

	assert(f != NULL);

	return f;
}

void
fsm_out_fsm(const struct fsm *fsm, FILE *f)
{
	struct fsm_state *s, *start;
	int end;

	assert(fsm != NULL);
	assert(f != NULL);

	for (s = fsm->sl; s != NULL; s = s->next) {
		struct fsm_edge *e;
		struct edge_iter it;

		{
			const struct fsm_state *a;

			a = findany(s);
			if (a != NULL) {
				fprintf(f, "%-2u -> %2u ?;\n", indexof(fsm, s), indexof(fsm, a));
				continue;
			}
		}

		for (e = edge_set_first(s->edges, &it); e != NULL; e = edge_set_next(&it)) {
			struct fsm_state *st;
			struct state_iter jt;

			for (st = state_set_first(e->sl, &jt); st != NULL; st = state_set_next(&jt)) {
				assert(st != NULL);

				fprintf(f, "%-2u -> %2u", indexof(fsm, s), indexof(fsm, st));

				/* TODO: print " ?" if all edges are equal */

				switch (e->symbol) {
				case FSM_EDGE_EPSILON:
					break;

				default:
					fputs(" \"", f);
					escputc(fsm->opt, e->symbol, f);
					putc('\"', f);
					break;
				}

				fprintf(f, ";");

				if (fsm->opt->comments) {
					if (st == fsm->start) {
						fprintf(f, " # start");
					} else if (fsm->start != NULL) {
						char buf[50];
						int n;

						n = fsm_example(fsm, st, buf, sizeof buf);
						if (-1 == n) {
							perror("fsm_example");
							return;
						}

						fprintf(f, " # e.g. \"");
						escputs(fsm->opt, f, buf);
						fprintf(f, "%s\"",
							n >= (int) sizeof buf - 1 ? "..." : "");
					}
				}

				fprintf(f, "\n");
			}
		}
	}

	fprintf(f, "\n");

	start = fsm_getstart(fsm);
	if (start == NULL) {
		return;
	}

	fprintf(f, "start: %u;\n", indexof(fsm, start));

	end = 0;
	for (s = fsm->sl; s != NULL; s = s->next) {
		end += !!fsm_isend(fsm, s);
	}

	if (end == 0) {
		return;
	}

	fprintf(f, "end:   ");
	for (s = fsm->sl; s != NULL; s = s->next) {
		if (fsm_isend(fsm, s)) {
			end--;

			fprintf(f, "%u%s", indexof(fsm, s), end > 0 ? ", " : ";\n");
		}
	}
}

