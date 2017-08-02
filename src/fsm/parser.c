/*
 * Automatically generated from the files:
 *	src/fsm/parser.sid
 * and
 *	src/fsm/parser.act
 * by:
 *	sid
 */

/* BEGINNING OF HEADER */

#line 98 "src/fsm/parser.act"


	#include <assert.h>
	#include <string.h>
	#include <stdlib.h>
	#include <stdarg.h>
	#include <stdio.h>
	#include <errno.h>

	#include <fsm/fsm.h>

	#include <adt/xalloc.h>
	#include <adt/hmap.h>

	#include "libfsm/internal.h"	/* XXX */

	#include "lexer.h"
	#include "parser.h"

	typedef char *             string;
	typedef struct fsm_state * state;

        /* default number of buckets for the idmap */
        enum { NBUCKETS = 1024 };
	static int debug_hmap = 0;
	struct act_state {
		int lex_tok;
		int lex_tok_save;
                struct hmap *idmap;
		struct act_statelist *sl;
	};

	struct lex_state {
		struct lx lx;
		struct lx_dynbuf buf;
	};

	struct act_statelist {
		char *id;
		struct fsm_state *state;
		struct act_statelist *next;
	};

	#define CURRENT_TERMINAL (act_state->lex_tok)
	#define ERROR_TERMINAL   TOK_UNKNOWN
	#define ADVANCE_LEXER    do { act_state->lex_tok = lx_next(&lex_state->lx); } while (0)
	#define SAVE_LEXER(tok)  do { act_state->lex_tok_save = act_state->lex_tok; \
	                              act_state->lex_tok = tok;                     } while (0)
	#define RESTORE_LEXER    do { act_state->lex_tok = act_state->lex_tok_save; } while (0)

	static void
	err(const struct lex_state *lex_state, const char *fmt, ...)
	{
		va_list ap;

		assert(lex_state != NULL);

		va_start(ap, fmt);
		fprintf(stderr, "%u:%u: ",
			lex_state->lx.start.line, lex_state->lx.start.col);
		vfprintf(stderr, fmt, ap);
		fprintf(stderr, "\n");
		va_end(ap);
	}

	static void
	err_expected(const struct lex_state *lex_state, const char *token)
	{
		err(lex_state, "Syntax error: expected %s", token);
		exit(EXIT_FAILURE);
	}

#line 86 "src/fsm/parser.c"


#ifndef ERROR_TERMINAL
#error "-s no-numeric-terminals given and ERROR_TERMINAL is not defined"
#endif

/* BEGINNING OF FUNCTION DECLARATIONS */

static void p_label(fsm, lex_state, act_state, char *);
static void p_edges(fsm, lex_state, act_state);
static void p_edges_C_Cedge(fsm, lex_state, act_state);
static void p_xstart(fsm, lex_state, act_state);
static void p_xend(fsm, lex_state, act_state);
static void p_58(fsm, lex_state, act_state);
extern void p_fsm(fsm, lex_state, act_state);
static void p_xend_C_Cend_Hids(fsm, lex_state, act_state);
static void p_xend_C_Cend_Hid(fsm, lex_state, act_state);

/* BEGINNING OF STATIC VARIABLES */


/* BEGINNING OF FUNCTION DEFINITIONS */

static void
p_label(fsm fsm, lex_state lex_state, act_state act_state, char *ZOc)
{
	char ZIc;

	if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
		return;
	}
	{
		/* BEGINNING OF INLINE: 34 */
		{
			switch (CURRENT_TERMINAL) {
			case (TOK_CHAR):
				{
					/* BEGINNING OF EXTRACT: CHAR */
					{
#line 187 "src/fsm/parser.act"

		assert(lex_state->buf.a[0] != '\0');
		assert(lex_state->buf.a[1] == '\0');

		ZIc = lex_state->buf.a[0];
	
#line 133 "src/fsm/parser.c"
					}
					/* END OF EXTRACT: CHAR */
					ADVANCE_LEXER;
				}
				break;
			case (TOK_ESC):
				{
					/* BEGINNING OF EXTRACT: ESC */
					{
#line 115 "src/fsm/parser.act"

		assert(0 == strncmp(lex_state->buf.a, "\\", 1));
		assert(2 == strlen(lex_state->buf.a));

		ZIc = lex_state->buf.a[1];

		switch (ZIc) {
		case '\\': ZIc = '\\'; break;
		case '\'': ZIc = '\''; break;
		case 'f':  ZIc = '\f'; break;
		case 'n':  ZIc = '\n'; break;
		case 'r':  ZIc = '\r'; break;
		case 't':  ZIc = '\t'; break;
		case 'v':  ZIc = '\v'; break;
		default:              break;
		}
	
#line 161 "src/fsm/parser.c"
					}
					/* END OF EXTRACT: ESC */
					ADVANCE_LEXER;
				}
				break;
			case (TOK_HEX):
				{
					/* BEGINNING OF EXTRACT: HEX */
					{
#line 180 "src/fsm/parser.act"

		unsigned long u;
		char *e;

		assert(0 == strncmp(lex_state->buf.a, "\\x", 2));
		assert(strlen(lex_state->buf.a) >= 3);

		errno = 0;

		u = strtoul(lex_state->buf.a + 2, &e, 16);
		assert(*e == '\0');

		if ((u == ULONG_MAX && errno == ERANGE) || u > UCHAR_MAX) {
			err(lex_state, "hex escape %s out of range: expected \\x0..\\x%x inclusive",
				lex_state->buf.a, UCHAR_MAX);
			exit(EXIT_FAILURE);
		}

		if ((u == ULONG_MAX && errno != 0) || *e != '\0') {
			err(lex_state, "%s: %s: expected \\x0..\\x%x inclusive",
				lex_state->buf.a, strerror(errno), UCHAR_MAX);
			exit(EXIT_FAILURE);
		}

		ZIc = (char) (unsigned char) u;
	
#line 198 "src/fsm/parser.c"
					}
					/* END OF EXTRACT: HEX */
					ADVANCE_LEXER;
				}
				break;
			case (TOK_OCT):
				{
					/* BEGINNING OF EXTRACT: OCT */
					{
#line 153 "src/fsm/parser.act"

		unsigned long u;
		char *e;

		assert(0 == strncmp(lex_state->buf.a, "\\", 1));
		assert(strlen(lex_state->buf.a) >= 2);

		errno = 0;

		u = strtoul(lex_state->buf.a + 1, &e, 8);
		assert(*e == '\0');

		if ((u == ULONG_MAX && errno == ERANGE) || u > UCHAR_MAX) {
			err(lex_state, "octal escape %s out of range: expected \\0..\\%o inclusive",
				lex_state->buf.a, UCHAR_MAX);
			exit(EXIT_FAILURE);
		}

		if ((u == ULONG_MAX && errno != 0) || *e != '\0') {
			err(lex_state, "%s: %s: expected \\0..\\%o inclusive",
				lex_state->buf.a, strerror(errno), UCHAR_MAX);
			exit(EXIT_FAILURE);
		}

		ZIc = (char) (unsigned char) u;
	
#line 235 "src/fsm/parser.c"
					}
					/* END OF EXTRACT: OCT */
					ADVANCE_LEXER;
				}
				break;
			default:
				goto ZL1;
			}
		}
		/* END OF INLINE: 34 */
		switch (CURRENT_TERMINAL) {
		case (TOK_LABEL):
			break;
		default:
			goto ZL1;
		}
		ADVANCE_LEXER;
	}
	goto ZL0;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOc = ZIc;
}

static void
p_edges(fsm fsm, lex_state lex_state, act_state act_state)
{
ZL2_edges:;
	switch (CURRENT_TERMINAL) {
	case (TOK_IDENT):
		{
			p_edges_C_Cedge (fsm, lex_state, act_state);
			/* BEGINNING OF INLINE: edges */
			if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
				RESTORE_LEXER;
				goto ZL1;
			} else {
				goto ZL2_edges;
			}
			/* END OF INLINE: edges */
		}
		/* UNREACHED */
	case (ERROR_TERMINAL):
		return;
	default:
		break;
	}
	return;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
}

static void
p_edges_C_Cedge(fsm fsm, lex_state lex_state, act_state act_state)
{
	if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
		return;
	}
	{
		string ZIa;
		string ZIb;
		state ZIx;
		state ZIy;

		/* BEGINNING OF INLINE: id */
		{
			{
				switch (CURRENT_TERMINAL) {
				case (TOK_IDENT):
					/* BEGINNING OF EXTRACT: IDENT */
					{
#line 191 "src/fsm/parser.act"

		ZIa = xstrdup(lex_state->buf.a);
		if (ZIa == NULL) {
			perror("xstrdup");
			exit(EXIT_FAILURE);
		}
	
#line 318 "src/fsm/parser.c"
					}
					/* END OF EXTRACT: IDENT */
					break;
				default:
					goto ZL1;
				}
				ADVANCE_LEXER;
			}
		}
		/* END OF INLINE: id */
		switch (CURRENT_TERMINAL) {
		case (TOK_TO):
			break;
		default:
			goto ZL1;
		}
		ADVANCE_LEXER;
		/* BEGINNING OF INLINE: id */
		{
			{
				switch (CURRENT_TERMINAL) {
				case (TOK_IDENT):
					/* BEGINNING OF EXTRACT: IDENT */
					{
#line 191 "src/fsm/parser.act"

		ZIb = xstrdup(lex_state->buf.a);
		if (ZIb == NULL) {
			perror("xstrdup");
			exit(EXIT_FAILURE);
		}
	
#line 351 "src/fsm/parser.c"
					}
					/* END OF EXTRACT: IDENT */
					break;
				default:
					goto ZL1;
				}
				ADVANCE_LEXER;
			}
		}
		/* END OF INLINE: id */
		/* BEGINNING OF ACTION: add-state */
		{
#line 203 "src/fsm/parser.act"

		struct act_statelist *p;

		assert((ZIa) != NULL);

                /*
		for (p = act_state->sl; p != NULL; p = p->next) {
			assert(p->id != NULL);
			assert(p->state != NULL);

			if (0 == strcmp(p->id, (ZIa))) {
				(ZIx) = p->state;
				break;
			}
		}
                */
                p = hmap_getptr(act_state->idmap, (ZIa));

                if (debug_hmap) {
			struct act_statelist *p0 = p;

			for (p = act_state->sl; p != NULL; p = p->next) {
				assert(p->id != NULL);
				assert(p->state != NULL);

				if (0 == strcmp(p->id, (ZIa))) {
					(ZIx) = p->state;
					break;
				}
			}
			assert(p == p0);
		}

		if (p == NULL) {
			struct act_statelist *new;

			new = malloc(sizeof *new);
			if (new == NULL) {
				perror("malloc");
				exit(EXIT_FAILURE);
			}

			new->id = xstrdup((ZIa));
			if (new->id == NULL) {
				perror("xstrdup");
				exit(EXIT_FAILURE);
			}

			(ZIx) = fsm_addstate(fsm);
			if ((ZIx) == NULL) {
				perror("fsm_addstate");
				exit(EXIT_FAILURE);
			}

			new->state = (ZIx);

			new->next = act_state->sl;
			act_state->sl = new;
                        hmap_setptr(act_state->idmap, new->id, new);
		} else {
                        (ZIx) = p->state;
                }
	
#line 428 "src/fsm/parser.c"
		}
		/* END OF ACTION: add-state */
		/* BEGINNING OF ACTION: add-state */
		{
#line 203 "src/fsm/parser.act"

		struct act_statelist *p;

		assert((ZIb) != NULL);

                /*
		for (p = act_state->sl; p != NULL; p = p->next) {
			assert(p->id != NULL);
			assert(p->state != NULL);

			if (0 == strcmp(p->id, (ZIb))) {
				(ZIy) = p->state;
				break;
			}
		}
                */
                p = hmap_getptr(act_state->idmap, (ZIb));

                if (debug_hmap) {
			struct act_statelist *p0 = p;

			for (p = act_state->sl; p != NULL; p = p->next) {
				assert(p->id != NULL);
				assert(p->state != NULL);

				if (0 == strcmp(p->id, (ZIb))) {
					(ZIy) = p->state;
					break;
				}
			}
			assert(p == p0);
		}

		if (p == NULL) {
			struct act_statelist *new;

			new = malloc(sizeof *new);
			if (new == NULL) {
				perror("malloc");
				exit(EXIT_FAILURE);
			}

			new->id = xstrdup((ZIb));
			if (new->id == NULL) {
				perror("xstrdup");
				exit(EXIT_FAILURE);
			}

			(ZIy) = fsm_addstate(fsm);
			if ((ZIy) == NULL) {
				perror("fsm_addstate");
				exit(EXIT_FAILURE);
			}

			new->state = (ZIy);

			new->next = act_state->sl;
			act_state->sl = new;
                        hmap_setptr(act_state->idmap, new->id, new);
		} else {
                        (ZIy) = p->state;
                }
	
#line 497 "src/fsm/parser.c"
		}
		/* END OF ACTION: add-state */
		/* BEGINNING OF ACTION: free */
		{
#line 277 "src/fsm/parser.act"

		free((ZIa));
	
#line 506 "src/fsm/parser.c"
		}
		/* END OF ACTION: free */
		/* BEGINNING OF ACTION: free */
		{
#line 277 "src/fsm/parser.act"

		free((ZIb));
	
#line 515 "src/fsm/parser.c"
		}
		/* END OF ACTION: free */
		/* BEGINNING OF INLINE: 44 */
		{
			switch (CURRENT_TERMINAL) {
			case (TOK_ANY):
				{
					ADVANCE_LEXER;
					/* BEGINNING OF ACTION: add-edge-any */
					{
#line 302 "src/fsm/parser.act"

		if (!fsm_addedge_any(fsm, (ZIx), (ZIy))) {
			perror("fsm_addedge_any");
			exit(EXIT_FAILURE);
		}
	
#line 533 "src/fsm/parser.c"
					}
					/* END OF ACTION: add-edge-any */
				}
				break;
			case (TOK_ESC): case (TOK_OCT): case (TOK_HEX): case (TOK_CHAR):
				{
					char ZIc;

					p_label (fsm, lex_state, act_state, &ZIc);
					if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
						RESTORE_LEXER;
						goto ZL5;
					}
					/* BEGINNING OF ACTION: add-edge-literal */
					{
#line 295 "src/fsm/parser.act"

		if (!fsm_addedge_literal(fsm, (ZIx), (ZIy), (ZIc))) {
			perror("fsm_addedge_literal");
			exit(EXIT_FAILURE);
		}
	
#line 556 "src/fsm/parser.c"
					}
					/* END OF ACTION: add-edge-literal */
				}
				break;
			default:
				{
					/* BEGINNING OF ACTION: add-edge-epsilon */
					{
#line 309 "src/fsm/parser.act"

		if (!fsm_addedge_epsilon(fsm, (ZIx), (ZIy))) {
			perror("fsm_addedge_epsilon");
			exit(EXIT_FAILURE);
		}
	
#line 572 "src/fsm/parser.c"
					}
					/* END OF ACTION: add-edge-epsilon */
				}
				break;
			}
			goto ZL4;
		ZL5:;
			{
				/* BEGINNING OF ACTION: err-expected-trans */
				{
#line 322 "src/fsm/parser.act"

		err_expected(lex_state, "transition");
	
#line 587 "src/fsm/parser.c"
				}
				/* END OF ACTION: err-expected-trans */
			}
		ZL4:;
		}
		/* END OF INLINE: 44 */
		p_58 (fsm, lex_state, act_state);
		if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
			RESTORE_LEXER;
			goto ZL1;
		}
	}
	return;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
}

static void
p_xstart(fsm fsm, lex_state lex_state, act_state act_state)
{
	switch (CURRENT_TERMINAL) {
	case (TOK_START):
		{
			string ZIn;
			state ZIs;

			/* BEGINNING OF INLINE: 47 */
			{
				{
					switch (CURRENT_TERMINAL) {
					case (TOK_START):
						break;
					default:
						goto ZL3;
					}
					ADVANCE_LEXER;
				}
				goto ZL2;
			ZL3:;
				{
					/* BEGINNING OF ACTION: err-expected-start */
					{
#line 330 "src/fsm/parser.act"

		err_expected(lex_state, "'start:'");
	
#line 635 "src/fsm/parser.c"
					}
					/* END OF ACTION: err-expected-start */
				}
			ZL2:;
			}
			/* END OF INLINE: 47 */
			/* BEGINNING OF INLINE: id */
			{
				{
					switch (CURRENT_TERMINAL) {
					case (TOK_IDENT):
						/* BEGINNING OF EXTRACT: IDENT */
						{
#line 191 "src/fsm/parser.act"

		ZIn = xstrdup(lex_state->buf.a);
		if (ZIn == NULL) {
			perror("xstrdup");
			exit(EXIT_FAILURE);
		}
	
#line 657 "src/fsm/parser.c"
						}
						/* END OF EXTRACT: IDENT */
						break;
					default:
						goto ZL1;
					}
					ADVANCE_LEXER;
				}
			}
			/* END OF INLINE: id */
			p_58 (fsm, lex_state, act_state);
			if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
				RESTORE_LEXER;
				goto ZL1;
			}
			/* BEGINNING OF ACTION: add-state */
			{
#line 203 "src/fsm/parser.act"

		struct act_statelist *p;

		assert((ZIn) != NULL);

                /*
		for (p = act_state->sl; p != NULL; p = p->next) {
			assert(p->id != NULL);
			assert(p->state != NULL);

			if (0 == strcmp(p->id, (ZIn))) {
				(ZIs) = p->state;
				break;
			}
		}
                */
                p = hmap_getptr(act_state->idmap, (ZIn));

                if (debug_hmap) {
			struct act_statelist *p0 = p;

			for (p = act_state->sl; p != NULL; p = p->next) {
				assert(p->id != NULL);
				assert(p->state != NULL);

				if (0 == strcmp(p->id, (ZIn))) {
					(ZIs) = p->state;
					break;
				}
			}
			assert(p == p0);
		}

		if (p == NULL) {
			struct act_statelist *new;

			new = malloc(sizeof *new);
			if (new == NULL) {
				perror("malloc");
				exit(EXIT_FAILURE);
			}

			new->id = xstrdup((ZIn));
			if (new->id == NULL) {
				perror("xstrdup");
				exit(EXIT_FAILURE);
			}

			(ZIs) = fsm_addstate(fsm);
			if ((ZIs) == NULL) {
				perror("fsm_addstate");
				exit(EXIT_FAILURE);
			}

			new->state = (ZIs);

			new->next = act_state->sl;
			act_state->sl = new;
                        hmap_setptr(act_state->idmap, new->id, new);
		} else {
                        (ZIs) = p->state;
                }
	
#line 739 "src/fsm/parser.c"
			}
			/* END OF ACTION: add-state */
			/* BEGINNING OF ACTION: mark-start */
			{
#line 265 "src/fsm/parser.act"

		assert((ZIs) != NULL);

		fsm_setstart(fsm, (ZIs));
	
#line 750 "src/fsm/parser.c"
			}
			/* END OF ACTION: mark-start */
			/* BEGINNING OF ACTION: free */
			{
#line 277 "src/fsm/parser.act"

		free((ZIn));
	
#line 759 "src/fsm/parser.c"
			}
			/* END OF ACTION: free */
		}
		break;
	case (ERROR_TERMINAL):
		return;
	default:
		break;
	}
	return;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
}

static void
p_xend(fsm fsm, lex_state lex_state, act_state act_state)
{
	switch (CURRENT_TERMINAL) {
	case (TOK_END):
		{
			/* BEGINNING OF INLINE: 57 */
			{
				{
					switch (CURRENT_TERMINAL) {
					case (TOK_END):
						break;
					default:
						goto ZL3;
					}
					ADVANCE_LEXER;
				}
				goto ZL2;
			ZL3:;
				{
					/* BEGINNING OF ACTION: err-expected-end */
					{
#line 334 "src/fsm/parser.act"

		err_expected(lex_state, "'end:'");
	
#line 801 "src/fsm/parser.c"
					}
					/* END OF ACTION: err-expected-end */
				}
			ZL2:;
			}
			/* END OF INLINE: 57 */
			p_xend_C_Cend_Hids (fsm, lex_state, act_state);
			p_58 (fsm, lex_state, act_state);
			if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
				RESTORE_LEXER;
				goto ZL1;
			}
		}
		break;
	case (ERROR_TERMINAL):
		return;
	default:
		break;
	}
	return;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
}

static void
p_58(fsm fsm, lex_state lex_state, act_state act_state)
{
	if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
		return;
	}
	{
		switch (CURRENT_TERMINAL) {
		case (TOK_SEP):
			break;
		default:
			goto ZL1;
		}
		ADVANCE_LEXER;
	}
	return;
ZL1:;
	{
		/* BEGINNING OF ACTION: err-expected-sep */
		{
#line 318 "src/fsm/parser.act"

		err_expected(lex_state, "';'");
	
#line 851 "src/fsm/parser.c"
		}
		/* END OF ACTION: err-expected-sep */
	}
}

void
p_fsm(fsm fsm, lex_state lex_state, act_state act_state)
{
	if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
		return;
	}
	{
		p_edges (fsm, lex_state, act_state);
		p_xstart (fsm, lex_state, act_state);
		p_xend (fsm, lex_state, act_state);
		switch (CURRENT_TERMINAL) {
		case (TOK_EOF):
			break;
		case (ERROR_TERMINAL):
			RESTORE_LEXER;
			goto ZL1;
		default:
			goto ZL1;
		}
		ADVANCE_LEXER;
		/* BEGINNING OF ACTION: free-statelist */
		{
#line 292 "src/fsm/parser.act"

		struct act_statelist *p;
		struct act_statelist *next;

		for (p = act_state->sl; p != NULL; p = next) {
			next = p->next;

			assert(p->id != NULL);

			free(p->id);
			free(p);
		}
	
#line 893 "src/fsm/parser.c"
		}
		/* END OF ACTION: free-statelist */
	}
	return;
ZL1:;
	{
		/* BEGINNING OF ACTION: err-syntax */
		{
#line 339 "src/fsm/parser.act"

		err(lex_state, "Syntax error");
		exit(EXIT_FAILURE);
	
#line 907 "src/fsm/parser.c"
		}
		/* END OF ACTION: err-syntax */
	}
}

static void
p_xend_C_Cend_Hids(fsm fsm, lex_state lex_state, act_state act_state)
{
	if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
		return;
	}
ZL2_xend_C_Cend_Hids:;
	{
		p_xend_C_Cend_Hid (fsm, lex_state, act_state);
		/* BEGINNING OF INLINE: 55 */
		{
			switch (CURRENT_TERMINAL) {
			case (TOK_COMMA):
				{
					/* BEGINNING OF INLINE: 56 */
					{
						{
							switch (CURRENT_TERMINAL) {
							case (TOK_COMMA):
								break;
							default:
								goto ZL5;
							}
							ADVANCE_LEXER;
						}
						goto ZL4;
					ZL5:;
						{
							/* BEGINNING OF ACTION: err-expected-comma */
							{
#line 326 "src/fsm/parser.act"

		err_expected(lex_state, "','");
	
#line 947 "src/fsm/parser.c"
							}
							/* END OF ACTION: err-expected-comma */
						}
					ZL4:;
					}
					/* END OF INLINE: 56 */
					/* BEGINNING OF INLINE: xend::end-ids */
					goto ZL2_xend_C_Cend_Hids;
					/* END OF INLINE: xend::end-ids */
				}
				/* UNREACHED */
			case (ERROR_TERMINAL):
				RESTORE_LEXER;
				goto ZL1;
			default:
				break;
			}
		}
		/* END OF INLINE: 55 */
	}
	return;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
}

static void
p_xend_C_Cend_Hid(fsm fsm, lex_state lex_state, act_state act_state)
{
	if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
		return;
	}
	{
		string ZIn;
		state ZIs;

		/* BEGINNING OF INLINE: id */
		{
			{
				switch (CURRENT_TERMINAL) {
				case (TOK_IDENT):
					/* BEGINNING OF EXTRACT: IDENT */
					{
#line 191 "src/fsm/parser.act"

		ZIn = xstrdup(lex_state->buf.a);
		if (ZIn == NULL) {
			perror("xstrdup");
			exit(EXIT_FAILURE);
		}
	
#line 999 "src/fsm/parser.c"
					}
					/* END OF EXTRACT: IDENT */
					break;
				default:
					goto ZL1;
				}
				ADVANCE_LEXER;
			}
		}
		/* END OF INLINE: id */
		/* BEGINNING OF ACTION: add-state */
		{
#line 203 "src/fsm/parser.act"

		struct act_statelist *p;

		assert((ZIn) != NULL);

                /*
		for (p = act_state->sl; p != NULL; p = p->next) {
			assert(p->id != NULL);
			assert(p->state != NULL);

			if (0 == strcmp(p->id, (ZIn))) {
				(ZIs) = p->state;
				break;
			}
		}
                */
                p = hmap_getptr(act_state->idmap, (ZIn));

                if (debug_hmap) {
			struct act_statelist *p0 = p;

			for (p = act_state->sl; p != NULL; p = p->next) {
				assert(p->id != NULL);
				assert(p->state != NULL);

				if (0 == strcmp(p->id, (ZIn))) {
					(ZIs) = p->state;
					break;
				}
			}
			assert(p == p0);
		}

		if (p == NULL) {
			struct act_statelist *new;

			new = malloc(sizeof *new);
			if (new == NULL) {
				perror("malloc");
				exit(EXIT_FAILURE);
			}

			new->id = xstrdup((ZIn));
			if (new->id == NULL) {
				perror("xstrdup");
				exit(EXIT_FAILURE);
			}

			(ZIs) = fsm_addstate(fsm);
			if ((ZIs) == NULL) {
				perror("fsm_addstate");
				exit(EXIT_FAILURE);
			}

			new->state = (ZIs);

			new->next = act_state->sl;
			act_state->sl = new;
                        hmap_setptr(act_state->idmap, new->id, new);
		} else {
                        (ZIs) = p->state;
                }
	
#line 1076 "src/fsm/parser.c"
		}
		/* END OF ACTION: add-state */
		/* BEGINNING OF ACTION: mark-end */
		{
#line 271 "src/fsm/parser.act"

		assert((ZIs) != NULL);

		fsm_setend(fsm, (ZIs), 1);
	
#line 1087 "src/fsm/parser.c"
		}
		/* END OF ACTION: mark-end */
		/* BEGINNING OF ACTION: free */
		{
#line 277 "src/fsm/parser.act"

		free((ZIn));
	
#line 1096 "src/fsm/parser.c"
		}
		/* END OF ACTION: free */
	}
	return;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
}

/* BEGINNING OF TRAILER */

#line 394 "src/fsm/parser.act"


	struct fsm *fsm_parse(FILE *f, const struct fsm_options *opt) {
		struct act_state act_state_s;
		struct act_state *act_state;
		struct lex_state lex_state_s;
		struct lex_state *lex_state;
		struct fsm *new;
		struct lx *lx;

		assert(f != NULL);
		assert(opt != NULL);

		lex_state = &lex_state_s;

		lx = &lex_state->lx;

		lx_init(lx);

		lx->lgetc  = lx_fgetc;
		lx->opaque = f;

		lex_state->buf.a   = NULL;
		lex_state->buf.len = 0;

		lx->buf   = &lex_state->buf;
		lx->push  = lx_dynpush;
		lx->pop   = lx_dynpop;
		lx->clear = lx_dynclear;
		lx->free  = lx_dynfree;

		act_state_s.sl = NULL;
                act_state_s.idmap = hmap_create_string(NBUCKETS, 0.6f);

		/* This is a workaround for ADVANCE_LEXER assuming a pointer */
		act_state = &act_state_s;

		/* TODO: pass in fsm_options */
		new = fsm_new(opt);
		if (new == NULL) {
			perror("fsm_new");
			return NULL;
		}

		ADVANCE_LEXER; /* XXX: what if the first token is unrecognised? */
		p_fsm(new, lex_state, act_state);

                hmap_free(act_state_s.idmap);
		lx->free(lx);

		return new;
	}

#line 1162 "src/fsm/parser.c"

/* END OF FILE */
