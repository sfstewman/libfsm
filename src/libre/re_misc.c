#include <limits.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <assert.h>

#include <re/re.h>

#include <fsm/fsm.h>
#include <fsm/options.h>

#include "ast.h"
#include "print.h"

struct ast *
re_parse_string(enum re_dialect dialect, const char *s, struct re_err *err, int only_parse)
{
	static const struct fsm_options opts_zero;

	struct fsm_options opts = opts_zero;
	enum re_flags flags = 0U;

	if (only_parse) {
		return re_parse_only(dialect, fsm_sgetc, &s, &opts, flags, err);
	} else {
		return re_parse(dialect, fsm_sgetc, &s, &opts, flags, err, NULL);
	}
}

const char *
ast_node_name(const struct ast_expr *node)
{
	switch (node->type) {
		case AST_EXPR_LITERAL:     return "LITERAL";
		case AST_EXPR_CONCAT:      return "CONCAT";
		case AST_EXPR_ALT:         return "ALT";
		case AST_EXPR_REPEAT:      return "REPEAT";
		case AST_EXPR_GROUP:       return "GROUP";
		case AST_EXPR_SUBTRACT:    return "SUBTRACT";
		case AST_EXPR_EMPTY:       return "EMPTY";
		case AST_EXPR_CODEPOINT:   return "CODEPOINT";
		case AST_EXPR_ANCHOR:      return "ANCHOR";
		case AST_EXPR_RANGE:       return "RANGE";
		case AST_EXPR_PLACEHOLDER: return "PLACEHOLDER";
		case AST_EXPR_TOMBSTONE:   return "TOMBSTONE";
	}

	// should not reach
	abort();
}

/* returns number of substitutions in tree */
static size_t
replace_literals_with_placeholders(struct ast_expr *node, const char *placeholders)
{
	switch (node->type) {
		case AST_EXPR_LITERAL:
			{
				const char *match;

				match = strchr(placeholders, node->u.literal.c);

				if (match != NULL) {
					/* literal is a "placeholder" */
					node->type = AST_EXPR_PLACEHOLDER;
					node->u.placeholder.index = match - placeholders;

					return 1;
				}

				return 0;
			}

		case AST_EXPR_CONCAT:
			{
				size_t i,n,nsubst;

				nsubst = 0;
				n = node->u.concat.count;
				for (i=0; i < n; i++) {
					nsubst += replace_literals_with_placeholders(node->u.concat.n[i], placeholders);
				}

				return nsubst;
			}

		case AST_EXPR_ALT:
			{
				size_t i,n,nsubst;

				nsubst = 0;
				n = node->u.alt.count;
				for (i=0; i < n; i++) {
					nsubst += replace_literals_with_placeholders(node->u.alt.n[i], placeholders);
				}

				return nsubst;
			}

		case AST_EXPR_REPEAT:
			return replace_literals_with_placeholders(node->u.repeat.e, placeholders);

		case AST_EXPR_GROUP:
			return replace_literals_with_placeholders(node->u.group.e, placeholders);

		case AST_EXPR_SUBTRACT:
			return replace_literals_with_placeholders(node->u.subtract.a, placeholders) +
				replace_literals_with_placeholders(node->u.subtract.b, placeholders);

		case AST_EXPR_EMPTY:
		case AST_EXPR_CODEPOINT:
		case AST_EXPR_ANCHOR:
		case AST_EXPR_RANGE:
		case AST_EXPR_PLACEHOLDER:
		case AST_EXPR_TOMBSTONE:
			return 0;
	}

	abort(); // should not reach
}

struct ast *
re_parse_ast_match(const char *s, struct re_err *err, const char *placeholders)
{
	struct ast *ast = re_parse_string(RE_NATIVE, s, err, 1);
	if (ast == NULL) {
		return NULL;
	}

	replace_literals_with_placeholders(ast->expr, placeholders);

	return ast;
}

struct ast_match {
	struct ast_expr **node;

	/* XXX: prototype.
	 *
	 * assumes that we have at most UCHAR_MAX+1 placeholders since
	 * we're generating PLACEHOLDER nodes from literals.
	 *
	 * This is both kind of wasteful and also a bad assumption;
	 * ideally placeholders would be something one could directly
	 * construct via a regexp matching dialect.
	 *
	 * TODO: replace with an allocated array of the correct size.
	 */

	int nplaceholders;
	struct ast_expr *placeholders[UCHAR_MAX+1];
};

static bool
match_placeholder(struct ast_match *match, struct ast_expr *node, struct ast_expr *placeholder)
{
	int index;
	bool equal;
	/*
	enum ast_flags flags1, flags2;
	*/

	assert(match != NULL);
	assert(node != NULL);
	assert(placeholder != NULL);
	assert(placeholder->type == AST_EXPR_PLACEHOLDER);

	index = placeholder->u.placeholder.index;
	assert(index >= 0 && index <= UCHAR_MAX);

	if (match->placeholders[index] == NULL) {
		match->placeholders[index] = node;
		match->nplaceholders++;
		return true;
	}

	/* FIXME: not sure how to handle flags! */
	/*
	flags1 = match->placeholders[index]->flags;
	flags2 = node->flags;
	match->placeholders[index]->flags = 0;
	node->flags = 0;
	*/
	equal = ast_expr_equal(match->placeholders[index], node);
	/*
	match->placeholders[index]->flags = flags1;
	node->flags = flags2;
	*/

	return equal;
}

enum match_result {
	MATCH_RESULT_STOP = -1,
	MATCH_RESULT_NO_MATCH = 0,
	MATCH_RESULT_MATCH = 1
};

typedef bool (*match_visitor)(struct ast *, struct ast_match *, void *);

static bool
ast_endpoint_equal(const struct ast_endpoint *a, const struct ast_endpoint *b)
{
	if (a->type != b->type) {
		return false;
	}

	switch (a->type) {
		case AST_ENDPOINT_LITERAL:
			return a->u.literal.c == b->u.literal.c;
		case AST_ENDPOINT_CODEPOINT:
			return a->u.codepoint.u == b->u.codepoint.u;
		case AST_ENDPOINT_NAMED:
			return a->u.named.class == b->u.named.class;
	}

	// should not reach
	abort();
}

static enum match_result
visit_matches_inner(struct ast *ast, struct ast_expr **ast_node, struct ast_expr *match_node, struct ast_match *in_match, match_visitor visitor, void *visitor_data)
{
	static const struct ast_match match_zero;
	struct ast_match match;
	bool has_match;
	bool match_root;

	assert(ast != NULL);
	assert(ast_node != NULL);
	assert(*ast_node != NULL);
	assert(match_node != NULL);
	assert(visitor != NULL);

	has_match = false;
	match_root = false;
	match = match_zero;

	if (in_match == NULL) {
		in_match = &match;
		match.node = ast_node;
		match_root = true;
	}

	switch ((*ast_node)->type) {
		case AST_EXPR_CONCAT:
		case AST_EXPR_ALT:
			{
				size_t i,n;
				struct ast_expr **children;

				n = ((*ast_node)->type == AST_EXPR_CONCAT) ? (*ast_node)->u.concat.count : (*ast_node)->u.alt.count;
				children = ((*ast_node)->type == AST_EXPR_CONCAT) ? (*ast_node)->u.concat.n : (*ast_node)->u.alt.n;

				if (match_root) {
					/* if we're the root of a match, then matching hasn't started.
					 * First try to match on our children.
					 */

					/*
					fprintf(stderr, "node %p (%s) is ROOT: matching children first\n",
						(void *)(*ast_node), (*ast_node)->type == AST_EXPR_CONCAT ? "CONCAT" : "ALT");
					*/
					for (i=0; i < n; i++) {
						enum match_result res;
						/*
						 * Match or no match isn't important here.  If a child matches, it's a root match and
						 * the child will call the visitor.
						 *
						 * We do need to check for a STOP condition.
						 */
						res = visit_matches_inner(ast, &children[i], match_node, NULL, visitor, visitor_data);
						if (res == MATCH_RESULT_STOP) {
							return res;
						}
					}
				}

				/* now try to match on ourselves */
				if (match_node->type == AST_EXPR_PLACEHOLDER) {
					has_match = match_placeholder(in_match, *ast_node, match_node);
					/*
					fprintf(stderr, "node %p (%s) placeholder[%d] match? %s\n",
						(void *)(*ast_node), (*ast_node)->type == AST_EXPR_CONCAT ? "CONCAT" : "ALT",
						match_node->u.placeholder.index, has_match ? "yes" : "no");
					*/
				} else if (match_node->type == (*ast_node)->type) {
					size_t match_n;
					struct ast_expr **match_children;

					/* TODO: matching ALTs should really not depend on ALT ordering.  Could this be
					 *       handled by ensuring that ALT children are somehow sorted (both ast_node and
					 *       match_node children)?
					 */
					match_n = (match_node->type == AST_EXPR_CONCAT) ? match_node->u.concat.count : match_node->u.alt.count;
					match_children = (match_node->type == AST_EXPR_CONCAT) ? match_node->u.concat.n : match_node->u.alt.n;

					if (match_n == n) {
						/*
						fprintf(stderr, "node %p (%s) matching %lu children\n",
							(void *)(*ast_node), (*ast_node)->type == AST_EXPR_CONCAT ? "CONCAT" : "ALT",
							(unsigned long)n);
						*/
						has_match = true;
						for (i=0; i < n; i++) {
							enum match_result res;

							res = visit_matches_inner(ast,
								&children[i],
								match_children[i],
								in_match,
								visitor,
								visitor_data
							);

							/*
							fprintf(stderr, "node %p (%s) matching child %lu: %s\n",
								(void *)(*ast_node), (*ast_node)->type == AST_EXPR_CONCAT ? "CONCAT" : "ALT",
								(unsigned long)i,
								(res == MATCH_RESULT_MATCH) ? "match" :
								((res == MATCH_RESULT_NO_MATCH) ? "no match" : "stop"));
							*/
							if (res != MATCH_RESULT_MATCH) {
								if (res == MATCH_RESULT_STOP) {
									return res;
								}

								has_match = false;
								break;
							}
						}
					}
				}
			}
			break;

		case AST_EXPR_REPEAT:
		case AST_EXPR_GROUP:
			{
				struct ast_expr **inner = ((*ast_node)->type == AST_EXPR_REPEAT) ? &(*ast_node)->u.repeat.e : &(*ast_node)->u.group.e;
				if (match_root) {
					enum match_result res;

					/*
					fprintf(stderr, "node %p (%s) is ROOT: matching inner first\n",
						(void *)(*ast_node), (*ast_node)->type == AST_EXPR_REPEAT ? "REPEAT" : "GROUP");
					*/

					/* if we're the root of a match, then matching hasn't started.
					 * First try to match on our children.
					 *
					 * Match or no match isn't important here.  If a child matches, it's a root match and
					 * the child will call the visitor.
					 *
					 * We do need to check for a STOP condition.
					 */
					res = visit_matches_inner(ast, inner, match_node, NULL, visitor, visitor_data);
					if (res == MATCH_RESULT_STOP) {
						return res;
					}
				}

				/* now try matching on ourselves */
				if (match_node->type == AST_EXPR_PLACEHOLDER) {
					has_match = match_placeholder(in_match, *ast_node, match_node);
					/*
					fprintf(stderr, "node %p (%s) placeholder[%d] match? %s\n",
						(void *)(*ast_node), (*ast_node)->type == AST_EXPR_REPEAT ? "REPEAT" : "GROUP",
						match_node->u.placeholder.index, has_match ? "yes" : "no");
					*/
				} else if (match_node->type == (*ast_node)->type) {
					if ((*ast_node)->type == AST_EXPR_GROUP) {
						enum match_result res;
						res = visit_matches_inner(
							ast,
							&(*ast_node)->u.group.e,
							match_node->u.group.e,
							in_match, visitor, visitor_data
						);

						if (res == MATCH_RESULT_STOP) {
							return res;
						}

						has_match = (res == MATCH_RESULT_MATCH);
						/*
						fprintf(stderr, "node %p (%s) match? %s\n",
							(void *)(*ast_node), (*ast_node)->type == AST_EXPR_REPEAT ? "REPEAT" : "GROUP",
							has_match ? "yes" : "no");
						*/
					} else {
						if ((*ast_node)->u.repeat.min == match_node->u.repeat.min
								&& (*ast_node)->u.repeat.max == match_node->u.repeat.max) {
							enum match_result res;
							res = visit_matches_inner(
								ast,
								&(*ast_node)->u.repeat.e,
								match_node->u.repeat.e,
								in_match, visitor, visitor_data);

							if (res == MATCH_RESULT_STOP) {
								return res;
							}

							has_match = (res == MATCH_RESULT_MATCH);
							/*
							fprintf(stderr, "node %p (%s) match? %s\n",
								(void *)(*ast_node),
								(*ast_node)->type == AST_EXPR_REPEAT ? "REPEAT" : "GROUP",
								has_match ? "yes" : "no");
							*/
						} else {
							/*
							fprintf(stderr, "node %p (%s) min/max do not match\n",
								(void *)(*ast_node),
								(*ast_node)->type == AST_EXPR_REPEAT ? "REPEAT" : "GROUP");
							*/
						}
					}
				}
			}
			break;

		case AST_EXPR_SUBTRACT:
			{
				if (match_root) {
					enum match_result res;

					/* if we're the root of a match, then matching hasn't started.
					 * First try to match on our children.
					 *
					 * Match or no match isn't important here.  If a child matches, it's a root match and
					 * the child will call the visitor.
					 *
					 * We do need to check for a STOP condition.
					 */
					res = visit_matches_inner(ast,&(*ast_node)->u.subtract.a, match_node, NULL, visitor, visitor_data);
					if (res == MATCH_RESULT_STOP) {
						return res;
					}

					res = visit_matches_inner(ast,&(*ast_node)->u.subtract.b, match_node, NULL, visitor, visitor_data);
					if (res == MATCH_RESULT_STOP) {
						return res;
					}
				}

				/* now try matching on ourselves */
				if (match_node->type == AST_EXPR_PLACEHOLDER) {
					has_match = match_placeholder(in_match, *ast_node, match_node);
				} else if (match_node->type == (*ast_node)->type) {
					enum match_result res;

					res = visit_matches_inner(
						ast,
						&(*ast_node)->u.subtract.a,
						match_node->u.subtract.a,
						in_match, visitor, visitor_data
					);

					if (res == MATCH_RESULT_STOP) {
						return res;
					}

					if (res == MATCH_RESULT_MATCH) {
						res = visit_matches_inner(
							ast,
							&(*ast_node)->u.subtract.b,
							match_node->u.subtract.b,
							in_match, visitor, visitor_data
						);

						if (res == MATCH_RESULT_STOP) {
							return res;
						}

						has_match = (res == MATCH_RESULT_MATCH);
					}
				}
			}
			break;

		case AST_EXPR_EMPTY:
		case AST_EXPR_LITERAL:
		case AST_EXPR_CODEPOINT:
		case AST_EXPR_ANCHOR:
		case AST_EXPR_RANGE:
			if (match_node->type == AST_EXPR_PLACEHOLDER) {
				has_match = match_placeholder(in_match, *ast_node, match_node);
				/*
				fprintf(stderr, "node %p (%s) placeholder[%d] match? %s\n",
					(void *)(*ast_node), ast_node_name(*ast_node),
					match_node->u.placeholder.index, has_match ? "yes" : "no");
				*/
			}
			else if (match_node->type == (*ast_node)->type) {
				if ((*ast_node)->type == AST_EXPR_EMPTY) {
					has_match = true;
				} else if ((*ast_node)->type == AST_EXPR_LITERAL) {
					has_match = ((*ast_node)->u.literal.c == match_node->u.literal.c);
				} else if ((*ast_node)->type == AST_EXPR_CODEPOINT) {
					has_match = ((*ast_node)->u.codepoint.u == match_node->u.codepoint.u);
				} else if ((*ast_node)->type == AST_EXPR_ANCHOR) {
					has_match = ((*ast_node)->u.anchor.type == match_node->u.anchor.type);
				} else if ((*ast_node)->type == AST_EXPR_RANGE) {
					has_match = ast_endpoint_equal(&(*ast_node)->u.range.from, &match_node->u.range.from)
						&& ast_endpoint_equal(&(*ast_node)->u.range.to, &match_node->u.range.to);
				} else {
					// should not reach
					abort();
				}
			}
			break;

		/* ast_node shouldn't be a PLACEHOLDER, and we ignore TOMBSTONE nodes */
		case AST_EXPR_PLACEHOLDER:
		case AST_EXPR_TOMBSTONE:
			break;
	}

	if (has_match && match_root) {
		if (!visitor(ast, &match, visitor_data)) {
			return MATCH_RESULT_STOP;
		}
	}

	return has_match ? MATCH_RESULT_MATCH : MATCH_RESULT_NO_MATCH;
}

static void
visit_matches(struct ast *ast, const struct ast *match, match_visitor visitor, void *visitor_data)
{
	assert(ast != NULL);
	assert(match != NULL);
	assert(visitor != NULL);

	visit_matches_inner(ast, &ast->expr, match->expr, NULL, visitor, visitor_data);
}

struct rewrite_data {
	const struct ast *subst;
	size_t nsubst;
};

static int
replace_placeholders(struct ast_expr_pool **pool, struct ast_expr **root, struct ast_match *match)
{
	switch ((*root)->type) {
		case AST_EXPR_CONCAT:
		case AST_EXPR_ALT:
			{
				size_t i,n;
				struct ast_expr **children;

				n = ((*root)->type == AST_EXPR_CONCAT) ? (*root)->u.concat.count : (*root)->u.alt.count;
				children = ((*root)->type == AST_EXPR_CONCAT) ? (*root)->u.concat.n : (*root)->u.alt.n;

				for (i=0; i < n; i++) {
					if (!replace_placeholders(pool, &children[i], match)) {
						return 0;
					}
				}
			}
			break;

		case AST_EXPR_REPEAT:
		case AST_EXPR_GROUP:
			{
				struct ast_expr **inner = ((*root)->type == AST_EXPR_REPEAT)
					? &(*root)->u.repeat.e
					: &(*root)->u.group.e;

				if (!replace_placeholders(pool, inner, match)) {
					return 0;
				}
			}
			break;

		case AST_EXPR_SUBTRACT:
			{
				if (!replace_placeholders(pool, &(*root)->u.subtract.a, match)) {
					return 0;
				}

				if (!replace_placeholders(pool, &(*root)->u.subtract.b, match)) {
					return 0;
				}
			}
			break;

		case AST_EXPR_PLACEHOLDER:
			{
				int index = (*root)->u.placeholder.index;
				struct ast_expr *subst;

				assert(index >= 0 && index <= UCHAR_MAX);
				assert(match->placeholders[index] != NULL);

				subst = match->placeholders[index];
				if (!ast_expr_clone(pool, &subst)) {
					// signal error!
					return 0;
				}

				*root = subst;
			}
			break;

		case AST_EXPR_EMPTY:
		case AST_EXPR_LITERAL:
		case AST_EXPR_CODEPOINT:
		case AST_EXPR_ANCHOR:
		case AST_EXPR_RANGE:
		case AST_EXPR_TOMBSTONE:
			/* no children and nothing to replace here */
			break;
	}

	return 1;
}

static bool
rewrite_visitor(struct ast *ast, struct ast_match *match, void *ud)
{
	static const struct fsm_options opts_zero;

	struct rewrite_data *rewrite_data = ud;
	struct ast_expr *subst;
	struct fsm_options opts;
	const enum re_flags flags = 0UL;
	int i;


	assert(ast != NULL);
	assert(match != NULL);
	assert(rewrite_data != NULL);

	assert(match->node != NULL);
	assert(*match->node != NULL);

	opts = opts_zero;

	/* print matched AST subtree */
	fprintf(stderr, ">>> MATCH <<<\n");
	ast_print_subtree(stderr, &opts, flags, *match->node);


	fprintf(stderr, "\n--> %d placeholders:\n", match->nplaceholders);
	for (i=0; i < UCHAR_MAX+1; i++) {
		if (match->placeholders[i] != NULL) {
			fprintf(stderr, "--> placeholders index=%d:\n", i);
			ast_print_subtree(stderr, &opts, flags, match->placeholders[i]);
			fprintf(stderr, "\n");
		}
	}

	/* build subst AST subtree */
	subst = rewrite_data->subst->expr;
	if (!ast_expr_clone(&ast->pool, &subst)) {
		// signal error!
		return false;
	}

	/* replace placeholders in subst with their nodes */
	if (!replace_placeholders(&ast->pool, &subst, match)) {
		// signal error!
		return false;
	}

	/* replace matched subtree with subst subtree */
	*match->node = subst;

	rewrite_data->nsubst++;

	/* continue onward! */
	return true;
}

size_t
re_ast_rewrite(struct ast *ast, const struct ast *match, const struct ast *subst)
{
	struct rewrite_data rewrite_data;

	rewrite_data.subst = subst;
	rewrite_data.nsubst = 0;

	visit_matches(ast, match, rewrite_visitor, &rewrite_data);

	return rewrite_data.nsubst;
}

