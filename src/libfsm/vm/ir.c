/*
 * Copyright 2019 Shannon F. Stewman
 *
 * See LICENCE for the full copyright terms.
 */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <errno.h>
#include <ctype.h>

#include <fsm/fsm.h>
#include <fsm/vm.h>

#include "libfsm/internal.h"

#include "vm.h"

#include "print/ir.h"

// VM intermediate representation
//
//   each opcode represents a change to the VM state.  Each opcode should
//   loosely translate into a single VM instruction, and should map fairly
//   directly to machine code instructions.
//
// Current IR opcodes:
//
//   FETCH succ:BOOL
//     fetches the next byte in the string buffer.  SP is advanced, SB is updated.
//
//     If the string buffer is empty, FETCH will attempt to fill it.  If the
//     buffer cannot be filled with any bytes, matching will end.
//
//     If the 'succ' parameter is true, an empty buffer is treated as a successful
//     match.  Otherwise it's treated as a failed match.
//
//     When FETCH completes the PC is advanced to the next instruction.
//
//   STOP cond:COND arg:BYTE succ:BOOL
//
//     Stops matching if cond(SB,arg) is true.
//
//     If the 'succ' parameter is true, the match is successful, otherwise the
//     match fails.
//
//     When STOP completes, the PC is advanced to the next instruction.  If STOP
//     'cond' is true, STOP never completes.
//
//   BRANCH cond:COND arg:BYTE dest:ADDR
//
//     If cond(SB,arg) is true, sets the PC to the instruction at 'dest'.
//     Otherwise advances the PC to the next instruction.
//
// Potential future opcodes:
//
//   FINDB arg:BYTE succ:BOOL
//
//     Searches the buffer for the first a byte equal to 'arg'.
//
//     If a byte is found, advances SP to its position, sets SB to that byte, and
//     advanced PC to the next instruction.
//
//     Until a byte is found equal to 'arg', FINDB will attempt to refill the
//     buffer and continue the search.
//
//     If the buffer cannot be filled:
//       if 'succ' is true, the match is considered successful
//       otherwise, the match is considered a failure
//
//   FINDS str:ADDR succ:BOOL
//
//     Like FINDB, but searches the buffer for the string 'str' instead of a byte.
//     String is length-encoded.
//
//   MATCHS str:ADDR
//
//     Matches the bytes given by 'str' with the current bytes in the buffer.
//     SB is set to the number of bytes that match.
//
//     Note that 'str' is limited to 255 bytes.
//
//     This instruction must be followed by BRANCH instructions to decode where
//     the match failed.
//
//  TBRANCH table:ADDR
//
//     This is a "table branch" instruction.  The table should have 256
//     addresses (0-255).  This instruction sets PC to the address at table[SB]

#define ARRAYLEN(a) (sizeof (a) / sizeof ((a)[0]))

struct dfavm_op_ir_pool {
	struct dfavm_op_ir_pool *next;

	unsigned int top;
	struct dfavm_op_ir ops[1024];
};

struct dfa_table {
	long tbl[FSM_SIGMA_COUNT];

	const struct ir_state *ir_state;

	int nerr;
	int ndst;

	int dst_ind_lo;
	int dst_ind_hi;

	struct {
		long to;
		struct ir_range syms;
	} longest_run;

	struct {
		unsigned char sym[FSM_SIGMA_COUNT];
		int count;
	} discontig;

	struct {
		long to;
		int count;
	} mode;
};

static struct dfavm_op_ir_pool *
new_op_pool(struct dfavm_op_ir_pool *pcurr)
{
	static const struct dfavm_op_ir_pool zero;

	struct dfavm_op_ir_pool *p;

	p = malloc(sizeof *p);
	if (p != NULL) {
		*p = zero;
		p->next = pcurr;
	}

	return p;
}

static struct dfavm_op_ir *
pool_newop(struct dfavm_op_ir_pool **poolp)
{
	struct dfavm_op_ir_pool *p;

	assert(poolp != NULL);

	p = *poolp;

	if (p == NULL || p->top >= ARRAYLEN(p->ops)) {
		p = new_op_pool(*poolp);
		if (p == NULL) {
			return NULL;
		}

		*poolp = p;
	}

	return &p->ops[p->top++];
}

static void
print_op_ir(FILE *f, struct dfavm_op_ir *op)
{
	const char *cmp;
	int nargs = 0;

	cmp = cmp_name(op->cmp);

	// fprintf(f, "[%4lu] %1lu\t", (unsigned long)op->offset, (unsigned long)op->num_encoded_bytes);

	char opstr_buf[128];
	size_t nop = sizeof opstr_buf;
	char *opstr = &opstr_buf[0];
	size_t n;

	switch (op->instr) {
	case VM_OP_FETCH:
		n = snprintf(opstr, nop, "FETCH%c%s",
			(op->u.fetch.end_bits == VM_END_FAIL) ? 'F' : 'S',
			cmp);
		break;

	case VM_OP_STOP:
		n = snprintf(opstr, nop, "STOP%c%s",
			(op->u.stop.end_bits == VM_END_FAIL) ? 'F' : 'S',
			cmp);
		break;

	case VM_OP_BRANCH:
		{
			n = snprintf(opstr, nop, "BR%s", cmp);
		}
		break;

	default:
		n = snprintf(opstr, nop, "UNK_%d_%s", (int)op->instr, cmp);
	}

	opstr += n;
	nop   -= n;

	if (op->cmp != VM_CMP_ALWAYS) {
		if (isprint(op->cmp_arg)) {
			n = snprintf(opstr, nop, " '%c'", op->cmp_arg);
		} else {
			n = snprintf(opstr, nop, " 0x%02x",(unsigned)op->cmp_arg);
		}

		opstr += n;
		nop -= n;

		nargs++;
	}

	if (op->instr == VM_OP_BRANCH) {
		n = snprintf(opstr, nop, "%s [st=%lu]", ((nargs>0) ? "," : " "),
			(unsigned long)op->u.br.dest_state);

		opstr += n;
		nop   -= n;

		nargs++;
	}

	char comment[128];
	opstr = &comment[0];
	nop = sizeof comment;

	n = snprintf(opstr, nop, "; incoming: %u", op->num_incoming);
	opstr += n;
	nop   -= n;

	switch (op->instr) {
	case VM_OP_FETCH:
		n = snprintf(opstr, nop, ", state: %u", op->state);
		break;

	case VM_OP_BRANCH:
		n = snprintf(opstr, nop, ", dest: %u (%p)",
			op->u.br.dest_arg->index, (void *)op->u.br.dest_arg);
		break;

	default:
		n = 0;
		break;
	}

	fprintf(f, "%-40s %s\n", opstr_buf, comment);
}

static void
opasm_free(struct dfavm_assembler_ir *a, struct dfavm_op_ir *op)
{
	static const struct dfavm_op_ir zero;

	*op = zero;
	op->next = a->freelist;
	a->freelist = op;
}

static void
opasm_free_list(struct dfavm_assembler_ir *a, struct dfavm_op_ir *op)
{
	struct dfavm_op_ir *next;
	while (op != NULL) {
		next = op->next;
		opasm_free(a,op);
		op = next;
	}
}

static struct dfavm_op_ir *
opasm_new(struct dfavm_assembler_ir *a, enum dfavm_op_instr instr, enum dfavm_op_cmp cmp, unsigned char arg,
	const struct ir_state *ir_state)
{
	static const struct dfavm_op_ir zero;

	struct dfavm_op_ir *op;

	if (a->freelist != NULL) {
		op = a->freelist;
		a->freelist = op->next;
	} else {
		op = pool_newop(&a->pool);
	}

	if (op != NULL) {
		*op = zero;

		op->asm_index = a->count++;
		op->index = 0;
		op->state = DFAVM_NOSTATE;

		op->cmp   = cmp;
		op->instr = instr;

		op->cmp_arg = arg;
	}

	op->ir_state = ir_state;

	return op;
}

static struct dfavm_op_ir *
opasm_new_fetch(struct dfavm_assembler_ir *a, unsigned state, enum dfavm_op_end end,
	const struct ir_state *ir_state)
{
	struct dfavm_op_ir *op;

	op = opasm_new(a, VM_OP_FETCH, VM_CMP_ALWAYS, 0, ir_state);
	if (op != NULL) {
		op->state = state;
		op->u.fetch.end_bits = end;
	}

	return op;
}

static struct dfavm_op_ir *
opasm_new_stop(struct dfavm_assembler_ir *a, enum dfavm_op_cmp cmp, unsigned char arg, enum dfavm_op_end end,
	const struct ir_state *ir_state)
{
	struct dfavm_op_ir *op;

	op = opasm_new(a, VM_OP_STOP, cmp, arg, ir_state);
	if (op != NULL) {
		op->u.stop.end_bits = end;
	}

	return op;
}

static struct dfavm_op_ir *
opasm_new_branch(struct dfavm_assembler_ir *a, enum dfavm_op_cmp cmp, unsigned char arg, uint32_t dest_state,
	const struct ir_state *ir_state)
{
	struct dfavm_op_ir *op;

	assert(dest_state < a->nstates);

	op = opasm_new(a, VM_OP_BRANCH, cmp, arg, ir_state);
	if (op != NULL) {
		// op->u.br.dest  = VM_DEST_FAR;  // start with all branches as 'far'
		op->u.br.dest_state = dest_state;
	}

	return op;
}

void
dfavm_opasm_finalize_op(struct dfavm_assembler_ir *a)
{
	struct dfavm_op_ir_pool *pool_curr, *pool_next;

	if (a == NULL) {
		return;
	}

	free(a->ops);

	for (pool_curr = a->pool; pool_curr != NULL; pool_curr = pool_next) {
		pool_next = pool_curr->next;
		free(pool_curr);
	}
}

static int
cmp_mode_dests(const void *a, const void *b) {
	const long *va = a;
	const long *vb = b;

	return (*va > *vb) - (*va < *vb);
}

static void
analyze_table(struct dfa_table *table)
{
	static const struct dfa_table zero;

	int i, lo, nerr, ndst, max_run;
	int run_lo, run_hi;
	int dst_ind_lo, dst_ind_hi;
	long dlo, run_to;

	long mode_dests[FSM_SIGMA_COUNT];

	lo = 0;
	dlo = table->tbl[0];

	nerr = (dlo == -1) ? 1 : 0;
	ndst = 1-nerr;

	dst_ind_lo = (dlo == -1) ? -1 : 0;
	dst_ind_hi = dst_ind_lo;

	max_run = 0;
	run_lo = -1;
	run_hi = -1;
	run_to = -1;

	mode_dests[0] = dlo;
	table->discontig = zero.discontig;

	for (i=1; i < FSM_SIGMA_COUNT+1; i++) {
		long dst = -1;

		if (i < FSM_SIGMA_COUNT) {
			dst = table->tbl[i];
			nerr += (dst == -1);
			ndst += (dst != -1);

			if (dst >= 0) {
				dst_ind_hi = i;
				if (dst_ind_lo < 0) {
					dst_ind_lo = i;
				}
			}

			mode_dests[i] = dst;
		}

		if (i == FSM_SIGMA_COUNT || dst != dlo) {
			int len = i - lo;

			if (len > max_run) {
				max_run = len;
				run_lo  = lo;
				run_hi  = i-1;
				run_to  = dlo;
			}

			if (len == 1) {
				table->discontig.sym[table->discontig.count++] = lo;
			}

			lo = i;
			dlo = dst;
		}
	}

	table->nerr = nerr;
	table->ndst = ndst;

	table->dst_ind_lo = dst_ind_lo;
	table->dst_ind_hi = dst_ind_hi;

	if (max_run > 0) {
		table->longest_run.to = run_to;
		table->longest_run.syms.start = run_lo;
		table->longest_run.syms.end   = run_hi;
	}

	table->mode.to = -1;
	table->mode.count = 0;

	// determine the mode
	qsort(&mode_dests[0], sizeof mode_dests / sizeof mode_dests[0], sizeof mode_dests[0], cmp_mode_dests);

	for (lo=0,i=1; i < FSM_SIGMA_COUNT+1; i++) {
		if (i == FSM_SIGMA_COUNT || mode_dests[lo] != mode_dests[i]) {
			int count = i-lo;
			if (count > table->mode.count) {
				table->mode.to    = mode_dests[lo];
				table->mode.count = count;
				lo = i;
			}
		}
	}
}

static int
xlate_table_ranges(struct dfavm_assembler_ir *a, struct dfa_table *table, struct dfavm_op_ir **opp)
{
	int i,lo;
	int count = 0;

	lo = 0;
	for (i=1; i < FSM_SIGMA_COUNT; i++) {
		int64_t dst;
		struct dfavm_op_ir *op;

		assert(lo < FSM_SIGMA_COUNT);

		if (table->tbl[lo] != table->tbl[i]) {
			dst = table->tbl[lo];

			/* emit instr */
			int arg = i-1;
			enum dfavm_op_cmp cmp = (i > lo+1) ? VM_CMP_LE : VM_CMP_EQ;

			op = (dst < 0)
				? opasm_new_stop(a, cmp, arg, VM_END_FAIL, table->ir_state)
				: opasm_new_branch(a, cmp, arg, dst, table->ir_state);

			if (op == NULL) {
				return -1;
			}

			*opp = op;
			opp = &(*opp)->next;
			count++;

			lo = i;
		}
	}

	if (lo < FSM_SIGMA_COUNT) {
		int64_t dst = table->tbl[lo];
		*opp = (dst < 0)
			? opasm_new_stop(a, VM_CMP_ALWAYS, 0, VM_END_FAIL, table->ir_state)
			: opasm_new_branch(a, VM_CMP_ALWAYS, 0, dst, table->ir_state);
		if (*opp == NULL) {
			return -1;
		}
		opp = &(*opp)->next;
		count++;
	}

	return count;
}

static int
xlate_table_cases(struct dfavm_assembler_ir *a, struct dfa_table *table, struct dfavm_op_ir **opp)
{
	int i, count = 0;
	int64_t mdst = table->mode.to;

	for (i=0; i < FSM_SIGMA_COUNT; i++) {
		int64_t dst;

		dst = table->tbl[i];

		if (dst == mdst) {
			continue;
		}

		*opp = (dst < 0)
			? opasm_new_stop(a, VM_CMP_EQ, i, VM_END_FAIL, table->ir_state)
			: opasm_new_branch(a, VM_CMP_EQ, i, dst, table->ir_state);
		if (*opp == NULL) {
			return -1;
		}
		opp = &(*opp)->next;
		count++;
	}

	*opp = (mdst < 0)
		? opasm_new_stop(a, VM_CMP_ALWAYS, 0, VM_END_FAIL, table->ir_state)
		: opasm_new_branch(a, VM_CMP_ALWAYS, 0, mdst, table->ir_state);
	if (*opp == NULL) {
		return -1;
	}
	opp = &(*opp)->next;
	count++;

	return count;
}

static int
initial_translate_table(struct dfavm_assembler_ir *a, struct dfa_table *table, struct dfavm_op_ir **opp)
{
	int count, best_count;
	struct dfavm_op_ir *op, *best_op;

	assert(a     != NULL);
	assert(table != NULL);
	assert(opp   != NULL);

	assert(*opp == NULL);

	analyze_table(table);

	// handle a couple of special cases...
	if (table->ndst == 1) {
		int sym;
		long dst;

		sym = table->dst_ind_lo;

		assert(sym >= 0);
		assert(sym == table->dst_ind_hi);

		dst = table->tbl[sym];

		assert(dst >= 0);
		assert((size_t)dst < a->nstates);

		*opp = opasm_new_stop(a, VM_CMP_NE, sym, VM_END_FAIL, table->ir_state);
		if (*opp == NULL) {
			return -1;
		}
		opp = &(*opp)->next;

		*opp = opasm_new_branch(a, VM_CMP_ALWAYS, 0, dst, table->ir_state);
		if (*opp == NULL) {
			return -1;
		}
		opp = &(*opp)->next;

		return 0;
	}

	best_op = NULL;
	best_count = xlate_table_ranges(a, table, &best_op);

	op = NULL;
	count = xlate_table_cases(a, table, &op);

	if (count < best_count) {
		opasm_free_list(a,best_op);
		best_op = op;
	} else {
		opasm_free_list(a,op);
	}

	*opp = best_op;

	return 0;
}

static void
ranges_to_table(long table[FSM_SIGMA_COUNT], const struct ir_range *r, const size_t n, const long to)
{
	size_t i;

	for (i=0; i < n; i++) {
		int c, end;

		end = r[i].end;
		for (c = r[i].start; c <= end; c++) {
			table[c] = to;
		}
	}
}

static void
error_to_table(struct dfa_table *table, const struct ir_error *err)
{
	ranges_to_table(table->tbl, err->ranges, err->n, -1);
}

static void
group_to_table(struct dfa_table *table, const struct ir_group *grp)
{
	ranges_to_table(table->tbl, grp->ranges, grp->n, grp->to);
}

static void
dfa_table_init(struct dfa_table *table, long default_dest, const struct ir_state *ir_state)
{
	static const struct dfa_table zero;
	int i;

	assert(table != NULL);

	*table = zero;

	table->ir_state = ir_state;

	for (i=0; i < FSM_SIGMA_COUNT; i++) {
		table->tbl[i] = default_dest;
	}
}

static int
initial_translate_partial(struct dfavm_assembler_ir *a, struct ir_state *st, struct dfavm_op_ir **opp)
{
	struct dfa_table table;
	size_t i, ngrps;

	assert(st->strategy == IR_PARTIAL);

	dfa_table_init(&table, -1, st);

	ngrps = st->u.partial.n;
	for (i=0; i < ngrps; i++) {
		group_to_table(&table, &st->u.partial.groups[i]);
	}

	return initial_translate_table(a, &table, opp);
}

static int
initial_translate_dominant(struct dfavm_assembler_ir *a, struct ir_state *st, struct dfavm_op_ir **opp)
{
	struct dfa_table table;
	size_t i, ngrps;

	assert(st->strategy == IR_DOMINANT);

	dfa_table_init(&table, st->u.dominant.mode, st);

	ngrps = st->u.dominant.n;
	for (i=0; i < ngrps; i++) {
		group_to_table(&table, &st->u.dominant.groups[i]);
	}

	return initial_translate_table(a, &table, opp);
}

static int
initial_translate_error(struct dfavm_assembler_ir *a, struct ir_state *st, struct dfavm_op_ir **opp)
{
	struct dfa_table table;
	size_t i, ngrps;

	assert(st->strategy == IR_ERROR);

	dfa_table_init(&table, st->u.error.mode, st);

	error_to_table(&table, &st->u.error.error);

	ngrps = st->u.error.n;
	for (i=0; i < ngrps; i++) {
		group_to_table(&table, &st->u.error.groups[i]);
	}

	return initial_translate_table(a, &table, opp);
}

static struct dfavm_op_ir *
initial_translate_state(struct dfavm_assembler_ir *a, const struct ir *ir, size_t ind)
{
	struct ir_state *st;
	struct dfavm_op_ir **opp;

	st = &ir->states[ind];
	opp = &a->ops[ind];

	if (st->isend && st->strategy == IR_SAME && st->u.same.to == ind) {
		*opp = opasm_new_stop(a, VM_CMP_ALWAYS, 0, VM_END_SUCC, st);
		(*opp)->state = ind;
		return a->ops[ind];
	}

	*opp = opasm_new_fetch(a, ind, (st->isend) ? VM_END_SUCC : VM_END_FAIL, st);
	opp = &(*opp)->next;
	assert(*opp == NULL);

	switch (st->strategy) {
	case IR_NONE:
		*opp = opasm_new_stop(a, VM_CMP_ALWAYS, 0, st->isend ? VM_END_SUCC : VM_END_FAIL, st);
		opp = &(*opp)->next;
		break;

	case IR_SAME:
		*opp = opasm_new_branch(a, VM_CMP_ALWAYS, 0, st->u.same.to, st);
		opp = &(*opp)->next;
		break;

	case IR_COMPLETE:
		/* groups should be sorted */

	/* _currently_ expand these into a table and build the
	 * transitions off of the table.  We can do this more
	 * intelligently.
	 */
	case IR_PARTIAL:
		if (initial_translate_partial(a, st, opp) < 0) {
			return NULL;
		}
		break;

	case IR_DOMINANT:
		if (initial_translate_dominant(a, st, opp) < 0) {
			return NULL;
		}
		break;

	case IR_ERROR:
		if (initial_translate_error(a, st, opp) < 0) {
			return NULL;
		}
		break;

	case IR_TABLE:
		/* currently not used */
		fprintf(stderr, "implement IR_TABLE!\n");
		abort();

	default:
		fprintf(stderr, "unknown strategy!\n");
		abort();
	}

	return a->ops[ind];
}

static int
initial_translate(const struct ir *ir, struct dfavm_assembler_ir *a)
{
	size_t i,n;

	n = a->nstates;

	for (i=0; i < n; i++) {
		a->ops[i] = initial_translate_state(a, ir, i);
	}

	return 0;
}

static void
fixup_dests(struct dfavm_assembler_ir *a)
{
	size_t i,n;

	n = a->nstates;
	for (i=0; i < n; i++) {
		struct dfavm_op_ir *op;

		for (op = a->ops[i]; op != NULL; op = op->next) {
			if (op->instr != VM_OP_BRANCH) {
				continue;
			}

			op->u.br.dest_arg = a->ops[op->u.br.dest_state];
			op->u.br.dest_arg->num_incoming++;
		}
	}
}

struct dfavm_op_ir **find_opchain_end(struct dfavm_op_ir **opp)
{
	assert(opp != NULL);

	while (*opp != NULL) {
		opp = &(*opp)->next;
	}

	return opp;
}

static void
dump_states(FILE *f, const struct dfavm_assembler_ir *a);

static void
eliminate_unnecessary_branches(struct dfavm_assembler_ir *a)
{
	int count;

	do {
		struct dfavm_op_ir **opp;

		count = 0;

		/* basic pass to eliminate unnecessary branches; branches to the
		 * next instruction can be elided
		 */
		for (opp = &a->linked; *opp != NULL;) {
			struct dfavm_op_ir *next, *dest;

			if ((*opp)->instr != VM_OP_BRANCH) {
				opp = &(*opp)->next;
				continue;
			}

			if ((*opp)->num_incoming > 0) {
				opp = &(*opp)->next;
				continue;
			}

			dest = (*opp)->u.br.dest_arg;
			next = (*opp)->next;

			assert(dest != NULL);

			if (dest == next) {
				// branch is to next instruction, eliminate
				//
				// condition doesn't matter since both cond and !cond
				// will end up at the same place
				*opp = next;
				next->num_incoming--;
				count++;
				continue;
			}

			// Rewrites:
			//   curr: BRANCH to next->next on condition C
			//   next: BRANCH ALWAYS to dest D
			// to:
			//   curr: BRANCH to dest D on condition not(C)
			//   next: <deleted>
			// 
			// Rewrites:
			//   curr: BRANCH to next->next on condition C
			//   next: STOP(S/F) ALWAYS
			// to:
			//   curr: STOP(S/F) on condition not(C)
			//   next: <deleted>
			//
			if (next != NULL && dest == next->next &&
					(next->instr == VM_OP_BRANCH || next->instr == VM_OP_STOP) &&
					(next->num_incoming == 0) &&
					(*opp)->cmp != VM_CMP_ALWAYS && next->cmp == VM_CMP_ALWAYS) {
				/* rewrite last two instructions to eliminate a
				 * branch
				 */
				struct dfavm_op_ir rewrite = *next;  // swapped
				int ok = 1;

				// invert the condition of current branch
				switch ((*opp)->cmp) {
				case VM_CMP_LT: rewrite.cmp = VM_CMP_GE; break;
				case VM_CMP_LE: rewrite.cmp = VM_CMP_GT; break;
				case VM_CMP_EQ: rewrite.cmp = VM_CMP_NE; break;
				case VM_CMP_GE: rewrite.cmp = VM_CMP_LT; break;
				case VM_CMP_GT: rewrite.cmp = VM_CMP_LE; break;
				case VM_CMP_NE: rewrite.cmp = VM_CMP_EQ; break;

				case VM_CMP_ALWAYS:
				default:
					// something is wrong
					ok = 0;
					break;
				}

				if (ok) {
					rewrite.cmp_arg = (*opp)->cmp_arg;

					**opp = rewrite;

					assert(dest->num_incoming > 0);
					dest->num_incoming--;

					count++;
					continue;
				}
			}

			opp = &(*opp)->next;
		}

	} while (count > 0);
}

#if 0
struct ir_edge {
	struct dfavm_op_ir *src;
	struct dfavm_op_ir *dst;
};

struct ir_predecessor_edges {
	uint32_t *offsets;
	struct ir_edge *edges;
};

static int
pred_edge_cmp(const void *a, const void *b)
{
	const struct ir_edge *ea = a;
	const struct ir_edge *eb = b;

	if (ea->dst != eb->dst) {
		return (ea->dst->asm_index > eb->dst->asm_index) - (ea->dst->asm_index < eb->dst->asm_index);
	}

	return (ea->src->asm_index > eb->src->asm_index) - (ea->src->asm_index < eb->src->asm_index);
}

static struct ir_predecessor_edges *
build_pred_edges(struct dfavm_assembler_ir *a)
{
	static const struct ir_predecessor_edges zero;

	struct dfavm_op_ir *op;
	struct ir_predecessor_edges *pred;
	size_t num_edges, edge_index, state_edge_count, state_index;
	uint32_t curr_asm_ind;

	/* count edges */
	num_edges = 0;
	for (op = a->linked; op != NULL; op = op->next) {
		if (op->next != NULL) {
			num_edges++;
		}

		if (op->instr == VM_OP_BRANCH) {
			num_edges++;
		}
	}

	/*
	printf("found %zu edges\n", num_edges);
	*/

	pred = malloc(sizeof *pred);
	if (pred == NULL) {
		return NULL;
	}

	*pred = zero;

	pred->offsets = calloc(a->count+1, sizeof *pred->offsets);
	if (pred->offsets == NULL) {
		goto error;
	}

	pred->edges = calloc(num_edges, sizeof *pred->edges);
	if (pred->edges == NULL) {
		goto error;
	}

	edge_index = 0;
	/* fill in edges */
	for (op = a->linked; op != NULL; op = op->next) {
		if (op->next != NULL) {
			assert(edge_index < num_edges);

			pred->edges[edge_index].src = op;
			pred->edges[edge_index].dst = op->next;
			edge_index++;
		}

		if (op->instr == VM_OP_BRANCH) {
			assert(edge_index < num_edges);

			pred->edges[edge_index].src = op;
			pred->edges[edge_index].dst = op->u.br.dest_arg;
			edge_index++;
		}
	}

	assert(edge_index == num_edges);

	/* sort edges */
	qsort(&pred->edges[0], num_edges, sizeof *pred->edges, pred_edge_cmp);

	/* count unique dests and setup offsets */
	curr_asm_ind = pred->edges[0].dst->asm_index;
	state_edge_count = 1;

	for (edge_index=1; edge_index < num_edges; edge_index++) {
		if (pred->edges[edge_index].dst->asm_index != curr_asm_ind) {
			pred->offsets[1+curr_asm_ind] = state_edge_count;
			curr_asm_ind = pred->edges[edge_index].dst->asm_index;
			state_edge_count = 1;
		} else {
			state_edge_count++;
		}
	}

	pred->offsets[1+curr_asm_ind] = state_edge_count;

	for (state_index=0; state_index < a->count; state_index++) {
		pred->offsets[state_index+1] += pred->offsets[state_index];
	}

	/*
	for (state_index=0; state_index < a->count+1; state_index++) {
		printf("edge offset[%4zu] = %lu\n", state_index, (unsigned long)pred->offsets[state_index]);
	}
	*/

	return pred;

error:
	if (pred != NULL) {
		free(pred->offsets);
		free(pred->edges);
		free(pred);
	}

	return NULL;
}

static struct dfavm_op_ir *
idom_intersect(struct dfavm_op_ir *a, struct dfavm_op_ir *b)
{
	while (a != b) {
		while (a->index < b->index) {
			a = a->idom;
		}

		while (b->index < a->index) {
			b = b->idom;
		}
	}

	return a;
}

static void
print_all_states(const struct dfavm_assembler_ir *a);

/* TODO: this method is very naive.  replace with a better method! */
static int
identify_idoms(struct dfavm_assembler_ir *a)
{
	struct ir_predecessor_edges *pred_edges = NULL;
	struct dfavm_op_ir *op, **ordered, **stack, *start;
	uint32_t ordered_top, stack_top;
	bool has_changed;
	int ret;

	ret = -1;

	/* allocate temporary structures */
	pred_edges = build_pred_edges(a);
	if (pred_edges == NULL) {
		goto cleanup;
	}

	ordered = calloc(2*a->count, sizeof *ordered);
	if (ordered == NULL) {
		goto cleanup;
	}

	stack = &ordered[a->count];

	/* clear visited bit, set idom to NULL */
	for (op=a->linked; op != NULL; op=op->next) {
		op->idom = NULL;
		op->visited = 0;
	}

	start = a->linked;

	stack[0]  = start;
	stack_top = 1;
	ordered_top = 0;
	start->visited = 1;
	while (stack_top > 0) {
		struct dfavm_op_ir *node;

		assert(stack_top > 0);

		node = stack[stack_top-1];

		assert(node != NULL);
		assert(node->visited);

		if (node->next != NULL && !node->next->visited) {
			assert(stack_top < a->count);
			stack[stack_top++] = node->next;
			node->next->visited = 1;
		} else if (node->instr == VM_OP_BRANCH && node->u.br.dest_arg != NULL && !node->u.br.dest_arg->visited) {
			struct dfavm_op_ir *dest;

			dest = node->u.br.dest_arg;
			assert(dest != NULL);
			assert(!dest->visited);

			stack[stack_top++] = dest;
			dest->visited = 1;
		} else {
			assert(ordered_top < a->count);

			/* index member is only assigned after
			 * optimizations.  We can borrow it for now
			 */
			node->index = ordered_top;
			ordered[ordered_top++] = node;
			stack_top--;
		}
	}

	start->idom = start;

	/*
	dump_states(stdout, a);
	*/

	unsigned long iter = 0;
	/* iterate until the sets no longer change */
	for (has_changed = true; has_changed; iter++) {
		uint32_t ind;

		/*
		printf("---[ iter %lu ]---\n", iter);
		*/
		has_changed = false;

		// iterate in reverse postorder
		for (ind = ordered_top; ind > 0; ind--) {
			struct dfavm_op_ir *node;

			node = ordered[ind-1];
			if (node != start) {
				const uint32_t idx = node->asm_index;
				const uint32_t ei0 = pred_edges->offsets[idx+0];
				const uint32_t ei1 = pred_edges->offsets[idx+1];

				struct dfavm_op_ir *new_idom;
				uint32_t ei;

				/*
				printf("node: %lu:%p idom=%lu:%p\n",
					(unsigned long)node->index, (void *)node,
					(node->idom) ?  (unsigned long)node->idom->index : 0UL,
					(node->idom) ?  (void *)node->idom : NULL);
				printf("  - asm_index = %lu, offsets: %lu ... %lu\n",
					(unsigned long)idx, (unsigned long)ei0, (unsigned long)ei1);
				*/

				new_idom = NULL;
				for (ei=ei0; ei < ei1; ei++) {
					struct dfavm_op_ir *pred;

					assert(pred_edges->edges[ei].dst == node);

					pred = pred_edges->edges[ei].src;
					/*
					printf("  - pred: %lu:%p idom=%lu:%p\n",
						(unsigned long)pred->index, (void *)pred,
						pred->idom ? (unsigned long)pred->idom->index : 0UL,
						pred->idom ? (void *)pred->idom : NULL);
					*/

					if (pred->idom == NULL) {
						continue;
					}

					if (new_idom == NULL) {
						new_idom = pred;
					} else {
						/*
						printf("  - intersect(%lu:%p, %lu:%p)\n",
							(unsigned long)new_idom->index, (void *)new_idom,
							(unsigned long)pred->index, (void *)pred);
						*/

						new_idom = idom_intersect(pred,new_idom);
					}
					/*
					printf("  - new_idom = %lu:%p\n",
						(unsigned long)new_idom->index, (void *)new_idom);
					*/
				}

				assert(new_idom != NULL);

				if (node->idom != new_idom) {
					node->idom = new_idom;
					/*
					printf("  * new_idom = %lu:%p\n",
						(unsigned long)new_idom->index, (void *)new_idom);
					*/
					has_changed = true;
				}
			}
		}
	}

	/*
	dump_states(stdout, a);
	*/

	/* debug dump of dominators */
	/*
	printf("--[ idoms ]--\n");
	{
		uint32_t i;
		for (i=0; i < ordered_top; i++) {
			printf("[%6lu:%p] idom %6lu:%p\n",
				(unsigned long)ordered[i]->index, (void *)ordered[i],
				(unsigned long)ordered[i]->idom->index, (void *)ordered[i]->idom);
		}
	}
	*/

	/* return success! */
	ret = 0;

cleanup:
	if (pred_edges != NULL) {
		free(pred_edges->offsets);
		free(pred_edges->edges);
		free(pred_edges);
	}

	free(ordered);

	for (op=a->linked; op != NULL; op=op->next) {
		op->visited = 0;
		op->index = 0;
	}

	return ret;
}

static bool
dominates(struct dfavm_op_ir *node, struct dfavm_op_ir *dom)
{
	struct dfavm_op_ir *idom;

	idom = node->idom;

	/* struct dfavm_op_ir *node; */
	if (idom == dom) {
		return true;
	}

	while (idom != idom->idom) {
		if (idom == dom) {
			return true;
		}

		idom = idom->idom;
	}

	return idom == dom;
}

struct ir_loop_entry {
	struct dfavm_op_ir *head;
	struct dfavm_op_ir *tail;
};

struct ir_loop {
	size_t len;
	size_t cap;

	struct ir_loop_entry *entries;
};

static int
cmp_loop(const void *a, const void *b)
{
	const struct ir_loop_entry *la = a;
	const struct ir_loop_entry *lb = b;

	if (la->head == lb->head) {
		return (la->tail->index > lb->tail->index) - (la->tail->index < lb->tail->index);
	}

	return (la->head->index > lb->head->index) - (la->head->index < lb->head->index);
}

static void
free_loops(struct ir_loop *l)
{
	if (l != NULL) {
		free(l->entries);
		free(l);
	}
}

static int
add_loop(struct ir_loop *l, struct dfavm_op_ir *head, struct dfavm_op_ir *tail)
{
	assert(l != NULL);
	if (l->len >= l->cap) {
		size_t new_cap;
		struct ir_loop_entry *new_entries;

		if (l->cap < 16) {
			new_cap = 16;
		} else if (l->cap < 2048) {
			new_cap = 2*l->cap;
		} else {
			new_cap = l->cap + l->cap/2;
		}

		new_entries = realloc(l->entries, new_cap * sizeof *new_entries);
		if (new_entries == NULL) {
			return 0;
		}

		l->cap = new_cap;
		l->entries = new_entries;
	}

	assert(l->len < l->cap);
	assert(l->entries != NULL);

	l->entries[l->len].head = head;
	l->entries[l->len].tail = tail;

	l->len++;

	return 1;
}

static struct ir_loop *
identify_loops(struct dfavm_assembler_ir *a)
{
	struct dfavm_op_ir *op;
	struct ir_loop *loops;
	unsigned ind;

	loops = malloc(sizeof *loops);
	if (loops == NULL) {
		return NULL;
	}

	loops->entries = NULL;
	loops->len = loops->cap = 0;

	/* index member is not set until after optimizations.
	 * we borrow it here to ensure that loops are ordered
	 */

	for (ind=0,op=a->linked; op != NULL; ind++,op=op->next) {
		op->index = ind;
	}

	for (op=a->linked; op != NULL; op=op->next) {
		if (op->instr == VM_OP_BRANCH) {
			struct dfavm_op_ir *dest;

			dest = op->u.br.dest_arg;
			if (dominates(op, dest)) {
				if (!add_loop(loops, dest, op)) {
					goto error;
				}
			}
		}
	}

	if (loops->len > 0) {
		qsort(loops->entries, loops->len, sizeof loops->entries[0], cmp_loop);
	}

	for (op=a->linked; op != NULL; op=op->next) {
		op->index = 0;
	}

	return loops;

error:
	free_loops(loops);

	for (op=a->linked; op != NULL; op=op->next) {
		op->index = 0;
	}

	return NULL;
}

static int
optimize_loops(struct dfavm_assembler_ir *a)
{
	struct ir_loop *loops;

	/* identify immediate dominators */
	if (identify_idoms(a) < 0) {
		return -1;
	}

	/* identify natural loops */
	loops = identify_loops(a);
	if (loops == NULL) {
		return -1;
	}

	dump_states(stdout, a);
	if (loops->len > 0) {
		size_t i;
		printf("---[ loops: %zu ]---\n", loops->len);
		for (i=0; i < loops->len; i++) {
			printf("[%4zu] head %4lu:%p  tail %4lu:%p\n", i,
				(unsigned long)loops->entries[i].head->asm_index, (void *)loops->entries[i].head,
				(unsigned long)loops->entries[i].tail->asm_index, (void *)loops->entries[i].tail);
		}
	} else {
		printf("\nno loops.\n\n");
	}

	/* analyze natural loops:
	 * - single-character chokepoints
	 * - fixed string portions
	 * - multiple fixed string portions
	 */

	free_loops(loops);

	return 0;
}
#endif /* 0 */

static void
order_basic_blocks(struct dfavm_assembler_ir *a)
{
	size_t i,n;
	struct dfavm_op_ir **opp;
	struct dfavm_op_ir *st;

	/* replace this with something that actually
	 * orders basic blocks ...
	 */

	n = a->nstates;

	/* mark all states as !in_trace */
	for (i=0; i < n; i++) {
		a->ops[i]->in_trace = 0;
	}

	opp = &a->linked;
	*opp = NULL;

	st = a->ops[a->start];
	while (st != NULL) {
		struct dfavm_op_ir *branches[FSM_SIGMA_COUNT];  /* at most FSM_SIGMA_COUNT branches per state */
		struct dfavm_op_ir *instr;
		size_t j,count;

		/* add state to trace */
		*opp = st;
		opp = find_opchain_end(opp);

		assert(opp != NULL);
		assert(*opp == NULL);

		st->in_trace = 1;

		/* look for branches to states not in the trace.
		 * Start at the last branch and work toward the first.
		 */
		count = 0;
		for (instr=st; instr != NULL; instr=instr->next) {
			if (instr->instr == VM_OP_BRANCH) {
				branches[count++] = instr;
			}
			assert(count <= sizeof branches/sizeof branches[0]);
		}

		st = NULL;
		for (j=count; j > 0; j--) {
			struct dfavm_op_ir *dest = branches[j-1]->u.br.dest_arg;
			if (!dest->in_trace) {
				st = dest;
				break;
			}
		}

		if (st == NULL) {
			/* look for a new state ... */
			for (j=0; j < n; j++) {
				if (!a->ops[j]->in_trace) {
					st = a->ops[j];
					break;
				}
			}
		}
	}
}

static uint32_t
assign_opcode_indexes(struct dfavm_assembler_ir *a)
{
	uint32_t index;
	struct dfavm_op_ir *op;

	assert(a != NULL);
	assert(a->linked != NULL);

	index = 0;
	for (op=a->linked; op != NULL; op = op->next) {
		op->index = index++;
	}

	return index;
}

static void
dump_states(FILE *f, const struct dfavm_assembler_ir *a)
{
	struct dfavm_op_ir *op;

	for (op = a->linked; op != NULL; op = op->next) {
		if (op->state != DFAVM_NOSTATE) {
			unsigned state = op->state;
			fprintf(f, "\n%p ;;; state %u (index: %lu, asm_index: %lu) %s\n",
				(void *)op, state, (unsigned long)op->index, (unsigned long)op->asm_index,
				(state == a->start) ? "(start)" : "");
		}

		fprintf(f, "%p | %6zu | %6lu |  ", (void *)op, (unsigned long)op->index, (unsigned long)op->asm_index);
		print_op_ir(f, op);
	}
}

void
dfavm_print_opcodes(FILE *f, const struct dfavm_assembler_ir *a)
{
	dump_states(f, a);
}

static void
print_all_states(const struct dfavm_assembler_ir *a)
{
	dump_states(stderr, a);
}

static void
print_sym_with_escaping(int sym, FILE *f)
{
	if (!isprint(sym)) {
		fprintf(f, "\\x%02x", sym);
		return;
	}

	if (sym == '[' || sym == ']' || sym == '-' || sym == '\\') {
		fputc('\\', f);
	}

	fputc(sym, f);
}

static void
print_sym_set(const struct bm *bm, FILE *f)
{
	int start, prev, bit;

	fputc('[', f);

	start = prev = bit = -1;
	for (;;) {
		bit = bm_next(bm, bit, 1);

		if (prev == -1 || bit > prev+1 || bit > UCHAR_MAX) {
			if (start != -1) {
				if (prev > start+1) {
					fputc('-', f);
					print_sym_with_escaping(prev, f);
				} else if (prev == start+1) {
					print_sym_with_escaping(prev, f);
				}
			}

			if (bit > UCHAR_MAX) {
				break;
			}

			print_sym_with_escaping(bit, f);

			start = bit;
		}

		prev = bit;
	}

	fputc(']', f);
}

static void
loop_analysis_print_network(const struct dfavm_loop_analysis *a, FILE *f)
{
	size_t i;

	fprintf(f, "---[ loop analysis : %zu nstates ]---\n", a->nstates);

	for (i = 0; i < a->nstates; i++) {
		size_t j;

		fprintf(f, "%6zu | %zu edges | RPorder: %u | idom: %u%s%s\n",
			i, a->states[i].nedges, a->states[i].order, a->states[i].idom,
			(i == a->start) ? " | start" : "",
			(a->states[i].isend) ? " | end" : "");

		fprintf(f, "       - no edges: ");
		print_sym_set(&a->states[i].no_edge_syms, f);
		fprintf(f, "\n");

		for (j=0; j < a->states[i].nedges; j++) {
			fprintf(f, "       - edge: %u ", a->states[i].edges[j].dst);
			print_sym_set(&a->states[i].edges[j].sym_bits, f);
			fprintf(f, "\n");
		}
	}
}

static void
dump_loop_analysis(const struct dfavm_loop_analysis *a)
{
	loop_analysis_print_network(a, stderr);
}

static int
loop_ir_node_from_groups(struct dfavm_loop_ir *node, size_t ngroup, const struct ir_group *groups)
{
	size_t grp;

	node->nedges = ngroup;
	node->edges = calloc(ngroup, sizeof node->edges[0]);
	if (node->edges == NULL) {
		return -1;
	}

	bm_setall(&node->no_edge_syms);

	for (grp=0; grp < ngroup; grp++) {
		unsigned to;
		size_t i,n;

		to = groups[grp].to;
		n  = groups[grp].n;

		node->edges[grp].dst = to;

		for (i=0; i < n; i++) {
			bm_setrange(&node->edges[grp].sym_bits, groups[grp].ranges[i].start, groups[grp].ranges[i].end);
			bm_clearrange(&node->no_edge_syms, groups[grp].ranges[i].start, groups[grp].ranges[i].end);
		}
	}

	return 0;
}

static int loop_ir_node_from_dominant(struct dfavm_loop_ir *node, const struct ir_state *ir_st)
{
	struct bm dom_edge_bits;
	size_t edge,grp,ngrp,dom_ind;
	unsigned dom;
	const struct ir_group *groups;

	bm_setall(&dom_edge_bits);

	ngrp = ir_st->u.dominant.n;
	dom = ir_st->u.dominant.mode;
	groups = ir_st->u.dominant.groups;

	bm_clear(&node->no_edge_syms);

	node->nedges = ngrp+1;
	node->edges = calloc(ngrp+1, sizeof node->edges[0]);
	if (node->edges == NULL) {
		return -1;
	}

	dom_ind = ngrp;
	for (grp=0, edge=0; grp < ngrp; grp++, edge++) {
		unsigned to = groups[grp].to;
		size_t i,nrange;

		assert(to != dom);

		if (dom_ind == ngrp && to > dom) {
			/* mark the position and fill this in afterwards */
			dom_ind = edge++;
		}

		node->edges[edge].dst = to;

		nrange = groups[grp].n;
		for (i=0; i < nrange; i++) {
			unsigned char start, end;

			start = groups[grp].ranges[i].start;
			end   = groups[grp].ranges[i].end;

			bm_setrange(&node->edges[edge].sym_bits, start, end);
			bm_clearrange(&dom_edge_bits, start, end);

			/*
			fprintf(stderr, "dom: %u edge: %zu to: %u %d - %d  | bits: ", dom, edge, to, start, end);
			print_sym_set(&node->edges[grp].sym_bits, stderr);
			fprintf(stderr, " | dom bits: ");
			print_sym_set(&dom_edge_bits, stderr);
			fprintf(stderr, "\n");
			*/
		}
	}

	/* fill in the dominant edge... */
	node->edges[dom_ind].dst = dom;
	node->edges[dom_ind].sym_bits = dom_edge_bits;

	return 0;
}

static int loop_ir_node_from_error(struct dfavm_loop_ir *node, const struct ir_state *ir_st)
{
	struct bm mode_edge_bits;
	size_t edge,grp,ngrp,mode_ind;
	unsigned mode;
	const struct ir_group *groups;

	bm_clear(&node->no_edge_syms);

	bm_setall(&mode_edge_bits);
	{
		size_t i, nerr;
		const struct ir_range *ranges;

		nerr = ir_st->u.error.error.n;
		ranges = ir_st->u.error.error.ranges;
		for (i=0; i < nerr; i++) {
			bm_clearrange(&mode_edge_bits, ranges[i].start, ranges[i].end);
			bm_setrange(&node->no_edge_syms, ranges[i].start, ranges[i].end);
		}
	}

	ngrp = ir_st->u.error.n;
	mode = ir_st->u.error.mode;
	groups = ir_st->u.error.groups;

	node->nedges = ngrp+1;
	node->edges = calloc(ngrp+1, sizeof node->edges[0]);
	if (node->edges == NULL) {
		return -1;
	}

	mode_ind = ngrp;
	for (grp=0, edge=0; grp < ngrp; grp++, edge++) {
		unsigned to = groups[grp].to;
		size_t i,nrange;

		assert(to != mode);

		if (mode_ind == ngrp && to > mode) {
			/* mark the position and fill this in afterwards */
			mode_ind = edge++;
		}

		node->edges[edge].dst = to;

		nrange = groups[grp].n;
		for (i=0; i < nrange; i++) {
			unsigned char start, end;

			start = groups[grp].ranges[i].start;
			end   = groups[grp].ranges[i].end;

			bm_setrange(&node->edges[edge].sym_bits, start, end);
			bm_clearrange(&mode_edge_bits, start, end);
		}
	}

	/* fill in the dominant edge... */
	node->edges[mode_ind].dst = mode;
	node->edges[mode_ind].sym_bits = mode_edge_bits;

	return 0;
}

static int
unsigned_cmp(const void *a, const void *b)
{
	const unsigned *ua = (const unsigned *)a;
	const unsigned *ub = (const unsigned *)b;

	return (*ua > *ub) - (*ua < *ub);
}

static int
loop_edge_cmp(const void *a, const void *b)
{
	const struct dfavm_loop_ir_edge *ea = a;
	const struct dfavm_loop_ir_edge *eb = b;

	return (ea->dst > eb->dst) - (ea->dst < eb->dst);
}

static int loop_ir_node_from_table(struct dfavm_loop_ir *node, const struct ir_state *ir_st)
{
	unsigned states[FSM_SIGMA_COUNT];
	unsigned i, nstates;

	memcpy(states, ir_st->u.table.to, sizeof states);

	// sort the table to determine the number of states
	qsort(states, FSM_SIGMA_COUNT, sizeof states[0], unsigned_cmp);

	// count states and remove duplicates
	{
		unsigned j;
		for (i=1,j=0; i < FSM_SIGMA_COUNT; i++) {
			assert(states[i] >= states[j]);

			if (states[i] != states[j]) {
				states[++j] = states[i];
			}
		}
		nstates = j+1;
	}

	bm_clear(&node->no_edge_syms);

	node->nedges = nstates;
	node->edges = calloc(nstates, sizeof node->edges[0]);
	if (node->edges == NULL) {
		return -1;
	}

	/* initialize edges */
	for (i=0; i < nstates; i++) {
		node->edges[i].dst = states[i];
	}

	/* now set the edge bits */
	{
		unsigned i, last_to;
		struct dfavm_loop_ir_edge *last_edge;

		last_to   = states[0];
		last_edge = &node->edges[0];
		for (i=0; i < FSM_SIGMA_COUNT; i++) {
			unsigned to;
			struct dfavm_loop_ir_edge *edge;

			to = ir_st->u.table.to[i];
			if (to == last_to) {
				edge = last_edge;
			} else {
				struct dfavm_loop_ir_edge key;

				/* TODO: there's probably a more efficient way to do this than a bsearch */
				key.dst = to;
				edge = bsearch(&key, node->edges, nstates, sizeof node->edges[0], loop_edge_cmp);
				assert(edge != NULL);

				last_to = to;
			}

			bm_set(&edge->sym_bits, i);
		}
	}

	return 0; /* not yet implemented */
}

static int
loop_analysis_initialize(struct dfavm_loop_analysis *a, const struct ir *ir)
{
	size_t i,n;

	n = ir->n;
	a->nstates = n;
	a->start = ir->start;
	a->states = calloc(n, sizeof a->states[0]);
	if (a->states == NULL) {
		return -1;
	}

	for (i=0; i < n; i++) {
		const struct ir_state *ir_st;
		struct dfavm_loop_ir *lp_st;

		ir_st = &ir->states[i];
		lp_st = &a->states[i];

		lp_st->isend = ir_st->isend;
		lp_st->idom = a->nstates;

		switch (ir_st->strategy) {
		case IR_NONE:
			lp_st->nedges = 0;
			lp_st->edges = NULL;
			bm_setall(&lp_st->no_edge_syms);
			break;

		case IR_SAME:
			lp_st->nedges = 1;
			lp_st->edges = calloc(1,sizeof lp_st->edges[0]);
			if (lp_st->edges == NULL) {
				return -1;
			}

			lp_st->edges[0].dst = ir_st->u.same.to;
			bm_setall(&lp_st->edges[0].sym_bits);
			bm_clear(&lp_st->no_edge_syms);
			break;

		case IR_COMPLETE:
			if (loop_ir_node_from_groups(lp_st, ir_st->u.complete.n, ir_st->u.complete.groups) != 0) {
				return -1;
			}
			break;

		case IR_PARTIAL:
			if (loop_ir_node_from_groups(lp_st, ir_st->u.partial.n, ir_st->u.partial.groups) != 0) {
				return -1;
			}
			break;

		case IR_DOMINANT:
			if (loop_ir_node_from_dominant(lp_st, ir_st) != 0) {
				return -1;
			}
			break;

		case IR_ERROR:
			if (loop_ir_node_from_error(lp_st, ir_st) != 0) {
				return -1;
			}
			break;

		case IR_TABLE:
			if (loop_ir_node_from_table(lp_st, ir_st) != 0) {
				return -1;
			}
			break;

		}

		{
			struct bm check;
			size_t i;

			bm_clear(&check);
			bm_or(&check, &lp_st->no_edge_syms);

			for (i=0; i < lp_st->nedges; i++) {
				struct bm intersect = check;
				assert(bm_and(&intersect, &lp_st->edges[i].sym_bits) == 0);

				bm_or(&check, &lp_st->edges[i].sym_bits);
			}

			assert(bm_isallset(&check));
		}
	}

	return 0;
}


struct loop_analysis_edge {
	unsigned src;
	unsigned dst;
};

struct loop_analysis_predecessor_edges {
	unsigned *offsets;
	struct loop_analysis_edge *edges;
};

static int
pred_edge_cmp(const void *a, const void *b)
{
	const struct loop_analysis_edge *ea = a;
	const struct loop_analysis_edge *eb = b;

	if (ea->dst != eb->dst) {
		return (ea->dst > eb->dst) - (ea->dst < eb->dst);
	}

	return (ea->src > eb->src) - (ea->src < eb->src);
}

/* builds a table of predecessor edges.  This allows us to lookup edges
 * in the graph by their destination so we can quickly look up the
 * predecessors of a node.  Here, the predecessors of node N is the 
 * set of all nodes with a edge that points to N.
 *
 * To do this, we construct an array of src->dst edges from the original
 * graph, and order them by (dst,src).  We then construct a table of
 * offsets into this array, so all edges that end on node N can be found
 * in the list between offsets[N] and offsets[N+1].
 */
static struct loop_analysis_predecessor_edges *
build_pred_edges(struct dfavm_loop_analysis *a)
{
	static const struct loop_analysis_predecessor_edges zero;

	size_t i, nedges, edge, edge_count;
	struct loop_analysis_predecessor_edges *pred;
	unsigned state;

	/*
	size_t num_edges, edge_index, state_edge_count, state_index;
	uint32_t curr_asm_ind;
	*/

	/* count edges */
	nedges = 0;
	for (i=0; i < a->nstates; i++) {
		nedges += a->states[i].nedges;
	}

	pred = malloc(sizeof *pred);
	if (pred == NULL) {
		return NULL;
	}

	*pred = zero;

	pred->offsets = calloc(a->nstates+1, sizeof *pred->offsets);
	if (pred->offsets == NULL) {
		goto error;
	}

	// special case
	if (nedges == 0) {
		pred->edges = NULL;
		pred->offsets[a->nstates] = 0;

		return pred;
	}

	pred->edges = calloc(nedges, sizeof *pred->edges);
	if (pred->edges == NULL) {
		goto error;
	}

	edge = 0;
	for (i=0; i < a->nstates; i++) {
		size_t j;

		for (j=0; j < a->states[i].nedges; j++) {
			assert(edge < nedges);

			pred->edges[edge].src = i;
			pred->edges[edge].dst = a->states[i].edges[j].dst;
			edge++;
		}
	}

	assert(edge == nedges);

	/* sort edges by destination */
	qsort(&pred->edges[0], nedges, sizeof pred->edges[0], pred_edge_cmp);

	/* count unique dests and setup offsets */
	state = pred->edges[0].dst;
	edge_count = 1;
	for (edge = 1; edge < nedges; edge++) {
		if (pred->edges[edge].dst != state) {
			pred->offsets[1+state] = edge_count;
			state = pred->edges[edge].dst;
			edge_count = 1;
		} else {
			edge_count++;
		}
	}

	pred->offsets[1+state] = edge_count;

	/* offsets are a cumulative sum of the counts */
	for (state=0; state < a->nstates; state++) {
		pred->offsets[1+state] += pred->offsets[state];
	}

	/*
	for (state_index=0; state_index < a->count+1; state_index++) {
		printf("edge offset[%4zu] = %lu\n", state_index, (unsigned long)pred->offsets[state_index]);
	}
	*/

	return pred;

error:
	if (pred != NULL) {
		free(pred->offsets);
		free(pred->edges);
		free(pred);
	}

	return NULL;
}

static unsigned
idom_intersect(const struct dfavm_loop_analysis *a, unsigned na, unsigned nb)
{
	while (na != nb) {
		while (a->states[na].order < a->states[nb].order) {
			na = a->states[na].idom;
		}

		while (a->states[nb].order < a->states[na].order) {
			nb = a->states[nb].idom;
		}
	}

	return na;
}

#if 0
static void
print_all_states(const struct dfavm_assembler_ir *a);
#endif /* 0 */

/* This is from "A Simple, Fast Dominance Algorithm" by Cooper, et al.
 * https://www.cs.rice.edu/~keith/EMBED/dom.pdf
 *
 * It's very easy to code, and often very fast, but still has a worst
 * case of O(N^2).  We should eventually replace this with Lengauer-Tarjan
 * which has a worst case of O(N log N).
 */
static int
identify_idoms(struct dfavm_loop_analysis *a)
{
	struct loop_analysis_predecessor_edges *pred_edges = NULL;
	struct {
		unsigned node;
		size_t edge;
	} *stack;

	unsigned *ordered;

	unsigned start;
	size_t i, iter;

	// struct dfavm_op_ir *op, **ordered, **stack, *start;
	uint32_t ordered_top, stack_top;
	bool has_changed;
	int ret;

	ret = -1;

	stack = NULL;
	ordered = NULL;

	/* allocate temporary structures */
	pred_edges = build_pred_edges(a);
	if (pred_edges == NULL) {
		goto cleanup;
	}

	ordered = calloc(a->nstates, sizeof *ordered);
	if (ordered == NULL) {
		goto cleanup;
	}

	stack = calloc(a->nstates, sizeof *stack);
	if (stack == NULL) {
		goto cleanup;
	}

	/* clear visited bit, set idom to NULL */
	for (i=0; i < a->nstates; i++) {
		a->states[i].idom = a->nstates;
		a->states[i].isvisited = 0;
	}

	start = a->start;

	stack[0].node = start;
	stack[0].edge = 0;
	stack_top = 1;

	ordered_top = 0;

	a->states[start].isvisited = 1;

	/* We need to traverse nodes by reverse postorder (the same
	 * as topological sorted order).
	 *
	 * To do this, we order the nodes by their postorder using a
	 * depth-first search, and adding nodes to the ordered list
	 * after we have finished traversing their edges.
	 */
	while (stack_top > 0) {
		unsigned node, unvisited;
		size_t edge;

		assert(stack_top > 0);
		assert(stack_top <= a->nstates);

		node = stack[stack_top-1].node;
		edge = stack[stack_top-1].edge;

		assert(node < a->nstates);
		assert(edge <= a->states[node].nedges);
		assert(a->states[node].isvisited);

		unvisited = a->nstates;
		for (; edge < a->states[node].nedges; edge++) {
			unsigned dst;

			dst = a->states[node].edges[edge].dst;
			assert(dst < a->nstates);

			if (!a->states[dst].isvisited) {
				unvisited = dst;
				break;
			}
		}

		if (unvisited < a->nstates) {
			assert(edge < a->states[node].nedges);
			assert(stack_top < a->nstates);

			a->states[unvisited].isvisited = 1;

			stack[stack_top-1].edge = edge+1;
			stack[stack_top].node = unvisited;
			stack[stack_top].edge = 0;
			stack_top++;
		} else {
			assert(ordered_top < a->nstates);

			a->states[node].order = ordered_top;
			ordered[ordered_top++] = node;
			stack_top--;
		}
	}

	/* Now that we have the nodes in reverse postorder and a list
	 * of predecessor edges, we can proceed quickly...
	 */
	a->states[start].idom = start;

	/*
	dump_loop_analysis(a);
	*/

	/* iterate until the sets no longer change */
	for (has_changed = true, iter = 0; has_changed; iter++) {
		uint32_t ind;

		/*
		fprintf(stderr, "---[ iter %lu ]---\n", iter);
		*/
		has_changed = false;

		// iterate in reverse postorder
		for (ind = ordered_top; ind > 0; ind--) {
			unsigned node;

			node = ordered[ind-1];
			if (node != start) {
				const unsigned ei0 = pred_edges->offsets[node+0];
				const unsigned ei1 = pred_edges->offsets[node+1];

				unsigned ei, new_idom;

				/*
				fprintf(stderr, "node: %u[order:%u] idom=%u:%p\n",
					node, a->states[node].order,
					a->states[node].idom,
					(void *)((a->states[node].idom < a->nstates) ? &a->states[a->states[node].idom] : NULL));
				fprintf(stderr, "  - offsets: %lu ... %lu\n",
					(unsigned long)ei0, (unsigned long)ei1);
				*/

				new_idom = a->nstates;
				for (ei=ei0; ei < ei1; ei++) {
					unsigned pred;

					assert(pred_edges->edges[ei].dst == node);

					pred = pred_edges->edges[ei].src;
					/*
					fprintf(stderr, "  - pred: %u[order:%u] idom=%u:%p\n",
						pred, a->states[pred].order,
						a->states[pred].idom,
						(void *)((a->states[pred].idom < a->nstates) ? &a->states[a->states[pred].idom] : NULL));
					*/

					if (a->states[pred].idom == a->nstates) {
						continue;
					}

					if (new_idom == a->nstates) {
						new_idom = pred;
					} else {
						/*
						fprintf(stderr, "  - intersect(%u[order:%u], %u[order:%u])\n",
							new_idom, a->states[new_idom].order,
							pred, a->states[pred].order);
						*/

						new_idom = idom_intersect(a,pred,new_idom);
					}

					assert(new_idom < a->nstates);
					/*
					fprintf(stderr, "  - new_idom = %u[order:%u]\n",
						new_idom, a->states[new_idom].order);
					*/
				}

				assert(new_idom < a->nstates);

				if (a->states[node].idom != new_idom) {
					a->states[node].idom = new_idom;
					/*
					fprintf(stderr, "  * new_idom = %u[order:%u]\n",
						new_idom, a->states[new_idom].order);
					*/
					has_changed = true;
				}
			}
		}
	}

	/* debug dump of dominators */

	/*
	dump_loop_analysis(a);

	fprintf(stderr, "--[ idoms ]--\n");
	{
		unsigned i;
		for (i=0; i < ordered_top; i++) {
			unsigned st = ordered[i];
			fprintf(stderr, "%6u[order:%6u] idom %u\n",
				st, a->states[st].order, a->states[st].idom);
		}
	}
	*/

	/* return success! */
	ret = 0;

cleanup:
	if (pred_edges != NULL) {
		free(pred_edges->offsets);
		free(pred_edges->edges);
		free(pred_edges);
	}

	free(ordered);
	free(stack);

	/*
	for (op=a->linked; op != NULL; op=op->next) {
		op->visited = 0;
		op->index = 0;
	}
	*/

	return ret;
}

static bool
dominates(const struct dfavm_loop_analysis *a, unsigned node, unsigned dom)
{
	unsigned idom;

	assert(node < a->nstates);
	assert(dom  < a->nstates);

	idom = a->states[node].idom;

	/* struct dfavm_op_ir *node; */
	if (idom == dom) {
		return true;
	}

	for (;;) {
		unsigned idom_idom = a->states[idom].idom;

		if (idom == idom_idom) {
			break;
		}

		if (idom == dom) {
			return true;
		}

		idom = idom_idom;
	}

	return idom == dom;
}

struct loop_entry {
	unsigned head;
	unsigned tail;
	const struct dfavm_loop_ir_edge *edge;
};

struct loop_array {
	size_t len;
	size_t cap;

	struct loop_entry *entries;
};

static int
cmp_loop(const void *a, const void *b)
{
	const struct loop_entry *la = a;
	const struct loop_entry *lb = b;

	if (la->head == lb->head) {
		return (la->tail > lb->tail) - (la->tail < lb->tail);
	}

	return (la->head > lb->head) - (la->head < lb->head);
}

static void
free_loops(struct loop_array *l)
{
	if (l != NULL) {
		free(l->entries);
		free(l);
	}
}

static int
add_loop(struct loop_array *l, unsigned head, unsigned tail, const struct dfavm_loop_ir_edge *edge)
{
	assert(l != NULL);
	if (l->len >= l->cap) {
		size_t new_cap;
		struct loop_entry *new_entries;

		if (l->cap < 16) {
			new_cap = 16;
		} else if (l->cap < 2048) {
			new_cap = 2*l->cap;
		} else {
			new_cap = l->cap + l->cap/2;
		}

		new_entries = realloc(l->entries, new_cap * sizeof *new_entries);
		if (new_entries == NULL) {
			return 0;
		}

		l->cap = new_cap;
		l->entries = new_entries;
	}

	assert(l->len < l->cap);
	assert(l->entries != NULL);

	l->entries[l->len].head = head;
	l->entries[l->len].tail = tail;
	l->entries[l->len].edge = edge;

	l->len++;

	return 1;
}

static struct loop_array *
identify_loops(struct dfavm_loop_analysis *a)
{
	size_t i;
	struct loop_array *loops;

	loops = malloc(sizeof *loops);
	if (loops == NULL) {
		return NULL;
	}

	loops->entries = NULL;
	loops->len = loops->cap = 0;

	/* index member is not set until after optimizations.
	 * we borrow it here to ensure that loops are ordered
	 */

	for (i = 0; i < a->nstates; i++) {
		size_t j;

		for (j = 0; j < a->states[i].nedges; j++) {
			unsigned dst = a->states[i].edges[j].dst;

			// look for natural loops (edges to dominators
			// or self-loops (edges to the same state)
			if (dominates(a, i, dst) || dst == i) {
				if (!add_loop(loops, dst, i, &a->states[i].edges[j])) {
					goto error;
				}
			}
		}
	}

	if (loops->len > 0) {
		qsort(loops->entries, loops->len, sizeof loops->entries[0], cmp_loop);
	}

	return loops;

error:
	free_loops(loops);
	return NULL;
}

#if 0
static int
optimize_loops(struct dfavm_assembler_ir *a)
{
	struct ir_loop *loops;

	/* identify immediate dominators */
	if (identify_idoms(a) < 0) {
		return -1;
	}

	/* identify natural loops */
	loops = identify_loops(a);
	if (loops == NULL) {
		return -1;
	}

	dump_states(stdout, a);
	if (loops->len > 0) {
		size_t i;
		printf("---[ loops: %zu ]---\n", loops->len);
		for (i=0; i < loops->len; i++) {
			printf("[%4zu] head %4lu:%p  tail %4lu:%p\n", i,
				(unsigned long)loops->entries[i].head->asm_index, (void *)loops->entries[i].head,
				(unsigned long)loops->entries[i].tail->asm_index, (void *)loops->entries[i].tail);
		}
	} else {
		printf("\nno loops.\n\n");
	}

	/* analyze natural loops:
	 * - single-character chokepoints
	 * - fixed string portions
	 * - multiple fixed string portions
	 */

	free_loops(loops);

	return 0;
}

#endif /* 0 */
























static int
loop_analysis_analyze(struct dfavm_loop_analysis *a)
{
	struct loop_array *loops;

	/* identify immediate dominators */
	if (identify_idoms(a) < 0) {
		return -1;
	}

	/* identify natural loops */
	loops = identify_loops(a);
	if (loops == NULL) {
		return -1;
	}

	dump_loop_analysis(a);

	if (loops->len > 0) {
		size_t i, i0;
		fprintf(stderr, "---[ loops: %zu ]---\n", loops->len);

		unsigned head;
		struct bm common;

		i0 = 0;
		head = a->nstates;
		bm_clear(&common);

		for (i=0; i < loops->len; i++) {
			if (i == 0 || loops->entries[i].head != head) {
				if (i != 0) {
					fprintf(stderr, "[----] head %u:  %zu loops, common edges: ", head, i-i0);
					print_sym_set(&common, stderr);
					fprintf(stderr, "\n");
				}

				i0   = i;
				head = loops->entries[i].head;

				bm_setall(&common);
			}

			bm_and(&common, &loops->entries[i].edge->sym_bits);

			fprintf(stderr, "[%4zu] head %4u  tail %4u%s ",
				i, loops->entries[i].head, loops->entries[i].tail,
				(loops->entries[i].head == loops->entries[i].tail) ? " SELF" : "");

			print_sym_set(&loops->entries[i].edge->sym_bits, stderr);
			fprintf(stderr, "\n");
		}

		fprintf(stderr, "[----] head %u:  %zu loops, common edges: ", head, i-i0);
		print_sym_set(&common, stderr);
		fprintf(stderr, "\n");
	} else {
		printf("\nno loops.\n\n");
	}

	free_loops(loops);

	/* todo:
	 * 2) identify loops
	 * 3) find mergeable loop exits
	 */

	return 0;
}

static void
loop_analysis_finalize(struct dfavm_loop_analysis *a)
{
	if (a->nstates > 0) {
		size_t i;

		for (i=0; i < a->nstates; i++) {
			free(a->states[i].edges);
		}
	}

	free(a->states);

	a->states = NULL;
	a->nstates = 0;
	a->start = 0;
}

int
dfavm_compile_ir(struct dfavm_assembler_ir *a, const struct ir *ir, struct fsm_vm_compile_opts opts)
{
	struct dfavm_loop_analysis loop_analysis;

	if (loop_analysis_initialize(&loop_analysis, ir) != 0) {
		return 0;
	}

	if (loop_analysis_analyze(&loop_analysis) != 0) {
		return 0;
	}

	loop_analysis_finalize(&loop_analysis);

	a->nstates = ir->n;
	a->start = ir->start;

	(void)dump_states; /* make clang happy */
	(void)print_all_states;

	a->ops = calloc(ir->n, sizeof a->ops[0]);
	if (a->ops == NULL) {
		return 0;
	}

	if (initial_translate(ir, a) < 0) {
		return 0;
	}

	fixup_dests(a);

	if (opts.flags & FSM_VM_COMPILE_PRINT_IR_PREOPT) {
		FILE *f = (opts.log != NULL) ? opts.log : stdout;

		fprintf(f, "---[ before optimization ]---\n");
		dump_states(f, a);
		fprintf(f, "\n");
	}

	order_basic_blocks(a);

	/* basic optimizations */
	if (opts.flags & FSM_VM_COMPILE_OPTIM) {
		// optimize_loops(a);
		eliminate_unnecessary_branches(a);
	}

	/* optimization is finished.  now assign opcode indexes */
	assign_opcode_indexes(a);

	if (opts.flags & FSM_VM_COMPILE_PRINT_IR) {
		FILE *f = (opts.log != NULL) ? opts.log : stdout;

		fprintf(f, "---[ final IR ]---\n");
		dump_states(f, a);
		fprintf(f, "\n");
	}

	return 1;
}

