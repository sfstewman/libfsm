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
	pred_edges = a->pred_edges;

	assert(pred_edges != NULL);

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

	if (node == dom) {
		/* every node dominates itself */
		return true;
	}

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

static void
print_idom_tree_inner(FILE *f, const unsigned *tree, const unsigned *offsets, unsigned node, unsigned indent)
{
	unsigned i0,i1, i;

	if (indent > 0) {
		size_t j;
		for (j=0; j < 2*indent; j++) {
			putc(' ', f);
		}
	}

	fprintf(f, "- node %u\n", node);

	i0 = offsets[node];
	i1 = offsets[node+1];

	assert(i0 <= i1);

	for (i=i0; i < i1; i++) {
		print_idom_tree_inner(f, tree, offsets, tree[i], indent+1);
	}
}

static void
print_idom_tree(const struct dfavm_loop_analysis *a, FILE *f)
{
	unsigned *tree, *offsets, *work;
	size_t i;
	unsigned root;

	assert(a != NULL);
	assert(a->nstates > 0);

	/* tree[0] is the root.
	 * counts[0] is the number of children
	 *
	 * offsets[0]
	 *
	 */
	tree = calloc(3*a->nstates+1, sizeof *tree);
	if (tree == NULL) {
		perror("allocating idom tree working space");
		return;
	}

	work = &tree[a->nstates];
	offsets = &tree[2*a->nstates];

	root = a->nstates;

	for (i=0; i < a->nstates; i++) {
		unsigned idom;

		assert(a->states[i].idom < a->nstates);

		idom = a->states[i].idom;
		if (idom != i) {
			offsets[idom+1]++;
		}
	}

	for (i=0; i < a->nstates; i++) {
		offsets[i+1] += offsets[i];
	}

	assert(offsets[a->nstates] == a->nstates-1);

	for (i=0; i < a->nstates; i++) {
		unsigned idom;
		size_t ind;

		assert(a->states[i].idom < a->nstates);

		idom = a->states[i].idom;

		if (idom == i) {
			root = i;
		} else {
			ind = offsets[idom] + work[idom];
			tree[ind] = i;
			work[idom]++;
		}
	}

	assert(root < a->nstates);

	print_idom_tree_inner(f, tree, offsets, root, 0);
	free(tree);
}

struct loop_entry {
	unsigned head;
	unsigned tail;
	const struct dfavm_loop_ir_edge *edge;

	unsigned n;
	unsigned *states;
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

static struct loop_entry *
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
			return NULL;
		}

		l->cap = new_cap;
		l->entries = new_entries;
	}

	assert(l->len < l->cap);
	assert(l->entries != NULL);

	l->entries[l->len].head = head;
	l->entries[l->len].tail = tail;
	l->entries[l->len].edge = edge;

	l->entries[l->len].n = 0;
	l->entries[l->len].states = NULL;

	return &l->entries[l->len++];
}

/* DFAs can produce a lot of loops that look like this:
 *
 *
 *      +--------------+
 *      |              |
 *      |   +-----+    |
 *      |  /      |    |
 *      v L       |    |
 * 0 -> 1 -> 2 -> 3 -> 4 -> 5
 *      ^    |
 *      |    |
 *      +----+
 *
 * Where the back edges from states 2, 3, and 4 lead to state 1.
 *
 * This indicates that states 1-4 are really part of one loop, and
 * in terms of flow control, we could rewrite this as:
 *
 *      +--------------+
 *      |              |
 *      |    +----+--> X
 *      |    |    |    |
 *      v    |    |    |
 * 0 -> 1 -> 2 -> 3 -> 4 -> 5
 *
 * where X marks an exit state which always transitions to 1.
 *
 * NOTE: this doesn't preclude exits to other states, which we will
 *       handle separately.
 *
 * The goal is to identify this kind of mergeable loop.  The following
 * conditions should hold:
 *
 * Loop (A,B) can be merged into loop (A,C) if:
 * 1) The heads are the same (A)
 * 2) A path exists from B -> C _that does not contain A_
 * 3) Every node along that path is dominated by A.
 *
 * So... how do we find the states?  First, start with the identified
 * loops.
 *
 * For each unique head H in the list of loops (H,T):
 *
 * - Initialize a set of states associated with H.  Add H to the set.
 * - Perform a limited BFS traversal of the graph starting with H.
 *
 *   Edges src -> dst are only traversed if dst is dominated by H, but
 *   is not H.
 *
 *   Add each node N in the traversal to the set of states associated
 *   with H
 *
 */

static int
cmp_unsigned(const void *a, const void *b)
{
	const unsigned *ua = a, *ub = b;
	return (*ua > *ub) - (*ua < *ub);
}

struct loop_tree_node {
	size_t nloops;
	size_t loops_cap;
	struct loop_tree_node **loops;

	size_t nstates;
	unsigned *states;

	unsigned head;

	unsigned pseudo:1;
};

struct loop_tree {
	size_t n;
	struct loop_tree_node *root;
};

static void
free_loop_tree(struct loop_tree *tree)
{
	size_t i,n;
	struct loop_tree_node *nodes;

	if (tree == NULL) {
		return;
	}

	n = tree->n;
	nodes = tree->root;
	free(tree);

	if (nodes == NULL) {
		return;
	}

	for (i=0; i < n; i++) {
		free(nodes[i].states);
		free(nodes[i].loops);
	}

	free(nodes);
}

static bool
loop_tree_node_contains(const struct loop_tree_node *l, unsigned node)
{
	assert(l != NULL);

	if (l->nstates == 0) {
		return false;
	}

	return bsearch(&node, &l->states[0], l->nstates, sizeof l->states[0], cmp_unsigned) != NULL;
}

static int
loop_tree_node_add_subloop(struct loop_tree_node *parent, struct loop_tree_node *child)
{
	assert(parent != NULL);
	assert(child  != NULL);

	assert(parent != child);

	assert(parent->pseudo ||  loop_tree_node_contains(parent, child->head));
	assert(parent->pseudo || !loop_tree_node_contains(child, parent->head));
	assert(!child->pseudo);

	if (parent->nloops >= parent->loops_cap) {
		size_t new_cap;
		struct loop_tree_node **new_loops;

		if (parent->loops_cap < 16) {
			new_cap = 16;
		} else if (parent->loops_cap < 1024) {
			new_cap = 2*parent->loops_cap;
		} else {
			new_cap = parent->loops_cap + parent->loops_cap/2;
		}

		assert(parent->nloops < new_cap);

		new_loops = realloc(parent->loops, new_cap * sizeof parent->loops[0]);
		if (new_loops == NULL) {
			return -1;
		}

		parent->loops_cap = new_cap;
		parent->loops     = new_loops;
	}

	assert(parent->nloops < parent->loops_cap);
	assert(parent->loops != NULL);

	parent->loops[parent->nloops++] = child;

	return 0;
}

struct loop_tree_node_proxy {
	const struct loop_tree_node *nodes;
	size_t indx;
	unsigned node;
};

static int
cmp_loop_tree_node_proxy(const void *a, const void *b)
{
	const struct loop_tree_node_proxy *pa = a, *pb = b;

	assert(pa != NULL);
	assert(pb != NULL);

	assert(pa->nodes != NULL);
	assert(pb->nodes != NULL);

	assert(pa->nodes == pb->nodes);

	// assert(pa->node < pa->nodes->nstates);
	// assert(pb->node < pa->nodes->nstates);

	if (loop_tree_node_contains(&pa->nodes[pa->indx], pb->node)) {
		return -1;
	} else if (loop_tree_node_contains(&pb->nodes[pb->indx], pa->node)) {
		return 1;
	} else {
		return 0;
	}
}

static void
print_indent(FILE *f, int indent)
{
	int i;
	for (i=0; i < indent; i++) {
		fputs("  ", f);
	}
}

static void
print_loop_tree_subtree(const struct loop_tree_node *nodes, FILE *f, int indent)
{
	size_t i;

	assert(nodes != NULL);

	print_indent(f,indent);
	if (nodes->pseudo) {
		fprintf(f, "> PSEUDO: %zu states, %zu inner loops\n", nodes->nstates, nodes->nloops);
	} else {
		fprintf(f, "> head %u: %zu states, %zu inner loops\n", nodes->head, nodes->nstates, nodes->nloops);
	}

	assert(nodes->nstates == 0 || nodes->states != NULL);

	if (nodes->nstates > 0) {
		print_indent(f,indent+1);
		fprintf(f, "- states:");
		for (i=0; i < nodes->nstates; i++) {
			fprintf(f, " %u", nodes->states[i]);
			if ((i+1) % 10 == 0) {
				fprintf(f, "\n");
				print_indent(f,indent+1);
				fprintf(f, "         ");
			}
		}
		fprintf(f,"\n");
	}

	fprintf(f,"\n");

	assert(nodes->nloops == 0 || nodes->loops != NULL);
	assert(nodes->nloops <= nodes->loops_cap);

	assert(
		(nodes->loops_cap == 0 && nodes->loops == NULL) ||
		(nodes->loops_cap >  0 && nodes->loops != NULL)
	);

	for (i=0; i < nodes->nloops; i++) {
		assert(nodes->loops[i] != NULL);
		print_loop_tree_subtree(nodes->loops[i], f, indent+1);
	}
}

static void
print_loop_tree(const struct loop_tree *tree, FILE *f)
{
	assert(tree != NULL);
	assert(tree->root != NULL);

	print_loop_tree_subtree(tree->root, f, 0);
}

static int 
loop_tree_node_initialize(struct loop_tree_node *li, unsigned head, unsigned *states, size_t nstates)
{
	size_t nuniq;

	qsort(&states[0], nstates, sizeof states[0], cmp_unsigned);

	{
		/* remove any duplicates */
		size_t i,j;

		for (i=1, j=0; i < nstates; i++) {
			if (states[i] != states[j]) {
				j++;
				states[j] = states[i];
			}
		}

		nuniq = j+1;
	}

	li->states = malloc(nuniq * sizeof li->states[0]);
	if (li->states == NULL) {
		return -1;
	}

	li->head = head;
	memcpy(&li->states[0], &states[0], nuniq * sizeof states[0]);
	li->nstates = nuniq;
	li->pseudo = 0;

	return 0;
}

static struct loop_tree *
gather_loop_states(const struct dfavm_loop_analysis *a, const struct loop_array *loops)
{
	unsigned *queue;
	unsigned *states;
	size_t *visited;
	size_t i;
	unsigned head;
	size_t tree_node_count, state_top;
	struct loop_tree *tree;
	struct loop_analysis_predecessor_edges *pred_edges;

	struct loop_tree_node *nodes;

	static const struct loop_tree tree_zero;

	assert(a != NULL);
	assert(a->pred_edges != NULL);
	assert(a->nstates > 0);
	assert(a->states != NULL);

	tree = malloc(sizeof *tree);
	if (tree == NULL) {
		return NULL;
	}

	*tree = tree_zero;

	queue   = calloc(a->nstates, sizeof *queue);
	states  = calloc(a->nstates, sizeof *states);
	visited = calloc(a->nstates, sizeof *visited);
	nodes   = calloc(loops->len+1, sizeof *nodes);

	if (queue == NULL || states == NULL || visited == NULL || nodes == NULL) {
		goto cleanup;
	}

	pred_edges = a->pred_edges;

	/* reserve the first entry for a pseudo-node that holds all of
	 * the non-loop states
	 *
	 * We'll fill these states in later...
	 */

	nodes[0].head    = a->nstates;
	nodes[0].pseudo  = 1;
	nodes[0].states  = NULL;
	nodes[0].nstates = 0;

	tree_node_count = 1;

	state_top = 0;
	head = 0;
	for (i=0; i < loops->len; i++) {
		size_t qtop;
		unsigned tail;

		if (i == 0) {
			head = loops->entries[i].head;
		} else if (loops->entries[i].head != head) {
			assert(tree_node_count < loops->len+1);

			if (loop_tree_node_initialize(&nodes[tree_node_count++], head, &states[0], state_top) < 0) {
				goto cleanup;
			}

			head = loops->entries[i].head;
			state_top = 0;
		}

		tail = loops->entries[i].tail;

		/*
		fprintf(stderr, ">> i = %zu, head = %u, tail = %u\n", i,head,tail);
		*/

		if (visited[tail] == head+1) {
			/*
			fprintf(stderr, "   SKIPPING: visited[tail = %u] = %zu\n", tail, visited[tail]);
			*/
			continue;
		}

		qtop = 0;
		queue[qtop++] = tail;
		visited[tail] = head+1;

		/*
		{
			size_t k;
			fprintf(stderr, "visited:");
			for (k=0; k < a->nstates; k++) {
				fprintf(stderr, " %zu%s", visited[k], visited[k] == head+1 ? "*" : "" );
			}
			fprintf(stderr, "\n");
		}
		*/

		while (qtop > 0) {
			unsigned node;
			unsigned ei0, ei1, ei;

			node = queue[--qtop];

			/*
			fprintf(stderr, "  ]] node = %u\n", node);
			*/

			assert(node < a->nstates);
			assert(state_top < a->nstates);

			states[state_top++] = node;

			/*
			{
				size_t k;
				fprintf(stderr, "states:");
				for (k=0; k < a->nstates; k++) {
					if (k == state_top) {
						fprintf(stderr, " | ");
					}

					fprintf(stderr, " %u", states[k]);
				}
				fprintf(stderr, "\n");
			}
			*/

			ei0 = pred_edges->offsets[node+0];
			ei1 = pred_edges->offsets[node+1];

			/*
			fprintf(stderr, "    }} visited[%u] = %zu\n", node, visited[node]);
			*/
			for (ei = ei0; ei < ei1; ei++) {
				unsigned pred;
				assert(pred_edges->edges[ei].dst == node);

				pred = pred_edges->edges[ei].src;

				assert(pred < a->nstates);

				/*
				fprintf(stderr, "    }} edge %u -> %u", node, pred);
				*/

				if (dominates(a, pred, head) && visited[pred] != head+1) {
					assert(qtop < a->nstates);

					queue[qtop++] = pred;
					visited[pred] = head+1;
					/*
					fprintf(stderr, " enqueued");
					*/
				}

				/*
				fprintf(stderr, "\n");
				*/
			}
		}
	}

	if (state_top > 0) {
		if (loop_tree_node_initialize(&nodes[tree_node_count++], head, &states[0], state_top) < 0) {
			goto cleanup;
		}
	}


	/* find any nodes that are not part of loops */
	{
		size_t state_top;

		for (i=0; i < a->nstates; i++) {
			visited[i] = 0;
			states[i] = 0;
		}

		for (i=0; i < tree_node_count; i++) {
			size_t j;

			for (j=0; j < nodes[i].nstates; j++) {
				unsigned node = nodes[i].states[j];
				visited[node] = 1;
			}
		}

		/* Find unvisited nodes.  We can simultaneously reset
		 * all visited values to zero. */
		state_top = 0;
		for (i=0; i < a->nstates; i++) {
			if (visited[i] == 0) {
				assert(state_top < a->nstates);
				states[state_top++] = i;
			}

			visited[i] = 0;
		}

		/* Fill any states not in loops into the pseudo-node at
		 * nodes[0]
		 */
		if (state_top > 0) {
			fprintf(stderr, ">>> %zu nodes not in loops\n", state_top);

			nodes[0].states = calloc(state_top, sizeof nodes[tree_node_count].states[0]);
			if (nodes[0].states == NULL) {
				goto cleanup;
			}

			nodes[0].nstates = state_top;
			memcpy(&nodes[0].states[0], &states[0], state_top * sizeof states[0]);
		}
	}

	/*
	fprintf(stderr, "----[ loop nodes (%zu items) ]----\n", tree_node_count);
	for (i=0; i < tree_node_count; i++) {
		size_t j;
		fprintf(stderr, "[%4zu] head: %u  nstates: %zu\n", i, nodes[i].head, nodes[i].nstates);
		for (j=0; j < nodes[i].nstates; j++) {
			fprintf(stderr, "    state %u\n", nodes[i].states[j]);
		}
	}
	*/

	/* Create a tree of loop nodes
	 *
	 * The elements of nodes form a natural tree, but the current
	 * representation is a bit indirect.  Each element of nodes has a
	 * list of nodes it contains, but this includes all elements of
	 * the tree below this node, not just its immediate children.
	 *
	 * To build the tree, we sort the elements of nodes (skipping the
	 * pseudo node at nodes[0]) according to their "contains" order:
	 *
	 * A < B if A contains B.
	 * A > B if B contains A.
	 * A = B if neither contains the other.
	 *
	 * This results in a list where element j, j>i, cannot be a
	 * parent loop of i, and must either be an inner loop of i or
	 * unrelated to i.
	 *
	 * Importantly, if a loop is at position i, there can be no
	 * further inner loops of that loop.
	 *
	 * We can then build the tree by starting at the right-most
	 * loop in the sorted list and moving left-wards.
	 *
	 * We keep a list of active loops.  For each new loop
	 * encountered L:
	 *
	 * 1. Find all active loops that are contained by L.  A loop is
	 *    contained by L if its head state is in the list of states
	 *    of L.
	 *
	 *    Add all active loops contained by L as inner loops in L and
	 *    remove them from the list of active loops.
	 *
	 * 2. Add loop L to the active list.
	 *
	 * After the final element, the active nodes should be added to
	 * the top-level pseudo-node.
	 *
	 *
	 * FIXME: this seems pretty inefficient.  There must be a better
	 * way.
	 *
	 */
	if (tree_node_count > 1) {
		/* FIXME: there must be a better way ... */
		struct loop_tree_node_proxy *tree_elts;
		size_t num_active;
		size_t first_tombstone;

		tree_elts = calloc(tree_node_count-1, sizeof *tree_elts);
		if (tree_elts == NULL) {
			goto cleanup;
		}

		/*
		fprintf(stderr, "----[ tree_elts ]----\n");
		*/

		for (i=0; i < tree_node_count-1; i++) {
			tree_elts[i].nodes = nodes;
			tree_elts[i].indx = i+1;
			tree_elts[i].node = nodes[i+1].head;

			/*
			fprintf(stderr, "[%4zu] %p %zu %u\n", i, (void *)nodes, i+1, nodes[i+1].head);
			*/
		}

		qsort(tree_elts, tree_node_count-1, sizeof tree_elts[0], cmp_loop_tree_node_proxy);

		/*
		fprintf(stderr, "----[ sorted by container order ]----\n");
		for (i=0; i < tree_node_count-1; i++) {
			fprintf(stderr, "[%4zu] loop index %zu, loop head %u\n",
				i, tree_elts[i].indx, tree_elts[i].node);
		}
		*/

		/* Use 'visited' to hold the active loop set.
		 *
		 * FIXME: This isn't great, but we're not using it for
		 * anything, and we don't want to allocate more space.
		 *
		 * Here, the value states[i] indicates the index into
		 * nodes.  The max index is tree_node_count-1, so we use the
		 * value tree_node_count to indidate a tombstone.
		 */

		/* zero visited */
		for (i=0; i < tree_node_count; i++) {
			visited[i] = 0;
		}

		num_active = 0;
		first_tombstone = tree_node_count;

		/* iterate nodes[tree_node_count] ... nodes[1].  Remember that
		 * nodes[0] holds the pseudo node
		 */
		for (i=tree_node_count-1; i > 0; i--) {
			size_t j, new_loop;

			new_loop = tree_elts[i-1].indx;
			assert(num_active < tree_node_count);

			for (j=0; j < num_active; j++) {
				size_t active_loop;

				active_loop = visited[j];
				if (active_loop < tree_node_count && loop_tree_node_contains(&nodes[new_loop], nodes[active_loop].head)) {
					/* add as subloop */
					if (loop_tree_node_add_subloop(&nodes[new_loop], &nodes[active_loop]) < 0) {
						goto cleanup;
					}

					/* removed from list */
					visited[j] = tree_node_count;
					if (j < first_tombstone) {
						first_tombstone = j;
					}
				}
			}

			j = (first_tombstone < tree_node_count) ? first_tombstone : 0;
			for (; j < num_active; j++) {
				if (visited[j] == tree_node_count) {
					first_tombstone = tree_node_count;
					break;
				}
			}

			if (j < num_active) {
				visited[j] = new_loop;
			} else {
				assert(num_active < tree_node_count);
				visited[num_active++] = new_loop;
			}

			/*
			fprintf(stderr, "\nvisited array for i=%zu, new_loop=%zu, num_active=%zu, first_tombstone=%zu\n",
				i, new_loop, num_active, first_tombstone);

			for (j=0; j < tree_node_count; j++) {
				fprintf(stderr, "  [%3zu] %zu%s%s\n",
					j, visited[j],
					j==num_active ? " A" : "",
					j==first_tombstone ? " T" : "");
			}
			fprintf(stderr, "\n");
			*/
		}

		/* gather up active nodes and add them to the root
		 * pseudo-node
		 */
		for (i=0; i < num_active; i++) {
			size_t loop = visited[i];
			if (loop < tree_node_count) {
				if (loop_tree_node_add_subloop(&nodes[0], &nodes[loop]) < 0) {
					goto cleanup;
				}
			}
		}

		free(tree_elts);
	}

	/* Build loop tree... */
	(void)print_loop_tree;
	(void)cmp_loop_tree_node_proxy;
	(void)loop_tree_node_add_subloop;

	tree->root = nodes;
	tree->n = tree_node_count;

	/* print out of tree */
	fprintf(stderr, "\n---------------[ LOOP TREE ]---------------\n");
	print_loop_tree(tree, stderr);
	fprintf(stderr, "\n\n");

cleanup:
	free(queue);
	free(states);
	free(visited);

	if (tree && tree->root == NULL) {
		free_loop_tree(tree);
		tree = NULL;
	}

	return tree;
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
				struct loop_entry *ent;

				ent = add_loop(loops, dst, i, &a->states[i].edges[j]);
				if (ent == NULL) {
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


static void
print_loops(const struct dfavm_loop_analysis *a, const struct loop_array *loops)
{
	size_t i, i0;
	unsigned head;
	struct bm common;

	if (loops->len == 0) {
		printf("\nno loops.\n\n");
		return;
	}

	fprintf(stderr, "---[ loops: %zu ]---\n", loops->len);

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
}

static int
loop_analysis_process_loop(struct dfavm_loop_analysis *a, const struct loop_tree_node *tree, int depth)
{
	assert(a    != NULL);
	assert(tree != NULL);

	print_indent(stderr, depth);
	fprintf(stderr, "processing loop head: %u\n", tree->head);

	/* process sub-loops */
	{
		size_t i,n;
		n = tree->nloops;
		for (i=0; i < n; i++) {
			assert(tree->loops != NULL);
			assert(tree->loops[i] != NULL);
			loop_analysis_process_loop(a, tree->loops[i], depth+1);
		}
	}

	/* now process states, unless the node is the pseudo root node */
	if (!tree->pseudo) {
		size_t i,n;
		n = tree->nstates;

		bool straight_path = true;

		/* looking for a straight path through the loop
		 *
		 * initial approach is to count in-loop edges.
		 * An in-loop edge is
		 * - an edge from one state the loop to another
		 * - that is not a back edge to the head of the loop
		 *
		 * So:
		 * 1) if edge is back edge to head, ignore
		 * 2) if edge is exit from the loop, ignore
		 * 3) otherwise, count
		 */
		for (i=0; i < n; i++) {
			unsigned st;
			size_t j;
			size_t inloop_edge_count = 0;

			assert(tree->states != NULL);
			assert(tree->states[i] < a->nstates);

			st = tree->states[i];

			for (j=0; j < a->states[st].nedges; j++) {
				unsigned dst;
				dst = a->states[st].edges[j].dst;

				if (dst != tree->head && loop_tree_node_contains(tree, dst)) {
					inloop_edge_count++;
				}
			}

			if (inloop_edge_count > 1) {
				straight_path = false;
				break;
			}
		}

		print_indent(stderr, depth);
		fprintf(stderr, "  >>> straight path? %s\n", straight_path ? "true" : "false");
	}

	fprintf(stderr, "\n");

	return 0;
}

static int
loop_analysis_analyze(struct dfavm_loop_analysis *a)
{
	int ret = -1;
	struct loop_array *loop_list = NULL;
	struct loop_tree *tree = NULL;

	ret = -1;

	a->pred_edges = build_pred_edges(a);
	if (a->pred_edges == NULL) {
		goto cleanup;
	}

	/* identify immediate dominators */
	if (identify_idoms(a) < 0) {
		goto cleanup;
	}

	/* identify natural loops */
	loop_list = identify_loops(a);
	if (loop_list == NULL) {
		goto cleanup;
	}

	/*
	fprintf(stderr, "---[ idom tree ]---\n");
	print_idom_tree(a, stderr);
	fprintf(stderr, "\n\n");

	dump_loop_analysis(a);

	print_loops(a, loop_list);
	*/

	tree = gather_loop_states(a, loop_list);
	if (tree == NULL) {
		goto cleanup;
	}

	/* Now identify straight paths through the loops
	 *
	 * We're looking for three kinds of optimizations:
	 *
	 * 1) searching for whole words
	 *
	 * 2) situations where loops, or initial parts of loops, can be
	 *    replaced by memchr, strspn, and strcspn
	 *    
	 *    NB: this may be a better peephole optimization?
	 *
	 */

	(void)print_loops;
	(void)print_idom_tree;
	(void)dump_loop_analysis;

	/* process the loop tree...
	 *
	 * We first process the inner-most loops.  Do a depth-first
	 * search, processing nodes in post-order:
	 *
	 * For each loop node:
	 *   1. process any children
	 *   2. process self
	 *
	 * TODO: depth-first search using recursion is convenient, but
	 *       probably not the safest.  Replace with an explicit
	 *       allocated stack.
	 */

	/* first mark all states as unvisited */
	{
		size_t i,n;
		
		n = a->nstates;
		for (i = 0; i < n; i++) {
			a->states[i].isvisited = 0;
		}
	}

	if (loop_analysis_process_loop(a, tree->root, 0) < 0) {
		goto cleanup;
	}

	/* original todo:
	 * 2) identify loops
	 * 3) find mergeable loop exits
	 *
	 *
	 * thoughts:
	 * - is it helpful to identify nested loops?
	 * - identify one or more "straight paths" through the loops
	 * - identify "entangled" paths like /^.*(abc|def).*$/ and
	 *   /^.*(abc|bcd).*$/
	 */

	ret = 0;

cleanup:
	free_loops(loop_list);
	free_loop_tree(tree);

	return ret;
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

	if (a->pred_edges != NULL) {
		free(a->pred_edges->offsets);
		free(a->pred_edges->edges);
		free(a->pred_edges);
	}

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
		loop_analysis_finalize(&loop_analysis);
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

