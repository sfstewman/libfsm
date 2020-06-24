/*
 * Copyright 2019 Shannon F. Stewman
 *
 * See LICENCE for the full copyright terms.
 */

#include <stdio.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdint.h>
#include <assert.h>
#include <ctype.h>
#include <errno.h>
#include <string.h>

#include <fsm/fsm.h>
#include <fsm/vm.h>
#include "internal.h"
#include "print/ir.h"

#include "dfavm.h"

// VM state:
//
//   Conceptually, the VM is composed of:
//   - string buffer: holds 8-bit bytes to match
//   - program buffer: holds the VM bytecode
//   - address buffer: holds various tables and data
//   - three additional registers:
//
//     SP - string pointer  - 32-bit unsigned offset into string buffer
//     SB - string byte     -  8-bit unsigned register, usually holds
//                                   string buffer byte at SP
//     PC - program counter - 32-bit unsigned offset into program buffer
//
// Note: currently the address buffer and string buffer are currently not used

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

//
// Fixed encoding VM state:
//
//   The VM address buffer holds addresses for indirect branches.
//
// VM bytecodes:
//
//   There are four instructions:
//     BRANCH, IBRANCH, FETCH, and STOP.
//
//   Each instruction is 32-bits, encoded as follows:
//
//                1098 765 4   32109876  5432 1098 7654 3210
//                3322 222 2   22221111  1111 1100 0000 0000
//
//     STOP       0000 CCC R   AAAAAAAA  0000 0000 0000 0000
//     FETCH      0001 000 R   00000000  0000 0000 0000 0000
//     BRANCH     0010 CCC 0   AAAAAAAA  DDDD DDDD DDDD DDDD
//     IBRANCH    0011 CCC 0   AAAAAAAA  IIII IIII IIII IIII
//
//                IIII CCC R
//
//     R  = 0 fail / R = 1 succeed
//
//     C = comparison bit
//     A = argument bit
//     D = relative destination bit
//     I = index bit
//
//   BRANCH and IBRANCH are both ways to implement the BRANCH opcode.  The
//   difference between them is how the address is determined.
//
//     BRANCH  address field is a 16-bit signed relative offset
//     IBRANCH address field is a 16-bit index into the address table,
//             which holds a 32-bit unsigned value stored in the address buffer.
//             The argument is the address buffer entry.
//
// Instructions are encoded into 4 bytes.  The first byte holds the instruction
// type, the condition (if applicable) and the success argument (if applicable).
// The remaining three bytes depend on the instruction:
//
// BRANCH : 8-bit arg, 16-bit signed relative dest
// STOP   : 8-bit arg, rest unused
// FETCH  : no args, rest unused
//
// unused bits should be zeroed to keep bytecode forward-compatible.
//
//
// Op codes:
//
//            bits
// BRANCH     0000CCC0
// IBRANCH    0001CCC0
// STOP       0010CCCR  R  = 0 fail / R = 1 succeed
// FETCH      0011000R  R  = 0 fail / R = 1 succeed
//
//
//            bits
// BRANCH     FR000CCC
// IBRANCH    FR001CCC
// STOP       FR01XCCC  X  = 0 fail / X = 1 succeed
//
//   NB: in the future, 'always' comparisons may use their argument byte
//       for other purposes.
//
// Argument 
//   ARG is an 8-bit unsigned byte
//
// BRANCH - compare and branch
//   
//   If the comparison between ARG and CB is true Sets the PC based on the relative
//
// FETCH - fetch instructions
//
//   Fetch instructions fetch the next character from the stream and have a stop
//   bit that indicates success/failure if the stream has no more characters.
//
//   E = 0 indicates FETCHF, failure if EOS
//   E = 1 indicates FETCHS, success if EOS
//
//   FETCHS/F instructions should currently have comparison bits set to 00
//   (always).  A future version reserves the right to support conditional
//   FETCH.
//
//   (NB: the comparison bits are currently just ignored for FETCH instructions)
//
// STOP - stop instructions
//
// Stop instructions have an end bit: 
//     E = 0 indicates STOPF, stop w/ failure
//     E = 1 indicates STOPS, stop w/ success
//
//    STOPF generally indicates that there is no transition from the current
//         state matching the read character
//
//    STOPS generally indicates that the current state is an end state, is
//         complete, and all edges point back to the current state.
//
// BR - branch instructions
//
//   Branch instructions always have a signed relative destination argument.
//   The D bits specify its length:
//
//   DD
//   00    8-bit destination, 1-byte destination argument
//   01   16-bit destination, 2-byte destination argument
//   10   32-bit destination, 4-byte destination argument, LSB ignored
//
//   DD=11 is reserved for future use
//

enum dfavm_io_result
fsm_dfavm_save(FILE *f, const struct fsm_dfavm *vm)
{
	if (vm->version_major == DFAVM_VARENC_MAJOR && vm->version_minor == DFAVM_VARENC_MINOR) {
		return dfavm_v1_save(f, &vm->u.v1);
	}
	else {
		return DFAVM_IO_UNSUPPORTED_VERSION;
	}
}

enum dfavm_io_result
fsm_dfavm_load(FILE *f, struct fsm_dfavm *vm)
{
	unsigned char header[8];
	/* read and check header */
	if (fread(&header[0], sizeof header, 1, f) != 1) {
		return DFAVM_IO_ERROR_READING;
	}

	if (memcmp(&header[0], DFAVM_MAGIC, 6) != 0) {
		return DFAVM_IO_BAD_HEADER;
	}

	if (header[6] == DFAVM_VARENC_MAJOR && header[7] == DFAVM_VARENC_MINOR) {
		vm->version_major = header[6];
		vm->version_minor = header[7];

		return dfavm_load_v1(f, &vm->u.v1);
	}

	return DFAVM_IO_UNSUPPORTED_VERSION;
}

const char *
cmp_name(int cmp)
{
	switch (cmp) {
	case VM_CMP_ALWAYS: return "";   break;
	case VM_CMP_LT:     return "LT"; break;
	case VM_CMP_LE:     return "LE"; break;
	case VM_CMP_EQ:     return "EQ"; break;
	case VM_CMP_GE:     return "GE"; break;
	case VM_CMP_GT:     return "GT"; break;
	case VM_CMP_NE:     return "NE"; break;
	default:            return "??"; break;
	}
}

static void
print_op_ir(FILE *f, struct dfavm_op_ir *op)
{
	const char *cmp;
	int nargs = 0;

	cmp = cmp_name(op->cmp);

	// fprintf(f, "[%4lu] %1lu\t", (unsigned long)op->offset, (unsigned long)op->num_encoded_bytes);

	switch (op->instr) {
	case VM_OP_FETCH:
		fprintf(f, "FETCH%c%s",
			(op->u.fetch.end_bits == VM_END_FAIL) ? 'F' : 'S',
			cmp);
		break;

	case VM_OP_STOP:
		fprintf(f, "STOP%c%s",
			(op->u.stop.end_bits == VM_END_FAIL) ? 'F' : 'S',
			cmp);
		break;

	case VM_OP_BRANCH:
		{
			fprintf(f, "BR%s", cmp);
		}
		break;

	default:
		fprintf(f, "UNK_%d_%s", (int)op->instr, cmp);
	}

	if (op->cmp != VM_CMP_ALWAYS) {
		if (isprint(op->cmp_arg)) {
			fprintf(f, " '%c'", op->cmp_arg);
		} else {
			fprintf(f, " 0x%02x",(unsigned)op->cmp_arg);
		}

		nargs++;
	}

	if (op->instr == VM_OP_BRANCH) {
		fprintf(f, "%s [st=%lu]", ((nargs>0) ? ", " : " "),
			(unsigned long)op->u.br.dest_state);
		nargs++;
	}

	fprintf(f, "\t; [%u incoming]", op->num_incoming);
	switch (op->instr) {
	case VM_OP_FETCH:
		fprintf(f, "  [state %u]", op->u.fetch.state);
		break;

	case VM_OP_BRANCH:
		fprintf(f, "  [dest=%p]", (void *)op->u.br.dest_arg);
		break;

	default:
		break;
	}

	fprintf(f, "\n");
}

static void
print_vm_op(FILE *f, struct dfavm_vm_op *op)
{
	const char *cmp;
	int nargs = 0;

	cmp = cmp_name(op->cmp);

	fprintf(f, "[%4lu] %1lu\t", (unsigned long)op->offset, (unsigned long)op->num_encoded_bytes);

	switch (op->instr) {
	case VM_OP_FETCH:
		fprintf(f, "FETCH%c%s",
			(op->u.fetch.end_bits == VM_END_FAIL) ? 'F' : 'S',
			cmp);
		break;

	case VM_OP_STOP:
		fprintf(f, "STOP%c%s",
			(op->u.stop.end_bits == VM_END_FAIL) ? 'F' : 'S',
			cmp);
		break;

	case VM_OP_BRANCH:
		{
			char dst;
			switch (op->u.br.dest) {
			case VM_DEST_NONE:  dst = 'Z'; break;
			case VM_DEST_SHORT: dst = 'S'; break;
			case VM_DEST_NEAR:  dst = 'N'; break;
			case VM_DEST_FAR:   dst = 'F'; break;
			default:            dst = '!'; break;
			}

			fprintf(f, "BR%c%s", dst, cmp);
		}
		break;

	default:
		fprintf(f, "UNK_%d_%s", (int)op->instr, cmp);
	}

	if (op->cmp != VM_CMP_ALWAYS) {
		if (isprint(op->cmp_arg)) {
			fprintf(f, " '%c'", op->cmp_arg);
		} else {
			fprintf(f, " 0x%02x",(unsigned)op->cmp_arg);
		}

		nargs++;
	}

	if (op->instr == VM_OP_BRANCH) {
		fprintf(f, "%s%ld [dst_ind=%lu]", ((nargs>0) ? ", " : " "),
			(long)op->u.br.rel_dest, (unsigned long)op->u.br.dest_index);
		nargs++;
	}

	fprintf(f, "\t; %6lu bytes",
		(unsigned long)op->num_encoded_bytes);
	switch (op->instr) {
	case VM_OP_FETCH:
		fprintf(f, "  [state %u]", op->u.fetch.state);
		break;

	case VM_OP_BRANCH:
		// fprintf(f, "  [dest=%p]", (void *)op->u.br.dest_arg);
		break;

	default:
		break;
	}

	fprintf(f, "\n");
}

static void
print_vm_instr(FILE *f, const struct dfavm_assembler *a)
{
	size_t i;
	for (i=0; i < a->ninstr; i++) {
		fprintf(f, "%6zu | ", i);
		print_vm_op(f, &a->instr[i]);
	}
}

struct dfavm_op_ir_pool {
	struct dfavm_op_ir_pool *next;

	unsigned int top;
	struct dfavm_op_ir ops[1024];
};

#define ARRAYLEN(a) (sizeof (a) / sizeof ((a)[0]))

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
opasm_free(struct dfavm_assembler *a, struct dfavm_op_ir *op)
{
	static const struct dfavm_op_ir zero;

	*op = zero;
	op->next = a->freelist;
	a->freelist = op;
}

static void
opasm_free_list(struct dfavm_assembler *a, struct dfavm_op_ir *op)
{
	struct dfavm_op_ir *next;
	while (op != NULL) {
		next = op->next;
		opasm_free(a,op);
		op = next;
	}
}

static struct dfavm_op_ir *
opasm_new(struct dfavm_assembler *a, enum dfavm_op_instr instr, enum dfavm_op_cmp cmp, unsigned char arg)
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

		op->cmp   = cmp;
		op->instr = instr;

		op->cmp_arg = arg;
	}

	return op;
}

static struct dfavm_op_ir *
opasm_new_fetch(struct dfavm_assembler *a, unsigned state, enum dfavm_op_end end)
{
	struct dfavm_op_ir *op;

	op = opasm_new(a, VM_OP_FETCH, VM_CMP_ALWAYS, 0);
	if (op != NULL) {
		op->u.fetch.state    = state;
		op->u.fetch.end_bits = end;
	}

	return op;
}

static struct dfavm_op_ir *
opasm_new_stop(struct dfavm_assembler *a, enum dfavm_op_cmp cmp, unsigned char arg, enum dfavm_op_end end)
{
	struct dfavm_op_ir *op;

	op = opasm_new(a, VM_OP_STOP, cmp, arg);
	if (op != NULL) {
		op->u.stop.end_bits = end;
	}

	return op;
}

static struct dfavm_op_ir *
opasm_new_branch(struct dfavm_assembler *a, enum dfavm_op_cmp cmp, unsigned char arg, uint32_t dest_state)
{
	struct dfavm_op_ir *op;

	assert(dest_state < a->nstates);

	op = opasm_new(a, VM_OP_BRANCH, cmp, arg);
	if (op != NULL) {
		// op->u.br.dest  = VM_DEST_FAR;  // start with all branches as 'far'
		op->u.br.dest_state = dest_state;
	}

	return op;
}

void
dfavm_opasm_finalize(struct dfavm_assembler *a)
{
	static const struct dfavm_assembler zero;

	struct dfavm_op_ir_pool *pool_curr, *pool_next;

	if (a == NULL) {
		return;
	}

	free(a->ops);

	for (pool_curr = a->pool; pool_curr != NULL; pool_curr = pool_next) {
		pool_next = pool_curr->next;
		free(pool_curr);
	}

	free(a->instr);

	*a = zero;
}

struct dfa_table {
	long tbl[FSM_SIGMA_COUNT];

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
xlate_table_ranges(struct dfavm_assembler *a, struct dfa_table *table, struct dfavm_op_ir **opp)
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
				? opasm_new_stop(a, cmp, arg, VM_END_FAIL)
				: opasm_new_branch(a, cmp, arg, dst);

			if (op == NULL) {
				return -1;
			}

			*opp = op;
			opp = &(*opp)->next;
			count++;

			lo = i;
		}
	}

	if (lo < FSM_SIGMA_COUNT-1) {
		int64_t dst = table->tbl[lo];
		*opp = (dst < 0)
			? opasm_new_stop(a, VM_CMP_ALWAYS, 0, VM_END_FAIL)
			: opasm_new_branch(a, VM_CMP_ALWAYS, 0, dst);
		if (*opp == NULL) {
			return -1;
		}
		opp = &(*opp)->next;
		count++;
	}

	return count;
}

static int
xlate_table_cases(struct dfavm_assembler *a, struct dfa_table *table, struct dfavm_op_ir **opp)
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
			? opasm_new_stop(a, VM_CMP_EQ, i, VM_END_FAIL)
			: opasm_new_branch(a, VM_CMP_EQ, i, dst);
		if (*opp == NULL) {
			return -1;
		}
		opp = &(*opp)->next;
		count++;
	}

	*opp = (mdst < 0)
		? opasm_new_stop(a, VM_CMP_ALWAYS, 0, VM_END_FAIL)
		: opasm_new_branch(a, VM_CMP_ALWAYS, 0, mdst);
	if (*opp == NULL) {
		return -1;
	}
	opp = &(*opp)->next;
	count++;

	return count;
}

static int
initial_translate_table(struct dfavm_assembler *a, struct dfa_table *table, struct dfavm_op_ir **opp)
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

		*opp = opasm_new_stop(a, VM_CMP_NE, sym, VM_END_FAIL);
		if (*opp == NULL) {
			return -1;
		}
		opp = &(*opp)->next;

		*opp = opasm_new_branch(a, VM_CMP_ALWAYS, 0, dst);
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
dfa_table_init(struct dfa_table *table, long default_dest)
{
	static const struct dfa_table zero;
	int i;

	assert(table != NULL);

	*table = zero;

	for (i=0; i < FSM_SIGMA_COUNT; i++) {
		table->tbl[i] = default_dest;
	}
}

static int
initial_translate_partial(struct dfavm_assembler *a, struct ir_state *st, struct dfavm_op_ir **opp)
{
	struct dfa_table table;
	size_t i, ngrps;

	assert(st->strategy == IR_PARTIAL);

	dfa_table_init(&table, -1);

	ngrps = st->u.partial.n;
	for (i=0; i < ngrps; i++) {
		group_to_table(&table, &st->u.partial.groups[i]);
	}

	return initial_translate_table(a, &table, opp);
}

static int
initial_translate_dominant(struct dfavm_assembler *a, struct ir_state *st, struct dfavm_op_ir **opp)
{
	struct dfa_table table;
	size_t i, ngrps;

	assert(st->strategy == IR_DOMINANT);

	dfa_table_init(&table, st->u.dominant.mode);

	ngrps = st->u.dominant.n;
	for (i=0; i < ngrps; i++) {
		group_to_table(&table, &st->u.dominant.groups[i]);
	}

	return initial_translate_table(a, &table, opp);
}

static int
initial_translate_error(struct dfavm_assembler *a, struct ir_state *st, struct dfavm_op_ir **opp)
{
	struct dfa_table table;
	size_t i, ngrps;

	assert(st->strategy == IR_ERROR);

	dfa_table_init(&table, st->u.error.mode);

	error_to_table(&table, &st->u.error.error);

	ngrps = st->u.error.n;
	for (i=0; i < ngrps; i++) {
		group_to_table(&table, &st->u.error.groups[i]);
	}

	return initial_translate_table(a, &table, opp);
}

static struct dfavm_op_ir *
initial_translate_state(struct dfavm_assembler *a, const struct ir *ir, size_t ind)
{
	struct ir_state *st;
	struct dfavm_op_ir **opp;

	st = &ir->states[ind];
	opp = &a->ops[ind];

	if (st->isend && st->strategy == IR_SAME && st->u.same.to == ind) {
		*opp = opasm_new_stop(a, VM_CMP_ALWAYS, 0, VM_END_SUCC);
		return a->ops[ind];
	}

	*opp = opasm_new_fetch(a, ind, (st->isend) ? VM_END_SUCC : VM_END_FAIL);
	opp = &(*opp)->next;
	assert(*opp == NULL);

	switch (st->strategy) {
	case IR_NONE:
		*opp = opasm_new_stop(a, VM_CMP_ALWAYS, 0, VM_END_FAIL);
		opp = &(*opp)->next;
		break;

	case IR_SAME:
		*opp = opasm_new_branch(a, VM_CMP_ALWAYS, 0, st->u.same.to);
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
initial_translate(const struct ir *ir, struct dfavm_assembler *a)
{
	size_t i,n;

	n = a->nstates;

	for (i=0; i < n; i++) {
		a->ops[i] = initial_translate_state(a, ir, i);
	}

	return 0;
}

static void
fixup_dests(struct dfavm_assembler *a)
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
eliminate_unnecessary_branches(struct dfavm_assembler *a)
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

			if (next != NULL && dest == next->next &&
					(next->instr == VM_OP_BRANCH || next->instr == VM_OP_STOP) &&
					(next->num_incoming == 0) &&
					(*opp)->cmp != VM_CMP_ALWAYS && next->cmp == VM_CMP_ALWAYS) {
				/* rewrite last two instructions to eliminate a
				 * branch
				 */
				struct dfavm_op_ir rewrite1 = *next, rewrite2 = **opp;  // swapped
				int ok = 1;

				// invert the condition of current branch
				switch (rewrite2.cmp) {
				case VM_CMP_LT: rewrite1.cmp = VM_CMP_GE; break;
				case VM_CMP_LE: rewrite1.cmp = VM_CMP_GT; break;
				case VM_CMP_EQ: rewrite1.cmp = VM_CMP_NE; break;
				case VM_CMP_GE: rewrite1.cmp = VM_CMP_LT; break;
				case VM_CMP_GT: rewrite1.cmp = VM_CMP_LE; break;
				case VM_CMP_NE: rewrite1.cmp = VM_CMP_EQ; break;

				case VM_CMP_ALWAYS:
				default:
					// something is wrong
					ok = 0;
					break;
				}

				if (ok) {
					rewrite1.cmp_arg = rewrite2.cmp_arg;

					rewrite2.cmp = VM_CMP_ALWAYS;
					rewrite2.cmp_arg = 0;

					**opp = rewrite1;
					*next = rewrite2;
					count++;
					continue;
				}
			}

			opp = &(*opp)->next;
		}

	} while (count > 0);
}

static void
order_basic_blocks(struct dfavm_assembler *a)
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

static const long min_dest_1b = INT8_MIN;
static const long max_dest_1b = INT8_MAX;

static const long min_dest_2b = INT16_MIN;
static const long max_dest_2b = INT16_MAX;

// static const long min_dest_4b = INT32_MIN;
// static const long max_dest_4b = INT32_MAX;

static int
op_encoding_size(struct dfavm_vm_op *op, int max_enc)
{
	int nbytes = 1;

	assert(op != NULL);

	if (op->cmp != VM_CMP_ALWAYS) {
		nbytes++;
	}

	if (op->instr == VM_OP_BRANCH) {
		int32_t rel_dest = op->u.br.rel_dest;
		if (!max_enc && rel_dest >= min_dest_1b && rel_dest <= max_dest_1b) {
			nbytes += 1;
			op->u.br.dest = VM_DEST_SHORT;
		}
		else if (!max_enc && rel_dest >= min_dest_2b && rel_dest <= max_dest_2b) {
			nbytes += 2;
			op->u.br.dest = VM_DEST_NEAR;
		}
		else {
			// need 32 bits
			nbytes += 4;
			op->u.br.dest = VM_DEST_FAR;
		}
	}

	return nbytes;
}

static void
build_vm_op(const struct dfavm_op_ir *ir, struct dfavm_vm_op *op)
{
	static const struct dfavm_vm_op zero;

	*op = zero;
	op->ir = ir;
	op->instr   = ir->instr;
	op->cmp     = ir->cmp;
	op->cmp_arg = ir->cmp_arg;

	switch (op->instr) {
	case VM_OP_STOP:
		op->u.stop.end_bits = ir->u.stop.end_bits;
		break;

	case VM_OP_FETCH:
		op->u.fetch.state    = ir->u.fetch.state;
		op->u.fetch.end_bits = ir->u.fetch.end_bits;
		break;

	case VM_OP_BRANCH:
		assert(ir->u.br.dest_arg != NULL);

		op->u.br.dest_index = ir->u.br.dest_arg->index;

		/* zero initialize the other fields */
		op->u.br.dest = VM_DEST_NONE;
		op->u.br.rel_dest = 0;

		break;
	}
}

static struct dfavm_vm_op *
build_vm_op_array(const struct dfavm_op_ir *ops, size_t *np)
{
	const struct dfavm_op_ir *op;

	struct dfavm_vm_op *ilist;
	size_t i,ninstr;

	assert(np != NULL);

	/* count number of instructions */
	for (op = ops, ninstr=0; op != NULL; op = op->next) {
		ninstr++;
	}

	errno = 0;

	if (ninstr == 0) {
		*np = 0;
		return NULL;
	}

	ilist = calloc(ninstr, sizeof *ilist);
	if (ilist == NULL) {
		return NULL;
	}

	for (op = ops, i=0; op != NULL; op = op->next, i++) {
		assert(i < ninstr);

		build_vm_op(op, &ilist[i]);
	}

	*np = ninstr;
	return ilist;
}

static uint32_t
assign_opcode_indexes(struct dfavm_assembler *a)
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
assign_rel_dests(struct dfavm_assembler *a)
{
	uint32_t off;
	size_t i;

	assert(a != NULL);
	assert(a->instr != NULL);

	/* start with maximum branch encoding */
	off = 0;
	for (i=0; i < a->ninstr; i++) {
		struct dfavm_vm_op *op;
		int nenc;

		op = &a->instr[i];

		nenc = op_encoding_size(op, 1);

		assert(nenc > 0 && nenc <= 6);

		op->offset = off;
		op->num_encoded_bytes = nenc;
		off += nenc;
	}

	a->nbytes = off;

	/* iterate until we converge */
	for (;;) {
		int nchanged = 0;
		size_t i;

		for (i=0; i < a->ninstr; i++) {
			struct dfavm_vm_op *op;

			op = &a->instr[i];

			if (op->instr == VM_OP_BRANCH) {
				struct dfavm_vm_op *dest;
				int64_t diff;
				int nenc;

				assert(op->u.br.dest_index < a->ninstr);
				dest = &a->instr[op->u.br.dest_index];

				diff = (int64_t)dest->offset - (int64_t)op->offset;

				assert(diff >= INT32_MIN && diff <= INT32_MAX);

				op->u.br.rel_dest = diff;

				nenc = op_encoding_size(op, 0);
				if (nenc != op->num_encoded_bytes) {
					op->num_encoded_bytes = nenc;
					nchanged++;
				}
			}
		}

		if (nchanged == 0) {
			break;
		}

		/* adjust offsets */
		off = 0;
		for (i=0; i < a->ninstr; i++) {
			struct dfavm_vm_op *op;

			op = &a->instr[i];
			op->offset = off;
			off += op->num_encoded_bytes;
		}

		a->nbytes = off;
	}
}

static void
dump_states(FILE *f, struct dfavm_assembler *a)
{
	struct dfavm_op_ir *op;
	size_t count;

	count = 0;
	for (op = a->linked; op != NULL; op = op->next) {
		if (op->instr == VM_OP_FETCH) {
			unsigned state = op->u.fetch.state;
			fprintf(f, "%6s |    ; state %u %p %s\n", "", state, (void *)op, (state == a->start) ? "(start)" : "");
		}

		fprintf(f, "%6zu | %p | %6lu |  ", count++, (void*)op, (unsigned long)op->index);
		print_op_ir(f, op);
	}

	fprintf(f, "%6lu total bytes\n", (unsigned long)a->nbytes);
}

static void
print_all_states(struct dfavm_assembler *a)
{
	dump_states(stderr, a);
}

static struct fsm_dfavm *
dfavm_compile(const struct ir *ir, struct fsm_vm_compile_opts opts)
{
	static const struct dfavm_assembler zero;

	struct fsm_dfavm *vm;
	struct dfavm_assembler a;
	size_t nstates;

	nstates = ir->n;
	a = zero;

	a.nstates = nstates;
	a.start = ir->start;

	a.ops = calloc(nstates, sizeof a.ops[0]);
	if (a.ops == NULL) {
		goto error;
	}

	if (initial_translate(ir, &a) < 0) {
		goto error;
	}

	fixup_dests(&a);

	if (opts.flags & FSM_VM_COMPILE_PRINT_IR_PREOPT) {
		FILE *f = (opts.log != NULL) ? opts.log : stdout;

		fprintf(f, "---[ before optimization ]---\n");
		dump_states(f, &a);
		fprintf(f, "\n");
	}

	order_basic_blocks(&a);

	/* basic optimizations */
	if (opts.flags & FSM_VM_COMPILE_OPTIM) {
		eliminate_unnecessary_branches(&a);
	}

	/* optimization is finished.  now assign opcode indexes */
	assign_opcode_indexes(&a);

	if (opts.flags & FSM_VM_COMPILE_PRINT_IR) {
		FILE *f = (opts.log != NULL) ? opts.log : stdout;

		fprintf(f, "---[ final IR ]---\n");
		dump_states(f, &a);
		fprintf(f, "\n");
	}

	/* build vm instructions */
	a.instr = build_vm_op_array(a.linked, &a.ninstr);
	if (a.instr == NULL) {
		goto error;
	}

	assign_rel_dests(&a);

#if DEBUG_VM_OPCODES
	dump_states(stdout, &a);
#endif /* DEBUG_VM_OPCODES */

	if (opts.flags & FSM_VM_COMPILE_PRINT_ENC) {
		FILE *f = (opts.log != NULL) ? opts.log : stdout;

		fprintf(f,"---[ vm instructions ]---\n");
		print_vm_instr(f, &a);
		fprintf(f, "\n");
	}

	/* XXX: better error handling */
	vm = NULL;
	errno = EINVAL;

	switch (opts.output) {
	case FSM_VM_COMPILE_VM_V1:
		vm = encode_opasm_v1(&a);
		break;

	case FSM_VM_COMPILE_VM_V2:
		vm = encode_opasm_v2(&a);
		break;
	}

	if (vm == NULL) {
		goto error;
	}

	dfavm_opasm_finalize(&a);

	return vm;

error:
	dfavm_opasm_finalize(&a);
	return NULL;
}

struct fsm_dfavm *
fsm_vm_compile_with_options(const struct fsm *fsm, struct fsm_vm_compile_opts opts)
{
	struct ir *ir;
	struct fsm_dfavm *vm;

	(void)dump_states;  /* make clang happy */
	(void)print_all_states;
	(void)print_vm_instr;

	ir = make_ir(fsm);
	if (ir == NULL) {
		return NULL;
	}

	vm = dfavm_compile(ir, opts);

	if (vm == NULL) {
		int errsv = errno;
		free_ir(fsm,ir);
		errno = errsv;

		return NULL;
	}

	free_ir(fsm,ir);
	return vm;
}

struct fsm_dfavm *
fsm_vm_compile(const struct fsm *fsm)
{
	// static const struct fsm_vm_compile_opts defaults = { FSM_VM_COMPILE_DEFAULT_FLAGS | FSM_VM_COMPILE_PRINT_IR_PREOPT | FSM_VM_COMPILE_PRINT_IR, NULL };
	static const struct fsm_vm_compile_opts defaults = { FSM_VM_COMPILE_DEFAULT_FLAGS, FSM_VM_COMPILE_VM_V1, NULL };

	return fsm_vm_compile_with_options(fsm, defaults);
}

void
fsm_vm_free(struct fsm_dfavm *vm)
{
	(void)vm;
}

static enum dfavm_state
vm_match(const struct fsm_dfavm *vm, struct vm_state *st, const char *buf, size_t n)
{
	if (vm->version_major == DFAVM_VARENC_MAJOR && vm->version_minor == DFAVM_VARENC_MINOR) {
		return vm_match_v1(&vm->u.v1, st, buf, n);
	} else if (vm->version_major == DFAVM_FIXEDENC_MAJOR && vm->version_minor == DFAVM_FIXEDENC_MINOR) {
		return vm_match_v2(&vm->u.v2, st, buf, n);
	}

	return VM_FAIL;
}

static enum dfavm_state 
vm_end(const struct fsm_dfavm *vm, struct vm_state *st)
{
	(void)vm;

#if DEBUG_VM_EXECUTION
	fprintf(stderr, "END: st->state = %d, st->fetch_state = %d\n",
		st->state, st->fetch_state);
#endif /* DEBUG_VM_EXECUTION */

	if (st->state != VM_MATCHING) {
		return st->state;
	}

	return (st->fetch_state == VM_END_SUCC) ? VM_SUCCESS : VM_FAIL;
}

static const struct vm_state state_init;

int
fsm_vm_match_file(const struct fsm_dfavm *vm, FILE *f)
{
	struct vm_state st = state_init;
	enum dfavm_state result;
	char buf[4096];

	result = VM_FAIL;
	for (;;) {
		size_t nb;

		nb = fread(buf, 1, sizeof buf, f);
		if (nb == 0) {
			break;
		}

		result = vm_match(vm, &st, buf, nb);
		if (result != VM_MATCHING) {
			return result == VM_SUCCESS;
		}
	}

	if (ferror(f)) {
		return 0;
	}

	return vm_end(vm, &st) == VM_SUCCESS;
}

int
fsm_vm_match_buffer(const struct fsm_dfavm *vm, const char *buf, size_t n)
{
	struct vm_state st = state_init;
	enum dfavm_state result;

	vm_match(vm, &st, buf, n);
	result = vm_end(vm, &st);

	return result == VM_SUCCESS;
}
