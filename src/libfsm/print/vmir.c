/*
 * Copyright 2020 Shannon F. Stewman
 *
 * See LICENCE for the full copyright terms.
 */

#include <assert.h>
#include <string.h>
#include <stdint.h>
#include <errno.h>
#include <stdio.h>

#include <adt/set.h>

#include <fsm/fsm.h>
#include <fsm/pred.h>
#include <fsm/walk.h>
#include <fsm/print.h>
#include <fsm/options.h>
#include <fsm/vm.h>

#include "libfsm/internal.h"

#include "libfsm/vm/vm.h"

#include "ir.h"

void
fsm_print_vmir(FILE *f, const struct fsm *fsm)
{
	static const struct fsm_vm_compile_opts vm_opts = { FSM_VM_COMPILE_DEFAULT_FLAGS, FSM_VM_COMPILE_VM_V1, NULL };
	static const struct dfavm_assembler_ir zero;

	struct ir *ir;
	struct dfavm_assembler_ir a;

	assert(f != NULL);
	assert(fsm != NULL);
	assert(fsm->opt != NULL);

	ir = make_ir(fsm);
	if (ir == NULL) {
		return;
	}

	assert(ir != NULL);

	a = zero;

	if (!dfavm_compile_ir(&a, ir, vm_opts)) {
		goto finish;
	}

	dfavm_print_opcodes(f, &a);

	dfavm_opasm_finalize_op(&a);

finish:
	free_ir(fsm, ir);
}
