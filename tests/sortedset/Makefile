.include "../../share/mk/top.mk"

TEST.tests/sortedset != ls -1 tests/sortedset/sortedset*.c
TEST_SRCDIR.tests/sortedset = tests/sortedset
TEST_OUTDIR.tests/sortedset = ${BUILD}/tests/sortedset

.for n in ${TEST.tests/sortedset:T:R:C/^sortedset//}
test:: ${TEST_OUTDIR.tests/sortedset}/res${n}

SRC += ${TEST_SRCDIR.tests/sortedset}/sortedset${n}.c
CFLAGS.${TEST_SRCDIR.tests/sortedset}/sortedset${n}.c = -UNDEBUG
${TEST_OUTDIR.tests/sortedset}/run${n}: ${TEST_OUTDIR.tests/sortedset}/sortedset${n}.o ${BUILD}/lib/adt.o
	${CC} ${CFLAGS} -o ${TEST_OUTDIR.tests/sortedset}/run${n} ${TEST_OUTDIR.tests/sortedset}/sortedset${n}.o ${BUILD}/lib/adt.o
${TEST_OUTDIR.tests/sortedset}/res${n}: ${TEST_OUTDIR.tests/sortedset}/run${n}
	( ${TEST_OUTDIR.tests/sortedset}/run${n} 1>&2 && echo PASS || echo FAIL ) > ${TEST_OUTDIR.tests/sortedset}/res${n}
.endfor
