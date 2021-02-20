.include "../../share/mk/top.mk"

TEST.tests/bitmap != ls -1 tests/bitmap/bm*.c
TEST_SRCDIR.tests/bitmap = tests/bitmap
TEST_OUTDIR.tests/bitmap = ${BUILD}/tests/bitmap

#.for n in ${TEST.tests/bitmap:T:R:C/^bm//}
#INCDIR.${TEST_SRCDIR.tests/bitmap}/bm${n}.c += src/adt
#.endfor

# not all concrete set interfaces use all static functions from set.inc
#.if ${CC:T:Mgcc} || ${CC:T:Mclang}
#.for n in ${TEST.tests/bitmap:T:R:C/^bm//}
#CFLAGS.${TEST_SRCDIR.tests/bitmap}/bm${n}.c += -Wno-unused-function
#.endfor
#.endif

.for n in ${TEST.tests/bitmap:T:R:C/^bm//}
test:: ${TEST_OUTDIR.tests/bitmap}/res${n}
SRC += ${TEST_SRCDIR.tests/bitmap}/bm${n}.c
CFLAGS.${TEST_SRCDIR.tests/bitmap}/bm${n}.c += -UNDEBUG
${TEST_OUTDIR.tests/bitmap}/run${n}: ${TEST_OUTDIR.tests/bitmap}/bm${n}.o ${BUILD}/lib/adt.o
	${CC} ${CFLAGS} ${CFLAGS.${TEST_SRCDIR.tests/bitmap}/bm${n}.c} -o ${TEST_OUTDIR.tests/bitmap}/run${n} ${TEST_OUTDIR.tests/bitmap}/bm${n}.o ${BUILD}/lib/adt.o
${TEST_OUTDIR.tests/bitmap}/res${n}: ${TEST_OUTDIR.tests/bitmap}/run${n}
	( ${TEST_OUTDIR.tests/bitmap}/run${n} 1>&2 && echo PASS || echo FAIL ) > ${TEST_OUTDIR.tests/bitmap}/res${n}
.endfor
