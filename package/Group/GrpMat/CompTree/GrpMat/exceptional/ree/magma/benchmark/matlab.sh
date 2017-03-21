#!/bin/sh

BASENAME=conjugacy
CHAR=@
RAW_INPUT=${BASENAME}.out
export BENCH_INPUT=${BASENAME}.txt
export BENCH_OUTPUT=${BASENAME}.eps
BENCH_FILE=conj_matlab

./benchmark_output.pl $CHAR < $RAW_INPUT > $BENCH_INPUT
OPTS='-nosplash -nodesktop -nodisplay'
matlab ${OPTS} -r $BENCH_FILE
