#!/bin/sh

START_M=1
STOP_M=50
START_N=2
STOP_N=2

TESTS=1

INPUT=conjugacy.mag
OUTPUT=conjugacy.out
CHAR=@

touch $OUTPUT

for ((i = $START_M; i <= $STOP_M; i = i + 1)) ; do 
    for ((j = $START_N; j <= $STOP_N; j = j + 1)) ; do 
	for ((k = 1; k <= $TESTS; k = k + 1)) ; do
	    nice -19 magma char:=$CHAR m:=$i n:=$j nTests:=100 < $INPUT >> $OUTPUT;
	done;
    done;
done
