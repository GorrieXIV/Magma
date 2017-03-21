#!/bin/sh

START_M=1
STOP_M=5
START_N=1
STOP_N=3
INPUT=blackbox.mag
OUTPUT=blackbox.out
CHAR=@

touch $OUTPUT

for ((i = $START_M; i <= $STOP_M; i = i + 1)) ; do 
    for ((j = $START_N; j <= $STOP_N; j = j + 1)) ; do 
	nice -19 magma char:=$CHAR m:=$i n:=$j < $INPUT >> $OUTPUT;
    done;
done

