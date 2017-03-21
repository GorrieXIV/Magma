#!/bin/bash

START_M=21
STOP_M=40
START_N=1
STOP_N=1

TESTS=1
NTESTS=100

INPUT=conjugacy.m
OUTPUT=conjugacy.out
CHAR=@

touch $OUTPUT

for ((i = $START_M; i <= $STOP_M; i = i + 1)) ; do 
    for ((j = $START_N; j <= $STOP_N; j = j + 1)) ; do 
	for ((k = 1; k <= $TESTS; k = k + 1)) ; do
	    nice -19 magma char:=$CHAR m:=$i n:=$j nTests:=$NTESTS < $INPUT >> $OUTPUT;
	done;
    done;
done
