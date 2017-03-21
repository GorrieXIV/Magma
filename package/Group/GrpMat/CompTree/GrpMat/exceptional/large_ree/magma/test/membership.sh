#!/bin/sh

for ((i = 5; i <= 30; i = i + 1)) ; do 
    nice -19 magma m:=21 batch:=$i < membership.mag ;
done
