#!/usr/bin/env bash

echo "testing directory " $1
for input in $1/*.lat ; do
    if ./latc_x86_64 $input
    then
        exe=$1/$(basename $input .lat)
        in=$exe.input
        myout=$exe.myout
        output=$exe.output
        echo $exe
        if [ -e $in ]
        then
            $exe < $in > $myout
        else
            $exe > $myout
        fi
        diff $myout $output
    fi
done
