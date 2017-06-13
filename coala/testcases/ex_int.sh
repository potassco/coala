#!/bin/bash
ls int*.bc | while read x; do
    echo $x

    res=`coala $x 2>/dev/null | clingcon - ../../encodings/arithmetic.lp 1000 -c k=0 2>&1 | tail -n 4 | head -n 1 | grep -o "[0-9]*"`
    c=`grep -o "[0-9]* States" $x | grep -o "[0-9]*"`
    if [ "$res" != "$c" ]; then
        echo " - "$res" States instead of "$c
        grep "States" $x
    fi

    res=`coala $x 2>/dev/null | clingcon - ../../encodings/arithmetic.lp 1000 2>&1 | tail -n 4 | head -n 1 | grep -o "[0-9]*"`
    c=`grep -o "[0-9]* Transit" $x | grep -o "[0-9]*"`
    if [ "$res" != "$c" ]; then
        echo " - "$res" Transitions instead of "$c
        grep "Transit" $x
    fi
done
ls add*.bc | while read x; do
    echo $x
    res=`coala $x 2>/dev/null | clingcon - ../../encodings/arithmetic_additive.lp 5000 -c k=0 2>&1 | tail -n 4 | head -n 1  | grep -o "[0-9]*"`   
    c=`grep -o "[0-9]* States" $x | grep -o "[0-9]*"`
    if [ "$res" != "$c" ]; then
        echo " - "$res" States instead of "$c
        grep "States" $x
    fi

    res=`coala $x 2>/dev/null | clingcon - ../../encodings/arithmetic_additive.lp 5000 2>&1 | tail -n 4 | head -n 1 | grep -o "[0-9]*"`
    c=`grep -o "[0-9]* Transit" $x | grep -o "[0-9]*"`
    if [ "$res" != "$c" ]; then
        echo " - "$res" Transitions instead of "$c
        grep "Transit" $x
    fi
done
