#!/bin/bash
ls int*.bc | while read x; do
    echo $x
    coala $x 2>/dev/null | clingcon - ../encodings/arithmetic.lp 1000 -c k=0 2>&1 | tail -n 4 | head -n 1    
    grep "States" $x
    coala $x 2>/dev/null | clingcon - ../encodings/arithmetic.lp 1000 2>&1 | tail -n 4 | head -n 1
    grep "Transit" $x
    echo ""
done
ls add*.bc | while read x; do
    echo $x
    coala $x 2>/dev/null | clingcon - ../encodings/arithmetic_additive.lp 5000 -c k=0 2>&1 | tail -n 4 | head -n 1    
    grep "States" $x
    coala $x 2>/dev/null | clingcon - ../encodings/arithmetic_additive.lp 5000 2>&1 | tail -n 4 | head -n 1
    grep "Transit" $x
    echo ""
done
