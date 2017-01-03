#!/bin/bash
ls int*.bc | while read x; do
    echo $x
    coala $x | clingcon - ../encodings/arithmetic.lp 1000 -c k=0 2>&1 | tail -n 4 | head -n 1    
    grep "States" $x
    coala $x  2>&1 | clingcon - ../encodings/arithmetic.lp 1000 2>&1 | tail -n 4 | head -n 1
    grep "Transit" $x
    echo ""
done
