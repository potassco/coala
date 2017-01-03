#!/bin/bash
echo "Renaming directories"
find -name "*bc2asp*" -type d | while read x; do
    y=${x//bc2asp/coala}; 
    svn mv $x $y;
    if [ "$?" != "0" ]; then
        mv $x $y
    fi
done

echo "Renaming files"
find -name "*bc2asp*" | while read x; do
    y=${x//bc2asp/coala}; 
    svn mv $x $y;
    if [ "$?" != "0" ]; then
        mv $x $y
    fi
done

echo "The tricky part: Replacing in files!"
grep -rl "bc2asp" --exclude "rename_to_coala.sh" | while read filet; do
     echo "Working on $filet"
     sed -i 's/bc2asp/coala/g' $filet
done

