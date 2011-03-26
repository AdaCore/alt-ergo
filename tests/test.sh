#!/bin/bash

#shopt -s nullglob
COLS=$(tput cols)
ccx="$1 $ALTERGO_OPTIONS "
KO='\E[1;31m'"*KO\033[1m\033[0m"
OK='\E[1;32m'"OK\033[1m\033[0m"


function print_ok {
    tput hpa $(($COLS - 2))
    echo -e $OK
}

function print_ko {
    tput hpa $(($COLS - 3)) 
    echo -e $KO
}

score=0
nb=0

rm -f tests/valid/testfile-*.mlw
rm -f tests/invalid/testfile-*.mlw
rm -f tests/incorrects/testfile-*.mlw

util/split tests/valid/valid.split
util/split tests/invalid/invalid.split
util/split tests/incorrects/incorrects.split

echo

# tests valides
for f in tests/valid/testfile-*.mlw; do 
    nb=`expr $nb + 1`
    echo -n "$f "
    if timeout 4 $ccx $f |grep -q -w Valid; then
	print_ok
	score=`expr $score + 1`
    else 
        print_ko
    fi
done

# tests invalides
for f in tests/invalid/testfile-*.mlw; do 
    nb=`expr $nb + 1`
    echo -n "$f "
    if timeout 4 $ccx $f |grep -q -w "I don't"; then
	print_ok
	score=`expr $score + 1`
    else 
	print_ko
    fi
done

# tests incorrects
for f in tests/incorrects/testfile-*.mlw; do 
    nb=`expr $nb + 1`
    echo -n "$f "
    if $ccx $f >/dev/null; then
	print_ko
    else 
	print_ok
	score=`expr $score + 1`
    fi
done


percent=`expr 100 \* $score / $nb`
diff=`expr $nb - $score`
echo "score: $score/$nb : $percent% (-$diff)"


