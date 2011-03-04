#!/bin/sh

#shopt -s nullglob

ccx="$1 $ALTERGO_OPTIONS "


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
    echo -n $f;
    if timeout 4 $ccx $f |grep -q -w Valid; then
	echo ": ok";
	score=`expr $score + 1`
    else 
	echo ": erreur";
    fi
done

# tests invalides
for f in tests/invalid/testfile-*.mlw; do 
    nb=`expr $nb + 1`
    echo -n $f;
    if timeout 4 $ccx $f |grep -q -w "I don't"; then
	echo ": ok";
	score=`expr $score + 1`
    else 
	echo ": erreur";
    fi
done

# tests incorrects
for f in tests/incorrects/testfile-*.mlw; do 
    nb=`expr $nb + 1`
    echo -n $f;
    if $ccx $f >/dev/null; then
	echo ": erreur";
    else 
	echo ": ok";
	score=`expr $score + 1`
    fi
done


percent=`expr 100 \* $score / $nb`
diff=`expr $nb - $score`
echo "score: $score/$nb : $percent% (-$diff)"


