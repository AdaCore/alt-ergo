VERSION=`grep "^VERSION=" Makefile | cut -d"=" -f2`

revision=""

svn_info=`svn info --xml 2> /dev/null`

if [ $? ]
then 
    for line in $svn_info
    do
        # detect revision
        rev_attr=`echo $line | grep "revision" | cut -d "\"" -f2`
        if [ "$rev_attr" != "" ]
        then
            revision="-svn-rev-$rev_attr"
        fi
    done
fi

echo "let version = \""$VERSION$revision"\""  >> version.ml

