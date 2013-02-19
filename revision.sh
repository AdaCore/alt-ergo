revision=""

svn_info=`svn info --xml 2> /dev/null`

if [ $? -eq 0 ]
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
else
    svn_info=`git svn info 2> /dev/null`

    if [ $? -eq 0 ]
    then
        rev_attr=`echo "$svn_info" | grep "Revision:" | cut -d " " -f2`
        if [ "$rev_attr" != "" ]
        then
            revision="-svn-rev-$rev_attr"
        fi
    fi

fi

echo $revision

