if true; then
    echo true is true   
else
    echo false is true   
fi
if false; then
    echo false is not true   
else
    echo false is false
fi
if false; then
    echo false is not true   
else
    # see https://pubs.opengroup.org/onlinepubs/9699919799/utilities/V3_chap02.html#colon
    :
fi
