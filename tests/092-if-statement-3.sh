if [ -x /usr/bin/true ]; then
	bintrue=correct
elif [ -x /bin/true ]; then
	bintrue=wrong
else
	bintrue=wrong
fi
echo $bintrue

bintrue=wrong
if [ -x /bin/doesnotexist ]; then
	bintrue=wrong
elif [ -x /usr/bin/true ]; then
	bintrue=correct
else
	bintrue=wrong
fi
echo $bintrue

bintrue=wrong
if [ -x /bin/doesnotexist ]; then
    bintrue=wrong
elif [ -x /usr/bin/doesnotexist ]; then
    bintrue=wrong
else
    bintrue=correct
fi
echo $bintrue

