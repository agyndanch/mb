if [ -x /usr/bin/true ]; then
	bintrue=/usr/bin/true
elif [ -x /sbin/true ]; then
	bintrue=/sbin/true
elif [ -x /bin/true ]; then
	bintrue=/bin/true
else
	bintrue=true
fi
echo $bintrue
