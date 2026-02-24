
for a in 1 2 "break" 3 4 "done"
do
    echo $a
    [ $a = "break" ] && break
done
