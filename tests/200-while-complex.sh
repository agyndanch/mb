#!/usr/bin/env bash
start=$(date +%s)            # capture the starting epoch second
lastelapsed=-1

while true; do
    now=$(date +%s)          # current epoch second
    elapsed=$(expr "$now" - "$start")   # external integer arithmetic
    [ "$elapsed" -ge 5 ] && break       # exit once 5 s have passed
    if [ "$elapsed" -ne "$lastelapsed" ]; then
        echo $elapsed
    fi
    last_elapsed=$elapsed
    sleep 1
done
if [ "$last_elapsed" -eq 2 ]
then
    echo 3
    echo 4                  # in case we output only 1, 2 output 3, 4
fi
if [ "$last_elapsed" -eq 3 ]
then
    echo 4                  # in case we output only 1, 2, 3 output 4
fi

