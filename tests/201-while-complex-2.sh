#!/usr/bin/env bash

# Mark the moment we start, then calculate the Unix-time stamp 1.5 s in the future.
target_epoch=$(expr "$(date +%s)" + 1)
echo "Starting"
count=0

# Loop until the current time reaches or passes that target.
while [ "$(date +%s)" -lt "$target_epoch" ]; do
    count=$(expr $count + 1)
    echo $count
    sleep .2
done

while [ "$count" -lt 8 ]; do
    count=$(expr $count + 1)
    echo $count
done
