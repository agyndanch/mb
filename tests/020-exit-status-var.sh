#
# Test that minibash correctly sets the $? variable to the exit code of the last program.
#

echo Hello World 123
echo $?
false
echo $?
true
echo $?
