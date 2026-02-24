#
# Test that minibash correctly sets the $? variable to the exit code of the last program
# even if it terminates with a signal.
# Assumes die is in PATH
#

die -segfault 
echo $?
# 139

die -abort
echo $?
# 134

die -divzero
echo $?
# 136
