# some variations on redirecting to standard error + out
# should redirect only stdout 
writetostderr | rev
# should redirect both stdout and stderr
writetostderr |& rev
# should redirect both stdout and stderr
writetostderr >& .out5
cat .out5
rm .out5
