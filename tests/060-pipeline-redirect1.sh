echo data > .inputfile
<.inputfile cat | rev | wc -m > .outputfile
cat .outputfile
rm .inputfile .outputfile
