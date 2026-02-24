# The operators "&&" and "||" shall have equal precedence and shall be evaluated 
# with left associativity. For example, both of the following commands write solely bar to standard output:
false && echo skipped || echo test andor ok
true || echo skipped && echo test orand ok
