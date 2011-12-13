../../util/test -n "alt-ergo -restricted -parse-only -rules parsing" ../parsing/parsing.split
../../util/test -n "alt-ergo -restricted -type-only -rules typing" ../typing/typing.split
../../util/test -n "alt-ergo -restricted -rules sat" ../sat/sat.split
../../util/test -n "alt-ergo -restricted -rules cc" ../cc_uf_ac/cc_uf_ac.split
../../util/test -n "alt-ergo -restricted -rules arith" ../arith/arith.split  
 rubber -d tests.tex