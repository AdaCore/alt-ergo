../../util/test -n "alt-ergo -parse-only -qualif 0" ../parsing/parsing.split
../../util/test -n "alt-ergo -type-only -qualif 1" ../typing/typing.split
../../util/test -n "alt-ergo -qualif 2" ../sat/sat.split
../../util/test -n "alt-ergo -qualif 3" ../cc_uf_ac/cc_uf_ac.split
../../util/test -n "alt-ergo -qualif 4" ../arith/arith.split  
 rubber -d tests.tex