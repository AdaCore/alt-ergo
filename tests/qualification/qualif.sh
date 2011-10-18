../../util/test -n "../../alt-ergo.opt -parse-only -qualif 0" ../parsing/parsing.split
../../util/test -n "../../alt-ergo.opt -type-only -qualif 1" ../typing/typing.split
../../util/test -n "../../alt-ergo.opt -qualif 2" ../sat/sat.split
../../util/test -n "../../alt-ergo.opt -qualif 3" ../cc_uf_ac/cc_uf_ac.split 
 rubber -d tests.tex