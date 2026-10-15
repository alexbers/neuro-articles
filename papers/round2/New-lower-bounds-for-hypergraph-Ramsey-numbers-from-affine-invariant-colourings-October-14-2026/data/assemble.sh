#!/bin/bash
# assemble final Main.lean (core Lean, no Mathlib) from the certificate parts
set -e
cd ./attempts2/B02-ramsey
R564=${1:-79}
{
echo "/-!"
echo "# New lower bounds for hypergraph Ramsey numbers (B02, October 14, 2026)"
echo ""
echo "Five explicit colourings, each checked by the Lean kernel (\`decide +kernel\`, no \`native_decide\`):"
echo "* \`R453.main\`: R(4,5;3) ≥ 38  (2-colouring of the triples of {0,…,36}, no red K₄^(3), no blue K₅^(3))"
echo "* \`R453f.main\`: the same bound, re-checked without using any symmetry (kernel search over all tuples)"
echo "* \`R553.main\`: R(5,5;3) ≥ 98  (2-colouring of the triples of {0,…,96}, no monochromatic K₅^(3))"
echo "* \`R463.main\`: R(4,6;3) ≥ 68  (2-colouring of the triples of {0,…,66}, no red K₄^(3), no blue K₆^(3))"
echo "* \`R554.main\`: R(5,5;4) ≥ 38  (2-colouring of the 4-sets of {0,…,36}, no monochromatic K₅^(4))"
echo "* \`R564.main\`: R(5,6;4) ≥ $((R564+1))  (2-colouring of the 4-sets of {0,…,$((R564-1))}, no red K₅^(4), no blue K₆^(4))"
echo ""
echo "A colouring of the r-subsets of {0,…,N-1} is given as a Boolean function \`col\` on increasing r-tuples"
echo "(true = red). Each colouring is defined from the differences to the smallest element, hence it is"
echo "translation invariant; the kernel checks that no monochromatic clique contains the vertex 0, and"
echo "\`col_shift\` reduces an arbitrary clique to one containing 0."
echo "-/"
echo ""
cat lean/R453/Prune37.lean; echo; cat lean/R453/MainGen37.lean; echo
cat lean/R453/FullNoSym37.lean | sed '/^set_option/d'; echo
cat lean/R553/Prune97.lean | sed '/^set_option/d'; echo; cat lean/R553/MainGen97.lean; echo
cat lean/R463/Prune67.lean | sed '/^set_option/d'; echo; cat lean/R463/MainGen67.lean; echo
cat lean/R554/Tree37.lean | sed '/^set_option/d'; echo
cat lean/R564/Tree${R564}.lean | sed '/^set_option/d'; echo
} > lean/Main.lean
wc -c lean/Main.lean
