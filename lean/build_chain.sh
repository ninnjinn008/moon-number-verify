#!/bin/bash
# 書き写しの検証の Lean ファイルを順にコンパイルする（TrLitB は時間がかかるので並行して作る）
cd "$(dirname "$0")"
export LEAN_PATH=$PWD:/opt/lean/lean-4.12.0-linux/lib/lean
L=/opt/lean/lean-4.12.0-linux/bin/lean
b() { echo "== $1 $(date +%T)"; ulimit -s unlimited; $L --tstack=1000000 -o $1.olean $1.lean 2>&1 | grep -v "unused\|linter\|consider restruct\|omit\|^  [a-zA-Z]* *$\|^note:" ; }
b TrCore; b TrPartsA; b TrPartsB; b TrPartsC; b TrPartsD; b TrPartsE; b TrPartsF; b TrPartsG; b TrPartsH; b TrPartsI; b TrPartsJ
( b TrLitB > /tmp/claude-0/litb.out 2>&1 ) &
b TrLitA; b TrLitC; b TrLitD; b TrLitE; b TrLitF; b TrLitG; b TrLitH; b TrLitI; b TrLitJ
b TrKer; b TrExp; b TrLem; b TrRel; b TrRelD; b TrRelE; b TrRelF; b TrRelG; b TrRelH; b TrRelI; b TrRelJ
wait
cat /tmp/claude-0/litb.out
b TrCheck; b TrMeans; b TrNat; b TrSyn; b TrSem; b G6; b TrDef; b TrL; b TrLO; b TrLO2; b TrLO3; b TrTh; b TrU; b TrUq1; b TrUq2; b TrUq3; b TrUq4
echo "== done $(date +%T)"
