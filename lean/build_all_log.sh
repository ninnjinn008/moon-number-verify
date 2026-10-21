#!/bin/bash
# 付録の Lean ファイルを、.olean をすべて消してから順にコンパイルし、記録を残す。
# 記録：Lean の版、各ファイルの SHA-256、コンパイル時間と終了コード、出力（#print axioms を含む）、sorry の有無。
cd "$(dirname "$0")"
export LEAN_PATH=$PWD:/opt/lean/lean-4.12.0-linux/lib/lean
L=/opt/lean/lean-4.12.0-linux/bin/lean
LOG=${1:-build_log.txt}
ulimit -s unlimited
FILES="Moon Export OldPair G5 G13 G14 G6 Tables G7 Dec Encode TrCore TrPartsA TrPartsB TrPartsC TrPartsD TrPartsE TrPartsF TrPartsG TrPartsH TrPartsI TrPartsJ TrLitA TrLitB TrLitC TrLitD TrLitE TrLitF TrLitG TrLitH TrLitI TrLitJ TrAttr TrKer TrExp TrLem TrRel TrRelD TrRelE TrRelF TrRelG TrRelH TrRelI TrRelJ TrCheck TrMeans TrNat TrSyn TrSem TrDef TrL TrLO TrLO2 TrLO3 TrTh TrU TrUq1 TrUq2 TrUq3 TrUq4"
b() {
  local t0=$(date +%s)
  echo "=== $1.lean  開始 $(date '+%F %T')" >> $2
  $L --tstack=1000000 -o $1.olean $1.lean > /tmp/claude-0/out_$1.txt 2>&1; local rc=$?
  grep -v "unused variable\|linter\.\|consider restructuring\|omit .* in theorem\|^  [A-Za-z0-9_']* *$\|^note: this linter\|^Note: This linter" /tmp/claude-0/out_$1.txt >> $2
  echo "=== $1.lean  終了コード $rc、$(( $(date +%s) - t0 )) 秒" >> $2
}
{
  echo "Lean のコンパイル記録（月絶天葬数・改訂61 の付録）"
  echo "日時: $(date '+%F %T %Z')"
  echo "Lean: $($L --version)"
  echo "環境: $(uname -sm)、メモリ $(free -g | awk '/Mem/{print $2}') GB"
  echo; echo "--- ソースの SHA-256 ---"
  for f in $FILES; do sha256sum $f.lean; done
  echo; echo "--- sorry / admit / axiom 宣言の検索（コメントを含む素朴な検索）---"
  grep -n "\bsorry\b\|\badmit\b\|^axiom " $(for f in $FILES; do echo $f.lean; done) || echo "（該当なし）"
  echo
} > $LOG
rm -f *.olean *.ilean
for f in Moon Export OldPair G5 G13 G14 G6 Tables G7 Dec Encode TrCore TrPartsA TrPartsB TrPartsC TrPartsD TrPartsE TrPartsF TrPartsG TrPartsH TrPartsI TrPartsJ; do b $f $LOG; done
# TrLitB は 20 分程度かかるので並行して作り、記録は別に取ってあとで連結する
rm -f /tmp/claude-0/log_litb.txt
( b TrLitB /tmp/claude-0/log_litb.txt ) &
for f in TrLitA TrLitC TrLitD TrLitE TrLitF TrLitG TrLitH TrLitI TrLitJ TrAttr TrKer TrExp TrLem TrRel TrRelD TrRelE TrRelF TrRelG TrRelH TrRelI TrRelJ; do b $f $LOG; done
wait
cat /tmp/claude-0/log_litb.txt >> $LOG
for f in TrCheck TrMeans TrNat TrSyn TrSem TrDef TrL TrLO TrLO2 TrLO3 TrTh TrU TrUq1 TrUq2 TrUq3 TrUq4; do b $f $LOG; done
echo >> $LOG
echo "--- まとめ ---" >> $LOG
echo "注：OldPair.lean は、改訂28 以前の旧版の順序対の式（pair_old）で同じ絶対性の構成を試し、証明が通らないことを確かめるためのファイル（lean_export.py --old が書き出す）。終了コード 1 は意図どおり。旧版が実際に絶対的でないことの反例は test_pair.py にある。" >> $LOG
grep "終了コード" $LOG | awk '{print $2, $4}' | sort | uniq -c | awk '{print}' >> /dev/null
echo "コンパイルしたファイル: $(grep '^=== .*終了コード' $LOG | wc -l) 個" >> $LOG
echo "終了コードが 0 でないファイル: $(grep '^=== .*終了コード' $LOG | grep -v '終了コード 0、' | awk '{print $2}' | tr '\n' ' ')" >> $LOG
echo "error を含む行の数: $(grep -c 'error' $LOG)" >> $LOG
echo "完了 $(date '+%F %T')" >> $LOG
