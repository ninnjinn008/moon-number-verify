#!/bin/bash
# CI（GitHub Actions）用：すべての Lean ファイルを、.olean を消してから一つずつ順にコンパイルし、記録を残す。
# build_all_log.sh と同じ順序・同じ記録の形式。並列にはしない（メモリの少ない環境でも通るように）。
# 終了コード：OldPair.lean（失敗するのが正しい）以外がすべて成功し、sorry・admit・axiom 宣言がなければ 0。
cd "$(dirname "$0")"
LOG=${1:-build_log_ci.txt}
export LEAN_PATH=$PWD:$(lean --print-libdir)
ulimit -s unlimited 2>/dev/null || true
FILES=$(grep '^FILES=' build_all_log.sh | sed 's/FILES="//; s/"$//')
{
  echo "Lean のコンパイル記録（CI、月絶天葬数）"
  echo "日時: $(date -u '+%F %T UTC')"
  echo "Lean: $(lean --version)"
  echo "環境: $(uname -sm)、メモリ $(free -g | awk '/Mem/{print $2}') GB、CPU $(nproc)"
  echo "コミット: ${GITHUB_SHA:-不明}"
  echo; echo "--- ソースの SHA-256 ---"
  for f in $FILES; do sha256sum $f.lean; done
  echo; echo "--- sorry / admit / axiom 宣言の検索 ---"
  grep -n "\bsorry\b\|\badmit\b\|^axiom " $(for f in $FILES; do echo $f.lean; done) || echo "（該当なし）"
  echo
} > $LOG
bad=0
grep -q "\bsorry\b\|\badmit\b\|^axiom " $(for f in $FILES; do echo $f.lean; done) && bad=1
rm -f *.olean *.ilean
for f in $FILES; do
  t0=$(date +%s)
  echo "=== $f.lean  開始 $(date -u '+%F %T')" >> $LOG
  lean --tstack=1000000 -o $f.olean $f.lean > out_$f.txt 2>&1; rc=$?
  grep -v "unused variable\|linter\.\|consider restructuring\|omit .* in theorem\|^  [A-Za-z0-9_']* *$\|^note: this linter\|^Note: This linter\|^warning: automatically included\|^warning: .*declaration uses" out_$f.txt >> $LOG
  rm -f out_$f.txt
  echo "=== $f.lean  終了コード $rc、$(( $(date +%s) - t0 )) 秒" >> $LOG
  echo "$f: 終了コード $rc（$(( $(date +%s) - t0 )) 秒）"
  if [ "$f" = OldPair ]; then [ $rc -ne 0 ] || bad=1; else [ $rc -eq 0 ] || bad=1; fi
done
echo >> $LOG
echo "コンパイルしたファイル: $(grep -c '^=== .*終了コード' $LOG) 個" >> $LOG
echo "判定: $([ $bad -eq 0 ] && echo '成功（OldPair 以外はすべて終了コード 0、OldPair は意図どおり失敗）' || echo '失敗')" >> $LOG
tail -3 $LOG
exit $bad
