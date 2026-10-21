# 月絶天葬数（N_Moon）の検証用ファイル

審議用文書「巨大数庭園数に対抗する数 N の定義」の付録 F のプログラムと Lean ファイル一式。

GitHub Actions（`.github/workflows/verify.yml`）が、push のたびに次を独立の環境で実行する。

- **lean**：Lean 4.12.0（elan で導入）で `lean/` のすべての Lean ファイルを、.olean を消してから順にコンパイルする（`lean/build_ci.sh`）。OldPair.lean は失敗するのが正しいファイル。記録は成果物 `lean-build-log` に残る。
- **formula**：最終式 φ の Merkle 方式のハッシュ照合（`tr_hash_check.py lngn`）と、全文（19,229,718,256 記号）の独立な構文検査（`phi_syntax_check.c`）。

これは文書の定理 G のうち、Lean による部分（書き写し・意味・一意性）と、最終式の構文の再現であり、紙の存在証明（別紙 G.23〜G.26）とメタな接続（G.19）は含まない。
