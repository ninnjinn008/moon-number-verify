"""
tr_expand_check.py の、共有のある大きな式でも動く版（改訂52）。

生成プログラムの出力は部分式を共有する DAG で、木として展開すると最終式では約 192 億記号になる。
そこで、木そのものではなく、木の構造から決まるハッシュ値（Merkle 木の方式：各節点のハッシュは、
節点の種類と子のハッシュ値から SHA-256 で作る）を、両側で同じ規則で計算して比べる。
  ・生成プログラムの出力：DAG の各節点について、id ごとにメモ化して計算する。
  ・部品から組み立て直した式：Lean の expand と同じく、部品の呼び出し .rel を、その部品の式を付け替え
    sig(v) = （v < 引数の個数なら引数、そうでなければ c + (v − 引数の個数)）で写したもので置き換える。
    付け替えの合成も同じ形 (引数の列, 基点) になる（下の層の呼び出しの番号 c は引数の個数以上：TrExp の relGe）。
    (部品, 付け替え) ごとにメモ化する。
二つのハッシュ値が一致すれば、（SHA-256 の衝突がない限り）二つの木は記号列として一致する。
"""
import sys, os, hashlib
sys.setrecursionlimit(1000000)
import lean_tr_export as X
from fol import Ctx, Atom, Not, And, All

def hx(*parts):
    return hashlib.sha256(repr(parts).encode()).digest()

RELIFIED = {}     # 部品名 → (引数の個数, 部品を .rel に置き換えた木)

def relify(f, root, memo):
    key = id(f)
    if key in memo:
        return memo[key]
    if f is not root and id(f) in X.REC:
        nm, as_, c = X.REC[id(f)]
        r = ("rel", nm, c, tuple(as_))
    elif isinstance(f, Atom): r = (f.op, f.a, f.b)
    elif isinstance(f, Not): r = ("neg", relify(f.p, root, memo))
    elif isinstance(f, And): r = ("conj", relify(f.p, root, memo), relify(f.q, root, memo))
    elif isinstance(f, All): r = ("all", f.v, relify(f.p, root, memo))
    else: raise TypeError(f)
    memo[key] = r
    return r

def h_plain(f, memo):
    key = id(f)
    if key in memo:
        return memo[key]
    if isinstance(f, Atom): r = hx("atom", f.op, f.a, f.b)
    elif isinstance(f, Not): r = hx("neg", h_plain(f.p, memo))
    elif isinstance(f, And): r = hx("conj", h_plain(f.p, memo), h_plain(f.q, memo))
    elif isinstance(f, All): r = hx("all", f.v, h_plain(f.p, memo))
    else: raise TypeError(f)
    memo[key] = r
    return r

def apply_sig(sig, v):
    args, base = sig
    return args[v] if v < len(args) else base + (v - len(args))

HE = {}
def h_expand(nm, sig):
    """部品 nm の展開した式を sig で付け替えた木のハッシュ値。"""
    key = (nm, sig)
    if key in HE:
        return HE[key]
    k, t = RELIFIED[nm]
    memo = {}
    def walk(t):
        tid = id(t)
        if tid in memo:
            return memo[tid]
        tag = t[0]
        if tag in ("∈", "="): r = hx("atom", tag, apply_sig(sig, t[1]), apply_sig(sig, t[2]))
        elif tag == "neg": r = hx("neg", walk(t[1]))
        elif tag == "conj": r = hx("conj", walk(t[1]), walk(t[2]))
        elif tag == "all": r = hx("all", apply_sig(sig, t[1]), walk(t[2]))
        elif tag == "rel":
            nm2, c, as_ = t[1], t[2], t[3]
            k2 = RELIFIED[nm2][0]
            assert len(as_) == k2 and c >= k, (nm, nm2, c, k)
            inner = (tuple(apply_sig(sig, a) for a in as_), apply_sig(sig, c) - 0)
            # 呼び出し側の付け替えの下で、内側の v ≥ k2 は c + (v − k2) ↦ sig(c + (v − k2))。
            # c ≥ k なので sig(c + j) = base + (c + j − len(args)) = sig(c) + j。
            r = h_expand(nm2, inner)
        else: raise TypeError(tag)
        memo[tid] = r
        return r
    r = walk(t)
    HE[key] = r
    return r

def main(targets, mutate=None):
    bad = 0
    for name, k, mk in X.PARTS:
        ctx = Ctx(start=0); vs = [ctx.fresh() for _ in range(k)]
        f = mk(ctx, *vs)
        t = relify(f, f, {})
        if mutate == name:              # 変異：深さ優先で最初に見つかる原子式の右の変数を一つずらす
            done = [False]
            def mut(t):
                if done[0]: return t
                if t[0] in ("∈", "="):
                    done[0] = True; return (t[0], t[1], t[2] + 1)
                if t[0] == "neg": return ("neg", mut(t[1]))
                if t[0] == "conj":
                    a = mut(t[1]); return ("conj", a, mut(t[2]))
                if t[0] == "all": return ("all", t[1], mut(t[2]))
                return t
            t = mut(t)
            assert done[0], "変異させる原子式がない"
        RELIFIED[name] = (k, t)
        if name in targets:
            ok = h_expand(name, (tuple(range(k)), k)) == h_plain(f, {})
            print(f"{name}: 組み立て直した式と生成プログラムの出力のハッシュ値は{'一致' if ok else '不一致'}", flush=True)
            bad += not ok
    return bad

if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    mut = next((a.split("=")[1] for a in sys.argv[1:] if a.startswith("--mutate=")), None)
    rc = 1 if main(set(args), mut) else 0
    print("終了コード", rc, flush=True)
    sys.stdout.flush()
    os._exit(rc)        # 大きなメモの解放を待たずに終了する（改訂53）
