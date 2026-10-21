"""
Lean の expand（lean/TrCore.lean・TrExp.lean）と同じ手順を Python で行い、
部品を .rel に置き換えた式を展開し直したものが、生成プログラムの出力そのものと一致するかを確かめる（改訂45）。
Lean では記号列としての照合（lit）を最上位の部品だけで行い、sat_ext のように省いた部品はここで確かめる。
"""
import sys
sys.setrecursionlimit(1000000)
import lean_tr_export as X
from fol import Ctx, Atom, Not, And, All

def relify(f, root):
    """部品の呼び出しの部分木を ('rel', 名前, c, 引数) に置き換えた木。"""
    if f is not root and id(f) in X.REC:
        nm, as_, c = X.REC[id(f)]
        return ("rel", nm, c, tuple(as_))
    if isinstance(f, Atom): return (f.op, f.a, f.b)
    if isinstance(f, Not): return ("neg", relify(f.p, root))
    if isinstance(f, And): return ("conj", relify(f.p, root), relify(f.q, root))
    if isinstance(f, All): return ("all", f.v, relify(f.p, root))
    raise TypeError(f)

def plain(f):
    if isinstance(f, Atom): return (f.op, f.a, f.b)
    if isinstance(f, Not): return ("neg", plain(f.p))
    if isinstance(f, And): return ("conj", plain(f.p), plain(f.q))
    if isinstance(f, All): return ("all", f.v, plain(f.p))
    raise TypeError(f)

def rename(sig, t):
    k = t[0]
    if k in ("∈", "="): return (k, sig(t[1]), sig(t[2]))
    if k == "neg": return ("neg", rename(sig, t[1]))
    if k == "conj": return ("conj", rename(sig, t[1]), rename(sig, t[2]))
    if k == "all": return ("all", sig(t[1]), rename(sig, t[2]))
    if k == "rel": return ("rel", t[1], t[2], tuple(sig(a) for a in t[3]))

FULL = {}
def expand(t):
    k = t[0]
    if k in ("∈", "="): return t
    if k == "neg": return ("neg", expand(t[1]))
    if k == "conj": return ("conj", expand(t[1]), expand(t[2]))
    if k == "all": return ("all", t[1], expand(t[2]))
    if k == "rel":
        nm, c, as_ = t[1], t[2], t[3]
        n = len(as_)
        sig = lambda v: as_[v] if v < n else c + (v - n)
        return rename(sig, FULL[nm])

def main(targets):
    bad = 0
    for name, k, mk in X.PARTS:
        ctx = Ctx(start=0); vs = [ctx.fresh() for _ in range(k)]
        f = mk(ctx, *vs)
        full = expand(relify(f, f))
        FULL[name] = full
        if name in targets:
            ok = full == plain(f)
            print(f"{name}: 展開した式と生成プログラムの出力は{'一致' if ok else '不一致'}")
            bad += not ok
    return bad

if __name__ == "__main__":
    sys.exit(main(set(sys.argv[1:]) or {"sat_ext", "sat", "formula", "certificate"}))
