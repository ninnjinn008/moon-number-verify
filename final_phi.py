"""
最終式 φ(x)（x = LNGN_I を定める L-式）の生成と記号数の計数。

  python3 final_phi.py                 記号数と自由変数を出力（数分）
  python3 final_phi.py --stream FILE   φ の全文を FILE に書き出す（約 224 億字。数時間かかり、ディスクも同程度必要）

記号の数え方は本文第 2 節のとおり（x とプライムを含め、基本記号 { x, ′, ¬, ∧, ∀, ∈, =, (, ) } を 1 つずつ数える。
∃・∨・→ は ¬・∧・∀ に展開済み）。自由変数は x（プライムなし）だけ。
"""
import sys
from fol import Ctx, length, has_oracle, free, Atom, Not, And, All, var
import ffunc as FF

def build():
    ctx = Ctx(start=0); x = ctx.fresh()
    return FF.lngn(ctx, x)

def stream(f, out):
    stack = [f]
    while stack:
        g = stack.pop()
        if isinstance(g, str): out.write(g); continue
        if isinstance(g, Atom): out.write("(" + var(g.a) + g.op + var(g.b) + ")")
        elif isinstance(g, Not): out.write("¬"); stack.append(g.p)
        elif isinstance(g, And): out.write("("); stack += [")", g.q, "∧", g.p]
        elif isinstance(g, All): out.write("∀" + var(g.v)); stack.append(g.p)
        else: raise TypeError

if __name__ == "__main__":
    sys.setrecursionlimit(100000)
    phi = build()
    assert not has_oracle(phi)
    print(f"|φ| = {length(phi):,}   自由変数 = {[var(v) for v in sorted(free(phi))]}")
    if "--stream" in sys.argv:
        with open(sys.argv[sys.argv.index("--stream") + 1], "w", encoding="utf-8") as out:
            stream(phi, out)
