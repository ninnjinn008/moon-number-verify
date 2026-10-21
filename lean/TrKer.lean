/-
  kernel_rfl：閉じた Bool の等式 b = true を、エラボレータでの簡約を経ずに Eq.refl true で閉じる。
  証明項の型検査はカーネルが行う（宣言を環境に加えるときに b を実際に計算する）。信頼の基盤は変わらない。
-/
import Lean
open Lean Elab Tactic Meta in
elab "kernel_rfl" : tactic =>
  closeMainGoalUsing `kernel_rfl fun _ =>
    return mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``true)
