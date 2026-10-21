import TrPartsG
set_option maxRecDepth 200000
namespace Tr

/-! 生成プログラムが書き出した部品（層 H。lean_tr_export.py による。手で編集しない）。 -/

def r_omega : F := (.conj (.conj (.conj (.rel .ordinal 2 [0]) (.neg (.rel .empty 7 [0]))) (.neg (.neg (.all 8 (.neg (.conj (.mem 8 0) (.rel .succ 9 [8, 0]))))))) (.all 1 (.neg (.conj (.mem 1 0) (.neg (.neg (.conj (.neg (.rel .empty 10 [1])) (.neg (.neg (.all 11 (.neg (.conj (.mem 11 1) (.rel .succ 12 [11, 1])))))))))))))
def tbl_omega : Nm → Option (Nat × F) := fun nm => match nm with
    | .empty => some (1, full_empty)
    | .ordinal => some (1, full_ordinal)
    | .succ => some (2, full_succ)
    | _ => none
def full_omega : F := expand tbl_omega r_omega

def r_func : F := (.conj (.conj (.all 3 (.neg (.conj (.mem 3 0) (.neg (.neg (.all 8 (.neg (.conj (.mem 8 3) (.neg (.all 9 (.neg (.conj (.mem 9 8) (.neg (.all 10 (.neg (.conj (.mem 10 8) (.conj (.rel .pair 11 [3, 9, 10]) (.conj (.mem 9 1) (.mem 10 2))))))))))))))))))) (.all 4 (.neg (.conj (.mem 4 1) (.neg (.neg (.all 13 (.neg (.conj (.mem 13 0) (.neg (.all 14 (.neg (.conj (.mem 14 13) (.neg (.all 15 (.neg (.conj (.mem 15 14) (.conj (.rel .pair 16 [13, 4, 15]) (.mem 15 2))))))))))))))))))) (.all 18 (.neg (.conj (.mem 18 0) (.neg (.all 19 (.neg (.conj (.mem 19 18) (.neg (.all 20 (.neg (.conj (.mem 20 19) (.neg (.all 21 (.neg (.conj (.mem 21 19) (.neg (.neg (.conj (.rel .pair 22 [18, 20, 21]) (.neg (.all 24 (.neg (.conj (.mem 24 0) (.neg (.all 25 (.neg (.conj (.mem 25 24) (.neg (.all 26 (.neg (.conj (.mem 26 25) (.neg (.all 27 (.neg (.conj (.mem 27 25) (.neg (.neg (.conj (.rel .pair 28 [24, 26, 27]) (.neg (.neg (.conj (.eq 20 26) (.neg (.eq 21 27)))))))))))))))))))))))))))))))))))))))))))
def tbl_func : Nm → Option (Nat × F) := fun nm => match nm with
    | .pair => some (3, full_pair)
    | _ => none
def full_func : F := expand tbl_func r_func

def r_bij : F := (.conj (.conj (.rel .func 22 [0, 1, 2]) (.all 3 (.neg (.conj (.mem 3 2) (.neg (.neg (.all 4 (.neg (.conj (.mem 4 1) (.neg (.all 5 (.neg (.conj (.mem 5 0) (.neg (.all 6 (.neg (.conj (.mem 6 5) (.neg (.all 7 (.neg (.conj (.mem 7 6) (.conj (.rel .pair 8 [5, 4, 7]) (.eq 7 3))))))))))))))))))))))) (.all 10 (.neg (.conj (.mem 10 0) (.neg (.all 11 (.neg (.conj (.mem 11 10) (.neg (.all 12 (.neg (.conj (.mem 12 11) (.neg (.all 13 (.neg (.conj (.mem 13 11) (.neg (.neg (.conj (.rel .pair 14 [10, 12, 13]) (.neg (.all 16 (.neg (.conj (.mem 16 0) (.neg (.all 17 (.neg (.conj (.mem 17 16) (.neg (.all 18 (.neg (.conj (.mem 18 17) (.neg (.all 19 (.neg (.conj (.mem 19 17) (.neg (.neg (.conj (.rel .pair 20 [16, 18, 19]) (.neg (.neg (.conj (.eq 13 19) (.neg (.eq 12 18)))))))))))))))))))))))))))))))))))))))))))
def tbl_bij : Nm → Option (Nat × F) := fun nm => match nm with
    | .func => some (3, full_func)
    | .pair => some (3, full_pair)
    | _ => none
def full_bij : F := expand tbl_bij r_bij

def r_regular : F := (.all 1 (.neg (.conj (.mem 1 0) (.neg (.all 2 (.neg (.conj (.rel .func 10 [2, 1, 0]) (.neg (.neg (.all 3 (.neg (.conj (.mem 3 0) (.all 4 (.neg (.conj (.mem 4 1) (.neg (.neg (.all 5 (.neg (.conj (.mem 5 2) (.neg (.all 6 (.neg (.conj (.mem 6 5) (.neg (.all 7 (.neg (.conj (.mem 7 6) (.conj (.rel .pair 8 [5, 4, 7]) (.mem 7 3))))))))))))))))))))))))))))))
def tbl_regular : Nm → Option (Nat × F) := fun nm => match nm with
    | .func => some (3, full_func)
    | .pair => some (3, full_pair)
    | _ => none
def full_regular : F := expand tbl_regular r_regular

def r_power_of : F := (.conj (.mem 1 0) (.all 2 (.conj (.neg (.conj (.mem 2 0) (.neg (.all 3 (.neg (.conj (.mem 3 2) (.neg (.mem 3 1)))))))) (.neg (.conj (.all 3 (.neg (.conj (.mem 3 2) (.neg (.mem 3 1))))) (.neg (.mem 2 0)))))))
def tbl_power_of : Nm → Option (Nat × F) := fun nm => match nm with
    | _ => none
def full_power_of : F := expand tbl_power_of r_power_of

def r_strong_limit : F := (.all 1 (.neg (.conj (.mem 1 0) (.neg (.neg (.all 2 (.neg (.conj (.rel .power_of 5 [2, 1]) (.neg (.all 3 (.neg (.conj (.mem 3 0) (.neg (.all 4 (.neg (.rel .bij 7 [4, 2, 3]))))))))))))))))
def tbl_strong_limit : Nm → Option (Nat × F) := fun nm => match nm with
    | .bij => some (3, full_bij)
    | .power_of => some (2, full_power_of)
    | _ => none
def full_strong_limit : F := expand tbl_strong_limit r_strong_limit

def r_inaccessible : F := (.conj (.conj (.conj (.rel .ordinal 2 [0]) (.neg (.all 1 (.neg (.conj (.rel .omega 7 [1]) (.mem 1 0)))))) (.rel .regular 19 [0])) (.rel .strong_limit 55 [0]))
def tbl_inaccessible : Nm → Option (Nat × F) := fun nm => match nm with
    | .omega => some (1, full_omega)
    | .ordinal => some (1, full_ordinal)
    | .regular => some (1, full_regular)
    | .strong_limit => some (1, full_strong_limit)
    | _ => none
def full_inaccessible : F := expand tbl_inaccessible r_inaccessible

def r_o_ok : F := (.conj (.conj (.all 5 (.neg (.conj (.mem 5 0) (.neg (.neg (.all 8 (.neg (.conj (.mem 8 5) (.neg (.all 9 (.neg (.conj (.mem 9 8) (.neg (.all 10 (.neg (.conj (.mem 10 8) (.conj (.rel .pair 11 [5, 9, 10]) (.mem 9 1)))))))))))))))))) (.all 13 (.neg (.conj (.mem 13 0) (.neg (.all 14 (.neg (.conj (.mem 14 13) (.neg (.all 15 (.neg (.conj (.mem 15 14) (.neg (.all 16 (.neg (.conj (.mem 16 14) (.neg (.neg (.conj (.rel .pair 17 [13, 15, 16]) (.neg (.all 19 (.neg (.conj (.mem 19 0) (.neg (.all 20 (.neg (.conj (.mem 20 19) (.neg (.all 21 (.neg (.conj (.mem 21 20) (.neg (.all 22 (.neg (.conj (.mem 22 20) (.neg (.neg (.conj (.rel .pair 23 [19, 21, 22]) (.neg (.neg (.conj (.eq 15 21) (.neg (.eq 16 22))))))))))))))))))))))))))))))))))))))))))) (.all 2 (.neg (.conj (.mem 2 1) (.neg (.neg (.all 25 (.neg (.conj (.mem 25 0) (.neg (.all 26 (.neg (.conj (.mem 26 25) (.neg (.all 27 (.neg (.conj (.mem 27 26) (.conj (.rel .pair 28 [25, 2, 27]) (.conj (.all 4 (.neg (.conj (.mem 4 27) (.neg (.neg (.all 3 (.neg (.conj (.mem 3 1) (.conj (.rel .cnf_lt 30 [3, 2]) (.neg (.all 1246 (.neg (.conj (.mem 1246 0) (.neg (.all 1247 (.neg (.conj (.mem 1247 1246) (.neg (.all 1248 (.neg (.conj (.mem 1248 1247) (.conj (.rel .pair 1249 [1246, 3, 1248]) (.eq 1248 4))))))))))))))))))))))) (.all 3 (.neg (.conj (.mem 3 1) (.neg (.neg (.conj (.rel .cnf_lt 1251 [3, 2]) (.neg (.neg (.all 2467 (.neg (.conj (.mem 2467 0) (.neg (.all 2468 (.neg (.conj (.mem 2468 2467) (.neg (.all 2469 (.neg (.conj (.mem 2469 2468) (.conj (.rel .pair 2470 [2467, 3, 2469]) (.mem 2469 27))))))))))))))))))))))))))))))))))))))))
def tbl_o_ok : Nm → Option (Nat × F) := fun nm => match nm with
    | .cnf_lt => some (2, full_cnf_lt)
    | .pair => some (3, full_pair)
    | _ => none
def full_o_ok : F := expand tbl_o_ok r_o_ok

def r_ord_of : F := (.neg (.all 2 (.neg (.conj (.rel .omega 4 [2]) (.neg (.all 3 (.neg (.conj (.rel .o_ok 16 [3, 2]) (.neg (.all 2486 (.neg (.conj (.mem 2486 3) (.neg (.all 2487 (.neg (.conj (.mem 2487 2486) (.neg (.all 2488 (.neg (.conj (.mem 2488 2487) (.conj (.rel .pair 2489 [2486, 0, 2488]) (.eq 2488 1))))))))))))))))))))))
def tbl_ord_of : Nm → Option (Nat × F) := fun nm => match nm with
    | .o_ok => some (2, full_o_ok)
    | .omega => some (1, full_omega)
    | .pair => some (3, full_pair)
    | _ => none
def full_ord_of : F := expand tbl_ord_of r_ord_of

def r_lam_ok : F := (.conj (.conj (.all 5 (.neg (.conj (.mem 5 0) (.neg (.neg (.all 6 (.neg (.conj (.mem 6 5) (.neg (.all 7 (.neg (.conj (.mem 7 6) (.neg (.all 8 (.neg (.conj (.mem 8 6) (.conj (.rel .pair 9 [5, 7, 8]) (.mem 7 1)))))))))))))))))) (.all 11 (.neg (.conj (.mem 11 0) (.neg (.all 12 (.neg (.conj (.mem 12 11) (.neg (.all 13 (.neg (.conj (.mem 13 12) (.neg (.all 14 (.neg (.conj (.mem 14 12) (.neg (.neg (.conj (.rel .pair 15 [11, 13, 14]) (.neg (.all 17 (.neg (.conj (.mem 17 0) (.neg (.all 18 (.neg (.conj (.mem 18 17) (.neg (.all 19 (.neg (.conj (.mem 19 18) (.neg (.all 20 (.neg (.conj (.mem 20 18) (.neg (.neg (.conj (.rel .pair 21 [17, 19, 20]) (.neg (.neg (.conj (.eq 13 19) (.neg (.eq 14 20))))))))))))))))))))))))))))))))))))))))))) (.all 2 (.neg (.conj (.mem 2 1) (.neg (.neg (.all 23 (.neg (.conj (.mem 23 0) (.neg (.all 24 (.neg (.conj (.mem 24 23) (.neg (.all 25 (.neg (.conj (.mem 25 24) (.conj (.rel .pair 26 [23, 2, 25]) (.conj (.conj (.rel .inaccessible 144 [25]) (.all 3 (.neg (.conj (.mem 3 2) (.neg (.neg (.all 28 (.neg (.conj (.mem 28 0) (.neg (.all 29 (.neg (.conj (.mem 29 28) (.neg (.all 30 (.neg (.conj (.mem 30 29) (.conj (.rel .pair 31 [28, 3, 30]) (.mem 30 25))))))))))))))))))) (.all 4 (.neg (.conj (.mem 4 25) (.neg (.neg (.conj (.rel .inaccessible 33 [4]) (.neg (.neg (.all 3 (.neg (.conj (.mem 3 2) (.neg (.all 139 (.neg (.conj (.mem 139 0) (.neg (.all 140 (.neg (.conj (.mem 140 139) (.neg (.all 141 (.neg (.conj (.mem 141 140) (.conj (.rel .pair 142 [139, 3, 141]) (.neg (.conj (.neg (.mem 4 141)) (.neg (.eq 4 141)))))))))))))))))))))))))))))))))))))))))))))))
def tbl_lam_ok : Nm → Option (Nat × F) := fun nm => match nm with
    | .inaccessible => some (1, full_inaccessible)
    | .pair => some (3, full_pair)
    | _ => none
def full_lam_ok : F := expand tbl_lam_ok r_lam_ok

def r_eps0 : F := (.neg (.all 1 (.neg (.conj (.rel .omega 15 [1]) (.neg (.all 2 (.neg (.conj (.rel .o_ok 27 [2, 1]) (.conj (.all 3 (.neg (.conj (.mem 3 0) (.neg (.neg (.all 4 (.neg (.conj (.mem 4 1) (.neg (.all 5 (.neg (.conj (.mem 5 2) (.neg (.all 6 (.neg (.conj (.mem 6 5) (.neg (.all 7 (.neg (.conj (.mem 7 6) (.conj (.rel .pair 8 [5, 4, 7]) (.eq 7 3)))))))))))))))))))))) (.all 4 (.neg (.conj (.mem 4 1) (.neg (.neg (.all 10 (.neg (.conj (.mem 10 2) (.neg (.all 11 (.neg (.conj (.mem 11 10) (.neg (.all 12 (.neg (.conj (.mem 12 11) (.conj (.rel .pair 13 [10, 4, 12]) (.mem 12 0)))))))))))))))))))))))))))
def tbl_eps0 : Nm → Option (Nat × F) := fun nm => match nm with
    | .o_ok => some (2, full_o_ok)
    | .omega => some (1, full_omega)
    | .pair => some (3, full_pair)
    | _ => none
def full_eps0 : F := expand tbl_eps0 r_eps0

def r_lam_of : F := (.neg (.all 2 (.neg (.conj (.rel .eps0 4 [2]) (.neg (.all 3 (.neg (.conj (.rel .lam_ok 2500 [3, 2]) (.neg (.all 2748 (.neg (.conj (.mem 2748 3) (.neg (.all 2749 (.neg (.conj (.mem 2749 2748) (.neg (.all 2750 (.neg (.conj (.mem 2750 2749) (.conj (.rel .pair 2751 [2748, 0, 2750]) (.eq 2750 1))))))))))))))))))))))
def tbl_lam_of : Nm → Option (Nat × F) := fun nm => match nm with
    | .eps0 => some (1, full_eps0)
    | .lam_ok => some (2, full_lam_ok)
    | .pair => some (3, full_pair)
    | _ => none
def full_lam_of : F := expand tbl_lam_of r_lam_of

end Tr
