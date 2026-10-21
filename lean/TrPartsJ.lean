import TrPartsI
set_option maxRecDepth 200000
namespace Tr

/-! 生成プログラムが書き出した部品（層 J。lean_tr_export.py による。手で編集しない）。 -/

def r_func_on2 : F := (.conj (.conj (.all 2 (.neg (.conj (.mem 2 0) (.neg (.neg (.all 4 (.neg (.conj (.mem 4 2) (.neg (.all 5 (.neg (.conj (.mem 5 4) (.neg (.all 6 (.neg (.conj (.mem 6 4) (.conj (.rel .pair 7 [2, 5, 6]) (.mem 5 1)))))))))))))))))) (.all 3 (.neg (.conj (.mem 3 1) (.neg (.neg (.all 9 (.neg (.conj (.mem 9 0) (.neg (.all 10 (.neg (.conj (.mem 10 9) (.neg (.all 11 (.neg (.conj (.mem 11 10) (.conj (.rel .pair 12 [9, 3, 11]) (.eq 11 11))))))))))))))))))) (.all 14 (.neg (.conj (.mem 14 0) (.neg (.all 15 (.neg (.conj (.mem 15 14) (.neg (.all 16 (.neg (.conj (.mem 16 15) (.neg (.all 17 (.neg (.conj (.mem 17 15) (.neg (.neg (.conj (.rel .pair 18 [14, 16, 17]) (.neg (.all 20 (.neg (.conj (.mem 20 0) (.neg (.all 21 (.neg (.conj (.mem 21 20) (.neg (.all 22 (.neg (.conj (.mem 22 21) (.neg (.all 23 (.neg (.conj (.mem 23 21) (.neg (.neg (.conj (.rel .pair 24 [20, 22, 23]) (.neg (.neg (.conj (.eq 16 22) (.neg (.eq 17 23)))))))))))))))))))))))))))))))))))))))))))
def tbl_func_on2 : Nm → Option (Nat × F) := fun nm => match nm with
    | .pair => some (3, full_pair)
    | _ => none
def full_func_on2 : F := expand tbl_func_on2 r_func_on2

def r_struct_table : F := (.conj (.rel .func_on2 3 [1, 0]) (.all 2 (.neg (.conj (.mem 2 0) (.neg (.neg (.all 27 (.neg (.conj (.mem 27 1) (.neg (.all 28 (.neg (.conj (.mem 28 27) (.neg (.all 29 (.neg (.conj (.mem 29 28) (.conj (.rel .pair 30 [27, 2, 29]) (.neg (.all 32 (.neg (.conj (.mem 32 29) (.neg (.all 33 (.neg (.conj (.mem 33 32) (.neg (.all 34 (.neg (.conj (.mem 34 32) (.conj (.rel .pair 35 [29, 33, 34]) (.neg (.all 37 (.neg (.conj (.mem 37 33) (.neg (.all 38 (.neg (.conj (.mem 38 37) (.neg (.all 39 (.neg (.conj (.mem 39 37) (.conj (.rel .pair 40 [33, 38, 39]) (.neg (.all 42 (.neg (.conj (.mem 42 34) (.neg (.all 43 (.neg (.conj (.mem 43 42) (.neg (.all 44 (.neg (.conj (.mem 44 42) (.conj (.rel .pair 45 [34, 43, 44]) (.neg (.all 47 (.neg (.conj (.mem 47 44) (.neg (.all 48 (.neg (.conj (.mem 48 47) (.neg (.all 49 (.neg (.conj (.mem 49 47) (.conj (.rel .pair 50 [44, 48, 49]) (.rel .struct_full 52 [2, 38, 39, 43, 48, 49])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def tbl_struct_table : Nm → Option (Nat × F) := fun nm => match nm with
    | .func_on2 => some (2, full_func_on2)
    | .pair => some (3, full_pair)
    | .struct_full => some (6, full_struct_full)
    | _ => none
def full_struct_table : F := expand tbl_struct_table r_struct_table

def r_definable_set : F := (.all 3 (.conj (.neg (.conj (.mem 3 2) (.neg (.conj (.rel .nat 14376 [3]) (.neg (.all 4 (.neg (.conj (.mem 4 0) (.neg (.all 7 (.neg (.conj (.mem 7 1) (.neg (.all 8 (.neg (.conj (.mem 8 7) (.neg (.all 9 (.neg (.conj (.mem 9 8) (.conj (.rel .pair 10 [7, 4, 9]) (.neg (.all 12 (.neg (.conj (.mem 12 9) (.neg (.all 13 (.neg (.conj (.mem 13 12) (.neg (.all 14 (.neg (.conj (.mem 14 12) (.conj (.rel .pair 15 [9, 13, 14]) (.neg (.all 17 (.neg (.conj (.mem 17 13) (.neg (.all 18 (.neg (.conj (.mem 18 17) (.neg (.all 19 (.neg (.conj (.mem 19 17) (.conj (.rel .pair 20 [13, 18, 19]) (.neg (.all 22 (.neg (.conj (.mem 22 14) (.neg (.all 23 (.neg (.conj (.mem 23 22) (.neg (.all 24 (.neg (.conj (.mem 24 22) (.conj (.rel .pair 25 [14, 23, 24]) (.neg (.all 27 (.neg (.conj (.mem 27 24) (.neg (.all 28 (.neg (.conj (.mem 28 27) (.neg (.all 29 (.neg (.conj (.mem 29 27) (.conj (.rel .pair 30 [24, 28, 29]) (.neg (.all 5 (.neg (.conj (.mem 5 0) (.neg (.all 6 (.neg (.conj (.conj (.rel .formula 32 [6]) (.rel .metacode 1600 [5, 6])) (.rel .definable_in 2759 [6, 18, 19, 23, 28, 29, 3])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.neg (.conj (.conj (.rel .nat 14376 [3]) (.neg (.all 4 (.neg (.conj (.mem 4 0) (.neg (.all 7 (.neg (.conj (.mem 7 1) (.neg (.all 8 (.neg (.conj (.mem 8 7) (.neg (.all 9 (.neg (.conj (.mem 9 8) (.conj (.rel .pair 10 [7, 4, 9]) (.neg (.all 12 (.neg (.conj (.mem 12 9) (.neg (.all 13 (.neg (.conj (.mem 13 12) (.neg (.all 14 (.neg (.conj (.mem 14 12) (.conj (.rel .pair 15 [9, 13, 14]) (.neg (.all 17 (.neg (.conj (.mem 17 13) (.neg (.all 18 (.neg (.conj (.mem 18 17) (.neg (.all 19 (.neg (.conj (.mem 19 17) (.conj (.rel .pair 20 [13, 18, 19]) (.neg (.all 22 (.neg (.conj (.mem 22 14) (.neg (.all 23 (.neg (.conj (.mem 23 22) (.neg (.all 24 (.neg (.conj (.mem 24 22) (.conj (.rel .pair 25 [14, 23, 24]) (.neg (.all 27 (.neg (.conj (.mem 27 24) (.neg (.all 28 (.neg (.conj (.mem 28 27) (.neg (.all 29 (.neg (.conj (.mem 29 27) (.conj (.rel .pair 30 [24, 28, 29]) (.neg (.all 5 (.neg (.conj (.mem 5 0) (.neg (.all 6 (.neg (.conj (.conj (.rel .formula 32 [6]) (.rel .metacode 1600 [5, 6])) (.rel .definable_in 2759 [6, 18, 19, 23, 28, 29, 3]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.neg (.mem 3 2))))))
def tbl_definable_set : Nm → Option (Nat × F) := fun nm => match nm with
    | .definable_in => some (7, full_definable_in)
    | .formula => some (1, full_formula)
    | .metacode => some (2, full_metacode)
    | .nat => some (1, full_nat)
    | .pair => some (3, full_pair)
    | _ => none
def full_definable_set : F := expand tbl_definable_set r_definable_set

def r_finite_sum : F := (.neg (.all 2 (.neg (.conj (.conj (.rel .nat 114 [2]) (.all 7 (.neg (.conj (.mem 7 0) (.neg (.mem 7 2)))))) (.neg (.all 3 (.neg (.conj (.rel .succ 122 [2, 3]) (.neg (.all 4 (.neg (.conj (.conj (.conj (.rel .func_on2 8 [4, 3]) (.neg (.all 7 (.neg (.conj (.rel .empty 32 [7]) (.neg (.all 33 (.neg (.conj (.mem 33 4) (.neg (.all 34 (.neg (.conj (.mem 34 33) (.neg (.all 35 (.neg (.conj (.mem 35 34) (.conj (.rel .pair 36 [33, 7, 35]) (.rel .empty 38 [35]))))))))))))))))))) (.all 5 (.neg (.conj (.mem 5 2) (.neg (.all 6 (.neg (.conj (.mem 6 3) (.neg (.neg (.conj (.rel .succ 39 [5, 6]) (.neg (.neg (.all 40 (.neg (.conj (.mem 40 4) (.neg (.all 41 (.neg (.conj (.mem 41 40) (.neg (.all 42 (.neg (.conj (.mem 42 41) (.conj (.rel .pair 43 [40, 5, 42]) (.neg (.all 45 (.neg (.conj (.mem 45 4) (.neg (.all 46 (.neg (.conj (.mem 46 45) (.neg (.all 47 (.neg (.conj (.mem 47 46) (.conj (.rel .pair 48 [45, 6, 47]) (.conj (.neg (.conj (.mem 5 0) (.neg (.rel .add 50 [42, 5, 47])))) (.neg (.conj (.neg (.mem 5 0)) (.neg (.eq 47 42))))))))))))))))))))))))))))))))))))))))))) (.neg (.all 109 (.neg (.conj (.mem 109 4) (.neg (.all 110 (.neg (.conj (.mem 110 109) (.neg (.all 111 (.neg (.conj (.mem 111 110) (.conj (.rel .pair 112 [109, 2, 111]) (.eq 111 1))))))))))))))))))))))))))
def tbl_finite_sum : Nm → Option (Nat × F) := fun nm => match nm with
    | .add => some (3, full_add)
    | .empty => some (1, full_empty)
    | .func_on2 => some (2, full_func_on2)
    | .nat => some (1, full_nat)
    | .pair => some (3, full_pair)
    | .succ => some (2, full_succ)
    | _ => none
def full_finite_sum : F := expand tbl_finite_sum r_finite_sum

def r_f_val : F := (.neg (.all 2 (.neg (.conj (.rel .struct_table 4 [0, 2]) (.neg (.all 3 (.neg (.conj (.rel .definable_set 29803 [0, 2, 3]) (.rel .finite_sum 44184 [3, 1])))))))))
def tbl_f_val : Nm → Option (Nat × F) := fun nm => match nm with
    | .definable_set => some (3, full_definable_set)
    | .finite_sum => some (2, full_finite_sum)
    | .struct_table => some (2, full_struct_table)
    | _ => none
def full_f_val : F := expand tbl_f_val r_f_val

def r_iterate10 : F := (.neg (.all 2 (.neg (.conj (.rel .numeral10 44357 [2]) (.neg (.all 3 (.neg (.conj (.rel .succ 44378 [2, 3]) (.neg (.all 4 (.neg (.conj (.conj (.conj (.rel .func_on2 8 [4, 3]) (.neg (.all 7 (.neg (.conj (.rel .empty 32 [7]) (.neg (.all 33 (.neg (.conj (.mem 33 4) (.neg (.all 34 (.neg (.conj (.mem 34 33) (.neg (.all 35 (.neg (.conj (.mem 35 34) (.conj (.rel .pair 36 [33, 7, 35]) (.eq 35 0))))))))))))))))))) (.all 5 (.neg (.conj (.mem 5 2) (.neg (.all 6 (.neg (.conj (.mem 6 3) (.neg (.neg (.conj (.rel .succ 38 [5, 6]) (.neg (.neg (.all 39 (.neg (.conj (.mem 39 4) (.neg (.all 40 (.neg (.conj (.mem 40 39) (.neg (.all 41 (.neg (.conj (.mem 41 40) (.conj (.rel .pair 42 [39, 5, 41]) (.neg (.all 44 (.neg (.conj (.mem 44 4) (.neg (.all 45 (.neg (.conj (.mem 45 44) (.neg (.all 46 (.neg (.conj (.mem 46 45) (.conj (.rel .pair 47 [44, 6, 46]) (.rel .f_val 49 [41, 46]))))))))))))))))))))))))))))))))))))))) (.neg (.all 44352 (.neg (.conj (.mem 44352 4) (.neg (.all 44353 (.neg (.conj (.mem 44353 44352) (.neg (.all 44354 (.neg (.conj (.mem 44354 44353) (.conj (.rel .pair 44355 [44352, 2, 44354]) (.eq 44354 1))))))))))))))))))))))))))
def tbl_iterate10 : Nm → Option (Nat × F) := fun nm => match nm with
    | .empty => some (1, full_empty)
    | .f_val => some (2, full_f_val)
    | .func_on2 => some (2, full_func_on2)
    | .numeral10 => some (1, full_numeral10)
    | .pair => some (3, full_pair)
    | .succ => some (2, full_succ)
    | _ => none
def full_iterate10 : F := expand tbl_iterate10 r_iterate10

def r_lngn : F := (.neg (.all 1 (.neg (.conj (.neg (.all 2 (.neg (.conj (.rel .numeral12 4 [2]) (.neg (.all 3 (.neg (.conj (.rel .numeral10 29 [3]) (.rel .hyper 50 [2, 3, 3, 1]))))))))) (.rel .iterate10 105 [1, 0])))))
def tbl_lngn : Nm → Option (Nat × F) := fun nm => match nm with
    | .hyper => some (4, full_hyper)
    | .iterate10 => some (2, full_iterate10)
    | .numeral10 => some (1, full_numeral10)
    | .numeral12 => some (1, full_numeral12)
    | _ => none
def full_lngn : F := expand tbl_lngn r_lngn

end Tr
