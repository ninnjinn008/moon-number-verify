import TrPartsD
set_option maxRecDepth 200000
namespace Tr

/-! 生成プログラムが書き出した部品（層 E。lean_tr_export.py による。手で編集しない）。 -/

def r_ordinal : F := (.conj (.all 2 (.neg (.conj (.mem 2 0) (.neg (.all 3 (.neg (.conj (.mem 3 2) (.neg (.mem 3 0))))))))) (.all 1 (.neg (.conj (.mem 1 0) (.neg (.all 4 (.neg (.conj (.mem 4 1) (.neg (.all 5 (.neg (.conj (.mem 5 4) (.neg (.mem 5 1))))))))))))))
def tbl_ordinal : Nm → Option (Nat × F) := fun nm => match nm with
    | _ => none
def full_ordinal : F := expand tbl_ordinal r_ordinal

def r_e_restrict : F := (.conj (.all 2 (.neg (.conj (.mem 2 1) (.neg (.neg (.all 5 (.neg (.conj (.mem 5 2) (.neg (.all 6 (.neg (.conj (.mem 6 5) (.neg (.all 7 (.neg (.conj (.mem 7 5) (.conj (.rel .pair 8 [2, 6, 7]) (.conj (.conj (.mem 6 0) (.mem 7 0)) (.mem 6 7))))))))))))))))))) (.all 4 (.neg (.conj (.mem 4 0) (.neg (.all 3 (.neg (.conj (.mem 3 4) (.neg (.neg (.all 2 (.neg (.conj (.mem 2 1) (.rel .pair 10 [2, 3, 4]))))))))))))))
def tbl_e_restrict : Nm → Option (Nat × F) := fun nm => match nm with
    | .pair => some (3, full_pair)
    | _ => none
def full_e_restrict : F := expand tbl_e_restrict r_e_restrict

def r_func_on : F := (.conj (.conj (.all 3 (.neg (.conj (.mem 3 0) (.neg (.neg (.all 5 (.neg (.conj (.mem 5 3) (.neg (.all 6 (.neg (.conj (.mem 6 5) (.neg (.all 7 (.neg (.conj (.mem 7 5) (.conj (.rel .pair 8 [3, 6, 7]) (.conj (.mem 6 1) (.mem 7 2))))))))))))))))))) (.all 4 (.neg (.conj (.mem 4 1) (.neg (.neg (.all 10 (.neg (.conj (.mem 10 0) (.neg (.all 11 (.neg (.conj (.mem 11 10) (.neg (.all 12 (.neg (.conj (.mem 12 11) (.conj (.rel .pair 13 [10, 4, 12]) (.eq 12 12))))))))))))))))))) (.all 15 (.neg (.conj (.mem 15 0) (.neg (.all 16 (.neg (.conj (.mem 16 15) (.neg (.all 17 (.neg (.conj (.mem 17 16) (.neg (.all 18 (.neg (.conj (.mem 18 16) (.neg (.neg (.conj (.rel .pair 19 [15, 17, 18]) (.neg (.all 21 (.neg (.conj (.mem 21 0) (.neg (.all 22 (.neg (.conj (.mem 22 21) (.neg (.all 23 (.neg (.conj (.mem 23 22) (.neg (.all 24 (.neg (.conj (.mem 24 22) (.neg (.neg (.conj (.rel .pair 25 [21, 23, 24]) (.neg (.neg (.conj (.eq 17 23) (.neg (.eq 18 24)))))))))))))))))))))))))))))))))))))))))))
def tbl_func_on : Nm → Option (Nat × F) := fun nm => match nm with
    | .pair => some (3, full_pair)
    | _ => none
def full_func_on : F := expand tbl_func_on r_func_on

def r_in_pair_l : F := (.neg (.all 3 (.neg (.conj (.mem 3 0) (.rel .pair 4 [3, 1, 2])))))
def tbl_in_pair_l : Nm → Option (Nat × F) := fun nm => match nm with
    | .pair => some (3, full_pair)
    | _ => none
def full_in_pair_l : F := expand tbl_in_pair_l r_in_pair_l

def r_pure : F := (.all 2 (.neg (.conj (.mem 2 1) (.neg (.neg (.all 3 (.neg (.conj (.mem 3 0) (.neg (.all 4 (.neg (.conj (.mem 4 3) (.neg (.all 5 (.neg (.conj (.mem 5 4) (.conj (.rel .pair 6 [3, 2, 5]) (.conj (.conj (.neg (.rel .symconst 8 [5])) (.neg (.rel .symfunc 52 [5]))) (.neg (.rel .symrel 228 [5]))))))))))))))))))))
def tbl_pure : Nm → Option (Nat × F) := fun nm => match nm with
    | .pair => some (3, full_pair)
    | .symconst => some (1, full_symconst)
    | .symfunc => some (1, full_symfunc)
    | .symrel => some (1, full_symrel)
    | _ => none
def full_pure : F := expand tbl_pure r_pure

def r_def_code : F := (.neg (.all 1 (.neg (.conj (.conj (.rel .formula_minus 3 [1]) (.rel .metacode 1645 [0, 1])) (.neg (.all 2 (.neg (.conj (.conj (.conj (.conj (.rel .nat 2828 [2]) (.all 2805 (.neg (.conj (.mem 2805 1) (.neg (.neg (.all 2806 (.neg (.conj (.mem 2806 2805) (.neg (.all 2807 (.neg (.conj (.mem 2807 2806) (.neg (.all 2808 (.neg (.conj (.mem 2808 2806) (.conj (.rel .pair 2809 [2805, 2807, 2808]) (.conj (.mem 2807 2) (.eq 2808 2808)))))))))))))))))))) (.all 2804 (.neg (.conj (.mem 2804 2) (.neg (.neg (.all 2811 (.neg (.conj (.mem 2811 1) (.neg (.all 2812 (.neg (.conj (.mem 2812 2811) (.neg (.all 2813 (.neg (.conj (.mem 2813 2812) (.conj (.rel .pair 2814 [2811, 2804, 2813]) (.eq 2813 2813))))))))))))))))))) (.all 2816 (.neg (.conj (.mem 2816 1) (.neg (.all 2817 (.neg (.conj (.mem 2817 2816) (.neg (.all 2818 (.neg (.conj (.mem 2818 2817) (.neg (.all 2819 (.neg (.conj (.mem 2819 2817) (.neg (.neg (.conj (.rel .pair 2820 [2816, 2818, 2819]) (.neg (.all 2822 (.neg (.conj (.mem 2822 1) (.neg (.all 2823 (.neg (.conj (.mem 2823 2822) (.neg (.all 2824 (.neg (.conj (.mem 2824 2823) (.neg (.all 2825 (.neg (.conj (.mem 2825 2823) (.neg (.neg (.conj (.rel .pair 2826 [2822, 2824, 2825]) (.neg (.neg (.conj (.eq 2818 2824) (.neg (.eq 2819 2825))))))))))))))))))))))))))))))))))))))))))) (.rel .pure 2836 [1, 2])))))))))
def tbl_def_code : Nm → Option (Nat × F) := fun nm => match nm with
    | .formula_minus => some (1, full_formula_minus)
    | .metacode => some (2, full_metacode)
    | .nat => some (1, full_nat)
    | .pair => some (3, full_pair)
    | .pure => some (2, full_pure)
    | _ => none
def full_def_code : F := expand tbl_def_code r_def_code

def r_defines : F := (.neg (.all 4 (.neg (.conj (.conj (.rel .formula_minus 3693 [4]) (.rel .metacode 5335 [0, 4])) (.neg (.all 5 (.neg (.conj (.conj (.conj (.conj (.conj (.rel .nat 6518 [5]) (.all 6495 (.neg (.conj (.mem 6495 4) (.neg (.neg (.all 6496 (.neg (.conj (.mem 6496 6495) (.neg (.all 6497 (.neg (.conj (.mem 6497 6496) (.neg (.all 6498 (.neg (.conj (.mem 6498 6496) (.conj (.rel .pair 6499 [6495, 6497, 6498]) (.conj (.mem 6497 5) (.eq 6498 6498)))))))))))))))))))) (.all 6494 (.neg (.conj (.mem 6494 5) (.neg (.neg (.all 6501 (.neg (.conj (.mem 6501 4) (.neg (.all 6502 (.neg (.conj (.mem 6502 6501) (.neg (.all 6503 (.neg (.conj (.mem 6503 6502) (.conj (.rel .pair 6504 [6501, 6494, 6503]) (.eq 6503 6503))))))))))))))))))) (.all 6506 (.neg (.conj (.mem 6506 4) (.neg (.all 6507 (.neg (.conj (.mem 6507 6506) (.neg (.all 6508 (.neg (.conj (.mem 6508 6507) (.neg (.all 6509 (.neg (.conj (.mem 6509 6507) (.neg (.neg (.conj (.rel .pair 6510 [6506, 6508, 6509]) (.neg (.all 6512 (.neg (.conj (.mem 6512 4) (.neg (.all 6513 (.neg (.conj (.mem 6513 6512) (.neg (.all 6514 (.neg (.conj (.mem 6514 6513) (.neg (.all 6515 (.neg (.conj (.mem 6515 6513) (.neg (.neg (.conj (.rel .pair 6516 [6512, 6514, 6515]) (.neg (.neg (.conj (.eq 6508 6514) (.neg (.eq 6509 6515))))))))))))))))))))))))))))))))))))))))))) (.rel .pure 6526 [4, 5])) (.neg (.all 6 (.neg (.conj (.conj (.all 6801 (.neg (.conj (.mem 6801 6) (.neg (.neg (.all 6800 (.neg (.conj (.mem 6800 5) (.neg (.all 6802 (.neg (.conj (.mem 6802 4) (.neg (.all 6803 (.neg (.conj (.mem 6803 6802) (.neg (.all 6804 (.neg (.conj (.mem 6804 6803) (.conj (.rel .pair 6805 [6802, 6800, 6804]) (.conj (.rel .symvar 6807 [6804]) (.neg (.all 6855 (.neg (.conj (.rel .numeral2 6856 [6855]) (.neg (.all 6861 (.neg (.conj (.mem 6861 6804) (.neg (.all 6862 (.neg (.conj (.mem 6862 6861) (.neg (.all 6863 (.neg (.conj (.mem 6863 6862) (.conj (.rel .pair 6864 [6861, 6855, 6863]) (.eq 6863 6801)))))))))))))))))))))))))))))))))))))))) (.all 6800 (.neg (.conj (.mem 6800 5) (.neg (.neg (.all 6866 (.neg (.conj (.mem 6866 4) (.neg (.all 6867 (.neg (.conj (.mem 6867 6866) (.neg (.all 6868 (.neg (.conj (.mem 6868 6867) (.conj (.rel .pair 6869 [6866, 6800, 6868]) (.neg (.conj (.rel .symvar 6871 [6868]) (.neg (.neg (.all 6919 (.neg (.conj (.rel .numeral2 6920 [6919]) (.neg (.all 6925 (.neg (.conj (.mem 6925 6868) (.neg (.all 6926 (.neg (.conj (.mem 6926 6925) (.neg (.all 6927 (.neg (.conj (.mem 6927 6926) (.conj (.rel .pair 6928 [6925, 6919, 6927]) (.mem 6927 6))))))))))))))))))))))))))))))))))))))) (.neg (.all 7 (.neg (.conj (.conj (.conj (.all 12 (.neg (.conj (.mem 12 7) (.neg (.conj (.mem 12 6) (.neg (.rel .empty 14 [12]))))))) (.all 12 (.neg (.conj (.mem 12 6) (.neg (.neg (.conj (.neg (.rel .empty 15 [12])) (.neg (.mem 12 7))))))))) (.rel .func_on 6930 [1, 7, 2])) (.neg (.all 9 (.neg (.conj (.rel .empty 6954 [9]) (.neg (.all 8 (.neg (.conj (.rel .e_restrict 6955 [2, 8]) (.conj (.all 10 (.neg (.conj (.mem 10 3) (.neg (.mem 10 2))))) (.all 10 (.neg (.conj (.mem 10 2) (.neg (.conj (.neg (.conj (.mem 10 3) (.neg (.neg (.all 11 (.neg (.conj (.conj (.conj (.all 13 (.neg (.conj (.mem 13 11) (.neg (.neg (.conj (.neg (.mem 13 1)) (.neg (.neg (.all 16 (.neg (.conj (.mem 16 13) (.neg (.all 17 (.neg (.conj (.mem 17 16) (.neg (.all 18 (.neg (.conj (.mem 18 16) (.conj (.rel .pair 19 [13, 17, 18]) (.conj (.rel .empty 21 [17]) (.eq 18 10)))))))))))))))))))))) (.all 13 (.neg (.conj (.mem 13 1) (.neg (.mem 13 11)))))) (.neg (.all 13 (.neg (.conj (.mem 13 11) (.neg (.all 22 (.neg (.conj (.mem 22 13) (.neg (.all 23 (.neg (.conj (.mem 23 22) (.neg (.all 24 (.neg (.conj (.mem 24 22) (.conj (.rel .pair 25 [13, 23, 24]) (.conj (.rel .empty 27 [23]) (.eq 24 10)))))))))))))))))))) (.rel .sat_ext 28 [4, 2, 8, 9, 9, 9, 11])))))))) (.neg (.conj (.neg (.all 11 (.neg (.conj (.conj (.conj (.all 13 (.neg (.conj (.mem 13 11) (.neg (.neg (.conj (.neg (.mem 13 1)) (.neg (.neg (.all 16 (.neg (.conj (.mem 16 13) (.neg (.all 17 (.neg (.conj (.mem 17 16) (.neg (.all 18 (.neg (.conj (.mem 18 16) (.conj (.rel .pair 19 [13, 17, 18]) (.conj (.rel .empty 21 [17]) (.eq 18 10)))))))))))))))))))))) (.all 13 (.neg (.conj (.mem 13 1) (.neg (.mem 13 11)))))) (.neg (.all 13 (.neg (.conj (.mem 13 11) (.neg (.all 22 (.neg (.conj (.mem 22 13) (.neg (.all 23 (.neg (.conj (.mem 23 22) (.neg (.all 24 (.neg (.conj (.mem 24 22) (.conj (.rel .pair 25 [13, 23, 24]) (.conj (.rel .empty 27 [23]) (.eq 24 10)))))))))))))))))))) (.rel .sat_ext 28 [4, 2, 8, 9, 9, 9, 11]))))) (.neg (.mem 10 3))))))))))))))))))))))))))))))))))
def tbl_defines : Nm → Option (Nat × F) := fun nm => match nm with
    | .e_restrict => some (2, full_e_restrict)
    | .empty => some (1, full_empty)
    | .formula_minus => some (1, full_formula_minus)
    | .func_on => some (3, full_func_on)
    | .metacode => some (2, full_metacode)
    | .nat => some (1, full_nat)
    | .numeral2 => some (1, full_numeral2)
    | .pair => some (3, full_pair)
    | .pure => some (2, full_pure)
    | .sat_ext => some (7, full_sat_ext)
    | .symvar => some (1, full_symvar)
    | _ => none
def full_defines : F := expand tbl_defines r_defines

def r_lex_less : F := (.neg (.all 3 (.neg (.conj (.mem 3 0) (.neg (.all 6 (.neg (.conj (.mem 6 3) (.neg (.all 7 (.neg (.conj (.mem 7 6) (.neg (.all 8 (.neg (.conj (.mem 8 6) (.conj (.rel .pair 9 [3, 7, 8]) (.neg (.all 4 (.neg (.conj (.mem 4 1) (.neg (.all 11 (.neg (.conj (.mem 11 4) (.neg (.all 12 (.neg (.conj (.mem 12 11) (.neg (.all 13 (.neg (.conj (.mem 13 11) (.conj (.rel .pair 14 [4, 12, 13]) (.conj (.conj (.eq 12 7) (.rel .in_pair_l 16 [2, 8, 13])) (.all 5 (.neg (.conj (.mem 5 0) (.neg (.neg (.all 19 (.neg (.conj (.mem 19 5) (.neg (.all 20 (.neg (.conj (.mem 20 19) (.neg (.all 21 (.neg (.conj (.mem 21 19) (.conj (.rel .pair 22 [5, 20, 21]) (.neg (.conj (.mem 20 7) (.neg (.neg (.all 4 (.neg (.conj (.mem 4 1) (.rel .pair 24 [4, 20, 21]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def tbl_lex_less : Nm → Option (Nat × F) := fun nm => match nm with
    | .in_pair_l => some (3, full_in_pair_l)
    | .pair => some (3, full_pair)
    | _ => none
def full_lex_less : F := expand tbl_lex_less r_lex_less

def r_def_less : F := (.neg (.conj (.neg (.mem 0 2)) (.neg (.conj (.eq 0 2) (.rel .lex_less 5 [1, 3, 4])))))
def tbl_def_less : Nm → Option (Nat × F) := fun nm => match nm with
    | .lex_less => some (3, full_lex_less)
    | _ => none
def full_def_less : F := expand tbl_def_less r_def_less

def r_def_table : F := (.conj (.all 2 (.neg (.conj (.mem 2 1) (.neg (.neg (.all 7 (.neg (.conj (.mem 7 2) (.neg (.all 8 (.neg (.conj (.mem 8 7) (.neg (.all 9 (.neg (.conj (.mem 9 7) (.conj (.rel .pair 10 [2, 8, 9]) (.neg (.all 12 (.neg (.conj (.mem 12 8) (.neg (.all 13 (.neg (.conj (.mem 13 12) (.neg (.all 14 (.neg (.conj (.mem 14 12) (.conj (.rel .pair 15 [8, 13, 14]) (.rel .def_code 17 [13]))))))))))))))))))))))))))))))) (.all 3 (.neg (.conj (.rel .def_code 3126 [3]) (.neg (.all 4 (.all 5 (.conj (.neg (.conj (.rel .defines 6235 [3, 4, 0, 5]) (.neg (.neg (.all 6 (.neg (.conj (.mem 6 1) (.rel .triple 13196 [6, 3, 4, 5])))))))) (.neg (.conj (.neg (.all 6 (.neg (.conj (.mem 6 1) (.rel .triple 13196 [6, 3, 4, 5]))))) (.neg (.rel .defines 6235 [3, 4, 0, 5]))))))))))))
def tbl_def_table : Nm → Option (Nat × F) := fun nm => match nm with
    | .def_code => some (1, full_def_code)
    | .defines => some (4, full_defines)
    | .pair => some (3, full_pair)
    | .triple => some (4, full_triple)
    | _ => none
def full_def_table : F := expand tbl_def_table r_def_table

def r_new_less : F := (.neg (.all 4 (.neg (.conj (.mem 4 2) (.neg (.all 6 (.neg (.conj (.mem 6 4) (.neg (.all 7 (.neg (.conj (.mem 7 6) (.neg (.all 8 (.neg (.conj (.mem 8 6) (.conj (.rel .pair 9 [4, 7, 8]) (.neg (.all 11 (.neg (.conj (.mem 11 7) (.neg (.all 12 (.neg (.conj (.mem 12 11) (.neg (.all 13 (.neg (.conj (.mem 13 11) (.conj (.rel .pair 14 [7, 12, 13]) (.conj (.eq 8 0) (.all 5 (.neg (.conj (.mem 5 2) (.neg (.neg (.all 16 (.neg (.conj (.mem 16 5) (.neg (.all 17 (.neg (.conj (.mem 17 16) (.neg (.all 18 (.neg (.conj (.mem 18 16) (.conj (.rel .pair 19 [5, 17, 18]) (.neg (.all 21 (.neg (.conj (.mem 21 17) (.neg (.all 22 (.neg (.conj (.mem 22 21) (.neg (.all 23 (.neg (.conj (.mem 23 21) (.conj (.rel .pair 24 [17, 22, 23]) (.neg (.conj (.eq 18 1) (.neg (.rel .def_less 26 [12, 13, 22, 23, 3])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def tbl_new_less : Nm → Option (Nat × F) := fun nm => match nm with
    | .def_less => some (5, full_def_less)
    | .pair => some (3, full_pair)
    | _ => none
def full_new_less : F := expand tbl_new_less r_new_less

def r_step : F := (.neg (.all 4 (.neg (.conj (.conj (.conj (.rel .def_table 34 [0, 4]) (.conj (.all 5 (.neg (.conj (.mem 5 2) (.neg (.neg (.all 8 (.neg (.conj (.mem 8 4) (.neg (.all 9 (.neg (.conj (.mem 9 8) (.neg (.all 10 (.neg (.conj (.mem 10 9) (.neg (.all 11 (.neg (.conj (.mem 11 9) (.conj (.rel .pair 12 [8, 10, 11]) (.neg (.all 14 (.neg (.conj (.mem 14 10) (.neg (.all 15 (.neg (.conj (.mem 15 14) (.neg (.all 16 (.neg (.conj (.mem 16 14) (.conj (.rel .pair 17 [10, 15, 16]) (.eq 11 5))))))))))))))))))))))))))))))))))) (.all 8 (.neg (.conj (.mem 8 4) (.neg (.neg (.all 19 (.neg (.conj (.mem 19 8) (.neg (.all 20 (.neg (.conj (.mem 20 19) (.neg (.all 21 (.neg (.conj (.mem 21 19) (.conj (.rel .pair 22 [8, 20, 21]) (.neg (.all 24 (.neg (.conj (.mem 24 20) (.neg (.all 25 (.neg (.conj (.mem 25 24) (.neg (.all 26 (.neg (.conj (.mem 26 24) (.conj (.rel .pair 27 [20, 25, 26]) (.mem 21 2))))))))))))))))))))))))))))))))) (.all 8 (.neg (.conj (.mem 8 3) (.neg (.neg (.all 29 (.neg (.conj (.mem 29 8) (.neg (.all 30 (.neg (.conj (.mem 30 29) (.neg (.all 31 (.neg (.conj (.mem 31 29) (.conj (.rel .pair 32 [8, 30, 31]) (.conj (.mem 30 2) (.mem 31 2)))))))))))))))))))) (.all 6 (.neg (.conj (.mem 6 2) (.neg (.all 7 (.neg (.conj (.mem 7 2) (.neg (.conj (.neg (.conj (.rel .in_pair_l 13282 [3, 6, 7]) (.neg (.neg (.conj (.neg (.neg (.conj (.neg (.conj (.conj (.mem 6 0) (.mem 7 0)) (.rel .in_pair_l 13234 [1, 6, 7]))) (.neg (.conj (.mem 6 0) (.neg (.mem 7 0))))))) (.neg (.conj (.conj (.neg (.mem 6 0)) (.neg (.mem 7 0))) (.rel .new_less 13237 [6, 7, 4, 1])))))))) (.neg (.conj (.neg (.conj (.neg (.neg (.conj (.neg (.conj (.conj (.mem 6 0) (.mem 7 0)) (.rel .in_pair_l 13234 [1, 6, 7]))) (.neg (.conj (.mem 6 0) (.neg (.mem 7 0))))))) (.neg (.conj (.conj (.neg (.mem 6 0)) (.neg (.mem 7 0))) (.rel .new_less 13237 [6, 7, 4, 1]))))) (.neg (.rel .in_pair_l 13282 [3, 6, 7])))))))))))))))))
def tbl_step : Nm → Option (Nat × F) := fun nm => match nm with
    | .def_table => some (2, full_def_table)
    | .in_pair_l => some (3, full_in_pair_l)
    | .new_less => some (4, full_new_less)
    | .pair => some (3, full_pair)
    | _ => none
def full_step : F := expand tbl_step r_step

def r_l_order : F := (.conj (.rel .ordinal 13384 [0]) (.neg (.all 3 (.neg (.conj (.rel .succ 13389 [0, 3]) (.neg (.all 4 (.neg (.conj (.conj (.conj (.all 8 (.neg (.conj (.mem 8 4) (.neg (.neg (.all 9 (.neg (.conj (.mem 9 8) (.neg (.all 10 (.neg (.conj (.mem 10 9) (.neg (.all 11 (.neg (.conj (.mem 11 9) (.conj (.rel .pair 12 [8, 10, 11]) (.mem 10 3)))))))))))))))))) (.all 14 (.neg (.conj (.mem 14 4) (.neg (.all 15 (.neg (.conj (.mem 15 14) (.neg (.all 16 (.neg (.conj (.mem 16 15) (.neg (.all 17 (.neg (.conj (.mem 17 15) (.neg (.neg (.conj (.rel .pair 18 [14, 16, 17]) (.neg (.all 20 (.neg (.conj (.mem 20 4) (.neg (.all 21 (.neg (.conj (.mem 21 20) (.neg (.all 22 (.neg (.conj (.mem 22 21) (.neg (.all 23 (.neg (.conj (.mem 23 21) (.neg (.neg (.conj (.rel .pair 24 [20, 22, 23]) (.neg (.neg (.conj (.eq 16 22) (.neg (.eq 17 23))))))))))))))))))))))))))))))))))))))))))) (.all 5 (.neg (.conj (.mem 5 3) (.neg (.neg (.all 26 (.neg (.conj (.mem 26 4) (.neg (.all 27 (.neg (.conj (.mem 27 26) (.neg (.all 28 (.neg (.conj (.mem 28 27) (.conj (.rel .pair 29 [26, 5, 28]) (.neg (.all 31 (.neg (.conj (.mem 31 28) (.neg (.all 32 (.neg (.conj (.mem 32 31) (.neg (.all 33 (.neg (.conj (.mem 33 31) (.conj (.rel .pair 34 [28, 32, 33]) (.conj (.conj (.neg (.conj (.rel .empty 36 [5]) (.neg (.conj (.rel .empty 37 [32]) (.rel .empty 38 [33]))))) (.all 6 (.neg (.conj (.mem 6 5) (.neg (.neg (.conj (.rel .succ 39 [6, 5]) (.neg (.neg (.all 40 (.neg (.conj (.mem 40 4) (.neg (.all 41 (.neg (.conj (.mem 41 40) (.neg (.all 42 (.neg (.conj (.mem 42 41) (.conj (.rel .pair 43 [40, 6, 42]) (.neg (.all 45 (.neg (.conj (.mem 45 42) (.neg (.all 46 (.neg (.conj (.mem 46 45) (.neg (.all 47 (.neg (.conj (.mem 47 45) (.conj (.rel .pair 48 [42, 46, 47]) (.rel .step 50 [46, 47, 32, 33]))))))))))))))))))))))))))))))))))) (.neg (.conj (.conj (.neg (.rel .empty 13331 [5])) (.neg (.neg (.all 13332 (.neg (.conj (.mem 13332 5) (.rel .succ 13333 [13332, 5]))))))) (.neg (.conj (.conj (.all 7 (.neg (.conj (.mem 7 32) (.neg (.neg (.all 6 (.neg (.conj (.mem 6 5) (.neg (.all 13334 (.neg (.conj (.mem 13334 4) (.neg (.all 13335 (.neg (.conj (.mem 13335 13334) (.neg (.all 13336 (.neg (.conj (.mem 13336 13335) (.conj (.rel .pair 13337 [13334, 6, 13336]) (.neg (.all 13339 (.neg (.conj (.mem 13339 13336) (.neg (.all 13340 (.neg (.conj (.mem 13340 13339) (.neg (.all 13341 (.neg (.conj (.mem 13341 13339) (.conj (.rel .pair 13342 [13336, 13340, 13341]) (.mem 7 13340))))))))))))))))))))))))))))))))))) (.all 6 (.neg (.conj (.mem 6 5) (.neg (.neg (.all 13344 (.neg (.conj (.mem 13344 4) (.neg (.all 13345 (.neg (.conj (.mem 13345 13344) (.neg (.all 13346 (.neg (.conj (.mem 13346 13345) (.conj (.rel .pair 13347 [13344, 6, 13346]) (.neg (.all 13349 (.neg (.conj (.mem 13349 13346) (.neg (.all 13350 (.neg (.conj (.mem 13350 13349) (.neg (.all 13351 (.neg (.conj (.mem 13351 13349) (.conj (.rel .pair 13352 [13346, 13350, 13351]) (.all 7 (.neg (.conj (.mem 7 13350) (.neg (.mem 7 32)))))))))))))))))))))))))))))))))))) (.conj (.all 7 (.neg (.conj (.mem 7 33) (.neg (.neg (.all 6 (.neg (.conj (.mem 6 5) (.neg (.all 13354 (.neg (.conj (.mem 13354 4) (.neg (.all 13355 (.neg (.conj (.mem 13355 13354) (.neg (.all 13356 (.neg (.conj (.mem 13356 13355) (.conj (.rel .pair 13357 [13354, 6, 13356]) (.neg (.all 13359 (.neg (.conj (.mem 13359 13356) (.neg (.all 13360 (.neg (.conj (.mem 13360 13359) (.neg (.all 13361 (.neg (.conj (.mem 13361 13359) (.conj (.rel .pair 13362 [13356, 13360, 13361]) (.mem 7 13361))))))))))))))))))))))))))))))))))) (.all 6 (.neg (.conj (.mem 6 5) (.neg (.neg (.all 13364 (.neg (.conj (.mem 13364 4) (.neg (.all 13365 (.neg (.conj (.mem 13365 13364) (.neg (.all 13366 (.neg (.conj (.mem 13366 13365) (.conj (.rel .pair 13367 [13364, 6, 13366]) (.neg (.all 13369 (.neg (.conj (.mem 13369 13366) (.neg (.all 13370 (.neg (.conj (.mem 13370 13369) (.neg (.all 13371 (.neg (.conj (.mem 13371 13369) (.conj (.rel .pair 13372 [13366, 13370, 13371]) (.all 7 (.neg (.conj (.mem 7 13371) (.neg (.mem 7 33)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.neg (.all 13374 (.neg (.conj (.mem 13374 4) (.neg (.all 13375 (.neg (.conj (.mem 13375 13374) (.neg (.all 13376 (.neg (.conj (.mem 13376 13375) (.conj (.rel .pair 13377 [13374, 0, 13376]) (.neg (.all 13379 (.neg (.conj (.mem 13379 13376) (.neg (.all 13380 (.neg (.conj (.mem 13380 13379) (.neg (.all 13381 (.neg (.conj (.mem 13381 13379) (.conj (.rel .pair 13382 [13376, 13380, 13381]) (.conj (.eq 13380 1) (.eq 13381 2)))))))))))))))))))))))))))))))))))))
def tbl_l_order : Nm → Option (Nat × F) := fun nm => match nm with
    | .empty => some (1, full_empty)
    | .ordinal => some (1, full_ordinal)
    | .pair => some (3, full_pair)
    | .step => some (4, full_step)
    | .succ => some (2, full_succ)
    | _ => none
def full_l_order : F := expand tbl_l_order r_l_order

end Tr
