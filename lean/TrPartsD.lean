import TrPartsC
set_option maxRecDepth 200000
namespace Tr

/-! 生成プログラムが書き出した部品（層 D。lean_tr_export.py による。手で編集しない）。 -/

def r_assign_w : F := (.conj (.conj (.all 3 (.neg (.conj (.mem 3 2) (.neg (.neg (.all 5 (.neg (.conj (.mem 5 3) (.neg (.all 6 (.neg (.conj (.mem 6 5) (.neg (.all 7 (.neg (.conj (.mem 7 5) (.conj (.rel .pair 8 [3, 6, 7]) (.conj (.mem 6 0) (.mem 7 1))))))))))))))))))) (.all 4 (.neg (.conj (.mem 4 0) (.neg (.neg (.all 10 (.neg (.conj (.mem 10 2) (.neg (.all 11 (.neg (.conj (.mem 11 10) (.neg (.all 12 (.neg (.conj (.mem 12 11) (.conj (.rel .pair 13 [10, 4, 12]) (.eq 12 12))))))))))))))))))) (.all 15 (.neg (.conj (.mem 15 2) (.neg (.all 16 (.neg (.conj (.mem 16 15) (.neg (.all 17 (.neg (.conj (.mem 17 16) (.neg (.all 18 (.neg (.conj (.mem 18 16) (.neg (.neg (.conj (.rel .pair 19 [15, 17, 18]) (.neg (.all 21 (.neg (.conj (.mem 21 2) (.neg (.all 22 (.neg (.conj (.mem 22 21) (.neg (.all 23 (.neg (.conj (.mem 23 22) (.neg (.all 24 (.neg (.conj (.mem 24 22) (.neg (.neg (.conj (.rel .pair 25 [21, 23, 24]) (.neg (.neg (.conj (.eq 17 23) (.neg (.eq 18 24)))))))))))))))))))))))))))))))))))))))))))
def tbl_assign_w : Nm → Option (Nat × F) := fun nm => match nm with
    | .pair => some (3, full_pair)
    | _ => none
def full_assign_w : F := expand tbl_assign_w r_assign_w

def r_update_w : F := (.conj (.conj (.rel .assign_w 6 [0, 1, 5]) (.neg (.all 30 (.neg (.conj (.mem 30 5) (.neg (.all 31 (.neg (.conj (.mem 31 30) (.neg (.all 32 (.neg (.conj (.mem 32 31) (.conj (.rel .pair 33 [30, 3, 32]) (.eq 32 4))))))))))))))) (.all 35 (.neg (.conj (.mem 35 2) (.neg (.all 36 (.neg (.conj (.mem 36 35) (.neg (.all 37 (.neg (.conj (.mem 37 36) (.neg (.all 38 (.neg (.conj (.mem 38 36) (.neg (.neg (.conj (.rel .pair 39 [35, 37, 38]) (.neg (.neg (.conj (.neg (.eq 37 3)) (.neg (.neg (.all 41 (.neg (.conj (.mem 41 5) (.neg (.all 42 (.neg (.conj (.mem 42 41) (.neg (.all 43 (.neg (.conj (.mem 43 42) (.conj (.rel .pair 44 [41, 37, 43]) (.eq 43 38)))))))))))))))))))))))))))))))))))))
def tbl_update_w : Nm → Option (Nat × F) := fun nm => match nm with
    | .assign_w => some (3, full_assign_w)
    | .pair => some (3, full_pair)
    | _ => none
def full_update_w : F := expand tbl_update_w r_update_w

def r_is_definition : F := (.neg (.all 9 (.neg (.conj (.rel .empty 143 [9]) (.neg (.all 10 (.neg (.conj (.rel .succ 144 [9, 10]) (.neg (.all 6 (.neg (.conj (.conj (.conj (.conj (.rel .nat 219 [6]) (.all 146 (.neg (.conj (.mem 146 0) (.neg (.neg (.all 147 (.neg (.conj (.mem 147 146) (.neg (.all 148 (.neg (.conj (.mem 148 147) (.neg (.all 149 (.neg (.conj (.mem 149 147) (.conj (.rel .pair 150 [146, 148, 149]) (.conj (.mem 148 6) (.rel .tuple4 152 [149])))))))))))))))))))) (.all 145 (.neg (.conj (.mem 145 6) (.neg (.neg (.all 202 (.neg (.conj (.mem 202 0) (.neg (.all 203 (.neg (.conj (.mem 203 202) (.neg (.all 204 (.neg (.conj (.mem 204 203) (.conj (.rel .pair 205 [202, 145, 204]) (.eq 204 204))))))))))))))))))) (.all 207 (.neg (.conj (.mem 207 0) (.neg (.all 208 (.neg (.conj (.mem 208 207) (.neg (.all 209 (.neg (.conj (.mem 209 208) (.neg (.all 210 (.neg (.conj (.mem 210 208) (.neg (.neg (.conj (.rel .pair 211 [207, 209, 210]) (.neg (.all 213 (.neg (.conj (.mem 213 0) (.neg (.all 214 (.neg (.conj (.mem 214 213) (.neg (.all 215 (.neg (.conj (.mem 215 214) (.neg (.all 216 (.neg (.conj (.mem 216 214) (.neg (.neg (.conj (.rel .pair 217 [213, 215, 216]) (.neg (.neg (.conj (.eq 209 215) (.neg (.eq 210 216))))))))))))))))))))))))))))))))))))))))))) (.neg (.all 7 (.neg (.conj (.conj (.all 12 (.neg (.conj (.mem 12 7) (.neg (.neg (.all 11 (.neg (.conj (.mem 11 6) (.neg (.all 14 (.neg (.conj (.mem 14 0) (.neg (.all 15 (.neg (.conj (.mem 15 14) (.neg (.all 16 (.neg (.conj (.mem 16 15) (.conj (.rel .pair 17 [14, 11, 16]) (.conj (.rel .symvar 19 [16]) (.neg (.all 67 (.neg (.conj (.rel .numeral2 68 [67]) (.neg (.all 73 (.neg (.conj (.mem 73 16) (.neg (.all 74 (.neg (.conj (.mem 74 73) (.neg (.all 75 (.neg (.conj (.mem 75 74) (.conj (.rel .pair 76 [73, 67, 75]) (.eq 75 12)))))))))))))))))))))))))))))))))))))))) (.all 11 (.neg (.conj (.mem 11 6) (.neg (.neg (.all 78 (.neg (.conj (.mem 78 0) (.neg (.all 79 (.neg (.conj (.mem 79 78) (.neg (.all 80 (.neg (.conj (.mem 80 79) (.conj (.rel .pair 81 [78, 11, 80]) (.neg (.conj (.rel .symvar 83 [80]) (.neg (.neg (.all 131 (.neg (.conj (.rel .numeral2 132 [131]) (.neg (.all 137 (.neg (.conj (.mem 137 80) (.neg (.all 138 (.neg (.conj (.mem 138 137) (.neg (.all 139 (.neg (.conj (.mem 139 138) (.conj (.rel .pair 140 [137, 131, 139]) (.mem 139 7))))))))))))))))))))))))))))))))))))))) (.neg (.all 8 (.neg (.conj (.conj (.conj (.conj (.all 142 (.neg (.conj (.mem 142 8) (.neg (.neg (.conj (.neg (.mem 142 7)) (.neg (.neg (.conj (.neg (.eq 142 9)) (.neg (.eq 142 10))))))))))) (.all 142 (.neg (.conj (.mem 142 7) (.neg (.mem 142 8)))))) (.mem 9 8)) (.mem 10 8)) (.all 227 (.neg (.conj (.rel .assign_w 3978 [8, 1, 227]) (.neg (.neg (.all 228 (.neg (.conj (.mem 228 1) (.conj (.neg (.all 230 (.neg (.conj (.rel .update_w 4002 [8, 1, 227, 9, 228, 230]) (.rel .sat_ext 4042 [0, 1, 2, 3, 4, 5, 230]))))) (.all 229 (.neg (.conj (.mem 229 1) (.neg (.neg (.conj (.neg (.all 232 (.neg (.conj (.rel .update_w 233 [8, 1, 227, 9, 229, 232]) (.neg (.all 231 (.neg (.conj (.rel .update_w 273 [8, 1, 232, 10, 229, 231]) (.rel .sat_ext 313 [0, 1, 2, 3, 4, 5, 231]))))))))) (.neg (.eq 229 228)))))))))))))))))))))))))))))))))))))
def tbl_is_definition : Nm → Option (Nat × F) := fun nm => match nm with
    | .assign_w => some (3, full_assign_w)
    | .empty => some (1, full_empty)
    | .nat => some (1, full_nat)
    | .numeral2 => some (1, full_numeral2)
    | .pair => some (3, full_pair)
    | .sat_ext => some (7, full_sat_ext)
    | .succ => some (2, full_succ)
    | .symvar => some (1, full_symvar)
    | .tuple4 => some (1, full_tuple4)
    | .update_w => some (6, full_update_w)
    | _ => none
def full_is_definition : F := expand tbl_is_definition r_is_definition

def r_param_true : F := (.neg (.all 10 (.neg (.conj (.rel .empty 144 [10]) (.neg (.all 11 (.neg (.conj (.rel .succ 145 [10, 11]) (.neg (.all 7 (.neg (.conj (.conj (.conj (.conj (.rel .nat 220 [7]) (.all 147 (.neg (.conj (.mem 147 0) (.neg (.neg (.all 148 (.neg (.conj (.mem 148 147) (.neg (.all 149 (.neg (.conj (.mem 149 148) (.neg (.all 150 (.neg (.conj (.mem 150 148) (.conj (.rel .pair 151 [147, 149, 150]) (.conj (.mem 149 7) (.rel .tuple4 153 [150])))))))))))))))))))) (.all 146 (.neg (.conj (.mem 146 7) (.neg (.neg (.all 203 (.neg (.conj (.mem 203 0) (.neg (.all 204 (.neg (.conj (.mem 204 203) (.neg (.all 205 (.neg (.conj (.mem 205 204) (.conj (.rel .pair 206 [203, 146, 205]) (.eq 205 205))))))))))))))))))) (.all 208 (.neg (.conj (.mem 208 0) (.neg (.all 209 (.neg (.conj (.mem 209 208) (.neg (.all 210 (.neg (.conj (.mem 210 209) (.neg (.all 211 (.neg (.conj (.mem 211 209) (.neg (.neg (.conj (.rel .pair 212 [208, 210, 211]) (.neg (.all 214 (.neg (.conj (.mem 214 0) (.neg (.all 215 (.neg (.conj (.mem 215 214) (.neg (.all 216 (.neg (.conj (.mem 216 215) (.neg (.all 217 (.neg (.conj (.mem 217 215) (.neg (.neg (.conj (.rel .pair 218 [214, 216, 217]) (.neg (.neg (.conj (.eq 210 216) (.neg (.eq 211 217))))))))))))))))))))))))))))))))))))))))))) (.neg (.all 8 (.neg (.conj (.conj (.all 13 (.neg (.conj (.mem 13 8) (.neg (.neg (.all 12 (.neg (.conj (.mem 12 7) (.neg (.all 15 (.neg (.conj (.mem 15 0) (.neg (.all 16 (.neg (.conj (.mem 16 15) (.neg (.all 17 (.neg (.conj (.mem 17 16) (.conj (.rel .pair 18 [15, 12, 17]) (.conj (.rel .symvar 20 [17]) (.neg (.all 68 (.neg (.conj (.rel .numeral2 69 [68]) (.neg (.all 74 (.neg (.conj (.mem 74 17) (.neg (.all 75 (.neg (.conj (.mem 75 74) (.neg (.all 76 (.neg (.conj (.mem 76 75) (.conj (.rel .pair 77 [74, 68, 76]) (.eq 76 13)))))))))))))))))))))))))))))))))))))))) (.all 12 (.neg (.conj (.mem 12 7) (.neg (.neg (.all 79 (.neg (.conj (.mem 79 0) (.neg (.all 80 (.neg (.conj (.mem 80 79) (.neg (.all 81 (.neg (.conj (.mem 81 80) (.conj (.rel .pair 82 [79, 12, 81]) (.neg (.conj (.rel .symvar 84 [81]) (.neg (.neg (.all 132 (.neg (.conj (.rel .numeral2 133 [132]) (.neg (.all 138 (.neg (.conj (.mem 138 81) (.neg (.all 139 (.neg (.conj (.mem 139 138) (.neg (.all 140 (.neg (.conj (.mem 140 139) (.conj (.rel .pair 141 [138, 132, 140]) (.mem 140 8))))))))))))))))))))))))))))))))))))))) (.neg (.all 9 (.neg (.conj (.conj (.conj (.conj (.all 143 (.neg (.conj (.mem 143 9) (.neg (.neg (.conj (.neg (.mem 143 8)) (.neg (.neg (.conj (.neg (.eq 143 10)) (.neg (.eq 143 11))))))))))) (.all 143 (.neg (.conj (.mem 143 8) (.neg (.mem 143 9)))))) (.mem 10 9)) (.mem 11 9)) (.all 228 (.neg (.conj (.conj (.rel .assign_w 229 [9, 1, 228]) (.neg (.all 253 (.neg (.conj (.mem 253 228) (.neg (.all 254 (.neg (.conj (.mem 254 253) (.neg (.all 255 (.neg (.conj (.mem 255 254) (.conj (.rel .pair 256 [253, 10, 255]) (.eq 255 6))))))))))))))) (.neg (.rel .sat_ext 258 [0, 1, 2, 3, 4, 5, 228])))))))))))))))))))))))))
def tbl_param_true : Nm → Option (Nat × F) := fun nm => match nm with
    | .assign_w => some (3, full_assign_w)
    | .empty => some (1, full_empty)
    | .nat => some (1, full_nat)
    | .numeral2 => some (1, full_numeral2)
    | .pair => some (3, full_pair)
    | .sat_ext => some (7, full_sat_ext)
    | .succ => some (2, full_succ)
    | .symvar => some (1, full_symvar)
    | .tuple4 => some (1, full_tuple4)
    | _ => none
def full_param_true : F := expand tbl_param_true r_param_true

def r_definable_in : F := (.conj (.conj (.mem 6 1) (.rel .is_definition 7 [0, 1, 2, 3, 4, 5])) (.rel .param_true 7708 [0, 1, 2, 3, 4, 5, 6]))
def tbl_definable_in : Nm → Option (Nat × F) := fun nm => match nm with
    | .is_definition => some (6, full_is_definition)
    | .param_true => some (7, full_param_true)
    | _ => none
def full_definable_in : F := expand tbl_definable_in r_definable_in

end Tr
