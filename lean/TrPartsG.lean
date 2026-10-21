import TrPartsF
set_option maxRecDepth 200000
namespace Tr

/-! 生成プログラムが書き出した部品（層 G。lean_tr_export.py による。手で編集しない）。 -/

def r_numeral10 : F := (.neg (.all 1 (.neg (.conj (.mem 1 0) (.conj (.rel .succ 2 [1, 0]) (.rel .numeral9 3 [1]))))))
def tbl_numeral10 : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral9 => some (1, full_numeral9)
    | .succ => some (2, full_succ)
    | _ => none
def full_numeral10 : F := expand tbl_numeral10 r_numeral10

def r_numeral11 : F := (.neg (.all 1 (.neg (.conj (.mem 1 0) (.conj (.rel .succ 2 [1, 0]) (.rel .numeral10 3 [1]))))))
def tbl_numeral11 : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral10 => some (1, full_numeral10)
    | .succ => some (2, full_succ)
    | _ => none
def full_numeral11 : F := expand tbl_numeral11 r_numeral11

def r_numeral12 : F := (.neg (.all 1 (.neg (.conj (.mem 1 0) (.conj (.rel .succ 2 [1, 0]) (.rel .numeral11 3 [1]))))))
def tbl_numeral12 : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral11 => some (1, full_numeral11)
    | .succ => some (2, full_succ)
    | _ => none
def full_numeral12 : F := expand tbl_numeral12 r_numeral12

def r_dec : F := (.conj (.neg (.rel .empty 479 [0])) (.neg (.all 3 (.neg (.conj (.rel .succ 480 [0, 3]) (.neg (.all 4 (.neg (.conj (.conj (.conj (.rel .prime 338 [4]) (.rel .divides 417 [4, 3])) (.all 8 (.neg (.conj (.mem 8 4) (.neg (.neg (.conj (.rel .prime 197 [8]) (.rel .divides 276 [8, 3])))))))) (.neg (.all 5 (.neg (.conj (.rel .succ 196 [1, 5]) (.neg (.all 6 (.neg (.conj (.rel .exp 133 [4, 5, 6]) (.neg (.all 7 (.neg (.conj (.conj (.rel .mul 9 [6, 7, 3]) (.rel .succ 70 [2, 7])) (.neg (.rel .divides 71 [4, 7])))))))))))))))))))))))
def tbl_dec : Nm → Option (Nat × F) := fun nm => match nm with
    | .divides => some (2, full_divides)
    | .empty => some (1, full_empty)
    | .exp => some (3, full_exp)
    | .mul => some (3, full_mul)
    | .prime => some (1, full_prime)
    | .succ => some (2, full_succ)
    | _ => none
def full_dec : F := expand tbl_dec r_dec

def r_row_shape0 : F := (.conj (.neg (.all 1 (.neg (.conj (.rel .numeral4 2 [1]) (.conj (.conj (.conj (.rel .nat 43 [1]) (.all 12 (.neg (.conj (.mem 12 0) (.neg (.neg (.all 13 (.neg (.conj (.mem 13 12) (.neg (.all 14 (.neg (.conj (.mem 14 13) (.neg (.all 15 (.neg (.conj (.mem 15 13) (.conj (.rel .pair 16 [12, 14, 15]) (.conj (.mem 14 1) (.rel .nat 18 [15])))))))))))))))))))) (.all 11 (.neg (.conj (.mem 11 1) (.neg (.neg (.all 26 (.neg (.conj (.mem 26 0) (.neg (.all 27 (.neg (.conj (.mem 27 26) (.neg (.all 28 (.neg (.conj (.mem 28 27) (.conj (.rel .pair 29 [26, 11, 28]) (.eq 28 28))))))))))))))))))) (.all 31 (.neg (.conj (.mem 31 0) (.neg (.all 32 (.neg (.conj (.mem 32 31) (.neg (.all 33 (.neg (.conj (.mem 33 32) (.neg (.all 34 (.neg (.conj (.mem 34 32) (.neg (.neg (.conj (.rel .pair 35 [31, 33, 34]) (.neg (.all 37 (.neg (.conj (.mem 37 0) (.neg (.all 38 (.neg (.conj (.mem 38 37) (.neg (.all 39 (.neg (.conj (.mem 39 38) (.neg (.all 40 (.neg (.conj (.mem 40 38) (.neg (.neg (.conj (.rel .pair 41 [37, 39, 40]) (.neg (.neg (.conj (.eq 33 39) (.neg (.eq 34 40))))))))))))))))))))))))))))))))))))))))))))))) (.neg (.all 51 (.neg (.conj (.rel .numeral0 52 [51]) (.neg (.all 53 (.neg (.conj (.mem 53 0) (.neg (.all 54 (.neg (.conj (.mem 54 53) (.neg (.all 55 (.neg (.conj (.mem 55 54) (.conj (.rel .pair 56 [53, 51, 55]) (.rel .numeral0 58 [55])))))))))))))))))))
def tbl_row_shape0 : Nm → Option (Nat × F) := fun nm => match nm with
    | .nat => some (1, full_nat)
    | .numeral0 => some (1, full_numeral0)
    | .numeral4 => some (1, full_numeral4)
    | .pair => some (3, full_pair)
    | _ => none
def full_row_shape0 : F := expand tbl_row_shape0 r_row_shape0

def r_row_shape1 : F := (.conj (.neg (.all 1 (.neg (.conj (.rel .numeral4 2 [1]) (.conj (.conj (.conj (.rel .nat 43 [1]) (.all 12 (.neg (.conj (.mem 12 0) (.neg (.neg (.all 13 (.neg (.conj (.mem 13 12) (.neg (.all 14 (.neg (.conj (.mem 14 13) (.neg (.all 15 (.neg (.conj (.mem 15 13) (.conj (.rel .pair 16 [12, 14, 15]) (.conj (.mem 14 1) (.rel .nat 18 [15])))))))))))))))))))) (.all 11 (.neg (.conj (.mem 11 1) (.neg (.neg (.all 26 (.neg (.conj (.mem 26 0) (.neg (.all 27 (.neg (.conj (.mem 27 26) (.neg (.all 28 (.neg (.conj (.mem 28 27) (.conj (.rel .pair 29 [26, 11, 28]) (.eq 28 28))))))))))))))))))) (.all 31 (.neg (.conj (.mem 31 0) (.neg (.all 32 (.neg (.conj (.mem 32 31) (.neg (.all 33 (.neg (.conj (.mem 33 32) (.neg (.all 34 (.neg (.conj (.mem 34 32) (.neg (.neg (.conj (.rel .pair 35 [31, 33, 34]) (.neg (.all 37 (.neg (.conj (.mem 37 0) (.neg (.all 38 (.neg (.conj (.mem 38 37) (.neg (.all 39 (.neg (.conj (.mem 39 38) (.neg (.all 40 (.neg (.conj (.mem 40 38) (.neg (.neg (.conj (.rel .pair 41 [37, 39, 40]) (.neg (.neg (.conj (.eq 33 39) (.neg (.eq 34 40))))))))))))))))))))))))))))))))))))))))))))))) (.neg (.all 51 (.neg (.conj (.rel .numeral0 52 [51]) (.neg (.all 53 (.neg (.conj (.mem 53 0) (.neg (.all 54 (.neg (.conj (.mem 54 53) (.neg (.all 55 (.neg (.conj (.mem 55 54) (.conj (.rel .pair 56 [53, 51, 55]) (.rel .numeral1 58 [55])))))))))))))))))))
def tbl_row_shape1 : Nm → Option (Nat × F) := fun nm => match nm with
    | .nat => some (1, full_nat)
    | .numeral0 => some (1, full_numeral0)
    | .numeral1 => some (1, full_numeral1)
    | .numeral4 => some (1, full_numeral4)
    | .pair => some (3, full_pair)
    | _ => none
def full_row_shape1 : F := expand tbl_row_shape1 r_row_shape1

def r_table_ok : F := (.all 1 (.neg (.conj (.mem 1 0) (.neg (.neg (.all 2 (.neg (.conj (.rel .numeral0 3 [2]) (.neg (.all 4 (.neg (.conj (.mem 4 1) (.neg (.all 5 (.neg (.conj (.mem 5 4) (.neg (.all 6 (.neg (.conj (.mem 6 5) (.conj (.rel .pair 7 [4, 2, 6]) (.neg (.all 9 (.neg (.conj (.rel .numeral1 10 [9]) (.neg (.all 13 (.neg (.conj (.mem 13 1) (.neg (.all 14 (.neg (.conj (.mem 14 13) (.neg (.all 15 (.neg (.conj (.mem 15 14) (.conj (.rel .pair 16 [13, 9, 15]) (.neg (.all 18 (.neg (.conj (.rel .numeral2 19 [18]) (.neg (.all 24 (.neg (.conj (.mem 24 1) (.neg (.all 25 (.neg (.conj (.mem 25 24) (.neg (.all 26 (.neg (.conj (.mem 26 25) (.conj (.rel .pair 27 [24, 18, 26]) (.neg (.all 29 (.neg (.conj (.rel .numeral3 30 [29]) (.neg (.all 37 (.neg (.conj (.mem 37 1) (.neg (.all 38 (.neg (.conj (.mem 38 37) (.neg (.all 39 (.neg (.conj (.mem 39 38) (.conj (.rel .pair 40 [37, 29, 39]) (.neg (.conj (.neg (.conj (.rel .numeral0 42 [6]) (.neg (.all 43 (.neg (.conj (.mem 43 15) (.neg (.all 44 (.neg (.conj (.mem 44 15) (.conj (.rel .dec 244 [15, 43, 44]) (.neg (.conj (.neg (.conj (.conj (.rel .empty 45 [44]) (.eq 26 43)) (.rel .empty 46 [39]))) (.neg (.conj (.neg (.rel .empty 47 [44])) (.neg (.all 48 (.neg (.conj (.mem 48 0) (.conj (.conj (.rel .row_shape0 49 [48]) (.neg (.all 107 (.neg (.conj (.rel .numeral1 108 [107]) (.neg (.all 111 (.neg (.conj (.mem 111 48) (.neg (.all 112 (.neg (.conj (.mem 112 111) (.neg (.all 113 (.neg (.conj (.mem 113 112) (.conj (.rel .pair 114 [111, 107, 113]) (.eq 113 44))))))))))))))))))) (.neg (.all 116 (.neg (.conj (.rel .numeral2 117 [116]) (.neg (.all 122 (.neg (.conj (.mem 122 48) (.neg (.all 123 (.neg (.conj (.mem 123 122) (.neg (.all 124 (.neg (.conj (.mem 124 123) (.conj (.rel .pair 125 [122, 116, 124]) (.neg (.all 127 (.neg (.conj (.rel .numeral3 128 [127]) (.neg (.all 135 (.neg (.conj (.mem 135 48) (.neg (.all 136 (.neg (.conj (.mem 136 135) (.neg (.all 137 (.neg (.conj (.mem 137 136) (.conj (.rel .pair 138 [135, 127, 137]) (.neg (.all 140 (.neg (.conj (.mem 140 0) (.conj (.conj (.conj (.rel .row_shape1 141 [140]) (.neg (.all 201 (.neg (.conj (.rel .numeral1 202 [201]) (.neg (.all 205 (.neg (.conj (.mem 205 140) (.neg (.all 206 (.neg (.conj (.mem 206 205) (.neg (.all 207 (.neg (.conj (.mem 207 206) (.conj (.rel .pair 208 [205, 201, 207]) (.eq 207 124))))))))))))))))))) (.neg (.all 210 (.neg (.conj (.rel .numeral2 211 [210]) (.neg (.all 216 (.neg (.conj (.mem 216 140) (.neg (.all 217 (.neg (.conj (.mem 217 216) (.neg (.all 218 (.neg (.conj (.mem 218 217) (.conj (.rel .pair 219 [216, 210, 218]) (.eq 218 43))))))))))))))))))) (.neg (.all 221 (.neg (.conj (.rel .numeral3 222 [221]) (.neg (.all 229 (.neg (.conj (.mem 229 140) (.neg (.all 230 (.neg (.conj (.mem 230 229) (.neg (.all 231 (.neg (.conj (.mem 231 230) (.conj (.rel .pair 232 [229, 221, 231]) (.neg (.conj (.neg (.conj (.conj (.rel .numeral2 234 [231]) (.eq 26 124)) (.eq 39 137))) (.neg (.conj (.conj (.neg (.rel .numeral2 239 [231])) (.eq 26 43)) (.eq 39 44))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.neg (.conj (.rel .numeral1 722 [6]) (.neg (.conj (.neg (.neg (.conj (.neg (.neg (.conj (.neg (.conj (.conj (.rel .empty 1105 [15]) (.rel .empty 1106 [26])) (.rel .numeral1 1107 [39]))) (.neg (.conj (.conj (.rel .empty 1110 [15]) (.neg (.rel .empty 1111 [26]))) (.rel .numeral0 1112 [39])))))) (.neg (.conj (.conj (.neg (.rel .empty 1113 [15])) (.rel .empty 1114 [26])) (.rel .numeral2 1115 [39])))))) (.neg (.conj (.conj (.neg (.rel .empty 725 [15])) (.neg (.rel .empty 726 [26]))) (.neg (.all 727 (.neg (.conj (.mem 727 0) (.conj (.conj (.rel .row_shape0 728 [727]) (.neg (.all 786 (.neg (.conj (.rel .numeral1 787 [786]) (.neg (.all 790 (.neg (.conj (.mem 790 727) (.neg (.all 791 (.neg (.conj (.mem 791 790) (.neg (.all 792 (.neg (.conj (.mem 792 791) (.conj (.rel .pair 793 [790, 786, 792]) (.eq 792 15))))))))))))))))))) (.neg (.all 795 (.neg (.conj (.rel .numeral2 796 [795]) (.neg (.all 801 (.neg (.conj (.mem 801 727) (.neg (.all 802 (.neg (.conj (.mem 802 801) (.neg (.all 803 (.neg (.conj (.mem 803 802) (.conj (.rel .pair 804 [801, 795, 803]) (.neg (.all 806 (.neg (.conj (.rel .numeral3 807 [806]) (.neg (.all 814 (.neg (.conj (.mem 814 727) (.neg (.all 815 (.neg (.conj (.mem 815 814) (.neg (.all 816 (.neg (.conj (.mem 816 815) (.conj (.rel .pair 817 [814, 806, 816]) (.neg (.all 819 (.neg (.conj (.mem 819 0) (.conj (.conj (.rel .row_shape0 820 [819]) (.neg (.all 878 (.neg (.conj (.rel .numeral1 879 [878]) (.neg (.all 882 (.neg (.conj (.mem 882 819) (.neg (.all 883 (.neg (.conj (.mem 883 882) (.neg (.all 884 (.neg (.conj (.mem 884 883) (.conj (.rel .pair 885 [882, 878, 884]) (.eq 884 26))))))))))))))))))) (.neg (.all 887 (.neg (.conj (.rel .numeral2 888 [887]) (.neg (.all 893 (.neg (.conj (.mem 893 819) (.neg (.all 894 (.neg (.conj (.mem 894 893) (.neg (.all 895 (.neg (.conj (.mem 895 894) (.conj (.rel .pair 896 [893, 887, 895]) (.neg (.all 898 (.neg (.conj (.rel .numeral3 899 [898]) (.neg (.all 906 (.neg (.conj (.mem 906 819) (.neg (.all 907 (.neg (.conj (.mem 907 906) (.neg (.all 908 (.neg (.conj (.mem 908 907) (.conj (.rel .pair 909 [906, 898, 908]) (.neg (.all 911 (.neg (.conj (.mem 911 0) (.conj (.conj (.conj (.rel .row_shape1 912 [911]) (.neg (.all 972 (.neg (.conj (.rel .numeral1 973 [972]) (.neg (.all 976 (.neg (.conj (.mem 976 911) (.neg (.all 977 (.neg (.conj (.mem 977 976) (.neg (.all 978 (.neg (.conj (.mem 978 977) (.conj (.rel .pair 979 [976, 972, 978]) (.eq 978 803))))))))))))))))))) (.neg (.all 981 (.neg (.conj (.rel .numeral2 982 [981]) (.neg (.all 987 (.neg (.conj (.mem 987 911) (.neg (.all 988 (.neg (.conj (.mem 988 987) (.neg (.all 989 (.neg (.conj (.mem 989 988) (.conj (.rel .pair 990 [987, 981, 989]) (.eq 989 895))))))))))))))))))) (.neg (.all 992 (.neg (.conj (.rel .numeral3 993 [992]) (.neg (.all 1000 (.neg (.conj (.mem 1000 911) (.neg (.all 1001 (.neg (.conj (.mem 1001 1000) (.neg (.all 1002 (.neg (.conj (.mem 1002 1001) (.conj (.rel .pair 1003 [1000, 992, 1002]) (.neg (.conj (.neg (.conj (.neg (.rel .numeral1 1005 [1002])) (.eq 39 1002))) (.neg (.conj (.rel .numeral1 1008 [1002]) (.neg (.all 1011 (.neg (.conj (.mem 1011 0) (.conj (.conj (.conj (.rel .row_shape1 1012 [1011]) (.neg (.all 1072 (.neg (.conj (.rel .numeral1 1073 [1072]) (.neg (.all 1076 (.neg (.conj (.mem 1076 1011) (.neg (.all 1077 (.neg (.conj (.mem 1077 1076) (.neg (.all 1078 (.neg (.conj (.mem 1078 1077) (.conj (.rel .pair 1079 [1076, 1072, 1078]) (.eq 1078 816))))))))))))))))))) (.neg (.all 1081 (.neg (.conj (.rel .numeral2 1082 [1081]) (.neg (.all 1087 (.neg (.conj (.mem 1087 1011) (.neg (.all 1088 (.neg (.conj (.mem 1088 1087) (.neg (.all 1089 (.neg (.conj (.mem 1089 1088) (.conj (.rel .pair 1090 [1087, 1081, 1089]) (.eq 1089 908))))))))))))))))))) (.neg (.all 1092 (.neg (.conj (.rel .numeral3 1093 [1092]) (.neg (.all 1100 (.neg (.conj (.mem 1100 1011) (.neg (.all 1101 (.neg (.conj (.mem 1101 1100) (.neg (.all 1102 (.neg (.conj (.mem 1102 1101) (.conj (.rel .pair 1103 [1100, 1092, 1102]) (.eq 1102 39)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def tbl_table_ok : Nm → Option (Nat × F) := fun nm => match nm with
    | .dec => some (3, full_dec)
    | .empty => some (1, full_empty)
    | .numeral0 => some (1, full_numeral0)
    | .numeral1 => some (1, full_numeral1)
    | .numeral2 => some (1, full_numeral2)
    | .numeral3 => some (1, full_numeral3)
    | .pair => some (3, full_pair)
    | .row_shape0 => some (1, full_row_shape0)
    | .row_shape1 => some (1, full_row_shape1)
    | _ => none
def full_table_ok : F := expand tbl_table_ok r_table_ok

def r_cnf_cmp : F := (.neg (.all 3 (.neg (.conj (.rel .table_ok 4 [3]) (.neg (.all 1123 (.neg (.conj (.mem 1123 3) (.conj (.conj (.conj (.rel .row_shape1 1124 [1123]) (.neg (.all 1184 (.neg (.conj (.rel .numeral1 1185 [1184]) (.neg (.all 1188 (.neg (.conj (.mem 1188 1123) (.neg (.all 1189 (.neg (.conj (.mem 1189 1188) (.neg (.all 1190 (.neg (.conj (.mem 1190 1189) (.conj (.rel .pair 1191 [1188, 1184, 1190]) (.eq 1190 0))))))))))))))))))) (.neg (.all 1193 (.neg (.conj (.rel .numeral2 1194 [1193]) (.neg (.all 1199 (.neg (.conj (.mem 1199 1123) (.neg (.all 1200 (.neg (.conj (.mem 1200 1199) (.neg (.all 1201 (.neg (.conj (.mem 1201 1200) (.conj (.rel .pair 1202 [1199, 1193, 1201]) (.eq 1201 1))))))))))))))))))) (.neg (.all 1204 (.neg (.conj (.rel .numeral3 1205 [1204]) (.neg (.all 1212 (.neg (.conj (.mem 1212 1123) (.neg (.all 1213 (.neg (.conj (.mem 1213 1212) (.neg (.all 1214 (.neg (.conj (.mem 1214 1213) (.conj (.rel .pair 1215 [1212, 1204, 1214]) (.eq 1214 2)))))))))))))))))))))))))))
def tbl_cnf_cmp : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral1 => some (1, full_numeral1)
    | .numeral2 => some (1, full_numeral2)
    | .numeral3 => some (1, full_numeral3)
    | .pair => some (3, full_pair)
    | .row_shape1 => some (1, full_row_shape1)
    | .table_ok => some (1, full_table_ok)
    | _ => none
def full_cnf_cmp : F := expand tbl_cnf_cmp r_cnf_cmp

def r_cnf_lt : F := (.neg (.all 2 (.neg (.conj (.rel .numeral0 3 [2]) (.rel .cnf_cmp 4 [0, 1, 2])))))
def tbl_cnf_lt : Nm → Option (Nat × F) := fun nm => match nm with
    | .cnf_cmp => some (3, full_cnf_cmp)
    | .numeral0 => some (1, full_numeral0)
    | _ => none
def full_cnf_lt : F := expand tbl_cnf_lt r_cnf_lt

end Tr
