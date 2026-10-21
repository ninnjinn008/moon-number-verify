import TrPartsA
set_option maxRecDepth 200000
namespace Tr

/-! 生成プログラムが書き出した部品（層 B。lean_tr_export.py による。手で編集しない）。 -/

def r_punct0 : F := (.conj (.conj (.conj (.neg (.all 1 (.neg (.conj (.rel .numeral0 2 [1]) (.neg (.all 3 (.neg (.conj (.mem 3 0) (.neg (.all 4 (.neg (.conj (.mem 4 3) (.neg (.all 5 (.neg (.conj (.mem 5 4) (.conj (.rel .pair 6 [3, 1, 5]) (.rel .numeral0 8 [5])))))))))))))))))) (.neg (.all 9 (.neg (.conj (.rel .numeral1 10 [9]) (.neg (.all 13 (.neg (.conj (.mem 13 0) (.neg (.all 14 (.neg (.conj (.mem 14 13) (.neg (.all 15 (.neg (.conj (.mem 15 14) (.conj (.rel .pair 16 [13, 9, 15]) (.rel .numeral0 18 [15]))))))))))))))))))) (.neg (.all 19 (.neg (.conj (.rel .numeral2 20 [19]) (.neg (.all 25 (.neg (.conj (.mem 25 0) (.neg (.all 26 (.neg (.conj (.mem 26 25) (.neg (.all 27 (.neg (.conj (.mem 27 26) (.conj (.rel .pair 28 [25, 19, 27]) (.rel .numeral0 30 [27]))))))))))))))))))) (.neg (.all 31 (.neg (.conj (.rel .numeral3 32 [31]) (.neg (.all 39 (.neg (.conj (.mem 39 0) (.neg (.all 40 (.neg (.conj (.mem 40 39) (.neg (.all 41 (.neg (.conj (.mem 41 40) (.conj (.rel .pair 42 [39, 31, 41]) (.rel .numeral0 44 [41])))))))))))))))))))
def tbl_punct0 : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral0 => some (1, full_numeral0)
    | .numeral1 => some (1, full_numeral1)
    | .numeral2 => some (1, full_numeral2)
    | .numeral3 => some (1, full_numeral3)
    | .pair => some (3, full_pair)
    | _ => none
def full_punct0 : F := expand tbl_punct0 r_punct0

def r_punct1 : F := (.conj (.conj (.conj (.neg (.all 1 (.neg (.conj (.rel .numeral0 2 [1]) (.neg (.all 3 (.neg (.conj (.mem 3 0) (.neg (.all 4 (.neg (.conj (.mem 4 3) (.neg (.all 5 (.neg (.conj (.mem 5 4) (.conj (.rel .pair 6 [3, 1, 5]) (.rel .numeral1 8 [5])))))))))))))))))) (.neg (.all 11 (.neg (.conj (.rel .numeral1 12 [11]) (.neg (.all 15 (.neg (.conj (.mem 15 0) (.neg (.all 16 (.neg (.conj (.mem 16 15) (.neg (.all 17 (.neg (.conj (.mem 17 16) (.conj (.rel .pair 18 [15, 11, 17]) (.rel .numeral0 20 [17]))))))))))))))))))) (.neg (.all 21 (.neg (.conj (.rel .numeral2 22 [21]) (.neg (.all 27 (.neg (.conj (.mem 27 0) (.neg (.all 28 (.neg (.conj (.mem 28 27) (.neg (.all 29 (.neg (.conj (.mem 29 28) (.conj (.rel .pair 30 [27, 21, 29]) (.rel .numeral0 32 [29]))))))))))))))))))) (.neg (.all 33 (.neg (.conj (.rel .numeral3 34 [33]) (.neg (.all 41 (.neg (.conj (.mem 41 0) (.neg (.all 42 (.neg (.conj (.mem 42 41) (.neg (.all 43 (.neg (.conj (.mem 43 42) (.conj (.rel .pair 44 [41, 33, 43]) (.rel .numeral0 46 [43])))))))))))))))))))
def tbl_punct1 : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral0 => some (1, full_numeral0)
    | .numeral1 => some (1, full_numeral1)
    | .numeral2 => some (1, full_numeral2)
    | .numeral3 => some (1, full_numeral3)
    | .pair => some (3, full_pair)
    | _ => none
def full_punct1 : F := expand tbl_punct1 r_punct1

def r_punct2 : F := (.conj (.conj (.conj (.neg (.all 1 (.neg (.conj (.rel .numeral0 2 [1]) (.neg (.all 3 (.neg (.conj (.mem 3 0) (.neg (.all 4 (.neg (.conj (.mem 4 3) (.neg (.all 5 (.neg (.conj (.mem 5 4) (.conj (.rel .pair 6 [3, 1, 5]) (.rel .numeral2 8 [5])))))))))))))))))) (.neg (.all 13 (.neg (.conj (.rel .numeral1 14 [13]) (.neg (.all 17 (.neg (.conj (.mem 17 0) (.neg (.all 18 (.neg (.conj (.mem 18 17) (.neg (.all 19 (.neg (.conj (.mem 19 18) (.conj (.rel .pair 20 [17, 13, 19]) (.rel .numeral0 22 [19]))))))))))))))))))) (.neg (.all 23 (.neg (.conj (.rel .numeral2 24 [23]) (.neg (.all 29 (.neg (.conj (.mem 29 0) (.neg (.all 30 (.neg (.conj (.mem 30 29) (.neg (.all 31 (.neg (.conj (.mem 31 30) (.conj (.rel .pair 32 [29, 23, 31]) (.rel .numeral0 34 [31]))))))))))))))))))) (.neg (.all 35 (.neg (.conj (.rel .numeral3 36 [35]) (.neg (.all 43 (.neg (.conj (.mem 43 0) (.neg (.all 44 (.neg (.conj (.mem 44 43) (.neg (.all 45 (.neg (.conj (.mem 45 44) (.conj (.rel .pair 46 [43, 35, 45]) (.rel .numeral0 48 [45])))))))))))))))))))
def tbl_punct2 : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral0 => some (1, full_numeral0)
    | .numeral1 => some (1, full_numeral1)
    | .numeral2 => some (1, full_numeral2)
    | .numeral3 => some (1, full_numeral3)
    | .pair => some (3, full_pair)
    | _ => none
def full_punct2 : F := expand tbl_punct2 r_punct2

def r_punct3 : F := (.conj (.conj (.conj (.neg (.all 1 (.neg (.conj (.rel .numeral0 2 [1]) (.neg (.all 3 (.neg (.conj (.mem 3 0) (.neg (.all 4 (.neg (.conj (.mem 4 3) (.neg (.all 5 (.neg (.conj (.mem 5 4) (.conj (.rel .pair 6 [3, 1, 5]) (.rel .numeral3 8 [5])))))))))))))))))) (.neg (.all 15 (.neg (.conj (.rel .numeral1 16 [15]) (.neg (.all 19 (.neg (.conj (.mem 19 0) (.neg (.all 20 (.neg (.conj (.mem 20 19) (.neg (.all 21 (.neg (.conj (.mem 21 20) (.conj (.rel .pair 22 [19, 15, 21]) (.rel .numeral0 24 [21]))))))))))))))))))) (.neg (.all 25 (.neg (.conj (.rel .numeral2 26 [25]) (.neg (.all 31 (.neg (.conj (.mem 31 0) (.neg (.all 32 (.neg (.conj (.mem 32 31) (.neg (.all 33 (.neg (.conj (.mem 33 32) (.conj (.rel .pair 34 [31, 25, 33]) (.rel .numeral0 36 [33]))))))))))))))))))) (.neg (.all 37 (.neg (.conj (.rel .numeral3 38 [37]) (.neg (.all 45 (.neg (.conj (.mem 45 0) (.neg (.all 46 (.neg (.conj (.mem 46 45) (.neg (.all 47 (.neg (.conj (.mem 47 46) (.conj (.rel .pair 48 [45, 37, 47]) (.rel .numeral0 50 [47])))))))))))))))))))
def tbl_punct3 : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral0 => some (1, full_numeral0)
    | .numeral1 => some (1, full_numeral1)
    | .numeral2 => some (1, full_numeral2)
    | .numeral3 => some (1, full_numeral3)
    | .pair => some (3, full_pair)
    | _ => none
def full_punct3 : F := expand tbl_punct3 r_punct3

def r_punct4 : F := (.conj (.conj (.conj (.neg (.all 1 (.neg (.conj (.rel .numeral0 2 [1]) (.neg (.all 3 (.neg (.conj (.mem 3 0) (.neg (.all 4 (.neg (.conj (.mem 4 3) (.neg (.all 5 (.neg (.conj (.mem 5 4) (.conj (.rel .pair 6 [3, 1, 5]) (.rel .numeral4 8 [5])))))))))))))))))) (.neg (.all 17 (.neg (.conj (.rel .numeral1 18 [17]) (.neg (.all 21 (.neg (.conj (.mem 21 0) (.neg (.all 22 (.neg (.conj (.mem 22 21) (.neg (.all 23 (.neg (.conj (.mem 23 22) (.conj (.rel .pair 24 [21, 17, 23]) (.rel .numeral0 26 [23]))))))))))))))))))) (.neg (.all 27 (.neg (.conj (.rel .numeral2 28 [27]) (.neg (.all 33 (.neg (.conj (.mem 33 0) (.neg (.all 34 (.neg (.conj (.mem 34 33) (.neg (.all 35 (.neg (.conj (.mem 35 34) (.conj (.rel .pair 36 [33, 27, 35]) (.rel .numeral0 38 [35]))))))))))))))))))) (.neg (.all 39 (.neg (.conj (.rel .numeral3 40 [39]) (.neg (.all 47 (.neg (.conj (.mem 47 0) (.neg (.all 48 (.neg (.conj (.mem 48 47) (.neg (.all 49 (.neg (.conj (.mem 49 48) (.conj (.rel .pair 50 [47, 39, 49]) (.rel .numeral0 52 [49])))))))))))))))))))
def tbl_punct4 : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral0 => some (1, full_numeral0)
    | .numeral1 => some (1, full_numeral1)
    | .numeral2 => some (1, full_numeral2)
    | .numeral3 => some (1, full_numeral3)
    | .numeral4 => some (1, full_numeral4)
    | .pair => some (3, full_pair)
    | _ => none
def full_punct4 : F := expand tbl_punct4 r_punct4

def r_punct5 : F := (.conj (.conj (.conj (.neg (.all 1 (.neg (.conj (.rel .numeral0 2 [1]) (.neg (.all 3 (.neg (.conj (.mem 3 0) (.neg (.all 4 (.neg (.conj (.mem 4 3) (.neg (.all 5 (.neg (.conj (.mem 5 4) (.conj (.rel .pair 6 [3, 1, 5]) (.rel .numeral5 8 [5])))))))))))))))))) (.neg (.all 19 (.neg (.conj (.rel .numeral1 20 [19]) (.neg (.all 23 (.neg (.conj (.mem 23 0) (.neg (.all 24 (.neg (.conj (.mem 24 23) (.neg (.all 25 (.neg (.conj (.mem 25 24) (.conj (.rel .pair 26 [23, 19, 25]) (.rel .numeral0 28 [25]))))))))))))))))))) (.neg (.all 29 (.neg (.conj (.rel .numeral2 30 [29]) (.neg (.all 35 (.neg (.conj (.mem 35 0) (.neg (.all 36 (.neg (.conj (.mem 36 35) (.neg (.all 37 (.neg (.conj (.mem 37 36) (.conj (.rel .pair 38 [35, 29, 37]) (.rel .numeral0 40 [37]))))))))))))))))))) (.neg (.all 41 (.neg (.conj (.rel .numeral3 42 [41]) (.neg (.all 49 (.neg (.conj (.mem 49 0) (.neg (.all 50 (.neg (.conj (.mem 50 49) (.neg (.all 51 (.neg (.conj (.mem 51 50) (.conj (.rel .pair 52 [49, 41, 51]) (.rel .numeral0 54 [51])))))))))))))))))))
def tbl_punct5 : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral0 => some (1, full_numeral0)
    | .numeral1 => some (1, full_numeral1)
    | .numeral2 => some (1, full_numeral2)
    | .numeral3 => some (1, full_numeral3)
    | .numeral5 => some (1, full_numeral5)
    | .pair => some (3, full_pair)
    | _ => none
def full_punct5 : F := expand tbl_punct5 r_punct5

def r_symvar : F := (.conj (.conj (.neg (.all 1 (.neg (.conj (.rel .numeral0 2 [1]) (.neg (.all 3 (.neg (.conj (.mem 3 0) (.neg (.all 4 (.neg (.conj (.mem 4 3) (.neg (.all 5 (.neg (.conj (.mem 5 4) (.conj (.rel .pair 6 [3, 1, 5]) (.rel .numeral7 8 [5])))))))))))))))))) (.neg (.all 23 (.neg (.conj (.rel .numeral1 24 [23]) (.neg (.all 27 (.neg (.conj (.mem 27 0) (.neg (.all 28 (.neg (.conj (.mem 28 27) (.neg (.all 29 (.neg (.conj (.mem 29 28) (.conj (.rel .pair 30 [27, 23, 29]) (.rel .numeral1 32 [29]))))))))))))))))))) (.neg (.all 35 (.neg (.conj (.rel .numeral3 36 [35]) (.neg (.all 43 (.neg (.conj (.mem 43 0) (.neg (.all 44 (.neg (.conj (.mem 44 43) (.neg (.all 45 (.neg (.conj (.mem 45 44) (.conj (.rel .pair 46 [43, 35, 45]) (.rel .numeral0 48 [45])))))))))))))))))))
def tbl_symvar : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral0 => some (1, full_numeral0)
    | .numeral1 => some (1, full_numeral1)
    | .numeral3 => some (1, full_numeral3)
    | .numeral7 => some (1, full_numeral7)
    | .pair => some (3, full_pair)
    | _ => none
def full_symvar : F := expand tbl_symvar r_symvar

def r_symconst : F := (.conj (.conj (.neg (.all 1 (.neg (.conj (.rel .numeral0 2 [1]) (.neg (.all 3 (.neg (.conj (.mem 3 0) (.neg (.all 4 (.neg (.conj (.mem 4 3) (.neg (.all 5 (.neg (.conj (.mem 5 4) (.conj (.rel .pair 6 [3, 1, 5]) (.rel .numeral6 8 [5])))))))))))))))))) (.neg (.all 21 (.neg (.conj (.rel .numeral1 22 [21]) (.neg (.all 25 (.neg (.conj (.mem 25 0) (.neg (.all 26 (.neg (.conj (.mem 26 25) (.neg (.all 27 (.neg (.conj (.mem 27 26) (.conj (.rel .pair 28 [25, 21, 27]) (.rel .numeral0 30 [27]))))))))))))))))))) (.neg (.all 31 (.neg (.conj (.rel .numeral3 32 [31]) (.neg (.all 39 (.neg (.conj (.mem 39 0) (.neg (.all 40 (.neg (.conj (.mem 40 39) (.neg (.all 41 (.neg (.conj (.mem 41 40) (.conj (.rel .pair 42 [39, 31, 41]) (.rel .numeral0 44 [41])))))))))))))))))))
def tbl_symconst : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral0 => some (1, full_numeral0)
    | .numeral1 => some (1, full_numeral1)
    | .numeral3 => some (1, full_numeral3)
    | .numeral6 => some (1, full_numeral6)
    | .pair => some (3, full_pair)
    | _ => none
def full_symconst : F := expand tbl_symconst r_symconst

def r_symfunc : F := (.neg (.conj (.neg (.neg (.conj (.neg (.conj (.conj (.conj (.neg (.all 1 (.neg (.conj (.rel .numeral0 2 [1]) (.neg (.all 3 (.neg (.conj (.mem 3 0) (.neg (.all 4 (.neg (.conj (.mem 4 3) (.neg (.all 5 (.neg (.conj (.mem 5 4) (.conj (.rel .pair 6 [3, 1, 5]) (.rel .numeral8 8 [5])))))))))))))))))) (.neg (.all 25 (.neg (.conj (.rel .numeral1 26 [25]) (.neg (.all 29 (.neg (.conj (.mem 29 0) (.neg (.all 30 (.neg (.conj (.mem 30 29) (.neg (.all 31 (.neg (.conj (.mem 31 30) (.conj (.rel .pair 32 [29, 25, 31]) (.rel .numeral2 34 [31]))))))))))))))))))) (.neg (.all 39 (.neg (.conj (.rel .numeral2 40 [39]) (.neg (.all 45 (.neg (.conj (.mem 45 0) (.neg (.all 46 (.neg (.conj (.mem 46 45) (.neg (.all 47 (.neg (.conj (.mem 47 46) (.conj (.rel .pair 48 [45, 39, 47]) (.rel .numeral0 50 [47]))))))))))))))))))) (.neg (.all 51 (.neg (.conj (.rel .numeral3 52 [51]) (.neg (.all 59 (.neg (.conj (.mem 59 0) (.neg (.all 60 (.neg (.conj (.mem 60 59) (.neg (.all 61 (.neg (.conj (.mem 61 60) (.conj (.rel .pair 62 [59, 51, 61]) (.rel .numeral1 64 [61])))))))))))))))))))) (.neg (.conj (.conj (.conj (.neg (.all 67 (.neg (.conj (.rel .numeral0 68 [67]) (.neg (.all 69 (.neg (.conj (.mem 69 0) (.neg (.all 70 (.neg (.conj (.mem 70 69) (.neg (.all 71 (.neg (.conj (.mem 71 70) (.conj (.rel .pair 72 [69, 67, 71]) (.rel .numeral8 74 [71])))))))))))))))))) (.neg (.all 91 (.neg (.conj (.rel .numeral1 92 [91]) (.neg (.all 95 (.neg (.conj (.mem 95 0) (.neg (.all 96 (.neg (.conj (.mem 96 95) (.neg (.all 97 (.neg (.conj (.mem 97 96) (.conj (.rel .pair 98 [95, 91, 97]) (.rel .numeral3 100 [97]))))))))))))))))))) (.neg (.all 107 (.neg (.conj (.rel .numeral2 108 [107]) (.neg (.all 113 (.neg (.conj (.mem 113 0) (.neg (.all 114 (.neg (.conj (.mem 114 113) (.neg (.all 115 (.neg (.conj (.mem 115 114) (.conj (.rel .pair 116 [113, 107, 115]) (.rel .numeral0 118 [115]))))))))))))))))))) (.neg (.all 119 (.neg (.conj (.rel .numeral3 120 [119]) (.neg (.all 127 (.neg (.conj (.mem 127 0) (.neg (.all 128 (.neg (.conj (.mem 128 127) (.neg (.all 129 (.neg (.conj (.mem 129 128) (.conj (.rel .pair 130 [127, 119, 129]) (.rel .numeral1 132 [129]))))))))))))))))))))))) (.neg (.conj (.neg (.all 135 (.neg (.conj (.rel .numeral0 136 [135]) (.neg (.all 137 (.neg (.conj (.mem 137 0) (.neg (.all 138 (.neg (.conj (.mem 138 137) (.neg (.all 139 (.neg (.conj (.mem 139 138) (.conj (.rel .pair 140 [137, 135, 139]) (.rel .numeral8 142 [139])))))))))))))))))) (.neg (.all 159 (.neg (.conj (.rel .numeral1 160 [159]) (.neg (.all 163 (.neg (.conj (.mem 163 0) (.neg (.all 164 (.neg (.conj (.mem 164 163) (.neg (.all 165 (.neg (.conj (.mem 165 164) (.conj (.rel .pair 166 [163, 159, 165]) (.rel .numeral4 168 [165]))))))))))))))))))))))
def tbl_symfunc : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral0 => some (1, full_numeral0)
    | .numeral1 => some (1, full_numeral1)
    | .numeral2 => some (1, full_numeral2)
    | .numeral3 => some (1, full_numeral3)
    | .numeral4 => some (1, full_numeral4)
    | .numeral8 => some (1, full_numeral8)
    | .pair => some (3, full_pair)
    | _ => none
def full_symfunc : F := expand tbl_symfunc r_symfunc

def r_symrel : F := (.conj (.neg (.all 1 (.neg (.conj (.rel .numeral0 2 [1]) (.neg (.all 3 (.neg (.conj (.mem 3 0) (.neg (.all 4 (.neg (.conj (.mem 4 3) (.neg (.all 5 (.neg (.conj (.mem 5 4) (.conj (.rel .pair 6 [3, 1, 5]) (.rel .numeral9 8 [5])))))))))))))))))) (.neg (.all 27 (.neg (.conj (.rel .numeral1 28 [27]) (.neg (.all 31 (.neg (.conj (.mem 31 0) (.neg (.all 32 (.neg (.conj (.mem 32 31) (.neg (.all 33 (.neg (.conj (.mem 33 32) (.conj (.rel .pair 34 [31, 27, 33]) (.rel .numeral6 36 [33])))))))))))))))))))
def tbl_symrel : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral0 => some (1, full_numeral0)
    | .numeral1 => some (1, full_numeral1)
    | .numeral6 => some (1, full_numeral6)
    | .numeral9 => some (1, full_numeral9)
    | .pair => some (3, full_pair)
    | _ => none
def full_symrel : F := expand tbl_symrel r_symrel

def r_symelem : F := (.conj (.conj (.conj (.neg (.all 1 (.neg (.conj (.rel .numeral0 2 [1]) (.neg (.all 3 (.neg (.conj (.mem 3 0) (.neg (.all 4 (.neg (.conj (.mem 4 3) (.neg (.all 5 (.neg (.conj (.mem 5 4) (.conj (.rel .pair 6 [3, 1, 5]) (.rel .numeral9 8 [5])))))))))))))))))) (.neg (.all 27 (.neg (.conj (.rel .numeral1 28 [27]) (.neg (.all 31 (.neg (.conj (.mem 31 0) (.neg (.all 32 (.neg (.conj (.mem 32 31) (.neg (.all 33 (.neg (.conj (.mem 33 32) (.conj (.rel .pair 34 [31, 27, 33]) (.rel .numeral5 36 [33]))))))))))))))))))) (.neg (.all 47 (.neg (.conj (.rel .numeral2 48 [47]) (.neg (.all 53 (.neg (.conj (.mem 53 0) (.neg (.all 54 (.neg (.conj (.mem 54 53) (.neg (.all 55 (.neg (.conj (.mem 55 54) (.conj (.rel .pair 56 [53, 47, 55]) (.rel .numeral0 58 [55]))))))))))))))))))) (.neg (.all 59 (.neg (.conj (.rel .numeral3 60 [59]) (.neg (.all 67 (.neg (.conj (.mem 67 0) (.neg (.all 68 (.neg (.conj (.mem 68 67) (.neg (.all 69 (.neg (.conj (.mem 69 68) (.conj (.rel .pair 70 [67, 59, 69]) (.rel .numeral2 72 [69])))))))))))))))))))
def tbl_symelem : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral0 => some (1, full_numeral0)
    | .numeral1 => some (1, full_numeral1)
    | .numeral2 => some (1, full_numeral2)
    | .numeral3 => some (1, full_numeral3)
    | .numeral5 => some (1, full_numeral5)
    | .numeral9 => some (1, full_numeral9)
    | .pair => some (3, full_pair)
    | _ => none
def full_symelem : F := expand tbl_symelem r_symelem

def r_symtheta : F := (.conj (.conj (.conj (.neg (.all 1 (.neg (.conj (.rel .numeral0 2 [1]) (.neg (.all 3 (.neg (.conj (.mem 3 0) (.neg (.all 4 (.neg (.conj (.mem 4 3) (.neg (.all 5 (.neg (.conj (.mem 5 4) (.conj (.rel .pair 6 [3, 1, 5]) (.rel .numeral8 8 [5])))))))))))))))))) (.neg (.all 25 (.neg (.conj (.rel .numeral1 26 [25]) (.neg (.all 29 (.neg (.conj (.mem 29 0) (.neg (.all 30 (.neg (.conj (.mem 30 29) (.neg (.all 31 (.neg (.conj (.mem 31 30) (.conj (.rel .pair 32 [29, 25, 31]) (.rel .numeral3 34 [31]))))))))))))))))))) (.neg (.all 41 (.neg (.conj (.rel .numeral2 42 [41]) (.neg (.all 47 (.neg (.conj (.mem 47 0) (.neg (.all 48 (.neg (.conj (.mem 48 47) (.neg (.all 49 (.neg (.conj (.mem 49 48) (.conj (.rel .pair 50 [47, 41, 49]) (.rel .numeral0 52 [49]))))))))))))))))))) (.neg (.all 53 (.neg (.conj (.rel .numeral3 54 [53]) (.neg (.all 61 (.neg (.conj (.mem 61 0) (.neg (.all 62 (.neg (.conj (.mem 62 61) (.neg (.all 63 (.neg (.conj (.mem 63 62) (.conj (.rel .pair 64 [61, 53, 63]) (.rel .numeral1 66 [63])))))))))))))))))))
def tbl_symtheta : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral0 => some (1, full_numeral0)
    | .numeral1 => some (1, full_numeral1)
    | .numeral2 => some (1, full_numeral2)
    | .numeral3 => some (1, full_numeral3)
    | .numeral8 => some (1, full_numeral8)
    | .pair => some (3, full_pair)
    | _ => none
def full_symtheta : F := expand tbl_symtheta r_symtheta

def r_plus2 : F := (.neg (.all 2 (.neg (.conj (.mem 2 1) (.conj (.rel .succ 3 [0, 2]) (.rel .succ 4 [2, 1]))))))
def tbl_plus2 : Nm → Option (Nat × F) := fun nm => match nm with
    | .succ => some (2, full_succ)
    | _ => none
def full_plus2 : F := expand tbl_plus2 r_plus2

def r_certificate : F := (.all 4 (.neg (.conj (.mem 4 1) (.neg (.neg (.all 5 (.neg (.conj (.mem 5 4) (.neg (.all 6 (.neg (.conj (.mem 6 5) (.neg (.all 7 (.neg (.conj (.mem 7 5) (.neg (.all 8 (.neg (.conj (.mem 8 6) (.neg (.all 9 (.neg (.conj (.mem 9 8) (.neg (.all 10 (.neg (.conj (.mem 10 8) (.conj (.rel .triple 11 [4, 9, 10, 7]) (.neg (.conj (.neg (.neg (.conj (.neg (.conj (.eq 7 2) (.neg (.conj (.neg (.conj (.rel .succ 17 [9, 10]) (.neg (.all 18 (.neg (.conj (.mem 18 0) (.neg (.all 19 (.neg (.conj (.mem 19 18) (.neg (.all 20 (.neg (.conj (.mem 20 19) (.conj (.rel .pair 21 [18, 9, 20]) (.neg (.conj (.neg (.rel .symvar 23 [20])) (.neg (.rel .symconst 71 [20]))))))))))))))))))) (.neg (.neg (.all 115 (.neg (.conj (.mem 115 0) (.neg (.all 116 (.neg (.conj (.mem 116 115) (.neg (.all 117 (.neg (.conj (.mem 117 116) (.conj (.rel .pair 118 [115, 9, 117]) (.neg (.all 120 (.neg (.conj (.rel .numeral3 121 [120]) (.neg (.all 128 (.neg (.conj (.mem 128 117) (.neg (.all 129 (.neg (.conj (.mem 129 128) (.neg (.all 130 (.neg (.conj (.mem 130 129) (.conj (.rel .pair 131 [128, 120, 130]) (.neg (.all 133 (.neg (.conj (.rel .succ 134 [9, 133]) (.neg (.all 135 (.neg (.conj (.rel .succ 136 [133, 135]) (.neg (.all 137 (.neg (.conj (.mem 137 10) (.conj (.rel .succ 138 [137, 10]) (.conj (.conj (.conj (.rel .symfunc 139 [117]) (.neg (.all 315 (.neg (.conj (.mem 315 0) (.neg (.all 316 (.neg (.conj (.mem 316 315) (.neg (.all 317 (.neg (.conj (.mem 317 316) (.conj (.rel .pair 318 [315, 133, 317]) (.rel .punct4 320 [317]))))))))))))))) (.neg (.all 372 (.neg (.conj (.mem 372 0) (.neg (.all 373 (.neg (.conj (.mem 373 372) (.neg (.all 374 (.neg (.conj (.mem 374 373) (.conj (.rel .pair 375 [372, 137, 374]) (.rel .punct5 377 [374]))))))))))))))) (.neg (.all 431 (.neg (.conj (.mem 431 1) (.neg (.all 432 (.neg (.conj (.mem 432 431) (.neg (.all 433 (.neg (.conj (.mem 433 432) (.neg (.all 434 (.neg (.conj (.mem 434 432) (.conj (.rel .triple 435 [431, 135, 137, 434]) (.rel .plus2 441 [130, 434]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.neg (.conj (.eq 7 3) (.neg (.conj (.neg (.neg (.conj (.neg (.neg (.conj (.neg (.neg (.conj (.neg (.neg (.conj (.neg (.conj (.rel .succ 445 [9, 10]) (.neg (.all 446 (.neg (.conj (.mem 446 0) (.neg (.all 447 (.neg (.conj (.mem 447 446) (.neg (.all 448 (.neg (.conj (.mem 448 447) (.conj (.rel .pair 449 [446, 9, 448]) (.rel .punct0 451 [448])))))))))))))))) (.neg (.conj (.neg (.all 495 (.neg (.conj (.mem 495 0) (.neg (.all 496 (.neg (.conj (.mem 496 495) (.neg (.all 497 (.neg (.conj (.mem 497 496) (.conj (.rel .pair 498 [495, 9, 497]) (.rel .punct4 500 [497])))))))))))))) (.neg (.all 552 (.neg (.conj (.rel .succ 553 [9, 552]) (.neg (.all 554 (.neg (.conj (.mem 554 10) (.conj (.rel .succ 555 [554, 10]) (.conj (.neg (.all 556 (.neg (.conj (.mem 556 0) (.neg (.all 557 (.neg (.conj (.mem 557 556) (.neg (.all 558 (.neg (.conj (.mem 558 557) (.conj (.rel .pair 559 [556, 554, 558]) (.rel .punct5 561 [558])))))))))))))) (.neg (.all 444 (.neg (.conj (.mem 444 10) (.conj (.conj (.neg (.all 615 (.neg (.conj (.mem 615 1) (.neg (.all 616 (.neg (.conj (.mem 616 615) (.neg (.all 617 (.neg (.conj (.mem 617 616) (.neg (.all 618 (.neg (.conj (.mem 618 616) (.conj (.rel .triple 619 [615, 552, 444, 618]) (.eq 618 2)))))))))))))))))) (.neg (.all 625 (.neg (.conj (.mem 625 0) (.neg (.all 626 (.neg (.conj (.mem 626 625) (.neg (.all 627 (.neg (.conj (.mem 627 626) (.conj (.rel .pair 628 [625, 444, 627]) (.rel .symelem 630 [627]))))))))))))))) (.neg (.all 706 (.neg (.conj (.rel .succ 707 [444, 706]) (.neg (.all 708 (.neg (.conj (.mem 708 1) (.neg (.all 709 (.neg (.conj (.mem 709 708) (.neg (.all 710 (.neg (.conj (.mem 710 709) (.neg (.all 711 (.neg (.conj (.mem 711 709) (.conj (.rel .triple 712 [708, 706, 554, 711]) (.eq 711 2)))))))))))))))))))))))))))))))))))))))))) (.neg (.neg (.all 718 (.neg (.conj (.mem 718 0) (.neg (.all 719 (.neg (.conj (.mem 719 718) (.neg (.all 720 (.neg (.conj (.mem 720 719) (.conj (.rel .pair 721 [718, 9, 720]) (.neg (.all 723 (.neg (.conj (.rel .numeral3 724 [723]) (.neg (.all 731 (.neg (.conj (.mem 731 720) (.neg (.all 732 (.neg (.conj (.mem 732 731) (.neg (.all 733 (.neg (.conj (.mem 733 732) (.conj (.rel .pair 734 [731, 723, 733]) (.neg (.all 736 (.neg (.conj (.rel .succ 737 [9, 736]) (.neg (.all 738 (.neg (.conj (.rel .succ 739 [736, 738]) (.neg (.all 740 (.neg (.conj (.mem 740 10) (.conj (.rel .succ 741 [740, 10]) (.conj (.conj (.conj (.rel .symrel 742 [720]) (.neg (.all 790 (.neg (.conj (.mem 790 0) (.neg (.all 791 (.neg (.conj (.mem 791 790) (.neg (.all 792 (.neg (.conj (.mem 792 791) (.conj (.rel .pair 793 [790, 736, 792]) (.rel .punct4 795 [792]))))))))))))))) (.neg (.all 847 (.neg (.conj (.mem 847 0) (.neg (.all 848 (.neg (.conj (.mem 848 847) (.neg (.all 849 (.neg (.conj (.mem 849 848) (.conj (.rel .pair 850 [847, 740, 849]) (.rel .punct5 852 [849]))))))))))))))) (.neg (.all 906 (.neg (.conj (.mem 906 1) (.neg (.all 907 (.neg (.conj (.mem 907 906) (.neg (.all 908 (.neg (.conj (.mem 908 907) (.neg (.all 909 (.neg (.conj (.mem 909 907) (.conj (.rel .triple 910 [906, 738, 740, 909]) (.rel .plus2 916 [733, 909])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.neg (.conj (.neg (.all 919 (.neg (.conj (.mem 919 0) (.neg (.all 920 (.neg (.conj (.mem 920 919) (.neg (.all 921 (.neg (.conj (.mem 921 920) (.conj (.rel .pair 922 [919, 9, 921]) (.rel .punct4 924 [921])))))))))))))) (.neg (.all 976 (.neg (.conj (.rel .succ 977 [9, 976]) (.neg (.all 978 (.neg (.conj (.mem 978 10) (.conj (.rel .succ 979 [978, 10]) (.conj (.neg (.all 980 (.neg (.conj (.mem 980 0) (.neg (.all 981 (.neg (.conj (.mem 981 980) (.neg (.all 982 (.neg (.conj (.mem 982 981) (.conj (.rel .pair 983 [980, 978, 982]) (.rel .punct5 985 [982])))))))))))))) (.neg (.all 444 (.neg (.conj (.mem 444 10) (.conj (.conj (.neg (.all 1039 (.neg (.conj (.mem 1039 1) (.neg (.all 1040 (.neg (.conj (.mem 1040 1039) (.neg (.all 1041 (.neg (.conj (.mem 1041 1040) (.neg (.all 1042 (.neg (.conj (.mem 1042 1040) (.conj (.rel .triple 1043 [1039, 976, 444, 1042]) (.eq 1042 3)))))))))))))))))) (.neg (.all 1049 (.neg (.conj (.mem 1049 0) (.neg (.all 1050 (.neg (.conj (.mem 1050 1049) (.neg (.all 1051 (.neg (.conj (.mem 1051 1050) (.conj (.rel .pair 1052 [1049, 444, 1051]) (.rel .punct1 1054 [1051]))))))))))))))) (.neg (.all 1100 (.neg (.conj (.rel .succ 1101 [444, 1100]) (.neg (.all 1102 (.neg (.conj (.mem 1102 1) (.neg (.all 1103 (.neg (.conj (.mem 1103 1102) (.neg (.all 1104 (.neg (.conj (.mem 1104 1103) (.neg (.all 1105 (.neg (.conj (.mem 1105 1103) (.conj (.rel .triple 1106 [1102, 1100, 978, 1105]) (.eq 1105 3)))))))))))))))))))))))))))))))))))))))))) (.neg (.conj (.neg (.all 1112 (.neg (.conj (.mem 1112 0) (.neg (.all 1113 (.neg (.conj (.mem 1113 1112) (.neg (.all 1114 (.neg (.conj (.mem 1114 1113) (.conj (.rel .pair 1115 [1112, 9, 1114]) (.rel .punct2 1117 [1114])))))))))))))) (.neg (.all 1165 (.neg (.conj (.rel .succ 1166 [9, 1165]) (.neg (.all 1167 (.neg (.conj (.mem 1167 1) (.neg (.all 1168 (.neg (.conj (.mem 1168 1167) (.neg (.all 1169 (.neg (.conj (.mem 1169 1168) (.neg (.all 1170 (.neg (.conj (.mem 1170 1168) (.conj (.rel .triple 1171 [1167, 1165, 10, 1170]) (.eq 1170 3))))))))))))))))))))))))))) (.neg (.conj (.neg (.all 1177 (.neg (.conj (.mem 1177 0) (.neg (.all 1178 (.neg (.conj (.mem 1178 1177) (.neg (.all 1179 (.neg (.conj (.mem 1179 1178) (.conj (.rel .pair 1180 [1177, 9, 1179]) (.rel .punct3 1182 [1179])))))))))))))) (.neg (.all 1232 (.neg (.conj (.rel .succ 1233 [9, 1232]) (.conj (.neg (.all 1234 (.neg (.conj (.mem 1234 0) (.neg (.all 1235 (.neg (.conj (.mem 1235 1234) (.neg (.all 1236 (.neg (.conj (.mem 1236 1235) (.conj (.rel .pair 1237 [1234, 1232, 1236]) (.rel .symvar 1239 [1236])))))))))))))) (.neg (.all 1287 (.neg (.conj (.rel .succ 1288 [1232, 1287]) (.conj (.neg (.all 1289 (.neg (.conj (.mem 1289 0) (.neg (.all 1290 (.neg (.conj (.mem 1290 1289) (.neg (.all 1291 (.neg (.conj (.mem 1291 1290) (.conj (.rel .pair 1292 [1289, 1287, 1291]) (.rel .punct4 1294 [1291])))))))))))))) (.neg (.all 1346 (.neg (.conj (.rel .succ 1347 [1287, 1346]) (.neg (.all 1348 (.neg (.conj (.mem 1348 10) (.conj (.rel .succ 1349 [1348, 10]) (.conj (.neg (.all 1350 (.neg (.conj (.mem 1350 0) (.neg (.all 1351 (.neg (.conj (.mem 1351 1350) (.neg (.all 1352 (.neg (.conj (.mem 1352 1351) (.conj (.rel .pair 1353 [1350, 1348, 1352]) (.rel .punct5 1355 [1352])))))))))))))) (.neg (.all 1409 (.neg (.conj (.mem 1409 1) (.neg (.all 1410 (.neg (.conj (.mem 1410 1409) (.neg (.all 1411 (.neg (.conj (.mem 1411 1410) (.neg (.all 1412 (.neg (.conj (.mem 1412 1410) (.conj (.rel .triple 1413 [1409, 1346, 1348, 1412]) (.eq 1412 3))))))))))))))))))))))))))))))))))))))))))))))) (.neg (.neg (.all 1470 (.neg (.conj (.mem 1470 7) (.neg (.all 1419 (.neg (.conj (.mem 1419 1470) (.conj (.rel .plus2 1471 [1419, 7]) (.neg (.conj (.neg (.conj (.rel .empty 1422 [1419]) (.eq 9 10))) (.neg (.neg (.all 1420 (.neg (.conj (.mem 1420 1419) (.conj (.rel .succ 1423 [1420, 1419]) (.neg (.conj (.neg (.neg (.all 1421 (.neg (.conj (.mem 1421 10) (.conj (.neg (.all 1424 (.neg (.conj (.mem 1424 1) (.neg (.all 1425 (.neg (.conj (.mem 1425 1424) (.neg (.all 1426 (.neg (.conj (.mem 1426 1425) (.neg (.all 1427 (.neg (.conj (.mem 1427 1425) (.conj (.rel .triple 1428 [1424, 9, 1421, 1427]) (.eq 1427 2)))))))))))))))))) (.neg (.all 1434 (.neg (.conj (.mem 1434 1) (.neg (.all 1435 (.neg (.conj (.mem 1435 1434) (.neg (.all 1436 (.neg (.conj (.mem 1436 1435) (.neg (.all 1437 (.neg (.conj (.mem 1437 1435) (.conj (.rel .triple 1438 [1434, 1421, 10, 1437]) (.rel .plus2 1444 [1420, 1437])))))))))))))))))))))))) (.neg (.conj (.neg (.all 1447 (.neg (.conj (.mem 1447 1) (.neg (.all 1448 (.neg (.conj (.mem 1448 1447) (.neg (.all 1449 (.neg (.conj (.mem 1449 1448) (.neg (.all 1450 (.neg (.conj (.mem 1450 1448) (.conj (.rel .triple 1451 [1447, 9, 10, 1450]) (.eq 1450 2)))))))))))))))))) (.neg (.all 1457 (.neg (.conj (.mem 1457 1) (.neg (.all 1458 (.neg (.conj (.mem 1458 1457) (.neg (.all 1459 (.neg (.conj (.mem 1459 1458) (.neg (.all 1460 (.neg (.conj (.mem 1460 1458) (.conj (.rel .triple 1461 [1457, 10, 10, 1460]) (.rel .plus2 1467 [1420, 1460])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def tbl_certificate : Nm → Option (Nat × F) := fun nm => match nm with
    | .empty => some (1, full_empty)
    | .numeral3 => some (1, full_numeral3)
    | .pair => some (3, full_pair)
    | .plus2 => some (2, full_plus2)
    | .punct0 => some (1, full_punct0)
    | .punct1 => some (1, full_punct1)
    | .punct2 => some (1, full_punct2)
    | .punct3 => some (1, full_punct3)
    | .punct4 => some (1, full_punct4)
    | .punct5 => some (1, full_punct5)
    | .succ => some (2, full_succ)
    | .symconst => some (1, full_symconst)
    | .symelem => some (1, full_symelem)
    | .symfunc => some (1, full_symfunc)
    | .symrel => some (1, full_symrel)
    | .symvar => some (1, full_symvar)
    | .triple => some (4, full_triple)
    | _ => none
def full_certificate : F := expand tbl_certificate r_certificate

def r_formula : F := (.neg (.all 1 (.neg (.conj (.rel .empty 1567 [1]) (.neg (.all 2 (.neg (.conj (.rel .succ 1568 [1, 2]) (.neg (.all 3 (.neg (.conj (.conj (.conj (.conj (.rel .nat 79 [3]) (.all 6 (.neg (.conj (.mem 6 0) (.neg (.neg (.all 7 (.neg (.conj (.mem 7 6) (.neg (.all 8 (.neg (.conj (.mem 8 7) (.neg (.all 9 (.neg (.conj (.mem 9 7) (.conj (.rel .pair 10 [6, 8, 9]) (.conj (.mem 8 3) (.rel .tuple4 12 [9])))))))))))))))))))) (.all 5 (.neg (.conj (.mem 5 3) (.neg (.neg (.all 62 (.neg (.conj (.mem 62 0) (.neg (.all 63 (.neg (.conj (.mem 63 62) (.neg (.all 64 (.neg (.conj (.mem 64 63) (.conj (.rel .pair 65 [62, 5, 64]) (.eq 64 64))))))))))))))))))) (.all 67 (.neg (.conj (.mem 67 0) (.neg (.all 68 (.neg (.conj (.mem 68 67) (.neg (.all 69 (.neg (.conj (.mem 69 68) (.neg (.all 70 (.neg (.conj (.mem 70 68) (.neg (.neg (.conj (.rel .pair 71 [67, 69, 70]) (.neg (.all 73 (.neg (.conj (.mem 73 0) (.neg (.all 74 (.neg (.conj (.mem 74 73) (.neg (.all 75 (.neg (.conj (.mem 75 74) (.neg (.all 76 (.neg (.conj (.mem 76 74) (.neg (.neg (.conj (.rel .pair 77 [73, 75, 76]) (.neg (.neg (.conj (.eq 69 75) (.neg (.eq 70 76))))))))))))))))))))))))))))))))))))))))))) (.neg (.all 4 (.neg (.conj (.neg (.all 87 (.neg (.conj (.mem 87 4) (.neg (.all 88 (.neg (.conj (.mem 88 87) (.neg (.all 89 (.neg (.conj (.mem 89 88) (.neg (.all 90 (.neg (.conj (.mem 90 88) (.conj (.rel .triple 91 [87, 1, 3, 90]) (.eq 90 2)))))))))))))))))) (.rel .certificate 97 [0, 4, 1, 2])))))))))))))))))
def tbl_formula : Nm → Option (Nat × F) := fun nm => match nm with
    | .certificate => some (4, full_certificate)
    | .empty => some (1, full_empty)
    | .nat => some (1, full_nat)
    | .pair => some (3, full_pair)
    | .succ => some (2, full_succ)
    | .triple => some (4, full_triple)
    | .tuple4 => some (1, full_tuple4)
    | _ => none
def full_formula : F := expand tbl_formula r_formula

def r_formula_minus : F := (.neg (.all 1 (.neg (.conj (.rel .empty 1641 [1]) (.neg (.all 2 (.neg (.conj (.rel .succ 1642 [1, 2]) (.neg (.all 3 (.neg (.conj (.conj (.conj (.conj (.conj (.rel .nat 79 [3]) (.all 6 (.neg (.conj (.mem 6 0) (.neg (.neg (.all 7 (.neg (.conj (.mem 7 6) (.neg (.all 8 (.neg (.conj (.mem 8 7) (.neg (.all 9 (.neg (.conj (.mem 9 7) (.conj (.rel .pair 10 [6, 8, 9]) (.conj (.mem 8 3) (.rel .tuple4 12 [9])))))))))))))))))))) (.all 5 (.neg (.conj (.mem 5 3) (.neg (.neg (.all 62 (.neg (.conj (.mem 62 0) (.neg (.all 63 (.neg (.conj (.mem 63 62) (.neg (.all 64 (.neg (.conj (.mem 64 63) (.conj (.rel .pair 65 [62, 5, 64]) (.eq 64 64))))))))))))))))))) (.all 67 (.neg (.conj (.mem 67 0) (.neg (.all 68 (.neg (.conj (.mem 68 67) (.neg (.all 69 (.neg (.conj (.mem 69 68) (.neg (.all 70 (.neg (.conj (.mem 70 68) (.neg (.neg (.conj (.rel .pair 71 [67, 69, 70]) (.neg (.all 73 (.neg (.conj (.mem 73 0) (.neg (.all 74 (.neg (.conj (.mem 74 73) (.neg (.all 75 (.neg (.conj (.mem 75 74) (.neg (.all 76 (.neg (.conj (.mem 76 74) (.neg (.neg (.conj (.rel .pair 77 [73, 75, 76]) (.neg (.neg (.conj (.eq 69 75) (.neg (.eq 70 76))))))))))))))))))))))))))))))))))))))))))) (.neg (.all 4 (.neg (.conj (.neg (.all 87 (.neg (.conj (.mem 87 4) (.neg (.all 88 (.neg (.conj (.mem 88 87) (.neg (.all 89 (.neg (.conj (.mem 89 88) (.neg (.all 90 (.neg (.conj (.mem 90 88) (.conj (.rel .triple 91 [87, 1, 3, 90]) (.eq 90 2)))))))))))))))))) (.rel .certificate 97 [0, 4, 1, 2])))))) (.neg (.neg (.all 1567 (.neg (.conj (.mem 1567 3) (.neg (.all 1568 (.neg (.conj (.mem 1568 0) (.neg (.all 1569 (.neg (.conj (.mem 1569 1568) (.neg (.all 1570 (.neg (.conj (.mem 1570 1569) (.conj (.rel .pair 1571 [1568, 1567, 1570]) (.rel .symtheta 1573 [1570])))))))))))))))))))))))))))))))
def tbl_formula_minus : Nm → Option (Nat × F) := fun nm => match nm with
    | .certificate => some (4, full_certificate)
    | .empty => some (1, full_empty)
    | .nat => some (1, full_nat)
    | .pair => some (3, full_pair)
    | .succ => some (2, full_succ)
    | .symtheta => some (1, full_symtheta)
    | .triple => some (4, full_triple)
    | .tuple4 => some (1, full_tuple4)
    | _ => none
def full_formula_minus : F := expand tbl_formula_minus r_formula_minus

end Tr
