import TrCore
set_option maxRecDepth 200000
namespace Tr

/-! 生成プログラムが書き出した部品（層 A。lean_tr_export.py による。手で編集しない）。 -/

def r_empty : F := (.all 1 (.neg (.mem 1 0)))
def tbl_empty : Nm → Option (Nat × F) := fun nm => match nm with
    | _ => none
def full_empty : F := expand tbl_empty r_empty

def r_succ : F := (.all 2 (.conj (.neg (.conj (.mem 2 1) (.neg (.neg (.conj (.neg (.mem 2 0)) (.neg (.eq 2 0))))))) (.neg (.conj (.neg (.conj (.neg (.mem 2 0)) (.neg (.eq 2 0)))) (.neg (.mem 2 1))))))
def tbl_succ : Nm → Option (Nat × F) := fun nm => match nm with
    | _ => none
def full_succ : F := expand tbl_succ r_succ

def r_trans : F := (.all 1 (.neg (.conj (.mem 1 0) (.neg (.all 2 (.neg (.conj (.mem 2 1) (.neg (.mem 2 0)))))))))
def tbl_trans : Nm → Option (Nat × F) := fun nm => match nm with
    | _ => none
def full_trans : F := expand tbl_trans r_trans

def r_pair : F := (.conj (.conj (.all 3 (.neg (.conj (.mem 3 0) (.neg (.neg (.conj (.neg (.conj (.mem 1 3) (.all 4 (.neg (.conj (.mem 4 3) (.neg (.eq 4 1))))))) (.neg (.conj (.conj (.mem 1 3) (.mem 2 3)) (.all 4 (.neg (.conj (.mem 4 3) (.neg (.neg (.conj (.neg (.eq 4 1)) (.neg (.eq 4 2)))))))))))))))) (.neg (.all 3 (.neg (.conj (.mem 3 0) (.conj (.mem 1 3) (.all 4 (.neg (.conj (.mem 4 3) (.neg (.eq 4 1))))))))))) (.neg (.all 3 (.neg (.conj (.mem 3 0) (.conj (.conj (.mem 1 3) (.mem 2 3)) (.all 4 (.neg (.conj (.mem 4 3) (.neg (.neg (.conj (.neg (.eq 4 1)) (.neg (.eq 4 2))))))))))))))
def tbl_pair : Nm → Option (Nat × F) := fun nm => match nm with
    | _ => none
def full_pair : F := expand tbl_pair r_pair

def r_is_one : F := (.neg (.all 1 (.neg (.conj (.mem 1 0) (.conj (.rel .empty 2 [1]) (.rel .succ 3 [1, 0]))))))
def tbl_is_one : Nm → Option (Nat × F) := fun nm => match nm with
    | .empty => some (1, full_empty)
    | .succ => some (2, full_succ)
    | _ => none
def full_is_one : F := expand tbl_is_one r_is_one

def r_numeral0 : F := (.all 1 (.neg (.mem 1 0)))
def tbl_numeral0 : Nm → Option (Nat × F) := fun nm => match nm with
    | _ => none
def full_numeral0 : F := expand tbl_numeral0 r_numeral0

def r_numeral1 : F := (.neg (.all 1 (.neg (.conj (.mem 1 0) (.conj (.rel .succ 2 [1, 0]) (.rel .numeral0 3 [1]))))))
def tbl_numeral1 : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral0 => some (1, full_numeral0)
    | .succ => some (2, full_succ)
    | _ => none
def full_numeral1 : F := expand tbl_numeral1 r_numeral1

def r_numeral2 : F := (.neg (.all 1 (.neg (.conj (.mem 1 0) (.conj (.rel .succ 2 [1, 0]) (.rel .numeral1 3 [1]))))))
def tbl_numeral2 : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral1 => some (1, full_numeral1)
    | .succ => some (2, full_succ)
    | _ => none
def full_numeral2 : F := expand tbl_numeral2 r_numeral2

def r_numeral3 : F := (.neg (.all 1 (.neg (.conj (.mem 1 0) (.conj (.rel .succ 2 [1, 0]) (.rel .numeral2 3 [1]))))))
def tbl_numeral3 : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral2 => some (1, full_numeral2)
    | .succ => some (2, full_succ)
    | _ => none
def full_numeral3 : F := expand tbl_numeral3 r_numeral3

def r_numeral4 : F := (.neg (.all 1 (.neg (.conj (.mem 1 0) (.conj (.rel .succ 2 [1, 0]) (.rel .numeral3 3 [1]))))))
def tbl_numeral4 : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral3 => some (1, full_numeral3)
    | .succ => some (2, full_succ)
    | _ => none
def full_numeral4 : F := expand tbl_numeral4 r_numeral4

def r_numeral5 : F := (.neg (.all 1 (.neg (.conj (.mem 1 0) (.conj (.rel .succ 2 [1, 0]) (.rel .numeral4 3 [1]))))))
def tbl_numeral5 : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral4 => some (1, full_numeral4)
    | .succ => some (2, full_succ)
    | _ => none
def full_numeral5 : F := expand tbl_numeral5 r_numeral5

def r_numeral6 : F := (.neg (.all 1 (.neg (.conj (.mem 1 0) (.conj (.rel .succ 2 [1, 0]) (.rel .numeral5 3 [1]))))))
def tbl_numeral6 : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral5 => some (1, full_numeral5)
    | .succ => some (2, full_succ)
    | _ => none
def full_numeral6 : F := expand tbl_numeral6 r_numeral6

def r_numeral7 : F := (.neg (.all 1 (.neg (.conj (.mem 1 0) (.conj (.rel .succ 2 [1, 0]) (.rel .numeral6 3 [1]))))))
def tbl_numeral7 : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral6 => some (1, full_numeral6)
    | .succ => some (2, full_succ)
    | _ => none
def full_numeral7 : F := expand tbl_numeral7 r_numeral7

def r_numeral8 : F := (.neg (.all 1 (.neg (.conj (.mem 1 0) (.conj (.rel .succ 2 [1, 0]) (.rel .numeral7 3 [1]))))))
def tbl_numeral8 : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral7 => some (1, full_numeral7)
    | .succ => some (2, full_succ)
    | _ => none
def full_numeral8 : F := expand tbl_numeral8 r_numeral8

def r_numeral9 : F := (.neg (.all 1 (.neg (.conj (.mem 1 0) (.conj (.rel .succ 2 [1, 0]) (.rel .numeral8 3 [1]))))))
def tbl_numeral9 : Nm → Option (Nat × F) := fun nm => match nm with
    | .numeral8 => some (1, full_numeral8)
    | .succ => some (2, full_succ)
    | _ => none
def full_numeral9 : F := expand tbl_numeral9 r_numeral9

def r_nat : F := (.conj (.conj (.rel .trans 6 [0]) (.all 1 (.neg (.conj (.mem 1 0) (.neg (.all 2 (.neg (.conj (.mem 2 1) (.neg (.all 3 (.neg (.conj (.mem 3 2) (.neg (.mem 3 1)))))))))))))) (.all 1 (.neg (.conj (.neg (.conj (.neg (.mem 1 0)) (.neg (.eq 1 0)))) (.neg (.neg (.conj (.neg (.rel .empty 8 [1])) (.neg (.neg (.all 4 (.neg (.conj (.mem 4 1) (.rel .succ 5 [4, 1])))))))))))))
def tbl_nat : Nm → Option (Nat × F) := fun nm => match nm with
    | .empty => some (1, full_empty)
    | .succ => some (2, full_succ)
    | .trans => some (1, full_trans)
    | _ => none
def full_nat : F := expand tbl_nat r_nat

def r_triple : F := (.neg (.all 4 (.neg (.conj (.mem 4 0) (.neg (.all 5 (.neg (.conj (.mem 5 4) (.conj (.rel .pair 6 [0, 5, 3]) (.rel .pair 8 [5, 1, 2]))))))))))
def tbl_triple : Nm → Option (Nat × F) := fun nm => match nm with
    | .pair => some (3, full_pair)
    | _ => none
def full_triple : F := expand tbl_triple r_triple

def r_hyper_table : F := (.all 2 (.neg (.conj (.mem 2 0) (.neg (.all 3 (.neg (.conj (.mem 3 2) (.neg (.all 4 (.neg (.conj (.mem 4 3) (.neg (.all 5 (.neg (.conj (.mem 5 3) (.neg (.all 6 (.neg (.conj (.mem 6 4) (.neg (.all 7 (.neg (.conj (.mem 7 6) (.neg (.all 8 (.neg (.conj (.mem 8 6) (.neg (.neg (.conj (.rel .triple 9 [2, 7, 8, 5]) (.neg (.neg (.conj (.neg (.neg (.conj (.neg (.conj (.rel .empty 31 [7]) (.rel .succ 32 [8, 5]))) (.neg (.neg (.all 15 (.neg (.conj (.mem 15 7) (.conj (.conj (.rel .succ 33 [15, 7]) (.rel .empty 34 [8])) (.neg (.conj (.neg (.neg (.conj (.neg (.conj (.rel .empty 22 [15]) (.eq 5 1))) (.neg (.conj (.neg (.all 21 (.neg (.conj (.mem 21 15) (.conj (.rel .empty 23 [21]) (.rel .succ 24 [21, 15])))))) (.rel .empty 25 [5])))))) (.neg (.conj (.conj (.neg (.rel .empty 26 [15])) (.neg (.neg (.all 21 (.neg (.conj (.mem 21 15) (.conj (.rel .empty 27 [21]) (.rel .succ 28 [21, 15])))))))) (.neg (.all 21 (.neg (.conj (.mem 21 5) (.conj (.rel .empty 29 [21]) (.rel .succ 30 [21, 5]))))))))))))))))))) (.neg (.neg (.all 15 (.neg (.conj (.mem 15 7) (.neg (.all 16 (.neg (.conj (.mem 16 8) (.conj (.conj (.rel .succ 35 [15, 7]) (.rel .succ 36 [16, 8])) (.neg (.all 17 (.neg (.conj (.mem 17 0) (.neg (.all 18 (.neg (.conj (.mem 18 17) (.neg (.all 19 (.neg (.conj (.mem 19 18) (.conj (.rel .triple 37 [17, 7, 16, 19]) (.neg (.all 20 (.neg (.conj (.mem 20 0) (.rel .triple 43 [20, 15, 19, 5])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def tbl_hyper_table : Nm → Option (Nat × F) := fun nm => match nm with
    | .empty => some (1, full_empty)
    | .succ => some (2, full_succ)
    | .triple => some (4, full_triple)
    | _ => none
def full_hyper_table : F := expand tbl_hyper_table r_hyper_table

def r_hyper : F := (.neg (.all 4 (.neg (.conj (.rel .hyper_table 6 [4, 1]) (.neg (.all 5 (.neg (.conj (.mem 5 4) (.rel .triple 53 [5, 0, 2, 3])))))))))
def tbl_hyper : Nm → Option (Nat × F) := fun nm => match nm with
    | .hyper_table => some (2, full_hyper_table)
    | .triple => some (4, full_triple)
    | _ => none
def full_hyper : F := expand tbl_hyper r_hyper

def r_add : F := (.neg (.all 3 (.neg (.conj (.rel .numeral1 4 [3]) (.rel .hyper 7 [3, 0, 1, 2])))))
def tbl_add : Nm → Option (Nat × F) := fun nm => match nm with
    | .hyper => some (4, full_hyper)
    | .numeral1 => some (1, full_numeral1)
    | _ => none
def full_add : F := expand tbl_add r_add

def r_mul : F := (.neg (.all 3 (.neg (.conj (.rel .numeral2 4 [3]) (.rel .hyper 9 [3, 0, 1, 2])))))
def tbl_mul : Nm → Option (Nat × F) := fun nm => match nm with
    | .hyper => some (4, full_hyper)
    | .numeral2 => some (1, full_numeral2)
    | _ => none
def full_mul : F := expand tbl_mul r_mul

def r_exp : F := (.neg (.all 3 (.neg (.conj (.rel .numeral3 4 [3]) (.rel .hyper 11 [3, 0, 1, 2])))))
def tbl_exp : Nm → Option (Nat × F) := fun nm => match nm with
    | .hyper => some (4, full_hyper)
    | .numeral3 => some (1, full_numeral3)
    | _ => none
def full_exp : F := expand tbl_exp r_exp

def r_divides : F := (.neg (.all 2 (.neg (.rel .mul 3 [0, 2, 1]))))
def tbl_divides : Nm → Option (Nat × F) := fun nm => match nm with
    | .mul => some (3, full_mul)
    | _ => none
def full_divides : F := expand tbl_divides r_divides

def r_prime : F := (.conj (.conj (.rel .nat 2 [0]) (.neg (.neg (.conj (.neg (.rel .empty 10 [0])) (.neg (.rel .is_one 11 [0])))))) (.all 1 (.neg (.conj (.mem 1 0) (.neg (.neg (.conj (.neg (.neg (.conj (.neg (.rel .empty 14 [1])) (.neg (.rel .is_one 15 [1]))))) (.neg (.neg (.rel .divides 18 [1, 0]))))))))))
def tbl_prime : Nm → Option (Nat × F) := fun nm => match nm with
    | .divides => some (2, full_divides)
    | .empty => some (1, full_empty)
    | .is_one => some (1, full_is_one)
    | .nat => some (1, full_nat)
    | _ => none
def full_prime : F := expand tbl_prime r_prime

def r_prime_table : F := (.all 1 (.neg (.conj (.mem 1 0) (.neg (.all 2 (.neg (.conj (.mem 2 1) (.neg (.all 3 (.neg (.conj (.mem 3 2) (.neg (.all 4 (.neg (.conj (.mem 4 2) (.neg (.neg (.conj (.rel .pair 5 [1, 3, 4]) (.neg (.neg (.conj (.neg (.conj (.rel .empty 9 [3]) (.rel .numeral2 10 [4]))) (.neg (.neg (.all 7 (.neg (.conj (.mem 7 3) (.conj (.rel .succ 15 [7, 3]) (.neg (.all 16 (.neg (.conj (.mem 16 0) (.neg (.all 17 (.neg (.conj (.mem 17 16) (.neg (.all 18 (.neg (.conj (.mem 18 17) (.conj (.rel .pair 19 [16, 7, 18]) (.conj (.conj (.mem 18 4) (.rel .prime 21 [4])) (.all 8 (.neg (.conj (.mem 8 4) (.neg (.neg (.conj (.mem 18 8) (.neg (.neg (.rel .prime 100 [8]))))))))))))))))))))))))))))))))))))))))))))))))))
def tbl_prime_table : Nm → Option (Nat × F) := fun nm => match nm with
    | .empty => some (1, full_empty)
    | .numeral2 => some (1, full_numeral2)
    | .pair => some (3, full_pair)
    | .prime => some (1, full_prime)
    | .succ => some (2, full_succ)
    | _ => none
def full_prime_table : F := expand tbl_prime_table r_prime_table

def r_nth_prime : F := (.neg (.all 2 (.neg (.conj (.rel .prime_table 3 [2]) (.neg (.all 181 (.neg (.conj (.mem 181 2) (.neg (.all 182 (.neg (.conj (.mem 182 181) (.neg (.all 183 (.neg (.conj (.mem 183 182) (.conj (.rel .pair 184 [181, 0, 183]) (.eq 183 1))))))))))))))))))
def tbl_nth_prime : Nm → Option (Nat × F) := fun nm => match nm with
    | .pair => some (3, full_pair)
    | .prime_table => some (1, full_prime_table)
    | _ => none
def full_nth_prime : F := expand tbl_nth_prime r_nth_prime

def r_seqfun : F := (.conj (.conj (.conj (.rel .nat 34 [1]) (.all 3 (.neg (.conj (.mem 3 0) (.neg (.neg (.all 4 (.neg (.conj (.mem 4 3) (.neg (.all 5 (.neg (.conj (.mem 5 4) (.neg (.all 6 (.neg (.conj (.mem 6 4) (.conj (.rel .pair 7 [3, 5, 6]) (.conj (.mem 5 1) (.rel .nat 9 [6])))))))))))))))))))) (.all 2 (.neg (.conj (.mem 2 1) (.neg (.neg (.all 17 (.neg (.conj (.mem 17 0) (.neg (.all 18 (.neg (.conj (.mem 18 17) (.neg (.all 19 (.neg (.conj (.mem 19 18) (.conj (.rel .pair 20 [17, 2, 19]) (.eq 19 19))))))))))))))))))) (.all 22 (.neg (.conj (.mem 22 0) (.neg (.all 23 (.neg (.conj (.mem 23 22) (.neg (.all 24 (.neg (.conj (.mem 24 23) (.neg (.all 25 (.neg (.conj (.mem 25 23) (.neg (.neg (.conj (.rel .pair 26 [22, 24, 25]) (.neg (.all 28 (.neg (.conj (.mem 28 0) (.neg (.all 29 (.neg (.conj (.mem 29 28) (.neg (.all 30 (.neg (.conj (.mem 30 29) (.neg (.all 31 (.neg (.conj (.mem 31 29) (.neg (.neg (.conj (.rel .pair 32 [28, 30, 31]) (.neg (.neg (.conj (.eq 24 30) (.neg (.eq 25 31)))))))))))))))))))))))))))))))))))))))))))
def tbl_seqfun : Nm → Option (Nat × F) := fun nm => match nm with
    | .nat => some (1, full_nat)
    | .pair => some (3, full_pair)
    | _ => none
def full_seqfun : F := expand tbl_seqfun r_seqfun

def r_prod_table : F := (.all 2 (.neg (.conj (.mem 2 0) (.neg (.all 3 (.neg (.conj (.mem 3 2) (.neg (.all 4 (.neg (.conj (.mem 4 3) (.neg (.all 5 (.neg (.conj (.mem 5 3) (.neg (.neg (.conj (.rel .pair 6 [2, 4, 5]) (.neg (.neg (.conj (.neg (.conj (.rel .empty 11 [4]) (.rel .is_one 12 [5]))) (.neg (.neg (.all 8 (.neg (.conj (.mem 8 4) (.conj (.rel .succ 15 [8, 4]) (.neg (.all 16 (.neg (.conj (.mem 16 0) (.neg (.all 17 (.neg (.conj (.mem 17 16) (.neg (.all 18 (.neg (.conj (.mem 18 17) (.conj (.rel .pair 19 [16, 8, 18]) (.neg (.all 21 (.neg (.conj (.mem 21 1) (.neg (.all 22 (.neg (.conj (.mem 22 21) (.neg (.all 23 (.neg (.conj (.mem 23 22) (.conj (.rel .pair 24 [21, 8, 23]) (.neg (.all 9 (.neg (.conj (.rel .nth_prime 26 [4, 9]) (.neg (.all 10 (.neg (.conj (.rel .exp 210 [9, 23, 10]) (.rel .mul 273 [18, 10, 5]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def tbl_prod_table : Nm → Option (Nat × F) := fun nm => match nm with
    | .empty => some (1, full_empty)
    | .exp => some (3, full_exp)
    | .is_one => some (1, full_is_one)
    | .mul => some (3, full_mul)
    | .nth_prime => some (2, full_nth_prime)
    | .pair => some (3, full_pair)
    | .succ => some (2, full_succ)
    | _ => none
def full_prod_table : F := expand tbl_prod_table r_prod_table

def r_encode : F := (.neg (.all 2 (.neg (.conj (.rel .seqfun 7 [0, 2]) (.neg (.all 3 (.neg (.conj (.rel .prod_table 47 [3, 0]) (.neg (.all 379 (.neg (.conj (.mem 379 3) (.neg (.all 380 (.neg (.conj (.mem 380 379) (.neg (.all 381 (.neg (.conj (.mem 381 380) (.conj (.rel .pair 382 [379, 2, 381]) (.neg (.all 4 (.neg (.conj (.rel .numeral2 384 [4]) (.neg (.all 5 (.neg (.conj (.rel .exp 389 [4, 2, 5]) (.neg (.all 6 (.neg (.conj (.rel .mul 452 [5, 381, 6]) (.rel .succ 513 [1, 6]))))))))))))))))))))))))))))))))))
def tbl_encode : Nm → Option (Nat × F) := fun nm => match nm with
    | .exp => some (3, full_exp)
    | .mul => some (3, full_mul)
    | .numeral2 => some (1, full_numeral2)
    | .pair => some (3, full_pair)
    | .prod_table => some (2, full_prod_table)
    | .seqfun => some (2, full_seqfun)
    | .succ => some (2, full_succ)
    | _ => none
def full_encode : F := expand tbl_encode r_encode

def r_tuple4 : F := (.neg (.all 1 (.neg (.conj (.rel .numeral4 2 [1]) (.conj (.conj (.conj (.rel .nat 43 [1]) (.all 12 (.neg (.conj (.mem 12 0) (.neg (.neg (.all 13 (.neg (.conj (.mem 13 12) (.neg (.all 14 (.neg (.conj (.mem 14 13) (.neg (.all 15 (.neg (.conj (.mem 15 13) (.conj (.rel .pair 16 [12, 14, 15]) (.conj (.mem 14 1) (.rel .nat 18 [15])))))))))))))))))))) (.all 11 (.neg (.conj (.mem 11 1) (.neg (.neg (.all 26 (.neg (.conj (.mem 26 0) (.neg (.all 27 (.neg (.conj (.mem 27 26) (.neg (.all 28 (.neg (.conj (.mem 28 27) (.conj (.rel .pair 29 [26, 11, 28]) (.eq 28 28))))))))))))))))))) (.all 31 (.neg (.conj (.mem 31 0) (.neg (.all 32 (.neg (.conj (.mem 32 31) (.neg (.all 33 (.neg (.conj (.mem 33 32) (.neg (.all 34 (.neg (.conj (.mem 34 32) (.neg (.neg (.conj (.rel .pair 35 [31, 33, 34]) (.neg (.all 37 (.neg (.conj (.mem 37 0) (.neg (.all 38 (.neg (.conj (.mem 38 37) (.neg (.all 39 (.neg (.conj (.mem 39 38) (.neg (.all 40 (.neg (.conj (.mem 40 38) (.neg (.neg (.conj (.rel .pair 41 [37, 39, 40]) (.neg (.neg (.conj (.eq 33 39) (.neg (.eq 34 40)))))))))))))))))))))))))))))))))))))))))))))))
def tbl_tuple4 : Nm → Option (Nat × F) := fun nm => match nm with
    | .nat => some (1, full_nat)
    | .numeral4 => some (1, full_numeral4)
    | .pair => some (3, full_pair)
    | _ => none
def full_tuple4 : F := expand tbl_tuple4 r_tuple4

def r_metacode : F := (.neg (.all 2 (.neg (.conj (.conj (.conj (.conj (.rel .nat 79 [2]) (.all 6 (.neg (.conj (.mem 6 1) (.neg (.neg (.all 7 (.neg (.conj (.mem 7 6) (.neg (.all 8 (.neg (.conj (.mem 8 7) (.neg (.all 9 (.neg (.conj (.mem 9 7) (.conj (.rel .pair 10 [6, 8, 9]) (.conj (.mem 8 2) (.rel .tuple4 12 [9])))))))))))))))))))) (.all 5 (.neg (.conj (.mem 5 2) (.neg (.neg (.all 62 (.neg (.conj (.mem 62 1) (.neg (.all 63 (.neg (.conj (.mem 63 62) (.neg (.all 64 (.neg (.conj (.mem 64 63) (.conj (.rel .pair 65 [62, 5, 64]) (.eq 64 64))))))))))))))))))) (.all 67 (.neg (.conj (.mem 67 1) (.neg (.all 68 (.neg (.conj (.mem 68 67) (.neg (.all 69 (.neg (.conj (.mem 69 68) (.neg (.all 70 (.neg (.conj (.mem 70 68) (.neg (.neg (.conj (.rel .pair 71 [67, 69, 70]) (.neg (.all 73 (.neg (.conj (.mem 73 1) (.neg (.all 74 (.neg (.conj (.mem 74 73) (.neg (.all 75 (.neg (.conj (.mem 75 74) (.neg (.all 76 (.neg (.conj (.mem 76 74) (.neg (.neg (.conj (.rel .pair 77 [73, 75, 76]) (.neg (.neg (.conj (.eq 69 75) (.neg (.eq 70 76))))))))))))))))))))))))))))))))))))))))))) (.neg (.all 3 (.neg (.conj (.conj (.rel .encode 87 [3, 0]) (.conj (.conj (.conj (.rel .nat 631 [2]) (.all 600 (.neg (.conj (.mem 600 3) (.neg (.neg (.all 601 (.neg (.conj (.mem 601 600) (.neg (.all 602 (.neg (.conj (.mem 602 601) (.neg (.all 603 (.neg (.conj (.mem 603 601) (.conj (.rel .pair 604 [600, 602, 603]) (.conj (.mem 602 2) (.rel .nat 606 [603])))))))))))))))))))) (.all 599 (.neg (.conj (.mem 599 2) (.neg (.neg (.all 614 (.neg (.conj (.mem 614 3) (.neg (.all 615 (.neg (.conj (.mem 615 614) (.neg (.all 616 (.neg (.conj (.mem 616 615) (.conj (.rel .pair 617 [614, 599, 616]) (.eq 616 616))))))))))))))))))) (.all 619 (.neg (.conj (.mem 619 3) (.neg (.all 620 (.neg (.conj (.mem 620 619) (.neg (.all 621 (.neg (.conj (.mem 621 620) (.neg (.all 622 (.neg (.conj (.mem 622 620) (.neg (.neg (.conj (.rel .pair 623 [619, 621, 622]) (.neg (.all 625 (.neg (.conj (.mem 625 3) (.neg (.all 626 (.neg (.conj (.mem 626 625) (.neg (.all 627 (.neg (.conj (.mem 627 626) (.neg (.all 628 (.neg (.conj (.mem 628 626) (.neg (.neg (.conj (.rel .pair 629 [625, 627, 628]) (.neg (.neg (.conj (.eq 621 627) (.neg (.eq 622 628)))))))))))))))))))))))))))))))))))))))))))) (.all 4 (.neg (.conj (.mem 4 2) (.neg (.neg (.all 639 (.neg (.conj (.mem 639 1) (.neg (.all 640 (.neg (.conj (.mem 640 639) (.neg (.all 641 (.neg (.conj (.mem 641 640) (.conj (.rel .pair 642 [639, 4, 641]) (.neg (.all 644 (.neg (.conj (.mem 644 3) (.neg (.all 645 (.neg (.conj (.mem 645 644) (.neg (.all 646 (.neg (.conj (.mem 646 645) (.conj (.rel .pair 647 [644, 4, 646]) (.rel .encode 649 [641, 646])))))))))))))))))))))))))))))))))))))))
def tbl_metacode : Nm → Option (Nat × F) := fun nm => match nm with
    | .encode => some (2, full_encode)
    | .nat => some (1, full_nat)
    | .pair => some (3, full_pair)
    | .tuple4 => some (1, full_tuple4)
    | _ => none
def full_metacode : F := expand tbl_metacode r_metacode

end Tr
