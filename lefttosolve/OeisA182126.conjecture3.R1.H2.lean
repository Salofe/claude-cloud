import OMAReductions.R_OeisA182126_conjecture3_R1

-- Step H2 of reduction OeisA182126.conjecture3.R1: the finite check of a(1), ..., a(61).
-- The first 63 primes are pinned down by Nat.nth_count (prime counts checked by the kernel),
-- then every case is evaluated.

namespace OMA.Helpers

theorem a182126_nth_of (p k : ℕ) (hp : p.Prime) (hc : Nat.count Nat.Prime p = k) :
    Nat.nth Nat.Prime k = p := hc ▸ Nat.nth_count hp

theorem a182126_p0 : Nat.nth Nat.Prime 0 = 2 :=
  a182126_nth_of 2 0 (by norm_num) (by decide +kernel)

theorem a182126_p1 : Nat.nth Nat.Prime 1 = 3 :=
  a182126_nth_of 3 1 (by norm_num) (by decide +kernel)

theorem a182126_p2 : Nat.nth Nat.Prime 2 = 5 :=
  a182126_nth_of 5 2 (by norm_num) (by decide +kernel)

theorem a182126_p3 : Nat.nth Nat.Prime 3 = 7 :=
  a182126_nth_of 7 3 (by norm_num) (by decide +kernel)

theorem a182126_p4 : Nat.nth Nat.Prime 4 = 11 :=
  a182126_nth_of 11 4 (by norm_num) (by decide +kernel)

theorem a182126_p5 : Nat.nth Nat.Prime 5 = 13 :=
  a182126_nth_of 13 5 (by norm_num) (by decide +kernel)

theorem a182126_p6 : Nat.nth Nat.Prime 6 = 17 :=
  a182126_nth_of 17 6 (by norm_num) (by decide +kernel)

theorem a182126_p7 : Nat.nth Nat.Prime 7 = 19 :=
  a182126_nth_of 19 7 (by norm_num) (by decide +kernel)

theorem a182126_p8 : Nat.nth Nat.Prime 8 = 23 :=
  a182126_nth_of 23 8 (by norm_num) (by decide +kernel)

theorem a182126_p9 : Nat.nth Nat.Prime 9 = 29 :=
  a182126_nth_of 29 9 (by norm_num) (by decide +kernel)

theorem a182126_p10 : Nat.nth Nat.Prime 10 = 31 :=
  a182126_nth_of 31 10 (by norm_num) (by decide +kernel)

theorem a182126_p11 : Nat.nth Nat.Prime 11 = 37 :=
  a182126_nth_of 37 11 (by norm_num) (by decide +kernel)

theorem a182126_p12 : Nat.nth Nat.Prime 12 = 41 :=
  a182126_nth_of 41 12 (by norm_num) (by decide +kernel)

theorem a182126_p13 : Nat.nth Nat.Prime 13 = 43 :=
  a182126_nth_of 43 13 (by norm_num) (by decide +kernel)

theorem a182126_p14 : Nat.nth Nat.Prime 14 = 47 :=
  a182126_nth_of 47 14 (by norm_num) (by decide +kernel)

theorem a182126_p15 : Nat.nth Nat.Prime 15 = 53 :=
  a182126_nth_of 53 15 (by norm_num) (by decide +kernel)

theorem a182126_p16 : Nat.nth Nat.Prime 16 = 59 :=
  a182126_nth_of 59 16 (by norm_num) (by decide +kernel)

theorem a182126_p17 : Nat.nth Nat.Prime 17 = 61 :=
  a182126_nth_of 61 17 (by norm_num) (by decide +kernel)

theorem a182126_p18 : Nat.nth Nat.Prime 18 = 67 :=
  a182126_nth_of 67 18 (by norm_num) (by decide +kernel)

theorem a182126_p19 : Nat.nth Nat.Prime 19 = 71 :=
  a182126_nth_of 71 19 (by norm_num) (by decide +kernel)

theorem a182126_p20 : Nat.nth Nat.Prime 20 = 73 :=
  a182126_nth_of 73 20 (by norm_num) (by decide +kernel)

theorem a182126_p21 : Nat.nth Nat.Prime 21 = 79 :=
  a182126_nth_of 79 21 (by norm_num) (by decide +kernel)

theorem a182126_p22 : Nat.nth Nat.Prime 22 = 83 :=
  a182126_nth_of 83 22 (by norm_num) (by decide +kernel)

theorem a182126_p23 : Nat.nth Nat.Prime 23 = 89 :=
  a182126_nth_of 89 23 (by norm_num) (by decide +kernel)

theorem a182126_p24 : Nat.nth Nat.Prime 24 = 97 :=
  a182126_nth_of 97 24 (by norm_num) (by decide +kernel)

theorem a182126_p25 : Nat.nth Nat.Prime 25 = 101 :=
  a182126_nth_of 101 25 (by norm_num) (by decide +kernel)

theorem a182126_p26 : Nat.nth Nat.Prime 26 = 103 :=
  a182126_nth_of 103 26 (by norm_num) (by decide +kernel)

theorem a182126_p27 : Nat.nth Nat.Prime 27 = 107 :=
  a182126_nth_of 107 27 (by norm_num) (by decide +kernel)

theorem a182126_p28 : Nat.nth Nat.Prime 28 = 109 :=
  a182126_nth_of 109 28 (by norm_num) (by decide +kernel)

theorem a182126_p29 : Nat.nth Nat.Prime 29 = 113 :=
  a182126_nth_of 113 29 (by norm_num) (by decide +kernel)

theorem a182126_p30 : Nat.nth Nat.Prime 30 = 127 :=
  a182126_nth_of 127 30 (by norm_num) (by decide +kernel)

theorem a182126_p31 : Nat.nth Nat.Prime 31 = 131 :=
  a182126_nth_of 131 31 (by norm_num) (by decide +kernel)

theorem a182126_p32 : Nat.nth Nat.Prime 32 = 137 :=
  a182126_nth_of 137 32 (by norm_num) (by decide +kernel)

theorem a182126_p33 : Nat.nth Nat.Prime 33 = 139 :=
  a182126_nth_of 139 33 (by norm_num) (by decide +kernel)

theorem a182126_p34 : Nat.nth Nat.Prime 34 = 149 :=
  a182126_nth_of 149 34 (by norm_num) (by decide +kernel)

theorem a182126_p35 : Nat.nth Nat.Prime 35 = 151 :=
  a182126_nth_of 151 35 (by norm_num) (by decide +kernel)

theorem a182126_p36 : Nat.nth Nat.Prime 36 = 157 :=
  a182126_nth_of 157 36 (by norm_num) (by decide +kernel)

theorem a182126_p37 : Nat.nth Nat.Prime 37 = 163 :=
  a182126_nth_of 163 37 (by norm_num) (by decide +kernel)

theorem a182126_p38 : Nat.nth Nat.Prime 38 = 167 :=
  a182126_nth_of 167 38 (by norm_num) (by decide +kernel)

theorem a182126_p39 : Nat.nth Nat.Prime 39 = 173 :=
  a182126_nth_of 173 39 (by norm_num) (by decide +kernel)

theorem a182126_p40 : Nat.nth Nat.Prime 40 = 179 :=
  a182126_nth_of 179 40 (by norm_num) (by decide +kernel)

theorem a182126_p41 : Nat.nth Nat.Prime 41 = 181 :=
  a182126_nth_of 181 41 (by norm_num) (by decide +kernel)

theorem a182126_p42 : Nat.nth Nat.Prime 42 = 191 :=
  a182126_nth_of 191 42 (by norm_num) (by decide +kernel)

theorem a182126_p43 : Nat.nth Nat.Prime 43 = 193 :=
  a182126_nth_of 193 43 (by norm_num) (by decide +kernel)

theorem a182126_p44 : Nat.nth Nat.Prime 44 = 197 :=
  a182126_nth_of 197 44 (by norm_num) (by decide +kernel)

theorem a182126_p45 : Nat.nth Nat.Prime 45 = 199 :=
  a182126_nth_of 199 45 (by norm_num) (by decide +kernel)

theorem a182126_p46 : Nat.nth Nat.Prime 46 = 211 :=
  a182126_nth_of 211 46 (by norm_num) (by decide +kernel)

theorem a182126_p47 : Nat.nth Nat.Prime 47 = 223 :=
  a182126_nth_of 223 47 (by norm_num) (by decide +kernel)

theorem a182126_p48 : Nat.nth Nat.Prime 48 = 227 :=
  a182126_nth_of 227 48 (by norm_num) (by decide +kernel)

theorem a182126_p49 : Nat.nth Nat.Prime 49 = 229 :=
  a182126_nth_of 229 49 (by norm_num) (by decide +kernel)

theorem a182126_p50 : Nat.nth Nat.Prime 50 = 233 :=
  a182126_nth_of 233 50 (by norm_num) (by decide +kernel)

theorem a182126_p51 : Nat.nth Nat.Prime 51 = 239 :=
  a182126_nth_of 239 51 (by norm_num) (by decide +kernel)

theorem a182126_p52 : Nat.nth Nat.Prime 52 = 241 :=
  a182126_nth_of 241 52 (by norm_num) (by decide +kernel)

theorem a182126_p53 : Nat.nth Nat.Prime 53 = 251 :=
  a182126_nth_of 251 53 (by norm_num) (by decide +kernel)

theorem a182126_p54 : Nat.nth Nat.Prime 54 = 257 :=
  a182126_nth_of 257 54 (by norm_num) (by decide +kernel)

theorem a182126_p55 : Nat.nth Nat.Prime 55 = 263 :=
  a182126_nth_of 263 55 (by norm_num) (by decide +kernel)

theorem a182126_p56 : Nat.nth Nat.Prime 56 = 269 :=
  a182126_nth_of 269 56 (by norm_num) (by decide +kernel)

theorem a182126_p57 : Nat.nth Nat.Prime 57 = 271 :=
  a182126_nth_of 271 57 (by norm_num) (by decide +kernel)

theorem a182126_p58 : Nat.nth Nat.Prime 58 = 277 :=
  a182126_nth_of 277 58 (by norm_num) (by decide +kernel)

theorem a182126_p59 : Nat.nth Nat.Prime 59 = 281 :=
  a182126_nth_of 281 59 (by norm_num) (by decide +kernel)

theorem a182126_p60 : Nat.nth Nat.Prime 60 = 283 :=
  a182126_nth_of 283 60 (by norm_num) (by decide +kernel)

theorem a182126_p61 : Nat.nth Nat.Prime 61 = 293 :=
  a182126_nth_of 293 61 (by norm_num) (by decide +kernel)

theorem a182126_p62 : Nat.nth Nat.Prime 62 = 307 :=
  a182126_nth_of 307 62 (by norm_num) (by decide +kernel)

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_OeisA182126_conjecture3_R1.H2 := by
  intro n hn hle hp
  interval_cases n <;>
    simp only [OeisA182126.a, OeisA182126.prime,
      a182126_p0, a182126_p1, a182126_p2, a182126_p3, a182126_p4, a182126_p5, a182126_p6, a182126_p7,
      a182126_p8, a182126_p9, a182126_p10, a182126_p11, a182126_p12, a182126_p13, a182126_p14, a182126_p15,
      a182126_p16, a182126_p17, a182126_p18, a182126_p19, a182126_p20, a182126_p21, a182126_p22, a182126_p23,
      a182126_p24, a182126_p25, a182126_p26, a182126_p27, a182126_p28, a182126_p29, a182126_p30, a182126_p31,
      a182126_p32, a182126_p33, a182126_p34, a182126_p35, a182126_p36, a182126_p37, a182126_p38, a182126_p39,
      a182126_p40, a182126_p41, a182126_p42, a182126_p43, a182126_p44, a182126_p45, a182126_p46, a182126_p47,
      a182126_p48, a182126_p49, a182126_p50, a182126_p51, a182126_p52, a182126_p53, a182126_p54, a182126_p55,
      a182126_p56, a182126_p57, a182126_p58, a182126_p59, a182126_p60, a182126_p61, a182126_p62,
      Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, one_ne_zero,
      OfNat.ofNat_ne_zero, if_false] at hp ⊢ <;>
    first | decide | exact absurd hp (by norm_num)
