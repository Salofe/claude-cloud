import OMAStatements.S_oeis_a282289
import Mathlib

namespace OMA.Helpers

/-- All prime powers `p ^ k` with `k ≥ 2` up to `340473`. -/
def L : List ℕ :=
  [4, 8, 9, 16, 25, 27, 32, 49, 64, 81, 121, 125,
    128, 169, 243, 256, 289, 343, 361, 512, 529, 625, 729, 841,
    961, 1024, 1331, 1369, 1681, 1849, 2048, 2187, 2197, 2209, 2401, 2809,
    3125, 3481, 3721, 4096, 4489, 4913, 5041, 5329, 6241, 6561, 6859, 6889,
    7921, 8192, 9409, 10201, 10609, 11449, 11881, 12167, 12769, 14641, 15625, 16129,
    16384, 16807, 17161, 18769, 19321, 19683, 22201, 22801, 24389, 24649, 26569, 27889,
    28561, 29791, 29929, 32041, 32761, 32768, 36481, 37249, 38809, 39601, 44521, 49729,
    50653, 51529, 52441, 54289, 57121, 58081, 59049, 63001, 65536, 66049, 68921, 69169,
    72361, 73441, 76729, 78125, 78961, 79507, 80089, 83521, 85849, 94249, 96721, 97969,
    100489, 103823, 109561, 113569, 117649, 120409, 121801, 124609, 128881, 130321, 131072, 134689,
    139129, 143641, 146689, 148877, 151321, 157609, 160801, 161051, 167281, 175561, 177147, 177241,
    185761, 187489, 192721, 196249, 201601, 205379, 208849, 212521, 214369, 218089, 226981, 229441,
    237169, 241081, 249001, 253009, 259081, 262144, 271441, 273529, 279841, 292681, 299209, 300763,
    310249, 316969, 323761, 326041, 332929]

/-- Bitset of `{m + x : x ∈ l, m ∈ M}`, where `M` is read as a bitset. -/
def sh (l : List ℕ) (M : ℕ) : ℕ := l.foldr (fun x acc => acc ||| (M <<< x)) 0

theorem testBit_sh (l : List ℕ) (M m : ℕ) (h : ∃ x ∈ l, x ≤ m ∧ M.testBit (m - x) = true) :
    (sh l M).testBit m = true := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    simp only [sh, List.foldr_cons] at ih ⊢
    rw [Nat.testBit_lor, Bool.or_eq_true]
    obtain ⟨x, hx, hxm, hb⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · right
      rw [Nat.testBit_shiftLeft, hb]
      simp [hxm]
    · left
      exact ih ⟨x, hx, hxm, hb⟩

/-- Bitset of the prime powers in `L`. -/
def mask : ℕ := sh L 1

/-- Bitset of the sums of two elements of `L`. -/
def S2 : ℕ := sh L mask

/-- Bitset of the sums of three elements of `L`. -/
def S3 : ℕ := sh L S2

theorem check : L.all (fun x => !(S3.testBit (340473 - x))) = true := by
  decide +kernel

/-- Trial division by `2, ..., 24` (enough below `625`). -/
def tdok (p : ℕ) : Bool := (List.range 25).all (fun d => decide (d < 2) || decide (p ≤ d) || p % d != 0)

theorem table : (List.range 584).all (fun p => (List.range 20).all (fun k =>
    decide (k < 2) || decide (340473 < p ^ k) || decide (p < 2) || !tdok p || L.contains (p ^ k))) =
      true := by
  decide +kernel

theorem tdok_of_prime (p : ℕ) (hp : p.Prime) : tdok p = true := by
  rw [tdok, List.all_eq_true]
  intro d _
  simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  by_cases h1 : d < 2
  · exact Or.inl (Or.inl h1)
  · by_cases h2 : p ≤ d
    · exact Or.inl (Or.inr h2)
    · right
      intro hmod
      rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hmod) with h | h <;> omega

theorem mem_L (q : ℕ) (hq : OMA.S_oeis_a282289.IsHigherPrimePower q) (hle : q ≤ 340473) :
    q ∈ L := by
  obtain ⟨p, k, hp, hk, rfl⟩ := hq
  have h2 := hp.two_le
  have hpk : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
  have hp584 : p < 584 := by
    by_contra hc
    have : 584 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hk20 : k < 20 := by
    by_contra hc
    have h1 : 2 ^ 20 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left h2 k
    omega
  have t := List.all_eq_true.mp (List.all_eq_true.mp table p (List.mem_range.mpr hp584)) k
    (List.mem_range.mpr hk20)
  have htd := tdok_of_prime p hp
  simp only [Bool.or_eq_true, decide_eq_true_eq, htd, Bool.not_true, Bool.false_eq_true,
    or_false, List.contains_iff_mem] at t
  rcases t with ((h | h) | h) | h
  · omega
  · omega
  · omega
  · exact h

end OMA.Helpers

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282289.main) := by
  intro h
  have h1 := h 340473 (by norm_num)
  have hempty : {q : Fin 4 → ℕ | (∀ i, OMA.S_oeis_a282289.IsHigherPrimePower (q i)) ∧
      ∑ i, q i = 340473} = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun q hq => ?_
    obtain ⟨hpp, hs⟩ := hq
    rw [Fin.sum_univ_four] at hs
    have m0 := OMA.Helpers.mem_L (q 0) (hpp 0) (by omega)
    have m1 := OMA.Helpers.mem_L (q 1) (hpp 1) (by omega)
    have m2 := OMA.Helpers.mem_L (q 2) (hpp 2) (by omega)
    have m3 := OMA.Helpers.mem_L (q 3) (hpp 3) (by omega)
    have b0 : OMA.Helpers.mask.testBit (q 0) = true :=
      OMA.Helpers.testBit_sh _ _ _ ⟨q 0, m0, le_refl _, by rw [Nat.sub_self]; rfl⟩
    have b1 : OMA.Helpers.S2.testBit (q 0 + q 1) = true :=
      OMA.Helpers.testBit_sh _ _ _ ⟨q 1, m1, by omega, by rw [Nat.add_sub_cancel]; exact b0⟩
    have b2 : OMA.Helpers.S3.testBit (q 0 + q 1 + q 2) = true :=
      OMA.Helpers.testBit_sh _ _ _ ⟨q 2, m2, by omega, by rw [Nat.add_sub_cancel]; exact b1⟩
    have c3 := List.all_eq_true.mp OMA.Helpers.check (q 3) m3
    rw [show 340473 - q 3 = q 0 + q 1 + q 2 by omega, b2] at c3
    exact absurd c3 (by decide)
  have h2 : OMA.S_oeis_a282289.a 340473 = 0 := by
    unfold OMA.S_oeis_a282289.a
    rw [hempty, Set.ncard_empty]
  omega
