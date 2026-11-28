import OMAStatements.S_oeis_a154145
import Mathlib

/-!
Proof of the conjectured recurrence and generating functions of A154145.

With x = 2k + 1 and y = m, the condition 15 + k(k+1)/2 = m^2 is the Pell-type equation
x^2 + 119 = 8y^2. Its solutions with x > 0, in increasing order, are (3,4), (9,5), (13,6), (23,9)
followed by multiplication by the unit 3 + 2 sqrt 2 every four steps: (x, y) -> (3x + 8y, x + 3y).
Completeness is a descent: for x >= 31 the inverse step (3x - 8y, 3y - x) is a smaller positive
solution. Hence a(n) = (x_(n-1) - 1)/2, and x_(i+8) = 6 x_(i+4) - x_i gives the recurrence; the
generating functions follow by comparing coefficients and a polynomial identity.
-/

namespace OMA.Helpers

open OMA.S_oeis_a154145

/-- The solutions `(x, y)` of `x ^ 2 + 119 = 8 y ^ 2` with `x > 0`, in increasing order: four
fundamental ones, then multiplication by the unit `3 + 2 √2` every four steps. -/
def pq : ℕ → ℕ × ℕ
  | 0 => (3, 4)
  | 1 => (9, 5)
  | 2 => (13, 6)
  | 3 => (23, 9)
  | n + 4 => (3 * (pq n).1 + 8 * (pq n).2, (pq n).1 + 3 * (pq n).2)

theorem pq_add4 (n : ℕ) :
    pq (n + 4) = (3 * (pq n).1 + 8 * (pq n).2, (pq n).1 + 3 * (pq n).2) := by
  rw [pq]

theorem pq_pell : ∀ n, (pq n).1 ^ 2 + 119 = 8 * (pq n).2 ^ 2
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | n + 4 => by
    have ih := pq_pell n
    rw [pq_add4]
    dsimp only
    nlinarith [ih]

theorem pq_odd : ∀ n, (pq n).1 % 2 = 1
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | n + 4 => by
    have ih := pq_odd n
    rw [pq_add4]
    dsimp only
    omega

theorem pq_mono : ∀ n, (pq n).1 < (pq (n + 1)).1 ∧ (pq n).2 < (pq (n + 1)).2
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | n + 4 => by
    have ih := pq_mono n
    rw [pq_add4, show n + 4 + 1 = (n + 1) + 4 by ring, pq_add4]
    constructor <;> simp only <;> omega

/-- The `n`-th term (0-based): `k = (x - 1) / 2`. -/
def f (n : ℕ) : ℕ := (pq n).1 / 2

theorem f_two (n : ℕ) : 2 * f n + 1 = (pq n).1 := by
  have := pq_odd n
  unfold f
  omega

theorem f_strictMono : StrictMono f := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h1 := f_two n
  have h2 := f_two (n + 1)
  have h3 := (pq_mono n).1
  omega

theorem P_iff (k y : ℕ) : 15 + k * (k + 1) / 2 = y ^ 2 ↔ (2 * k + 1) ^ 2 + 119 = 8 * y ^ 2 := by
  have h2 : k * (k + 1) / 2 * 2 = k * (k + 1) :=
    Nat.div_mul_cancel (Nat.even_mul_succ_self k).two_dvd
  constructor
  · intro h
    nlinarith [h, h2]
  · intro h
    nlinarith [h, h2]

theorem P_f (n : ℕ) : P (f n) := by
  refine ⟨(pq n).2, ?_⟩
  rw [P_iff, f_two]
  exact pq_pell n

/-- Every solution is a term: descent by the inverse unit `3 - 2 √2`. -/
theorem P_surj : ∀ k, P k → ∃ n, f n = k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rintro ⟨y, hy⟩
    rw [P_iff] at hy
    by_cases hk : k ≤ 14
    · have hy11 : y ≤ 11 := by nlinarith
      interval_cases k <;> interval_cases y <;>
        first
        | exact ⟨0, rfl⟩
        | exact ⟨1, rfl⟩
        | exact ⟨2, rfl⟩
        | exact ⟨3, rfl⟩
        | (exfalso; norm_num at hy)
    · push_neg at hk
      set x := 2 * k + 1 with hx
      have hx31 : 31 ≤ x := by omega
      have h1 : 8 * y < 3 * x := by nlinarith
      have h2 : x < 3 * y := by nlinarith
      have h3 : 3 * x - 8 * y < x := by
        have : x < 4 * y := by nlinarith
        omega
      have hpell' : ((3 * x - 8 * y : ℕ) : ℤ) ^ 2 + 119 = 8 * ((3 * y - x : ℕ) : ℤ) ^ 2 := by
        rw [Nat.cast_sub h1.le, Nat.cast_sub h2.le]
        push_cast
        have : ((x : ℤ)) ^ 2 + 119 = 8 * (y : ℤ) ^ 2 := by exact_mod_cast hy
        linear_combination this
      have hpell : (3 * x - 8 * y) ^ 2 + 119 = 8 * (3 * y - x) ^ 2 := by exact_mod_cast hpell'
      have hodd : (3 * x - 8 * y) % 2 = 1 := by omega
      obtain ⟨n, hn⟩ := ih ((3 * x - 8 * y) / 2) (by omega) ⟨3 * y - x, by
        rw [P_iff, show 2 * ((3 * x - 8 * y) / 2) + 1 = 3 * x - 8 * y by omega]
        exact hpell⟩
      have hx' : (pq n).1 = 3 * x - 8 * y := by
        have := f_two n
        omega
      have hy' : (pq n).2 = 3 * y - x := by
        have e1 := pq_pell n
        rw [hx'] at e1
        have e2 : (pq n).2 ^ 2 = (3 * y - x) ^ 2 :=
          Nat.eq_of_mul_eq_mul_left (by norm_num) (e1.symm.trans hpell)
        exact (pow_left_inj₀ (Nat.zero_le _) (Nat.zero_le _) two_ne_zero).mp e2
      refine ⟨n + 4, ?_⟩
      have e := f_two (n + 4)
      rw [pq_add4, hx', hy'] at e
      simp only at e
      omega

theorem nth_eq (n : ℕ) : Nat.nth P n = f n := by
  have hinf : (Set.ofPred P).Infinite :=
    Set.infinite_of_injective_forall_mem f_strictMono.injective P_f
  have h := Nat.nth_comp_of_strictMono (p := P) (n := n) f_strictMono
    (fun k hk => P_surj k hk) (fun hfi => absurd hfi hinf)
  have e : (fun i => P (f i)) = fun _ => True :=
    funext fun i => propext ⟨fun _ => trivial, fun _ => P_f i⟩
  rw [e, Nat.nth_true] at h
  exact h.symm

theorem a_eq (n : ℕ) (hn : 1 ≤ n) : a n = f (n - 1) := by
  unfold a
  exact nth_eq (n - 1)

theorem x_rec (i : ℕ) : ((pq (i + 8)).1 : ℤ) = 6 * (pq (i + 4)).1 - (pq i).1 := by
  rw [show i + 8 = (i + 4) + 4 by ring, pq_add4 (i + 4), pq_add4 i]
  push_cast
  ring

theorem f_rec (i : ℕ) : (f (i + 8) : ℤ) = 6 * f (i + 4) - f i + 2 := by
  have h1 := f_two (i + 8)
  have h2 := f_two (i + 4)
  have h3 := f_two i
  have h := x_rec i
  have h1' : (2 * f (i + 8) + 1 : ℤ) = (pq (i + 8)).1 := by exact_mod_cast h1
  have h2' : (2 * f (i + 4) + 1 : ℤ) = (pq (i + 4)).1 := by exact_mod_cast h2
  have h3' : (2 * f i + 1 : ℤ) = (pq i).1 := by exact_mod_cast h3
  linarith

theorem rec_part (n : ℕ) (hn : 9 < n) :
    (a n : ℤ) = a (n - 1) + 6 * a (n - 4) - 6 * a (n - 5) - a (n - 8) + a (n - 9) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 10 := ⟨n - 10, by omega⟩
  rw [a_eq _ (by omega), a_eq _ (by omega), a_eq _ (by omega), a_eq _ (by omega),
    a_eq _ (by omega), a_eq _ (by omega)]
  rw [show j + 10 - 1 - 1 = j + 8 by omega, show j + 10 - 1 = j + 9 by omega,
    show j + 10 - 4 - 1 = j + 5 by omega, show j + 10 - 5 - 1 = j + 4 by omega,
    show j + 10 - 8 - 1 = j + 1 by omega, show j + 10 - 9 - 1 = j by omega]
  have r1 : (f (j + 9) : ℤ) = 6 * f (j + 5) - f (j + 1) + 2 := f_rec (j + 1)
  have r2 : (f (j + 8) : ℤ) = 6 * f (j + 4) - f j + 2 := f_rec j
  linarith

theorem a_small : a 1 = 1 ∧ a 2 = 4 ∧ a 3 = 6 ∧ a 4 = 11 ∧ a 5 = 20 ∧ a 6 = 33 ∧ a 7 = 43 ∧
    a 8 = 70 ∧ a 9 = 121 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a_eq 1 (by norm_num)]; decide
  · rw [a_eq 2 (by norm_num)]; decide
  · rw [a_eq 3 (by norm_num)]; decide
  · rw [a_eq 4 (by norm_num)]; decide
  · rw [a_eq 5 (by norm_num)]; decide
  · rw [a_eq 6 (by norm_num)]; decide
  · rw [a_eq 7 (by norm_num)]; decide
  · rw [a_eq 8 (by norm_num)]; decide
  · rw [a_eq 9 (by norm_num)]; decide

open PowerSeries in
theorem gf1 : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((X - 1) * (X ^ 4 + 2 * X ^ 2 - 1) * (X ^ 4 - 2 * X ^ 2 - 1)) =
        X * (-1 - 3 * X - 2 * X ^ 2 - 5 * X ^ 3 - 3 * X ^ 4 + 5 * X ^ 5 + 2 * X ^ 6 +
          3 * X ^ 7 + 2 * X ^ 8) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have hc : ∀ n, coeff n A = if n = 0 then (0 : ℚ) else (a n : ℚ) := fun n => coeff_mk _ _
  have h6 : (6 : ℚ⟦X⟧) = C 6 := (map_ofNat C 6).symm
  have h5 : (5 : ℚ⟦X⟧) = C 5 := (map_ofNat C 5).symm
  have h3 : (3 : ℚ⟦X⟧) = C 3 := (map_ofNat C 3).symm
  have h2 : (2 : ℚ⟦X⟧) = C 2 := (map_ofNat C 2).symm
  have eL : A * ((X - 1) * (X ^ 4 + 2 * X ^ 2 - 1) * (X ^ 4 - 2 * X ^ 2 - 1)) =
      X ^ 9 * A - X ^ 8 * A - C 6 * (X ^ 5 * A) + C 6 * (X ^ 4 * A) + X ^ 1 * A - A := by
    rw [← h6]; ring
  have eR : (X : ℚ⟦X⟧) * (-1 - 3 * X - 2 * X ^ 2 - 5 * X ^ 3 - 3 * X ^ 4 + 5 * X ^ 5 +
      2 * X ^ 6 + 3 * X ^ 7 + 2 * X ^ 8) =
      C 2 * X ^ 9 + C 3 * X ^ 8 + C 2 * X ^ 7 + C 5 * X ^ 6 - C 3 * X ^ 5 - C 5 * X ^ 4 -
        C 2 * X ^ 3 - C 3 * X ^ 2 - X ^ 1 := by
    rw [← h2, ← h3, ← h5]; ring
  rw [eL, eR]
  ext n
  simp only [map_add, map_sub, coeff_X_pow_mul', coeff_C_mul, coeff_X_pow]
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := a_small
  rcases (show n < 10 ∨ 10 ≤ n by omega) with hn | hn
  · interval_cases n <;> simp [hc, a1, a2, a3, a4, a5, a6, a7, a8, a9] <;> norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 10 := ⟨n - 10, by omega⟩
    have r := rec_part (j + 10) (by omega)
    have r' : ((a (j + 10) : ℤ) : ℚ) = ((a (j + 10 - 1) + 6 * a (j + 10 - 4) - 6 * a (j + 10 - 5) -
        a (j + 10 - 8) + a (j + 10 - 9) : ℤ) : ℚ) := by rw [r]
    push_cast at r'
    simp only [hc, if_pos (show 9 ≤ j + 10 by omega), if_pos (show 8 ≤ j + 10 by omega),
      if_pos (show 5 ≤ j + 10 by omega), if_pos (show 4 ≤ j + 10 by omega),
      if_pos (show 1 ≤ j + 10 by omega),
      show j + 10 - 9 = j + 1 by omega, show j + 10 - 8 = j + 2 by omega,
      show j + 10 - 5 = j + 5 by omega, show j + 10 - 4 = j + 6 by omega,
      show j + 10 - 1 = j + 9 by omega,
      if_neg (show j + 1 ≠ 0 by omega), if_neg (show j + 2 ≠ 0 by omega),
      if_neg (show j + 5 ≠ 0 by omega), if_neg (show j + 6 ≠ 0 by omega),
      if_neg (show j + 9 ≠ 0 by omega), if_neg (show j + 10 ≠ 0 by omega),
      if_neg (show j + 10 ≠ 9 by omega), if_neg (show j + 10 ≠ 8 by omega),
      if_neg (show j + 10 ≠ 7 by omega), if_neg (show j + 10 ≠ 6 by omega),
      if_neg (show j + 10 ≠ 5 by omega), if_neg (show j + 10 ≠ 4 by omega),
      if_neg (show j + 10 ≠ 3 by omega), if_neg (show j + 10 ≠ 2 by omega),
      if_neg (show j + 10 ≠ 1 by omega)]
    linarith

open PowerSeries in
theorem gf2 : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
      C (1 / 2 : ℚ) * (4 + (7 + 4 * X + 16 * X ^ 2 + 11 * X ^ 3) * (X ^ 4 - 2 * X ^ 2 - 1)⁻¹ +
        (X - 1)⁻¹ + (-4 - 7 * X - 3 * X ^ 2 - 2 * X ^ 3) * (X ^ 4 + 2 * X ^ 2 - 1)⁻¹) := by
  have hg := gf1
  have c1 : constantCoeff (X ^ 4 - 2 * X ^ 2 - 1 : ℚ⟦X⟧) ≠ 0 := by simp
  have c2 : constantCoeff (X ^ 4 + 2 * X ^ 2 - 1 : ℚ⟦X⟧) ≠ 0 := by simp
  have c3 : constantCoeff (X - 1 : ℚ⟦X⟧) ≠ 0 := by simp
  have h1 := PowerSeries.mul_inv_cancel _ c1
  have h2 := PowerSeries.mul_inv_cancel _ c2
  have h3 := PowerSeries.mul_inv_cancel _ c3
  have hD : ((X - 1) * (X ^ 4 + 2 * X ^ 2 - 1) * (X ^ 4 - 2 * X ^ 2 - 1) : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    simp at this
  have hC : C (1 / 2 : ℚ) * 2 = 1 := by
    rw [show (2 : ℚ⟦X⟧) = C 2 from (map_ofNat C 2).symm, ← map_mul]
    norm_num
  apply mul_right_cancel₀ hD
  rw [hg]
  generalize (X ^ 4 - 2 * X ^ 2 - 1 : ℚ⟦X⟧)⁻¹ = I1 at h1 ⊢
  generalize (X ^ 4 + 2 * X ^ 2 - 1 : ℚ⟦X⟧)⁻¹ = I2 at h2 ⊢
  generalize (X - 1 : ℚ⟦X⟧)⁻¹ = I3 at h3 ⊢
  generalize C (1 / 2 : ℚ) = H at hC ⊢
  linear_combination (-(H * (7 + 4 * X + 16 * X ^ 2 + 11 * X ^ 3) * (X - 1) *
      (X ^ 4 + 2 * X ^ 2 - 1))) * h1 -
    H * (X ^ 4 + 2 * X ^ 2 - 1) * (X ^ 4 - 2 * X ^ 2 - 1) * h3 -
    H * (-4 - 7 * X - 3 * X ^ 2 - 2 * X ^ 3) * (X - 1) * (X ^ 4 - 2 * X ^ 2 - 1) * h2 -
    X * (-1 - 3 * X - 2 * X ^ 2 - 5 * X ^ 3 - 3 * X ^ 4 + 5 * X ^ 5 + 2 * X ^ 6 +
          3 * X ^ 7 + 2 * X ^ 8) * hC

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a154145.main :=
  ⟨OMA.Helpers.rec_part, OMA.Helpers.gf1, OMA.Helpers.gf2⟩
