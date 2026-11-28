import OMAStatements.S_oeis_a176612
import Mathlib

-- Problem: A176612: Sequence defined by the recurrence formula a(n+1)=sum(a(p)*a(n-p)+k,p=0..n)+l for n>=1, with here a(0)=1, a(1)=2, k=1 and l=1.
-- Upstream: formal-conjectures statements/oeis-a176612.lean:0 (declaration OMA.S_oeis_a176612.main)
-- Credit: @Salofe (the owner of the agent is credited as the solver)
-- Proof: the g.f. A satisfies (1-x)^2 (x A^2 - A) + 1 - x (1-x)^2 = 0, so S = (1-x)(1-2xA) has
-- S^2 = E = 1 - 6x + 5x^2 - 8x^3 + 4x^4; differentiating gives 2 E S1 = E1 S (S1, E1 the derivatives),
-- whose coefficient of x^n is -4 times the conjectured recurrence, via s(k) = -2 a(k-1) + 2 a(k-2).

namespace OMA.Helpers

open PowerSeries OMA.S_oeis_a176612

theorem aList_succ (n : ℕ) : ∃ x, aList (n + 1) = aList n ++ [x] := by
  cases n with
  | zero => exact ⟨2, rfl⟩
  | succ n => exact ⟨_, rfl⟩

theorem aList_length (n : ℕ) : (aList n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨x, hx⟩ := aList_succ n
    rw [hx, List.length_append, ih]
    rfl

theorem aList_getD (n i : ℕ) (hi : i ≤ n) : (aList n).getD i 0 = a i := by
  induction n with
  | zero =>
    have : i = 0 := by omega
    subst this
    rfl
  | succ n ih =>
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · obtain ⟨x, hx⟩ := aList_succ n
      rw [hx, List.getD_append _ _ _ _ (by rw [aList_length]; exact h), ih (by omega)]
    · have : i = n + 1 := by omega
      subst this
      rfl

theorem a_zero : a 0 = 1 := rfl

theorem a_one : a 1 = 2 := rfl

theorem a_rec (n : ℕ) : a (n + 2) =
    ∑ p ∈ Finset.range (n + 2), a p * a (n + 1 - p) + ((n : ℤ) + 2) + 1 := by
  have h1 : a (n + 2) = (aList (n + 2)).getD (n + 2) 0 := rfl
  rw [h1, aList, List.getD_append_right _ _ _ _ (by rw [aList_length]),
    aList_length, Nat.sub_self]
  simp only [List.getD_cons_zero]
  congr 2
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_range] at hp
  rw [aList_getD _ _ (by omega), aList_getD _ _ (by omega)]

/-- The generating function of A176612. -/
noncomputable def A : PowerSeries ℤ := PowerSeries.mk a

/-- `X * A^2 - A`. -/
noncomputable def F : PowerSeries ℤ := X * A ^ 2 - A

theorem coeff_ofNat_mul (k : ℕ) [k.AtLeastTwo] (n : ℕ) (φ : PowerSeries ℤ) :
    coeff n ((no_index (OfNat.ofNat k) : PowerSeries ℤ) * φ) = (OfNat.ofNat k : ℤ) * coeff n φ := by
  rw [← map_ofNat (C (R := ℤ)) k, coeff_C_mul]

theorem coeff_F (n : ℕ) : coeff n F = -(if n = 1 then 1 else (n : ℤ) + 1) := by
  rcases n with _ | _ | n
  · simp [F, A, a_zero]
  · rw [F, map_sub, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul]
    simp [A, a_zero, a_one, pow_two, coeff_mul]
  · have e : coeff (n + 2) (X * A ^ 2) = ∑ p ∈ Finset.range (n + 2), a p * a (n + 1 - p) := by
      rw [coeff_succ_X_mul, pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp [A]
    rw [F, map_sub, e]
    simp only [A, coeff_mk]
    rw [a_rec]
    simp
    ring

theorem key :
    F - 2 * (X ^ 1 * F) + X ^ 2 * F + 1 - X ^ 1 + 2 * X ^ 2 - X ^ 3 = 0 := by
  ext n
  simp only [map_add, map_sub, coeff_ofNat_mul, coeff_X_pow_mul', coeff_one, coeff_X_pow, coeff_F,
    map_zero]
  match n with
  | 0 => norm_num
  | 1 => norm_num
  | 2 => norm_num
  | 3 => norm_num
  | n + 4 =>
    simp
    ring

/-- `(1 - X) * (1 - 2 X A)`, a square root of `E`. -/
noncomputable def S : PowerSeries ℤ := 1 - X - 2 * (X * A) + 2 * (X ^ 2 * A)

/-- `1 - 6x + 5x^2 - 8x^3 + 4x^4`. -/
noncomputable def E : PowerSeries ℤ := 1 - 6 * X + 5 * X ^ 2 - 8 * X ^ 3 + 4 * X ^ 4

theorem coeff_S (j : ℕ) (hj : 2 ≤ j) : coeff j S = -2 * a (j - 1) + 2 * a (j - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  have e1 : (X : PowerSeries ℤ) = X ^ 1 := (pow_one X).symm
  rw [S, e1]
  simp only [map_add, map_sub, coeff_ofNat_mul, coeff_X_pow_mul', coeff_one, coeff_X_pow]
  simp [A]

theorem S_sq : S ^ 2 = E := by
  have k2 := key
  simp only [F, pow_one] at k2
  rw [S, E]
  linear_combination (4 * X) * k2

theorem deriv_ofNat (k : ℕ) [k.AtLeastTwo] :
    d⁄dX ℤ (no_index (OfNat.ofNat k) : PowerSeries ℤ) = 0 := by
  have := Derivation.map_natCast (d⁄dX ℤ) (A := PowerSeries ℤ) k
  exact this

theorem deriv_E : d⁄dX ℤ E = -6 + 10 * X - 24 * X ^ 2 + 16 * X ^ 3 := by
  simp [E, deriv_ofNat]
  ring

theorem ode : 2 * E * d⁄dX ℤ S = d⁄dX ℤ E * S := by
  have h1 : d⁄dX ℤ (S ^ 2) = d⁄dX ℤ E := by rw [S_sq]
  rw [derivative_pow] at h1
  norm_num at h1
  linear_combination S * h1 + (-2 * d⁄dX ℤ S) * S_sq

theorem ode' : 2 * d⁄dX ℤ S - 12 * (X ^ 1 * d⁄dX ℤ S) + 10 * (X ^ 2 * d⁄dX ℤ S)
    - 16 * (X ^ 3 * d⁄dX ℤ S) + 8 * (X ^ 4 * d⁄dX ℤ S) =
    10 * (X ^ 1 * S) + 16 * (X ^ 3 * S) - 6 * S - 24 * (X ^ 2 * S) := by
  have h := ode
  rw [deriv_E, E] at h
  linear_combination h

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a176612.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have h := congrArg (PowerSeries.coeff (m + 5)) OMA.Helpers.ode'
  simp only [map_add, map_sub, OMA.Helpers.coeff_ofNat_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_derivative] at h
  simp at h
  simp only [show m + 5 + 1 = m + 6 by omega, show m + 4 + 1 = m + 5 by omega,
    show m + 3 + 1 = m + 4 by omega, show m + 2 + 1 = m + 3 by omega,
    show m + 1 + 1 = m + 2 by omega] at h
  rw [OMA.Helpers.coeff_S (m + 6) (by omega), OMA.Helpers.coeff_S (m + 5) (by omega),
    OMA.Helpers.coeff_S (m + 4) (by omega), OMA.Helpers.coeff_S (m + 3) (by omega),
    OMA.Helpers.coeff_S (m + 2) (by omega)] at h
  simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
    show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega] at h
  simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
    show m + 5 - 5 = m by omega]
  push_cast at h ⊢
  have h4 : 4 * (((m : ℤ) + 5 + 1) * OMA.S_oeis_a176612.a (m + 5)
      + (-7 * ((m : ℤ) + 5) + 2) * OMA.S_oeis_a176612.a (m + 4)
      + (11 * ((m : ℤ) + 5) - 13) * OMA.S_oeis_a176612.a (m + 3)
      + (-13 * ((m : ℤ) + 5) + 38) * OMA.S_oeis_a176612.a (m + 2)
      + 12 * (((m : ℤ) + 5) - 4) * OMA.S_oeis_a176612.a (m + 1)
      + 4 * (-((m : ℤ) + 5) + 5) * OMA.S_oeis_a176612.a m) = 0 := by
    linear_combination (-1 : ℤ) * h
  linarith
