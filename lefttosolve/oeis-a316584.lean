import OMAStatements.S_oeis_a316584
import Mathlib

/-!
Proof of the conjecture of OEIS A316584: T(p,p) = p^2 for every prime p.

In characteristic p, (x - 1)^p = x^p - 1, so x^p = 1 iff N = x - 1 is nilpotent. A nilpotent
2 x 2 matrix over a field satisfies N^2 = 0 (its determinant vanishes, so N^2 = t N by
Cayley-Hamilton, and N^p = t^(p-1) N). Conversely 1 + N is invertible with inverse 1 - N, so
x -> x - 1 is a bijection onto the matrices with N^2 = 0. These are the matrices [[a, b], [c, -a]]
with a^2 + b c = 0, and (a, b, c) -> (b, if b = 0 then c else a) is a bijection onto pairs, so
there are exactly p^2 of them.
-/

namespace OMA.Helpers

open OMA.S_oeis_a316584 Matrix

/-- Over a field, a 2 x 2 matrix squares to zero iff it has the shape [[a, b], [c, -a]] with
a^2 + b c = 0. -/
theorem sq_zero_iff {F : Type*} [Field F] (N : Matrix (Fin 2) (Fin 2) F) :
    N * N = 0 ↔ N 1 1 = - N 0 0 ∧ N 0 0 ^ 2 + N 0 1 * N 1 0 = 0 := by
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    have h10 := congrFun (congrFun h 1) 0
    have h11 := congrFun (congrFun h 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply] at h00 h01 h10 h11
    by_cases ht : N 0 0 + N 1 1 = 0
    · exact ⟨by linear_combination ht, by linear_combination h00⟩
    · exfalso
      have hb : N 0 1 = 0 := by
        have e : N 0 1 * (N 0 0 + N 1 1) = 0 := by linear_combination h01
        rcases mul_eq_zero.mp e with e | e
        · exact e
        · exact absurd e ht
      have hc : N 1 0 = 0 := by
        have e : N 1 0 * (N 0 0 + N 1 1) = 0 := by linear_combination h10
        rcases mul_eq_zero.mp e with e | e
        · exact e
        · exact absurd e ht
      have ha : N 0 0 = 0 := by
        have e : N 0 0 ^ 2 = 0 := by rw [hb] at h00; linear_combination h00
        exact pow_eq_zero_iff (two_ne_zero) |>.mp e
      have hd : N 1 1 = 0 := by
        have e : N 1 1 ^ 2 = 0 := by rw [hb] at h11; linear_combination h11
        exact pow_eq_zero_iff (two_ne_zero) |>.mp e
      exact ht (by rw [ha, hd]; ring)
  · rintro ⟨h1, h2⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two]; linear_combination h2
    · simp [Matrix.mul_apply, Fin.sum_univ_two]; linear_combination N 0 1 * h1
    · simp [Matrix.mul_apply, Fin.sum_univ_two]; linear_combination N 1 0 * h1
    · simp [Matrix.mul_apply, Fin.sum_univ_two]; linear_combination h2 + (N 1 1 - N 0 0) * h1

/-- Cayley-Hamilton for 2 x 2 matrices. -/
theorem cayley_two {F : Type*} [Field F] (N : Matrix (Fin 2) (Fin 2) F) :
    N * N = (N 0 0 + N 1 1) • N - (N 0 0 * N 1 1 - N 0 1 * N 1 0) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- A nilpotent 2 x 2 matrix over a field squares to zero. -/
theorem sq_zero_of_pow {F : Type*} [Field F] (N : Matrix (Fin 2) (Fin 2) F) (k : ℕ)
    (h : N ^ k = 0) : N * N = 0 := by
  have hdet : N 0 0 * N 1 1 - N 0 1 * N 1 0 = 0 := by
    have e : N.det ^ k = 0 := by rw [← Matrix.det_pow, h, Matrix.det_zero]
    rw [Matrix.det_fin_two] at e
    exact (pow_eq_zero_iff'.mp e).1
  have hk : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at h
    exact one_ne_zero h
  set t := N 0 0 + N 1 1 with ht
  have hsq : N * N = t • N := by rw [cayley_two, hdet, zero_smul, sub_zero]
  have hpow : ∀ j : ℕ, N ^ (j + 1) = t ^ j • N := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ih, smul_mul_assoc, hsq, smul_smul, pow_succ]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [hpow j] at h
  rcases smul_eq_zero.mp h with h' | h'
  · rw [hsq, (pow_eq_zero_iff'.mp h').1, zero_smul]
  · rw [h', zero_mul]

variable {p : ℕ} [Fact p.Prime]

/-- In GL(2, Z/p), x^p = 1 iff (x - 1)^2 = 0. -/
theorem pow_p_iff (x : GL (Fin 2) (ZMod p)) :
    x ^ p = 1 ↔ ((x : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) * ((x : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) = 0 := by
  have hp : (p.Prime) := Fact.out
  have key : ((x : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) ^ p
      = (x : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ p - 1 := by
    rw [sub_pow_char_of_commute p (Commute.one_right _), one_pow]
  constructor
  · intro hx
    apply sq_zero_of_pow _ p
    rw [key, ← Units.val_pow_eq_pow_val, hx, Units.val_one, sub_self]
  · intro hx
    have h2 : ((x : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) ^ p = 0 := by
      exact pow_eq_zero_of_le hp.two_le (by rw [pow_two]; exact hx)
    rw [key, sub_eq_zero, ← Units.val_pow_eq_pow_val] at h2
    exact Units.ext h2

/-- The bijection x ↦ x - 1 between the solutions of x^p = 1 and the matrices squaring to zero. -/
def E : {x : GL (Fin 2) (ZMod p) // x ^ p = 1} ≃
    {N : Matrix (Fin 2) (Fin 2) (ZMod p) // N * N = 0} where
  toFun x := ⟨(x.1 : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1, (pow_p_iff x.1).mp x.2⟩
  invFun N := ⟨⟨1 + N.1, 1 - N.1, by rw [add_mul, one_mul, mul_sub, mul_one, N.2]; abel,
      by rw [sub_mul, one_mul, mul_add, mul_one, N.2]; abel⟩,
    (pow_p_iff _).mpr (by simp only [add_sub_cancel_left]; exact N.2)⟩
  left_inv x := by
    apply Subtype.ext
    apply Units.ext
    simp
  right_inv N := by
    apply Subtype.ext
    simp

theorem card_sq_zero :
    Fintype.card {N : Matrix (Fin 2) (Fin 2) (ZMod p) // N * N = 0} = p ^ 2 := by
  rw [Fintype.card_subtype]
  have h1 : (Finset.univ.filter (fun N : Matrix (Fin 2) (Fin 2) (ZMod p) => N * N = 0)).card =
      (Finset.univ.filter (fun t : ZMod p × ZMod p × ZMod p => t.1 ^ 2 + t.2.1 * t.2.2 = 0)).card := by
    apply Finset.card_nbij' (fun N => (N 0 0, N 0 1, N 1 0)) (fun t => !![t.1, t.2.1; t.2.2, -t.1])
    · intro N hN
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hN ⊢
      exact ((sq_zero_iff N).mp hN).2
    · intro t ht
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
      rw [sq_zero_iff]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      exact ⟨by simp, by simpa using ht⟩
    · intro N hN
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hN
      have := ((sq_zero_iff N).mp hN).1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [this]
    · intro t _
      simp
  have h2 : (Finset.univ.filter (fun t : ZMod p × ZMod p × ZMod p => t.1 ^ 2 + t.2.1 * t.2.2 = 0)).card =
      (Finset.univ : Finset (ZMod p × ZMod p)).card := by
    apply Finset.card_nbij' (fun t => (t.2.1, if t.2.1 = 0 then t.2.2 else t.1))
      (fun u => if u.1 = 0 then (0, 0, u.2) else (u.2, u.1, -(u.2 ^ 2 / u.1)))
    · intro t _
      simp
    · intro u _
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      by_cases hu : u.1 = 0
      · simp [hu]
      · simp only [hu, if_false]
        field_simp
        ring
    · intro t ht
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht
      obtain ⟨a, b, c⟩ := t
      simp only at ht ⊢
      by_cases hb : b = 0
      · subst hb
        have ha : a = 0 := by
          have : a ^ 2 = 0 := by simpa using ht
          exact (pow_eq_zero_iff'.mp this).1
        simp [ha]
      · simp only [hb, if_false]
        have hc : c = -(a ^ 2 / b) := by
          field_simp
          linear_combination ht
        rw [hc]
    · intro u _
      obtain ⟨b, y⟩ := u
      by_cases hu : b = 0
      · subst hu; simp
      · simp [hu]
  rw [h1, h2, Finset.card_univ, Fintype.card_prod, ZMod.card]
  ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a316584.main := by
  intro p hp
  have := Fact.mk hp
  unfold OMA.S_oeis_a316584.T
  rw [Nat.card_congr OMA.Helpers.E, Nat.card_eq_fintype_card, OMA.Helpers.card_sq_zero]
