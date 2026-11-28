import OMAStatements.S_oeis_a127710
import Mathlib

namespace OMA.Helpers

open Matrix Finset

theorem a127710_two_mul (x : ℕ) (hx : x ≠ 0) :
    padicValNat 2 (2 * x) = 1 + padicValNat 2 x := by
  rw [padicValNat.mul (by norm_num) hx, padicValNat.self (by norm_num)]

/-- `G n = ∑_{⌈n/2⌉ ≤ k ≤ n} ν₂(2(k+1))`. -/
def a127710_G (n : ℕ) : ℕ :=
  ∑ k ∈ Ico ((n + 1) / 2) (n + 1), padicValNat 2 (2 * (k + 1))

theorem a127710_G_step (n : ℕ) : a127710_G (n + 1) = a127710_G n + 1 := by
  rcases Nat.even_or_odd' n with ⟨t, rfl | rfl⟩
  · -- n = 2t
    have e1 : (2 * t + 1 + 1) / 2 = t + 1 := by omega
    have e0 : (2 * t + 1) / 2 = t := by omega
    unfold a127710_G
    rw [e1, e0]
    have h1 : ∑ k ∈ Ico t (2 * t + 1 + 1), padicValNat 2 (2 * (k + 1)) =
        padicValNat 2 (2 * (t + 1)) +
          ∑ k ∈ Ico (t + 1) (2 * t + 1 + 1), padicValNat 2 (2 * (k + 1)) :=
      Finset.sum_eq_sum_Ico_succ_bot (by omega) _
    have h2 : ∑ k ∈ Ico t (2 * t + 1 + 1), padicValNat 2 (2 * (k + 1)) =
        ∑ k ∈ Ico t (2 * t + 1), padicValNat 2 (2 * (k + 1)) +
          padicValNat 2 (2 * (2 * t + 1 + 1)) :=
      Finset.sum_Ico_succ_top (by omega) _
    have h3 : padicValNat 2 (2 * (2 * t + 1 + 1)) = 1 + padicValNat 2 (2 * (t + 1)) := by
      have : 2 * (2 * t + 1 + 1) = 2 * (2 * (t + 1)) := by ring
      rw [this, a127710_two_mul _ (by omega)]
    omega
  · -- n = 2t+1
    have e1 : (2 * t + 1 + 1 + 1) / 2 = t + 1 := by omega
    have e0 : (2 * t + 1 + 1) / 2 = t + 1 := by omega
    unfold a127710_G
    rw [e1, e0]
    have h2 : ∑ k ∈ Ico (t + 1) (2 * t + 1 + 1 + 1), padicValNat 2 (2 * (k + 1)) =
        ∑ k ∈ Ico (t + 1) (2 * t + 1 + 1), padicValNat 2 (2 * (k + 1)) +
          padicValNat 2 (2 * (2 * t + 1 + 1 + 1)) :=
      Finset.sum_Ico_succ_top (by omega) _
    have h3 : padicValNat 2 (2 * (2 * t + 1 + 1 + 1)) = 1 := by
      rw [a127710_two_mul _ (by omega), padicValNat.eq_zero_of_not_dvd (by omega)]
    omega

theorem a127710_G_eq (n : ℕ) : a127710_G n = n + 1 := by
  induction n with
  | zero =>
    show ∑ k ∈ Ico 0 1, padicValNat 2 (2 * (k + 1)) = 1
    rw [Finset.sum_Ico_succ_top (le_refl 0), Finset.Ico_self, Finset.sum_empty]
    simp
  | succ n ih => rw [a127710_G_step, ih]

/-- The 0/1 integer matrix `B(n,k) = [k ≤ n ≤ 2k]`. -/
def a127710_Bz (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℤ :=
  fun n k => if (k : ℕ) ≤ n ∧ (n : ℕ) ≤ 2 * k then 1 else 0

def a127710_Bq (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ :=
  (a127710_Bz N).map (Int.castRingHom ℚ)

theorem a127710_Bq_apply (N : ℕ) (n k : Fin (N + 1)) :
    a127710_Bq N n k = if (k : ℕ) ≤ n ∧ (n : ℕ) ≤ 2 * k then 1 else 0 := by
  unfold a127710_Bq
  rw [Matrix.map_apply]
  unfold a127710_Bz
  split_ifs <;> simp

theorem a127710_det (N : ℕ) : (a127710_Bq N).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · apply Finset.prod_eq_one
    intro i _
    rw [a127710_Bq_apply, if_pos (by omega)]
  · intro i j hij
    rw [a127710_Bq_apply, if_neg]
    have h1 : i < j := hij
    have h2 : (i : ℕ) < j := h1
    omega

theorem a127710_inv_Bq (N : ℕ) :
    (a127710_Bq N)⁻¹ = (Int.castRingHom ℚ).mapMatrix (a127710_Bz N).adjugate := by
  rw [Matrix.inv_def, a127710_det, Ring.inverse_one, one_smul, a127710_Bq,
    ← RingHom.mapMatrix_apply, RingHom.map_adjugate]

theorem a127710_tri_eq (N : ℕ) :
    OMA.S_oeis_a127710.tri N =
      Matrix.diagonal (fun n : Fin (N + 1) => 1 / (((n : ℕ) : ℚ) + 1)) * a127710_Bq N := by
  ext n k
  rw [Matrix.diagonal_mul, a127710_Bq_apply]
  unfold OMA.S_oeis_a127710.tri
  split_ifs <;> simp

theorem a127710_inv_tri (N : ℕ) :
    (OMA.S_oeis_a127710.tri N)⁻¹ =
      (a127710_Bq N)⁻¹ * Matrix.diagonal (fun n : Fin (N + 1) => ((n : ℕ) : ℚ) + 1) := by
  apply Matrix.inv_eq_left_inv
  rw [a127710_tri_eq, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal _),
    Matrix.diagonal_mul_diagonal]
  have : (fun n : Fin (N + 1) => (((n : ℕ) : ℚ) + 1) * (1 / (((n : ℕ) : ℚ) + 1))) =
      fun _ => 1 := by
    funext n
    have : (((n : ℕ) : ℚ) + 1) ≠ 0 := by positivity
    field_simp
  rw [this, Matrix.diagonal_one, Matrix.one_mul]
  exact Matrix.nonsing_inv_mul _ (by rw [a127710_det]; exact isUnit_one)

theorem a127710_mulVec (N : ℕ) :
    a127710_Bq N *ᵥ (fun k : Fin (N + 1) => ((OMA.S_oeis_a127710.ruler ((k : ℕ) + 1) : ℕ) : ℚ)) =
      fun n : Fin (N + 1) => ((n : ℕ) : ℚ) + 1 := by
  funext n
  simp only [Matrix.mulVec, dotProduct, a127710_Bq_apply, ite_mul, one_mul, zero_mul]
  have hn : (n : ℕ) ≤ N := Nat.lt_succ_iff.mp n.isLt
  rw [Fin.sum_univ_eq_sum_range
    (fun k => if k ≤ (n : ℕ) ∧ (n : ℕ) ≤ 2 * k then
      ((OMA.S_oeis_a127710.ruler (k + 1) : ℕ) : ℚ) else 0) (N + 1)]
  rw [← Finset.sum_filter]
  have hf : (range (N + 1)).filter (fun k => k ≤ (n : ℕ) ∧ (n : ℕ) ≤ 2 * k) =
      Ico (((n : ℕ) + 1) / 2) ((n : ℕ) + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hf]
  have := a127710_G_eq n
  unfold a127710_G at this
  unfold OMA.S_oeis_a127710.ruler
  rw [← Nat.cast_sum, this]
  push_cast
  ring

theorem a127710_main : ∀ N : ℕ,
    (∀ n k : Fin (N + 1), ∃ z : ℤ, (OMA.S_oeis_a127710.tri N)⁻¹ n k = z) ∧
    (∀ n : Fin (N + 1), ∑ k, (OMA.S_oeis_a127710.tri N)⁻¹ n k =
      ((OMA.S_oeis_a127710.ruler ((n : ℕ) + 1) : ℕ) : ℚ)) := by
  intro N
  rw [a127710_inv_tri]
  constructor
  · intro n k
    refine ⟨(a127710_Bz N).adjugate n k * ((k : ℕ) + 1), ?_⟩
    rw [Matrix.mul_diagonal, a127710_inv_Bq]
    simp
  · intro n
    simp only [Matrix.mul_diagonal]
    have h := congrFun (congrArg (fun v => (a127710_Bq N)⁻¹ *ᵥ v) (a127710_mulVec N)) n
    simp only [Matrix.mulVec_mulVec] at h
    rw [Matrix.nonsing_inv_mul _ (by rw [a127710_det]; exact isUnit_one),
      Matrix.one_mulVec] at h
    rw [h]
    rfl

end OMA.Helpers

/-- Every entry of the inverse triangle is an integer (the inverse is `B⁻¹ · diag(k+1)` with `B`
an integer unitriangular matrix), and its rows sum to the ruler function. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a127710.main :=
  OMA.Helpers.a127710_main
