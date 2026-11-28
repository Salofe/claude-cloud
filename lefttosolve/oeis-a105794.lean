import OMAStatements.S_oeis_a105794
import Mathlib

namespace OMA.Helpers

open Polynomial OMA.S_oeis_a105794

/-- The falling factorial of `x + 1` with `k` factors. -/
noncomputable abbrev E (k : ℕ) : ℚ[X] := (descPochhammer ℚ k).comp (X + 1)

theorem natDegree_X_add_one' : (X + 1 : ℚ[X]).natDegree = 1 := by
  simpa using natDegree_X_add_C (1 : ℚ)

theorem E_natDegree (k : ℕ) : (E k).natDegree = k := by
  rw [E, natDegree_comp, descPochhammer_natDegree, natDegree_X_add_one', mul_one]

theorem E_coeff_self (k : ℕ) : (E k).coeff k = 1 := by
  have hm : (E k).Monic := (monic_descPochhammer ℚ k).comp (monic_X_add_C 1)
    (by rw [natDegree_X_add_one']; exact one_ne_zero)
  have := hm.leadingCoeff
  rw [leadingCoeff, E_natDegree] at this
  exact this

theorem E_coeff_gt {n k : ℕ} (h : n < k) : (E n).coeff k = 0 :=
  coeff_eq_zero_of_natDegree_lt (by rw [E_natDegree]; exact h)

theorem A_eq (n k : ℕ) : A105793 n k = (E n).coeff k := rfl

/-- The recursively defined inverse. -/
noncomputable def Tr : ℕ → ℕ → ℚ
  | n, k => (if n = k then 1 else 0) - ∑ j : Fin n, A105793 n j * Tr j k
termination_by n => n
decreasing_by exact j.2

theorem Tr_isInverse : IsInverse Tr := by
  intro n k
  rw [Finset.sum_range_succ, A_eq n n, E_coeff_self, one_mul]
  conv_lhs => rw [Tr]
  rw [Fin.sum_univ_eq_sum_range (fun j => A105793 n j * Tr j k) n]
  ring

/-- From a right inverse to a left inverse, for each truncation. -/
theorem left_inv (T : ℕ → ℕ → ℚ) (hT : IsInverse T) (n i k : ℕ) (hi : i ≤ n) (hk : k ≤ n) :
    ∑ j ∈ Finset.range (n + 1), T i j * A105793 j k = if i = k then 1 else 0 := by
  let M1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ := Matrix.of fun a b => A105793 a b
  let M2 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ := Matrix.of fun a b => T a b
  have h12 : M1 * M2 = 1 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [M1, M2, Matrix.of_apply]
    rw [Fin.sum_univ_eq_sum_range (fun j => A105793 a j * T j b) (n + 1)]
    have hsub : Finset.range (a + 1) ⊆ Finset.range (n + 1) := by
      intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
    rw [← Finset.sum_subset hsub, hT a b]
    · simp only [Fin.ext_iff]
    · intro x _ hx
      simp only [Finset.mem_range, not_lt] at hx
      rw [A_eq, E_coeff_gt (by omega), zero_mul]
  have h21 : M2 * M1 = 1 := mul_eq_one_comm.1 h12
  have := congrFun (congrFun h21 ⟨i, by omega⟩) ⟨k, by omega⟩
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  simp only [M1, M2, Matrix.of_apply, Fin.ext_iff] at this
  rw [Fin.sum_univ_eq_sum_range (fun j => T i j * A105793 j k) (n + 1)] at this
  exact this

theorem poly_id (T : ℕ → ℕ → ℚ) (hT : IsInverse T) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), C (T n j) * E j = X ^ n := by
  ext k
  rw [finsetSum_coeff, coeff_X_pow]
  simp only [coeff_C_mul]
  rcases Nat.lt_or_ge n k with h | h
  · rw [if_neg (by omega)]
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [E_coeff_gt (by omega), mul_zero]
  · have := left_inv T hT n n k le_rfl h
    simp only [A_eq] at this
    rw [this]
    by_cases hnk : n = k
    · rw [if_pos hnk, if_pos hnk.symm]
    · rw [if_neg hnk, if_neg (Ne.symm hnk)]


theorem fact_ratio (k m : ℕ) :
    ((k + m).factorial : ℚ) / m.factorial = (ascPochhammer ℚ k).eval ((m : ℚ) + 1) := by
  have h := ascPochhammer_nat_eq_natCast_ascFactorial ℚ (m + 1) k
  push_cast at h
  rw [h, add_comm k m, ← Nat.factorial_mul_ascFactorial, Nat.cast_mul,
    mul_div_cancel_left₀ _ (by exact_mod_cast (Nat.factorial_pos m).ne')]

theorem D_eval_neg (k : ℕ) (r : ℚ) :
    (descPochhammer ℚ k).eval (-r) = (-1) ^ k * (ascPochhammer ℚ k).eval r := by
  have h := ascPochhammer_eval_neg_eq_descPochhammer ℚ (-r) k
  rw [neg_neg] at h
  rw [h, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

theorem neg_one_pow_sub {n k : ℕ} (hk : k ≤ n) :
    (-1 : ℚ) ^ (n - k) = (-1) ^ n * (-1) ^ k := by
  rw [show (-1 : ℚ) ^ n = (-1) ^ (n - k) * (-1) ^ k by rw [← pow_add, Nat.sub_add_cancel hk]]
  rw [mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]

/-- The Bernoulli functional `X ^ j ↦ B_j`. -/
noncomputable def β : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum (fun j => (_root_.bernoulli j) • (LinearMap.id : ℚ →ₗ[ℚ] ℚ))

theorem β_apply (p : ℚ[X]) : β p = p.sum (fun j c => _root_.bernoulli j * c) := by
  simp [β, lsum_apply]

theorem β_monomial (n : ℕ) (c : ℚ) : β (monomial n c) = _root_.bernoulli n * c := by
  rw [β_apply, sum_monomial_index]
  simp

theorem β_X_pow (n : ℕ) : β (X ^ n) = _root_.bernoulli n := by
  rw [← monomial_one_right_eq_X_pow, β_monomial, mul_one]

theorem β_one : β 1 = 1 := by
  rw [← pow_zero (X : ℚ[X]), β_X_pow, _root_.bernoulli_zero]

theorem β_X_add_one_pow (n : ℕ) :
    β ((X + 1) ^ n) = _root_.bernoulli n + if n = 1 then 1 else 0 := by
  have hdeg : ((X + 1 : ℚ[X]) ^ n).natDegree < n + 1 := by
    have := natDegree_pow_le (p := (X + 1 : ℚ[X])) (n := n)
    rw [natDegree_X_add_one', mul_one] at this
    omega
  rw [β_apply, sum_over_range' _ (fun _ => mul_zero _) (n + 1) hdeg]
  simp only [coeff_X_add_one_pow]
  rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, mul_one]
  simp_rw [mul_comm (_root_.bernoulli _)]
  rw [_root_.sum_bernoulli]
  ring

theorem β_comp (p : ℚ[X]) : β (p.comp (X + 1)) = β p + p.coeff 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, map_add, map_add, hp, hq, coeff_add]; ring
  | monomial n c =>
    rw [monomial_comp, C_mul', map_smul, β_X_add_one_pow, β_monomial, coeff_monomial,
      smul_eq_mul]
    split_ifs <;> ring

theorem E_succ (k : ℕ) : E (k + 1) = (X + 1) * descPochhammer ℚ k := by
  have h : (X - 1 : ℚ[X]).comp (X + 1) = X := by
    rw [sub_comp, X_comp, one_comp]; ring
  rw [E, descPochhammer_succ_left, mul_comp, X_comp, comp_assoc, h, comp_X]

theorem D_succ_coeff_one (k : ℕ) :
    (descPochhammer ℚ (k + 1)).coeff 1 = (-1) ^ k * (k.factorial : ℚ) := by
  rw [descPochhammer_succ_left, show (1 : ℕ) = 0 + 1 from rfl, coeff_X_mul,
    coeff_zero_eq_eval_zero, eval_comp, eval_sub, eval_X, eval_one, zero_sub, D_eval_neg,
    ascPochhammer_eval_one]

theorem β_D (k : ℕ) :
    β (descPochhammer ℚ k) = (-1) ^ k * (k.factorial : ℚ) / ((k : ℚ) + 1) := by
  have h1 := β_comp (descPochhammer ℚ (k + 1))
  rw [← E, E_succ, D_succ_coeff_one, descPochhammer_succ_right] at h1
  have hpoly : (X + 1) * descPochhammer ℚ k =
      descPochhammer ℚ k * (X - (k : ℚ[X])) + C ((k : ℚ) + 1) * descPochhammer ℚ k := by
    rw [C_add, C_1, map_natCast]; ring
  rw [hpoly, map_add, C_mul', map_smul, smul_eq_mul] at h1
  have hk : (k : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  linarith

theorem β_E {k : ℕ} (hk : 1 ≤ k) :
    -β (E k) = (-1) ^ k * ((k - 1).factorial : ℚ) / ((k : ℚ) + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [E, β_comp, β_D, D_succ_coeff_one, Nat.add_sub_cancel, Nat.factorial_succ]
  have hj : (j : ℚ) + 1 + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem T_zero (T : ℕ → ℕ → ℚ) (hT : IsInverse T) (n : ℕ) : T n 0 = (-1) ^ n := by
  have hp := congrArg (eval (-1 : ℚ)) (poly_id T hT n)
  rw [eval_finsetSum] at hp
  simp only [eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_one, eval_pow, neg_add_cancel,
    descPochhammer_eval_zero] at hp
  rw [← hp, Finset.sum_eq_single 0]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; simp at h

end OMA.Helpers

open Polynomial OMA.S_oeis_a105794 OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a105794.main := by
  refine ⟨⟨Tr, Tr_isInverse⟩, fun T hT => ⟨?_, ?_⟩⟩
  · intro n m
    have hp := congrArg (eval (-(m : ℚ) - 2)) (poly_id T hT n)
    rw [eval_finsetSum] at hp
    simp only [eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_one, eval_pow] at hp
    rw [show -(m : ℚ) - 2 + 1 = -((m : ℚ) + 1) by ring] at hp
    simp only [D_eval_neg] at hp
    simp only [fact_ratio]
    calc ∑ k ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ (n - k) * T n k * (ascPochhammer ℚ k).eval ((m : ℚ) + 1)
        = (-1) ^ n * ∑ k ∈ Finset.range (n + 1),
            T n k * ((-1) ^ k * (ascPochhammer ℚ k).eval ((m : ℚ) + 1)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mem_range] at hk
          rw [neg_one_pow_sub (by omega)]
          ring
      _ = (-1) ^ n * (-(m : ℚ) - 2) ^ n := by rw [hp]
      _ = ((m : ℚ) + 2) ^ n := by rw [← mul_pow]; congr 1; ring
  · intro n
    have hB := congrArg β (poly_id T hT n)
    rw [map_sum, β_X_pow] at hB
    simp only [C_mul', map_smul, smul_eq_mul] at hB
    have hr : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
      ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hr, Finset.sum_insert (by simp), E, descPochhammer_zero, one_comp, β_one, mul_one,
      T_zero T hT n] at hB
    have hs : ∑ k ∈ Finset.Icc 1 n, (-1 : ℚ) ^ k * T n k * (((k - 1).factorial : ℚ) / ((k : ℚ) + 1))
        = - ∑ k ∈ Finset.Icc 1 n, T n k * β (E k) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [neg_mul_eq_mul_neg, β_E hk.1]
      ring
    rw [hs]
    linarith
