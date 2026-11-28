import OMAStatements.S_oeis_a269538
import Mathlib

/-!
Proof of Barker's conjectures for A269538.

An array of length 4 is good iff its entries a b c d satisfy: not a = b = c, not b = c = d,
and if a = b and c = d then a and c differ by one. Counting over b, c first gives
a n = n^4 + 4 n^3 + 3 n^2 + 2 n, from which the recurrence and the g.f. follow.
-/

namespace OMA.Helpers

open OMA.S_oeis_a269538 Finset

/-- Two values differ by exactly one. -/
def adj269538 {n : ℕ} (p c : Fin (n + 1)) : Prop := (c : ℕ) = (p : ℕ) + 1 ∨ (p : ℕ) = (c : ℕ) + 1

instance {n : ℕ} (p c : Fin (n + 1)) : Decidable (adj269538 p c) := by
  unfold adj269538; infer_instance

/-- The goodness condition written on the four entries. -/
def P269538 {n : ℕ} (a b c d : Fin (n + 1)) : Prop :=
  ¬ (a = b ∧ b = c) ∧ ¬ (b = c ∧ c = d) ∧ (a = b → c = d → adj269538 a c)

instance {n : ℕ} (a b c d : Fin (n + 1)) : Decidable (P269538 a b c d) := by
  unfold P269538; infer_instance

theorem reps269538_four {n : ℕ} (x : Fin 4 → Fin (n + 1)) :
    reps x = (if x 0 = x 1 then [x 0] else []) ++
      ((if x 1 = x 2 then [x 1] else []) ++ (if x 2 = x 3 then [x 2] else [])) := by
  unfold reps
  rw [show List.finRange 3 = [0, 1, 2] by decide]
  simp only [List.filterMap_cons, List.filterMap_nil]
  have e0 : (Fin.castSucc (0 : Fin 3) : Fin 4) = 0 := rfl
  have e1 : (Fin.castSucc (1 : Fin 3) : Fin 4) = 1 := rfl
  have e2 : (Fin.castSucc (2 : Fin 3) : Fin 4) = 2 := rfl
  have f0 : (Fin.succ (0 : Fin 3) : Fin 4) = 1 := rfl
  have f1 : (Fin.succ (1 : Fin 3) : Fin 4) = 2 := rfl
  have f2 : (Fin.succ (2 : Fin 3) : Fin 4) = 3 := rfl
  rw [e0, e1, e2, f0, f1, f2]
  split_ifs <;> rfl

theorem good269538_iff {n : ℕ} (x : Fin 4 → Fin (n + 1)) :
    good x ↔ P269538 (x 0) (x 1) (x 2) (x 3) := by
  unfold good P269538 adj269538
  rw [reps269538_four]
  split_ifs <;>
    simp only [List.cons_append, List.nil_append, List.isChain_cons_cons,
      List.isChain_singleton, List.isChain_nil] <;>
    simp only [Fin.ext_iff, and_true, true_iff] at * <;> omega

theorem sum_cons269538 {α : Type*} [Fintype α] {k : ℕ} (f : (Fin (k + 1) → α) → ℤ) :
    ∑ x, f x = ∑ a, ∑ y : Fin k → α, f (Fin.cons a y) := by
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => α).symm _ (fun p => f (Fin.cons p.1 p.2))
    (fun A => by simp), Fintype.sum_prod_type]

theorem pointwise269538 {n : ℕ} (a b c d : Fin (n + 1)) :
    (if P269538 a b c d then (1 : ℤ) else 0) =
      if b = c then (if a = b then 0 else 1) * (if d = b then 0 else 1)
      else 1 - (if a = b then 1 else 0) * ((if d = c then 1 else 0) *
        (if adj269538 b c then 0 else 1)) := by
  unfold P269538
  by_cases hbc : b = c
  · subst hbc
    by_cases hab : a = b <;> by_cases hdb : d = b <;> simp [hab, hdb] <;>
      exact fun h => hdb h.symm
  · by_cases hab : a = b <;> by_cases hdc : d = c <;> by_cases hadj : adj269538 b c <;>
      simp_all <;> intro h <;> exact absurd h.symm hdc

theorem ne_count269538 {n : ℕ} (b : Fin (n + 1)) :
    ∑ a : Fin (n + 1), (if a = b then (0 : ℤ) else 1) = n := by
  have h : ∀ a : Fin (n + 1), (if a = b then (0 : ℤ) else 1) = 1 - if a = b then 1 else 0 := by
    intro a; split_ifs <;> simp
  simp only [h, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  push_cast; ring

theorem inner269538 {n : ℕ} (b c : Fin (n + 1)) :
    ∑ a : Fin (n + 1), ∑ d : Fin (n + 1), (if P269538 a b c d then (1 : ℤ) else 0) =
      (n : ℤ) ^ 2 * (if b = c then 1 else 0) + ((n + 1) ^ 2 - 1) * (if b = c then 0 else 1) +
        (if adj269538 b c then 1 else 0) := by
  simp only [pointwise269538]
  by_cases hbc : b = c
  · subst hbc
    have hadj : ¬ adj269538 b b := by unfold adj269538; omega
    simp only [if_true, if_neg hadj, ← Finset.sum_mul, ← Finset.mul_sum, ne_count269538]
    ring
  · simp only [if_neg hbc]
    rw [Finset.sum_comm]
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp only [← Finset.mul_sum]
    by_cases hadj : adj269538 b c <;> simp [hadj] <;> ring

theorem ind_val269538 {n : ℕ} (k : ℕ) :
    ∑ c : Fin (n + 1), (if (c : ℕ) = k then (1 : ℤ) else 0) = if k < n + 1 then 1 else 0 := by
  split_ifs with hk
  · rw [Finset.sum_eq_single ⟨k, hk⟩]
    · simp
    · intro c _ hc
      rw [if_neg]
      intro h; exact hc (Fin.ext h)
    · simp
  · apply Finset.sum_eq_zero
    intro c _
    rw [if_neg]
    have := c.isLt; omega

theorem last_count269538 (n : ℕ) :
    ∑ b : Fin (n + 1), (if (b : ℕ) + 1 < n + 1 then (1 : ℤ) else 0) = n := by
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ i : Fin n, (if ((Fin.castSucc i : Fin (n + 1)) : ℕ) + 1 < n + 1 then (1 : ℤ)
      else 0) = 1 := by
    intro i; rw [if_pos]; simp only [Fin.val_castSucc]; omega
  simp only [h1, Fin.val_last, lt_irrefl, if_false, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, add_zero]
  simp

theorem adj_sum269538 (n : ℕ) :
    ∑ b : Fin (n + 1), ∑ c : Fin (n + 1), (if adj269538 b c then (1 : ℤ) else 0) = 2 * n := by
  have h : ∀ b c : Fin (n + 1), (if adj269538 b c then (1 : ℤ) else 0) =
      (if (c : ℕ) = (b : ℕ) + 1 then 1 else 0) + (if (b : ℕ) = (c : ℕ) + 1 then 1 else 0) := by
    intro b c
    unfold adj269538
    split_ifs <;> omega
  simp only [h, Finset.sum_add_distrib]
  have hs : (∑ b : Fin (n + 1), ∑ c : Fin (n + 1), if (b : ℕ) = (c : ℕ) + 1 then (1 : ℤ) else 0)
      = ∑ c : Fin (n + 1), ∑ b : Fin (n + 1), if (b : ℕ) = (c : ℕ) + 1 then (1 : ℤ) else 0 :=
    Finset.sum_comm
  rw [hs]
  simp only [ind_val269538, last_count269538]
  ring

theorem closed269538 (n : ℕ) : (a n : ℤ) = n ^ 4 + 4 * n ^ 3 + 3 * n ^ 2 + 2 * n := by
  have h1 : (a n : ℤ) = ∑ x : Fin 4 → Fin (n + 1), if good x then 1 else 0 := by
    unfold a
    rw [Finset.card_filter]
    push_cast
    rfl
  have h2 : (∑ x : Fin 4 → Fin (n + 1), if good x then (1 : ℤ) else 0) =
      ∑ a : Fin (n + 1), ∑ b : Fin (n + 1), ∑ c : Fin (n + 1), ∑ d : Fin (n + 1),
        if P269538 a b c d then 1 else 0 := by
    rw [sum_cons269538]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sum_cons269538]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [sum_cons269538]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sum_cons269538]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Fintype.sum_unique]
    exact if_congr (good269538_iff _) rfl rfl
  rw [h1, h2, Finset.sum_comm]
  have h3 : ∀ b : Fin (n + 1), (∑ a : Fin (n + 1), ∑ c : Fin (n + 1), ∑ d : Fin (n + 1),
      if P269538 a b c d then (1 : ℤ) else 0) =
      ∑ c : Fin (n + 1), ((n : ℤ) ^ 2 * (if b = c then 1 else 0) +
        ((n + 1) ^ 2 - 1) * (if b = c then 0 else 1) + (if adj269538 b c then 1 else 0)) := by
    intro b
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => inner269538 b c
  simp only [h3, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  have h4 : ∀ b : Fin (n + 1), ∑ c : Fin (n + 1), (if b = c then (0 : ℤ) else 1) = n := by
    intro b
    rw [← ne_count269538 b]
    exact Finset.sum_congr rfl fun c _ => by simp only [eq_comm]
  simp only [h4, adj_sum269538, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  ring

theorem rec269538 (n : ℕ) (hn : 5 < n) : (a n : ℤ) =
    5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  rw [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega,
    show k + 5 - 5 = k by omega]
  simp only [closed269538]
  push_cast
  ring

open PowerSeries in
theorem gf_generic269538 (f : ℕ → ℚ)
    (hf : ∀ n, f n = (n : ℚ) ^ 4 + 4 * n ^ 3 + 3 * n ^ 2 + 2 * n) :
    PowerSeries.mk f * (1 - X) ^ 5 = 2 * X * (1 + X) * (5 + 2 * X - X ^ 2) := by
  have key : PowerSeries.mk f * (1 - X) ^ 5 =
      C 1 * (PowerSeries.mk f * X ^ 0) - C 5 * (PowerSeries.mk f * X ^ 1) +
      C 10 * (PowerSeries.mk f * X ^ 2) - C 10 * (PowerSeries.mk f * X ^ 3) +
      C 5 * (PowerSeries.mk f * X ^ 4) - C 1 * (PowerSeries.mk f * X ^ 5) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (2 : ℚ⟦X⟧) * X * (1 + X) * (5 + 2 * X - X ^ 2) =
      C 10 * X ^ 1 + C 14 * X ^ 2 + C 2 * X ^ 3 - C 2 * X ^ 4 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 5
  · interval_cases k <;> norm_num [hf]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
    simp only [show 0 ≤ j + 5 by omega, show 1 ≤ j + 5 by omega, show 2 ≤ j + 5 by omega,
      show 3 ≤ j + 5 by omega, show 4 ≤ j + 5 by omega, show 5 ≤ j + 5 by omega,
      show j + 5 - 0 = j + 5 by omega, show j + 5 - 1 = j + 4 by omega,
      show j + 5 - 2 = j + 3 by omega, show j + 5 - 3 = j + 2 by omega,
      show j + 5 - 4 = j + 1 by omega, show j + 5 - 5 = j by omega,
      show ¬ (j + 5 = 1) by omega, show ¬ (j + 5 = 2) by omega, show ¬ (j + 5 = 3) by omega,
      show ¬ (j + 5 = 4) by omega, if_true, if_false, hf]
    push_cast
    ring

open PowerSeries in
theorem gf269538 :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      2 * X * (1 + X) * (5 + 2 * X - X ^ 2) := by
  apply gf_generic269538
  intro n
  have h := closed269538 n
  have hQ : (a n : ℚ) = (n : ℚ) ^ 4 + 4 * n ^ 3 + 3 * n ^ 2 + 2 * n := by exact_mod_cast h
  split_ifs with hn
  · subst hn; simp
  · exact hQ

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a269538.main :=
  ⟨OMA.Helpers.gf269538, OMA.Helpers.rec269538⟩
