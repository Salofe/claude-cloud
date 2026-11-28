import OMAStatements.S_mo_385518
import Mathlib

/-! Proof for mo-385518: reachability for convex mixtures of stochastic matrices. -/

namespace OMA.Helpers

open Matrix OMA.S_mo_385518

theorem mo385518_mem_hull_iff {n m : ℕ} (P : Fin m → Mat n) (M : Mat n) :
    M ∈ convexHull ℝ (Set.range P) ↔ ∃ p : Row m, Distribution p ∧ M = ∑ a, p a • P a := by
  classical
  constructor
  · intro hM
    let S : Set (Mat n) := {M | ∃ p : Row m, Distribution p ∧ M = ∑ a, p a • P a}
    have hsub : Set.range P ⊆ S := by
      rintro _ ⟨a, rfl⟩
      refine ⟨Pi.single a 1, ⟨fun i => ?_, ?_⟩, ?_⟩
      · by_cases h : i = a
        · subst h; simp
        · simp [h]
      · simp
      · simp [Pi.single_apply]
    have hconv : Convex ℝ S := by
      rintro _ ⟨p, ⟨hp0, hp1⟩, rfl⟩ _ ⟨p', ⟨hp0', hp1'⟩, rfl⟩ a b ha hb hab
      refine ⟨fun i => a * p i + b * p' i, ⟨fun i => ?_, ?_⟩, ?_⟩
      · have := hp0 i; have := hp0' i; positivity
      · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp1, hp1']
        linarith
      · simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
    exact convexHull_min hsub hconv hM
  · rintro ⟨p, ⟨hp0, hp1⟩, rfl⟩
    exact (convex_convexHull ℝ _).sum_mem (fun i _ => hp0 i) hp1
      (fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩)

theorem mo385518_expand {n m : ℕ} (P : Fin m → Mat n) :
    ∀ (z : ℕ) (p : Fin z → Row m),
      (List.ofFn (fun t => ∑ a, p t a • P a)).prod =
        ∑ w : Fin z → Fin m, (∏ t, p t (w t)) • (List.ofFn (P ∘ w)).prod := by
  intro z
  induction z with
  | zero =>
    intro p
    simp
  | succ z ih =>
    intro p
    rw [List.ofFn_succ, List.prod_cons, ih (fun t => p t.succ)]
    rw [← (Fin.consEquiv (fun _ => Fin m)).sum_comp, Fintype.sum_prod_type,
      Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun w _ => ?_))
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ, List.ofFn_succ, Function.comp_apply, List.prod_cons]
    rw [smul_mul_smul_comm]
    rfl

theorem mo385518_endpoint_expand {n m z : ℕ} (x : Row n) (P : Fin m → Mat n)
    (p : Fin z → Row m) :
    endpoint x (fun t => ∑ a, p t a • P a) =
      ∑ w : Fin z → Fin m, (∏ t, p t (w t)) • wordEnd x P w := by
  unfold endpoint wordEnd endpoint
  rw [mo385518_expand P z p, vecMul_sum]
  simp only [vecMul_smul]

theorem mo385518_reach_iff {n m z : ℕ} (x : Row n) (P : Fin m → Mat n) (y : Row n) :
    y ∈ reachable z x P ↔ ∃ p : Fin z → Row m, (∀ t, Distribution (p t)) ∧
        y = ∑ w : Fin z → Fin m, (∏ t, p t (w t)) • wordEnd x P w := by
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    have h := fun t => (mo385518_mem_hull_iff P (Q t)).mp (hQ t)
    choose p hp hpQ using h
    refine ⟨p, hp, ?_⟩
    have : Q = fun t => ∑ a, p t a • P a := funext hpQ
    rw [this, mo385518_endpoint_expand]
  · rintro ⟨p, hp, rfl⟩
    refine ⟨fun t => ∑ a, p t a • P a, fun t => (mo385518_mem_hull_iff P _).mpr ⟨p t, hp t, rfl⟩, ?_⟩
    rw [mo385518_endpoint_expand]

theorem mo385518_hull_eq {n m z : ℕ} (x : Row n) (P : Fin m → Mat n) :
    convexHull ℝ (reachable z x P) = convexHull ℝ (Set.range (wordEnd (z := z) x P)) := by
  classical
  apply le_antisymm
  · apply convexHull_min _ (convex_convexHull ℝ _)
    intro y hy
    obtain ⟨p, hp, rfl⟩ := (mo385518_reach_iff x P y).mp hy
    apply (convex_convexHull ℝ _).sum_mem
    · intro w _
      exact Finset.prod_nonneg (fun t _ => (hp t).1 (w t))
    · rw [← Fintype.prod_sum (fun t a => p t a)]
      exact Finset.prod_eq_one (fun t _ => (hp t).2)
    · intro w _
      exact subset_convexHull ℝ _ ⟨w, rfl⟩
  · apply convexHull_mono
    rintro _ ⟨w, rfl⟩
    exact ⟨P ∘ w, fun t => subset_convexHull ℝ _ ⟨w t, rfl⟩, rfl⟩

/-- The starting row of the example. -/
def mo385518_x0 : Row 3 := ![1, 0, 0]

/-- The two stochastic matrices of the example: stay, or shift one state to the right. -/
def mo385518_P0 : Fin 2 → Mat 3 := ![1, !![0, 1, 0; 0, 0, 1; 0, 0, 1]]

theorem mo385518_example_dist : Distribution mo385518_x0 := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp [mo385518_x0]
  · simp [mo385518_x0, Fin.sum_univ_three]

theorem mo385518_example_stoch : ∀ a, Stochastic (mo385518_P0 a) := by
  intro a i
  refine ⟨fun j => ?_, ?_⟩
  · fin_cases a <;> fin_cases i <;> fin_cases j <;> simp [mo385518_P0, Matrix.one_apply]
  · fin_cases a <;> fin_cases i <;> simp [mo385518_P0, Fin.sum_univ_three]

theorem mo385518_example_nonconvex : ¬ Convex ℝ (reachable 2 mo385518_x0 mo385518_P0) := by
  intro hconv
  have h0 : (![1, 0, 0] : Row 3) ∈ reachable 2 mo385518_x0 mo385518_P0 := by
    refine ⟨fun _ => mo385518_P0 0, fun t => subset_convexHull ℝ _ ⟨0, rfl⟩, ?_⟩
    ext j
    fin_cases j <;> simp [endpoint, mo385518_P0, mo385518_x0, List.ofFn_succ]
  have h2 : (![0, 0, 1] : Row 3) ∈ reachable 2 mo385518_x0 mo385518_P0 := by
    refine ⟨fun _ => mo385518_P0 1, fun t => subset_convexHull ℝ _ ⟨1, rfl⟩, ?_⟩
    ext j
    fin_cases j <;> simp [endpoint, mo385518_P0, mo385518_x0, List.ofFn_succ, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_three]
  have hmid := hconv h0 h2 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  obtain ⟨Q, hQ, hy⟩ := hmid
  obtain ⟨a, ⟨ha0, ha1⟩, hQa⟩ := (mo385518_mem_hull_iff _ (Q 0)).mp (hQ 0)
  obtain ⟨b, ⟨hb0, hb1⟩, hQb⟩ := (mo385518_mem_hull_iff _ (Q 1)).mp (hQ 1)
  have hy' : (1 / 2 : ℝ) • (![1, 0, 0] : Row 3) + (1 / 2 : ℝ) • ![0, 0, 1] =
      mo385518_x0 ᵥ* (Q 0 * Q 1) := by
    rw [hy]; simp [endpoint, List.ofFn_succ]
  rw [hQa, hQb] at hy'
  have e0 := congrFun hy' 0
  have e1 := congrFun hy' 1
  have e2 := congrFun hy' 2
  simp [mo385518_x0, mo385518_P0, Fin.sum_univ_two, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_three, Matrix.one_apply] at e0 e1 e2
  have pa0 := ha0 0; have pa1 := ha0 1; have pb0 := hb0 0; have pb1 := hb0 1
  have k1 : 0 ≤ a 0 * b 1 := mul_nonneg pa0 pb1
  have k2 : 0 ≤ a 1 * b 0 := mul_nonneg pa1 pb0
  have z1 : a 0 * b 1 = 0 := by nlinarith
  have hprod : a 0 * b 0 * (a 1 * b 1) = (a 0 * b 1) * (a 1 * b 0) := by ring
  rw [z1] at hprod
  nlinarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_mo_385518.main :=
  ⟨fun {_ _ _} _ x P _ _ =>
    ⟨fun y => OMA.Helpers.mo385518_reach_iff x P y, OMA.Helpers.mo385518_hull_eq x P⟩,
   ⟨OMA.Helpers.mo385518_x0, OMA.Helpers.mo385518_P0, OMA.Helpers.mo385518_example_dist,
    OMA.Helpers.mo385518_example_stoch, OMA.Helpers.mo385518_example_nonconvex⟩⟩
