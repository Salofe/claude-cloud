import OMAReductions.R_Erdos103_erdos_103_variants_two_le_R1
import Mathlib

open Filter Finset EuclideanGeometry
open Erdos103

namespace OMA.Helpers

theorem sep_iff (x y : ℝ²) : (1:ENNReal) ≤ edist x y ↔ 1 ≤ dist x y := by
  rw [edist_dist, ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff dist_nonneg]

theorem sup_eq_diam {n : ℕ} (hne : (univ : Finset (Fin n × Fin n)).Nonempty) (x : Fin n → ℝ²) :
    univ.sup' hne (fun p => dist (x p.1) (x p.2)) = Metric.diam (Set.range x) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro p _
    exact Metric.dist_le_diam_of_mem (Set.finite_range x).isBounded
      (Set.mem_range_self _) (Set.mem_range_self _)
  · obtain ⟨p0, -⟩ := hne
    apply Metric.diam_le_of_forall_dist_le
    · exact dist_nonneg.trans
        (Finset.le_sup' (fun p : Fin n × Fin n => dist (x p.1) (x p.2)) (mem_univ p0))
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact Finset.le_sup' (fun p : Fin n × Fin n => dist (x p.1) (x p.2)) (mem_univ (i, j))

theorem image_mem {n : ℕ} (x : Fin n → ℝ²) (hx : ∀ i j, i ≠ j → 1 ≤ dist (x i) (x j)) :
    univ.image x ∈ separatedSets n := by
  have hinj : Function.Injective x := by
    intro i j h
    by_contra hij
    have := hx i j hij
    rw [h, dist_self] at this
    norm_num at this
  refine ⟨by rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin], ?_⟩
  intro p hp q hq hpq
  simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at hp hq
  obtain ⟨i, rfl⟩ := hp
  obtain ⟨j, rfl⟩ := hq
  exact (sep_iff _ _).mpr (hx i j (fun h => hpq (h ▸ rfl)))

theorem exists_minimiser (n : ℕ) (hn : 0 < n) : ∃ A : Finset ℝ², IsMinimiser n A := by
  have hne : (univ : Finset (Fin n × Fin n)).Nonempty := ⟨(⟨0, hn⟩, ⟨0, hn⟩), mem_univ _⟩
  let F : (Fin n → ℝ²) → ℝ := fun x => univ.sup' hne (fun p => dist (x p.1) (x p.2))
  have enum : ∀ B ∈ separatedSets n, ∀ D : ℝ, Metric.diam (B : Set ℝ²) ≤ D →
      ∃ x : Fin n → ℝ², (∀ i, ‖x i‖ ≤ D) ∧ (∀ i j, i ≠ j → 1 ≤ dist (x i) (x j)) ∧
        F x = Metric.diam (B : Set ℝ²) := by
    intro B hB D hD
    let e := Finset.equivFinOfCardEq hB.1
    let y : Fin n → ℝ² := fun i => (e.symm i : ℝ²)
    have hy : Set.range y = (B : Set ℝ²) := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        exact (e.symm i).2
      · intro hz
        exact ⟨e ⟨z, hz⟩, by simp [y]⟩
    let c := y ⟨0, hn⟩
    refine ⟨fun i => y i - c, ?_, ?_, ?_⟩
    · intro i
      rw [← dist_eq_norm]
      refine le_trans ?_ hD
      rw [← hy]
      exact Metric.dist_le_diam_of_mem (Set.finite_range y).isBounded
        (Set.mem_range_self _) (Set.mem_range_self _)
    · intro i j hij
      rw [dist_sub_right]
      have hyne : y i ≠ y j := fun h => hij (e.symm.injective (Subtype.ext h))
      exact (sep_iff _ _).mp (hB.2 (e.symm i).2 (e.symm j).2 hyne)
    · have h1 : F (fun i => y i - c) = F y := by simp only [F, dist_sub_right]
      rw [h1, ← hy]
      exact sup_eq_diam hne y
  let x0 : Fin n → ℝ² := fun i => EuclideanSpace.single 0 ((i : ℕ) : ℝ)
  have hx0 : ∀ i j, i ≠ j → 1 ≤ dist (x0 i) (x0 j) := by
    intro i j hij
    have hd : dist (x0 i) (x0 j) = |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
      simp [x0, Real.dist_eq]
    rw [hd]
    have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hij' with h | h
    · have h' : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast h
      rw [abs_sub_comm]
      exact le_trans (by linarith) (le_abs_self _)
    · have h' : ((j : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast h
      exact le_trans (by linarith) (le_abs_self _)
  have hB0 := image_mem x0 hx0
  let D0 := Metric.diam ((univ.image x0 : Finset ℝ²) : Set ℝ²)
  let K : Set (Fin n → ℝ²) := (Set.univ.pi fun _ => Metric.closedBall 0 D0) ∩
    ⋂ i, ⋂ j, ⋂ (_ : i ≠ j), {x | 1 ≤ dist (x i) (x j)}
  have hKc : IsCompact K := by
    apply IsCompact.inter_right (isCompact_univ_pi fun _ => isCompact_closedBall 0 D0)
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro _
    exact isClosed_le continuous_const ((continuous_apply i).dist (continuous_apply j))
  have memK : ∀ x, x ∈ K ↔ (∀ i, ‖x i‖ ≤ D0) ∧ (∀ i j, i ≠ j → 1 ≤ dist (x i) (x j)) := by
    intro x
    simp [K, Set.mem_pi, Metric.mem_closedBall, dist_zero_right]
  obtain ⟨x1, hx1a, hx1b, hx1F⟩ := enum _ hB0 D0 le_rfl
  have hFc : Continuous F :=
    Continuous.finset_sup'_apply hne (fun p _ => (continuous_apply p.1).dist (continuous_apply p.2))
  obtain ⟨xs, hxsK, hmin⟩ := hKc.exists_isMinOn ⟨x1, (memK x1).mpr ⟨hx1a, hx1b⟩⟩ hFc.continuousOn
  have hxs := (memK xs).mp hxsK
  have hA : Metric.diam ((univ.image xs : Finset ℝ²) : Set ℝ²) = F xs := by
    rw [coe_image, coe_univ, Set.image_univ]
    exact (sup_eq_diam hne xs).symm
  refine ⟨univ.image xs, image_mem xs hxs.2, isMinOn_iff.mpr fun B hB => ?_⟩
  change Metric.diam ((univ.image xs : Finset ℝ²) : Set ℝ²) ≤ Metric.diam (B : Set ℝ²)
  rw [hA]
  by_cases hBD : Metric.diam (B : Set ℝ²) ≤ D0
  · obtain ⟨x, hxa, hxb, hxF⟩ := enum B hB D0 hBD
    rw [← hxF]
    exact isMinOn_iff.mp hmin x ((memK x).mpr ⟨hxa, hxb⟩)
  · push_neg at hBD
    calc F xs ≤ F x1 := isMinOn_iff.mp hmin x1 ((memK x1).mpr ⟨hx1a, hx1b⟩)
      _ = D0 := hx1F
      _ ≤ _ := hBD.le

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos103_erdos_103_variants_two_le_R1.H1 := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact OMA.Helpers.exists_minimiser n hn
