import OMAReductions.R_Erdos104_erdos_104_R1

/-!
# Step H2 of the reduction Erdos104.erdos_104.R1

Fix a distance d. Two distinct points u, v of the plane have at most two points at prescribed
distances from both (two circles with distinct centres meet in at most two points).

* Unit circles: a unit circle through a pair (a, b) at distance d is determined by its centre,
  which is at distance 1 from a and from b, so each ordered pair accounts for at most two circles.
  Hence the number of circles is at most 2 S, where S is the number of ordered pairs of P at
  distance d.
* Second moment: expanding deg(a)^2 as a double sum over (b, c) and summing over a first, each
  pair b /= c has at most two common distance-d neighbours, and the diagonal b = c contributes at
  most |P|, so the sum of deg(a)^2 is at most 3 |P|^2.
* Cauchy-Schwarz gives S^2 <= 3 |P|^3 <= 3 n^3, so (2 S)^2 <= 12 n^3 <= (eps n^2)^2 as soon as
  n >= 12 / eps^2.
-/

open EuclideanGeometry
open scoped EuclideanGeometry

namespace OMA.Helpers

/-- The points of the plane at prescribed distances from two distinct points all lie in one
finite set with at most two elements. -/
theorem exists_two_candidates (u v : ℝ²) (r t : ℝ) :
    ∃ F : Finset ℝ², F.card ≤ 2 ∧
      (u ≠ v → ∀ c : ℝ², dist c u = r → dist c v = t → c ∈ F) := by
  classical
  by_cases h : ∃ p q : ℝ², p ≠ q ∧ dist p u = r ∧ dist p v = t ∧ dist q u = r ∧ dist q v = t
  · obtain ⟨p, q, hpq, hpu, hpv, hqu, hqv⟩ := h
    refine ⟨{p, q}, Finset.card_le_two, fun huv c hcu hcv => ?_⟩
    rcases eq_of_dist_eq_of_dist_eq_of_finrank_eq_two finrank_euclideanSpace_fin huv hpq
      hpu hqu hcu hpv hqv hcv with hc | hc
    · simp [hc]
    · simp [hc]
  · by_cases h' : ∃ p : ℝ², dist p u = r ∧ dist p v = t
    · obtain ⟨p, hpu, hpv⟩ := h'
      refine ⟨{p}, by simp, fun _ c hcu hcv => ?_⟩
      by_contra hc
      exact h ⟨c, p, by simpa using hc, hcu, hcv, hpu, hpv⟩
    · exact ⟨∅, by simp, fun _ c hcu hcv => (h' ⟨c, hcu, hcv⟩).elim⟩

/-- Second moment of the distance-`d` degrees: a point pair has at most two common neighbours. -/
theorem sum_sq_degree_le (P : Finset ℝ²) (d : ℝ) :
    ∑ a ∈ P, (P.filter fun b => dist a b = d).card ^ 2 ≤ 3 * P.card ^ 2 := by
  classical
  have hexp : ∀ a : ℝ², (P.filter fun b => dist a b = d).card ^ 2 =
      ∑ b ∈ P, ∑ c ∈ P, if dist a b = d ∧ dist a c = d then 1 else 0 := by
    intro a
    rw [Finset.card_filter, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    by_cases h1 : dist a b = d <;> by_cases h2 : dist a c = d <;> simp [h1, h2]
  have hswap : ∑ a ∈ P, (P.filter fun b => dist a b = d).card ^ 2 =
      ∑ b ∈ P, ∑ c ∈ P, (P.filter fun a => dist a b = d ∧ dist a c = d).card := by
    simp_rw [hexp, Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
  have hinner : ∀ b c : ℝ², (P.filter fun a => dist a b = d ∧ dist a c = d).card ≤
      (if b = c then P.card else 0) + 2 := by
    intro b c
    by_cases hbc : b = c
    · rw [if_pos hbc]
      exact (Finset.card_filter_le _ _).trans (Nat.le_add_right _ _)
    · rw [if_neg hbc, zero_add]
      obtain ⟨F, hF2, hF⟩ := exists_two_candidates b c d d
      refine (Finset.card_le_card fun a ha => ?_).trans hF2
      obtain ⟨_, hab, hac⟩ := Finset.mem_filter.mp ha
      exact hF hbc a hab hac
  calc
    _ = ∑ b ∈ P, ∑ c ∈ P, (P.filter fun a => dist a b = d ∧ dist a c = d).card := hswap
    _ ≤ ∑ b ∈ P, ∑ c ∈ P, ((if b = c then P.card else 0) + 2) :=
      Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun c _ => hinner b c
    _ = ∑ _b ∈ P, (P.card + P.card * 2) := by
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos hb, Finset.sum_const, smul_eq_mul]
    _ = 3 * P.card ^ 2 := by
      rw [Finset.sum_const, smul_eq_mul]
      ring

/-- Cauchy-Schwarz turns the second moment bound into a bound on the number of ordered pairs. -/
theorem sum_degree_sq_le (P : Finset ℝ²) (d : ℝ) :
    (∑ a ∈ P, (P.filter fun b => dist a b = d).card) ^ 2 ≤ 3 * P.card ^ 3 := by
  calc
    _ ≤ P.card * ∑ a ∈ P, (P.filter fun b => dist a b = d).card ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := P) (f := fun a => (P.filter fun b => dist a b = d).card)
    _ ≤ P.card * (3 * P.card ^ 2) := Nat.mul_le_mul_left _ (sum_sq_degree_le P d)
    _ = 3 * P.card ^ 3 := by ring

/-- Each unit circle through a pair at distance `d` is determined by its centre, and each ordered
pair admits at most two centres. -/
theorem chord_circles_ncard_le (P : Finset ℝ²) (d : ℝ) :
    {s : Sphere ℝ² | s.radius = 1 ∧
      ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ dist a b = d ∧ a ∈ s ∧ b ∈ s}.ncard ≤
      2 * ∑ a ∈ P, (P.filter fun b => dist a b = d).card := by
  classical
  have hcand := fun x : ℝ² × ℝ² => exists_two_candidates x.1 x.2 1 1
  choose F hF2 hF using hcand
  set E : Finset (ℝ² × ℝ²) := (P ×ˢ P).filter fun x => dist x.1 x.2 = d with hEdef
  have hEcard : E.card = ∑ a ∈ P, (P.filter fun b => dist a b = d).card := by
    rw [hEdef, Finset.card_filter, Finset.sum_product]
    simp only [Finset.card_filter]
  have hmaps : ∀ s ∈ {s : Sphere ℝ² | s.radius = 1 ∧
      ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ dist a b = d ∧ a ∈ s ∧ b ∈ s},
      s.center ∈ (↑(E.biUnion F) : Set ℝ²) := by
    rintro s ⟨hs1, a, ha, b, hb, hab, hd, has, hbs⟩
    rw [Finset.mem_coe, Finset.mem_biUnion]
    refine ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hd⟩, ?_⟩
    refine hF (a, b) hab s.center ?_ ?_
    · rw [dist_comm, ← hs1]
      exact mem_sphere.mp has
    · rw [dist_comm, ← hs1]
      exact mem_sphere.mp hbs
  have hinj : Set.InjOn Sphere.center {s : Sphere ℝ² | s.radius = 1 ∧
      ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ dist a b = d ∧ a ∈ s ∧ b ∈ s} := by
    intro s hs t ht hst
    exact Sphere.ext hst (hs.1.trans ht.1.symm)
  calc
    _ ≤ (↑(E.biUnion F) : Set ℝ²).ncard :=
      Set.ncard_le_ncard_of_injOn _ hmaps hinj (Finset.finite_toSet _)
    _ = (E.biUnion F).card := Set.ncard_coe_finset _
    _ ≤ ∑ x ∈ E, (F x).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ E, 2 := Finset.sum_le_sum fun x _ => hF2 x
    _ = 2 * E.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ = _ := by rw [hEcard]

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos104_erdos_104_R1.H2 := by
  unfold OMA.R_Erdos104_erdos_104_R1.H2
  intro d ε hε
  refine ⟨⌈12 / ε ^ 2⌉₊, fun n hn P hP => ?_⟩
  have hX := OMA.Helpers.chord_circles_ncard_le P d
  have hS := (OMA.Helpers.sum_degree_sq_le P d).trans
    (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hP 3))
  set S := ∑ a ∈ P, (P.filter fun b => dist a b = d).card
  have hXr : ({s : Sphere ℝ² | s.radius = 1 ∧
      ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ dist a b = d ∧ a ∈ s ∧ b ∈ s}.ncard : ℝ) ≤ 2 * (S : ℝ) := by
    exact_mod_cast hX
  have hSr : (S : ℝ) ^ 2 ≤ 3 * (n : ℝ) ^ 3 := by exact_mod_cast hS
  have hε2 : 0 < ε ^ 2 := by positivity
  have hn' : 12 / ε ^ 2 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have h12 : 12 ≤ ε ^ 2 * (n : ℝ) := by
    rw [div_le_iff₀ hε2] at hn'
    linarith
  have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  have hsq : (2 * (S : ℝ)) ^ 2 ≤ (ε * (n : ℝ) ^ 2) ^ 2 := by
    calc
      (2 * (S : ℝ)) ^ 2 = 4 * (S : ℝ) ^ 2 := by ring
      _ ≤ 4 * (3 * (n : ℝ) ^ 3) := by linarith
      _ = 12 * (n : ℝ) ^ 3 := by ring
      _ ≤ (ε ^ 2 * (n : ℝ)) * (n : ℝ) ^ 3 := mul_le_mul_of_nonneg_right h12 hn0
      _ = (ε * (n : ℝ) ^ 2) ^ 2 := by ring
  have hle : 2 * (S : ℝ) ≤ ε * (n : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  linarith
