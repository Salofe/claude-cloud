import FormalConjectures.ErdosProblems.«332»

-- Problem: Erdős Problem 332 (it asks for a value)
-- Answer: positive upper density is sufficient (Prikry, Stewart, Tijdeman).

open Filter

/-- The sufficient condition: `A` has positive upper density. -/
def OMA.answer : Set ℕ → Prop := fun A => 0 < A.upperDensity

namespace OMA.Helpers

open Classical in
theorem fin_of_not_mem (A : Set ℕ) (d : ℤ) (h : d ∉ Erdos332.D_A A) :
    {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ (p.1 : ℤ) - (p.2 : ℤ) = d}.Finite := by
  unfold Erdos332.D_A at h
  rw [Set.mem_setOf_eq, Set.not_infinite] at h
  refine h.subset ?_
  rintro ⟨a, b⟩ hp
  exact hp

theorem neg_mem (A : Set ℕ) (d : ℤ) (h : d ∈ Erdos332.D_A A) : -d ∈ Erdos332.D_A A := by
  unfold Erdos332.D_A at h ⊢
  rw [Set.mem_setOf_eq] at h ⊢
  have h2 := h.image (Prod.swap_injective.injOn)
  refine h2.mono ?_
  rintro _ ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, rfl⟩
  refine ⟨hb, ha, ?_⟩
  simp only [Prod.swap_prod_mk]
  omega

theorem freq (A : Set ℕ) (h : 0 < A.upperDensity) :
    ∃ k : ℕ, ∃ᶠ N : ℕ in atTop, N ≤ k * (A ∩ Set.Iio N).ncard := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt h
  refine ⟨k + 1, ?_⟩
  unfold Set.upperDensity at hk
  have hco : IsCoboundedUnder (· ≤ ·) atTop
      (fun b : ℕ => ((A ∩ Set.univ ∩ Set.Iio b).ncard : ℝ) / ((Set.univ ∩ Set.Iio b).ncard : ℝ)) := by
    refine isCoboundedUnder_le_of_le atTop (x := 0) ?_
    intro b
    positivity
  have hfr := frequently_lt_of_lt_limsup hco hk
  refine hfr.mono ?_
  intro N hN
  simp only [Set.inter_univ, Set.univ_inter] at hN
  have hN' : ((Set.Iio N : Set ℕ).ncard : ℝ) = N := by
    rw [← Finset.coe_Iio, Set.ncard_coe_finset]
    simp
  rw [hN'] at hN
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0
    simp
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast h0
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ hk1 hNpos] at hN
    have : (N : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * ((A ∩ Set.Iio N).ncard : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast this

open Classical in
theorem core (A : Set ℕ) (k : ℕ)
    (hf : ∃ᶠ N : ℕ in atTop, N ≤ k * (A ∩ Set.Iio N).ncard) (f : ℕ → ℤ)
    (hfD : ∀ i < k + 1, ∀ j < k + 1, i ≠ j → f i - f j ∉ Erdos332.D_A A) : False := by
  -- bound on the shifts
  obtain ⟨C, hC⟩ : ∃ C : ℕ, ∀ i < k + 1, (f i).natAbs ≤ C := by
    refine ⟨∑ i ∈ Finset.range (k + 1), (f i).natAbs, ?_⟩
    intro i hi
    exact Finset.single_le_sum (f := fun i => (f i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr hi)
  -- bound on the exceptional pairs
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ a ∈ A, ∀ b ∈ A, ∀ i < k + 1, ∀ j < k + 1, i ≠ j →
      (a : ℤ) - (b : ℤ) = f i - f j → a ≤ B := by
    have hfin : (⋃ i ∈ (Finset.range (k + 1) : Set ℕ), ⋃ j ∈ (Finset.range (k + 1) : Set ℕ),
        {p : ℕ × ℕ | i ≠ j ∧ p.1 ∈ A ∧ p.2 ∈ A ∧ (p.1 : ℤ) - (p.2 : ℤ) = f i - f j}).Finite := by
      refine Set.Finite.biUnion (Finset.finite_toSet _) ?_
      intro i hi
      refine Set.Finite.biUnion (Finset.finite_toSet _) ?_
      intro j hj
      by_cases hij : i = j
      · refine Set.Finite.subset Set.finite_empty ?_
        intro p hp
        exact (hp.1 hij).elim
      · refine (fin_of_not_mem A (f i - f j) (hfD i (by simpa using hi) j (by simpa using hj) hij)).subset ?_
        intro p hp
        exact hp.2
    obtain ⟨⟨B1, B2⟩, hB⟩ := hfin.bddAbove
    refine ⟨B1, ?_⟩
    intro a ha b hb i hi j hj hij hab
    have hmem : (a, b) ∈ (⋃ i ∈ (Finset.range (k + 1) : Set ℕ), ⋃ j ∈ (Finset.range (k + 1) : Set ℕ),
        {p : ℕ × ℕ | i ≠ j ∧ p.1 ∈ A ∧ p.2 ∈ A ∧ (p.1 : ℤ) - (p.2 : ℤ) = f i - f j}) := by
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.coe_range, Set.mem_Iio]
      exact ⟨i, hi, j, hj, hij, ha, hb, hab⟩
    exact (hB hmem).1
  obtain ⟨N, hN, hNbig⟩ :=
    (hf.and_eventually (eventually_gt_atTop ((k + 1) * k * (B + 1) + 2 * k * C))).exists
  set A' : Finset ℕ := (Finset.range N).filter (fun a => a ∈ A ∧ B < a) with hA'
  set S : ℕ → Finset ℤ := fun i => A'.image (fun a : ℕ => (a : ℤ) + f i) with hS
  have hdisj : ((Finset.range (k + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint S := by
    intro i hi j hj hij
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxi hxj
    simp only [hS, Finset.mem_image] at hxi hxj
    obtain ⟨a, ha, rfl⟩ := hxi
    obtain ⟨b, hb, hab⟩ := hxj
    simp only [hA', Finset.mem_filter, Finset.mem_range] at ha hb
    have := hB a ha.2.1 b hb.2.1 j (by simpa using hj) i (by simpa using hi) (Ne.symm hij) (by omega)
    omega
  have hcard : ((Finset.range (k + 1)).biUnion S).card = (k + 1) * A'.card := by
    rw [Finset.card_biUnion hdisj]
    have : ∀ i ∈ Finset.range (k + 1), (S i).card = A'.card := by
      intro i _
      simp only [hS]
      exact Finset.card_image_of_injective _ (fun a b hab => by simpa using hab)
    rw [Finset.sum_congr rfl this]
    simp
  have hsub : (Finset.range (k + 1)).biUnion S ⊆ Finset.Ico (-(C : ℤ)) ((N : ℤ) + C) := by
    intro x hx
    simp only [Finset.mem_biUnion, hS, Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, hi, a, ha, rfl⟩ := hx
    simp only [hA', Finset.mem_filter, Finset.mem_range] at ha
    have := hC i hi
    rw [Finset.mem_Ico]
    omega
  have h1 : (k + 1) * A'.card ≤ N + 2 * C := by
    have := Finset.card_le_card hsub
    rw [hcard, Int.card_Ico] at this
    omega
  have h2 : (A ∩ Set.Iio N).ncard ≤ (B + 1) + A'.card := by
    have hss : A ∩ Set.Iio N ⊆ ((Finset.range (B + 1) ∪ A' : Finset ℕ) : Set ℕ) := by
      intro a ha
      rw [Finset.mem_coe, Finset.mem_union]
      by_cases hab : a ≤ B
      · left
        exact Finset.mem_range.mpr (by omega)
      · right
        simp only [hA', Finset.mem_filter, Finset.mem_range]
        exact ⟨ha.2, ha.1, by omega⟩
    have h3 := Set.ncard_le_ncard hss (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h3
    have h4 := Finset.card_union_le (Finset.range (B + 1)) A'
    rw [Finset.card_range] at h4
    omega
  have h5 : N ≤ k * (B + 1) + k * A'.card := by
    calc N ≤ k * (A ∩ Set.Iio N).ncard := hN
      _ ≤ k * ((B + 1) + A'.card) := Nat.mul_le_mul_left k h2
      _ = k * (B + 1) + k * A'.card := by ring
  have h6 : (k + 1) * N ≤ (k + 1) * k * (B + 1) + k * (N + 2 * C) := by
    calc (k + 1) * N ≤ (k + 1) * (k * (B + 1) + k * A'.card) := Nat.mul_le_mul_left _ h5
      _ = (k + 1) * k * (B + 1) + k * ((k + 1) * A'.card) := by ring
      _ ≤ (k + 1) * k * (B + 1) + k * (N + 2 * C) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left k h1) _
  have h7 : (k + 1) * N = k * N + N := by ring
  have h8 : k * (N + 2 * C) = k * N + 2 * k * C := by ring
  omega

theorem seq (A : Set ℕ) (hns : ¬ Erdos332.HasBoundedGaps (Erdos332.D_A A)) :
    ∀ n : ℕ, ∃ f : ℕ → ℤ, ∀ i < n, ∀ j < n, i ≠ j → f i - f j ∉ Erdos332.D_A A := by
  intro n
  induction n with
  | zero => exact ⟨fun _ => 0, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    obtain ⟨f, hf⟩ := ih
    obtain ⟨C, hC⟩ : ∃ C : ℕ, ∀ i < n, (f i).natAbs ≤ C := by
      refine ⟨∑ i ∈ Finset.range n, (f i).natAbs, ?_⟩
      intro i hi
      exact Finset.single_le_sum (f := fun i => (f i).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr hi)
    unfold Erdos332.HasBoundedGaps at hns
    have hgap : ∃ z : ℤ, ∀ s ∈ Erdos332.D_A A, ¬ (z ≤ s ∧ s < z + ((2 * C + 1 : ℕ) : ℤ)) := by
      by_contra hcon
      apply hns
      refine ⟨2 * C + 1, by omega, ?_⟩
      intro z
      by_contra hz
      apply hcon
      refine ⟨z, ?_⟩
      intro s hs hzs
      exact hz ⟨s, hs, hzs.1, hzs.2⟩
    obtain ⟨z, hz⟩ := hgap
    have hu : ∀ i < n, (z + C) - f i ∉ Erdos332.D_A A := by
      intro i hi hmem
      have := hC i hi
      apply hz _ hmem
      push_cast
      constructor <;> omega
    refine ⟨fun i => if i = n then z + C else f i, ?_⟩
    intro i hi j hj hij
    by_cases hin : i = n
    · have hjn : j ≠ n := fun h => hij (hin.trans h.symm)
      simp only [hin, hjn, if_true, if_false]
      exact hu j (by omega)
    · by_cases hjn : j = n
      · simp only [hin, hjn, if_true, if_false]
        intro hmem
        have := neg_mem A _ hmem
        rw [neg_sub] at this
        exact hu i (by omega) this
      · simp only [hin, hjn, if_false]
        exact hf i (by omega) j (by omega) hij

end OMA.Helpers

theorem OMA.solution : Erdos332.erdos_332.answer = OMA.answer → type_of% @Erdos332.erdos_332 := by
  intro hans A hA
  rw [hans] at hA
  by_contra hns
  obtain ⟨k, hk⟩ := OMA.Helpers.freq A hA
  obtain ⟨f, hf⟩ := OMA.Helpers.seq A hns (k + 1)
  exact OMA.Helpers.core A k hk f hf
