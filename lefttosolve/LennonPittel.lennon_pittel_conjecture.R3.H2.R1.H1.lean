import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1

/-!
# Score-space law of the number of stable matchings

Independent uniform scores on `[0, 1]` induce a uniformly random preference profile.
The score cube splits, up to the null set of ties, into the regions `Ereg p` of score vectors
whose induced orders are those of the profile `p`. Coordinatewise permutations of the scores
preserve the product measure and move these regions onto each other, so all regions have the
same mass `1 / card (Profile n)`, and on `Ereg p` the score-space count equals
`numStableMatchings p`.
-/

open MeasureTheory Set StableMarriage
open scoped ENNReal

namespace OMA.Helpers

/-- The ranking used by agent `a` in a profile. -/
def rk {n : ℕ} (p : Profile n) : Fin n ⊕ Fin n → Equiv.Perm (Fin n) :=
  Sum.elim p.manRank p.womanRank

/-- The region of score space whose induced profile is `p`. -/
def Ereg {n : ℕ} (p : Profile n) : Set ((Fin n ⊕ Fin n) → Fin n → ℝ) :=
  {x | ∀ a j k, x a j < x a k ↔ rk p a j < rk p a k}

/-- Score vectors with a tie for some agent. -/
def Ties (n : ℕ) : Set ((Fin n ⊕ Fin n) → Fin n → ℝ) :=
  {x | ∃ a j k, j ≠ k ∧ x a j = x a k}

theorem measurableSet_Ereg {n : ℕ} (p : Profile n) : MeasurableSet (Ereg p) := by
  have : Ereg p = ⋂ a, ⋂ j, ⋂ k, {x : (Fin n ⊕ Fin n) → Fin n → ℝ |
      x a j < x a k ↔ rk p a j < rk p a k} := by
    ext x; simp [Ereg]
  rw [this]
  refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun k => ?_
  exact measurableSet_setOfPred.2 (Measurable.iff (measurableSet_setOfPred.1
    (measurableSet_lt (by fun_prop) (by fun_prop))) measurable_const)

theorem inner_diag_null {n : ℕ} {j k : Fin n} (hjk : j ≠ k) :
    (Measure.pi fun _ : Fin n => volume.restrict (Icc (0 : ℝ) 1))
      {y : Fin n → ℝ | y j = y k} = 0 := by
  have h1 : (Measure.pi fun _ : Fin n => volume.restrict (Icc (0 : ℝ) 1)) =
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)).restrict
        (Set.univ.pi fun _ => Icc (0 : ℝ) 1) :=
    (Measure.restrict_pi_pi _ _).symm
  rw [h1]
  refine nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans (le_of_eq ?_))
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j -
      LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k
  have hsub : {y : Fin n → ℝ | y j = y k} = (LinearMap.ker L : Set (Fin n → ℝ)) := by
    ext y; simp [L, sub_eq_zero]
  have hne : LinearMap.ker L ≠ ⊤ := by
    intro h
    have hmem : (Pi.single j (1 : ℝ) : Fin n → ℝ) ∈ LinearMap.ker L := h ▸ Submodule.mem_top
    simp [L, hjk.symm] at hmem
  rw [hsub]
  exact Measure.addHaar_submodule (volume : Measure (Fin n → ℝ)) _ hne

theorem ties_null (n : ℕ) :
    (Measure.pi fun _ : Fin n ⊕ Fin n ↦ Measure.pi fun _ : Fin n ↦
      volume.restrict (Icc (0 : ℝ) 1)) (Ties n) = 0 := by
  have : Ties n = ⋃ a, ⋃ j, ⋃ k, ⋃ (_ : j ≠ k),
      (Function.eval a) ⁻¹' {y : Fin n → ℝ | y j = y k} := by
    ext x; simp [Ties]
  rw [this]
  refine measure_iUnion_null fun a => measure_iUnion_null fun j => measure_iUnion_null fun k =>
    measure_iUnion_null fun hjk => ?_
  exact Measure.pi_eval_preimage_null _ (inner_diag_null hjk)

theorem exists_perm_of_injective {n : ℕ} (f : Fin n → ℝ) (hf : Function.Injective f) :
    ∃ σ : Equiv.Perm (Fin n), ∀ j k, f j < f k ↔ σ j < σ k := by
  refine ⟨(Tuple.sort f).symm, fun j k => ?_⟩
  have hmono : StrictMono (f ∘ Tuple.sort f) :=
    (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)
  have := hmono.lt_iff_lt (a := (Tuple.sort f).symm j) (b := (Tuple.sort f).symm k)
  simpa using this

theorem perm_eq_of_order_iff {n : ℕ} (σ τ : Equiv.Perm (Fin n))
    (h : ∀ j k, σ j < σ k ↔ τ j < τ k) : σ = τ := by
  have hρ : StrictMono (fun u => τ (σ.symm u)) := by
    intro u v huv
    exact (h (σ.symm u) (σ.symm v)).1 (by simpa using huv)
  have hrange : Set.range (fun u => τ (σ.symm u)) = Set.range id := by
    rw [Set.range_id, Set.range_eq_univ]
    intro v
    exact ⟨σ (τ.symm v), by simp⟩
  have hid := (hρ.range_inj strictMono_id).1 hrange
  refine Equiv.ext fun j => ?_
  have := congrFun hid (σ j)
  simp only [Equiv.symm_apply_apply, id] at this
  exact this.symm

theorem mp_perm {n : ℕ} (ν : Measure ℝ) [SigmaFinite ν] (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun (y : Fin n → ℝ) (j : Fin n) => y (σ j))
      (Measure.pi fun _ => ν) (Measure.pi fun _ => ν) := by
  have h := measurePreserving_piCongrLeft (fun _ : Fin n => ν) σ.symm
  convert h using 1
  funext y j
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  simp

theorem preimage_Ereg {n : ℕ} (p q : Profile n) :
    (fun (x : (Fin n ⊕ Fin n) → Fin n → ℝ) a j => x a ((rk q a).symm (rk p a j))) ⁻¹' Ereg p
      = Ereg q := by
  ext x
  simp only [Set.mem_preimage, Ereg, Set.mem_ofPred_eq]
  constructor
  · intro h a j k
    have := h a ((rk p a).symm (rk q a j)) ((rk p a).symm (rk q a k))
    simpa using this
  · intro h a j k
    have := h a ((rk q a).symm (rk p a j)) ((rk q a).symm (rk p a k))
    simpa using this

theorem measure_Ereg_eq {n : ℕ} (p q : Profile n) :
    (Measure.pi fun _ : Fin n ⊕ Fin n ↦ Measure.pi fun _ : Fin n ↦
      volume.restrict (Icc (0 : ℝ) 1)) (Ereg q) =
    (Measure.pi fun _ : Fin n ⊕ Fin n ↦ Measure.pi fun _ : Fin n ↦
      volume.restrict (Icc (0 : ℝ) 1)) (Ereg p) := by
  rw [← preimage_Ereg p q]
  exact (measurePreserving_pi _ _
    (fun a => mp_perm _ ((rk p a).trans (rk q a).symm))).measure_preimage
      (measurableSet_Ereg p).nullMeasurableSet

theorem Ereg_eq_of_mem {n : ℕ} {p q : Profile n} {x : (Fin n ⊕ Fin n) → Fin n → ℝ}
    (hp : x ∈ Ereg p) (hq : x ∈ Ereg q) : p = q := by
  have hrk : ∀ a, rk p a = rk q a := fun a =>
    perm_eq_of_order_iff _ _ (fun j k => (hp a j k).symm.trans (hq a j k))
  cases p with
  | mk m1 w1 =>
    cases q with
    | mk m2 w2 =>
      simp only [Profile.mk.injEq]
      constructor
      · funext i; exact hrk (Sum.inl i)
      · funext j; exact hrk (Sum.inr j)

theorem exists_Ereg {n : ℕ} (x : (Fin n ⊕ Fin n) → Fin n → ℝ) (hx : x ∉ Ties n) :
    ∃ p : Profile n, x ∈ Ereg p := by
  have hinj : ∀ a, Function.Injective (x a) := by
    intro a j k hjk
    by_contra hne
    exact hx ⟨a, j, k, hne, hjk⟩
  choose σ hσ using fun a => exists_perm_of_injective (x a) (hinj a)
  refine ⟨⟨fun i => σ (Sum.inl i), fun j => σ (Sum.inr j)⟩, ?_⟩
  intro a j k
  cases a with
  | inl i => exact hσ (Sum.inl i) j k
  | inr i => exact hσ (Sum.inr i) j k

theorem not_ties_of_Ereg {n : ℕ} {p : Profile n} {x : (Fin n ⊕ Fin n) → Fin n → ℝ}
    (hx : x ∈ Ereg p) : x ∉ Ties n := by
  rintro ⟨a, j, k, hjk, hx'⟩
  rcases lt_or_gt_of_ne ((rk p a).injective.ne hjk) with h | h
  · have := (hx a j k).2 h
    rw [hx'] at this
    exact lt_irrefl _ this
  · have := (hx a k j).2 h
    rw [hx'] at this
    exact lt_irrefl _ this

theorem S_eq {n : ℕ} {p : Profile n} {x : (Fin n ⊕ Fin n) → Fin n → ℝ} (hx : x ∈ Ereg p) :
    Nat.card {m : Matching n // ∀ i j, ¬ (m i ≠ j ∧ x (.inl i) j < x (.inl i) (m i) ∧
      x (.inr j) i < x (.inr j) (m.symm j))} = numStableMatchings p := by
  classical
  unfold numStableMatchings
  rw [Fintype.card_eq_nat_card]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun m => ?_)
  simp only [IsStable, IsBlockingPair]
  have h1 : ∀ i j k, x (Sum.inl i) j < x (Sum.inl i) k ↔ p.manRank i j < p.manRank i k :=
    fun i j k => hx (Sum.inl i) j k
  have h2 : ∀ i j k, x (Sum.inr i) j < x (Sum.inr i) k ↔ p.womanRank i j < p.womanRank i k :=
    fun i j k => hx (Sum.inr i) j k
  simp only [h1, h2]

theorem main_eq (n : ℕ) (t : ℝ) :
    (Measure.pi fun _ : Fin n ⊕ Fin n ↦ Measure.pi fun _ : Fin n ↦
      volume.restrict (Icc (0 : ℝ) 1))
      {x | t ≤ ((Nat.card {m : Matching n // ∀ i j, ¬ (m i ≠ j ∧
        x (.inl i) j < x (.inl i) (m i) ∧ x (.inr j) i < x (.inr j) (m.symm j))} : ℕ) : ℝ)} =
    (uniformProfile n).toMeasure {p | t ≤ (numStableMatchings p : ℝ)} := by
  classical
  have : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp [Real.volume_Icc]⟩
  set μ := (Measure.pi fun _ : Fin n ⊕ Fin n ↦ Measure.pi fun _ : Fin n ↦
      volume.restrict (Icc (0 : ℝ) 1))
  set c := μ (Ereg (default : Profile n))
  have hE : ∀ p, μ (Ereg p) = c := fun p => measure_Ereg_eq default p
  have hT : μ (Ties n) = 0 := ties_null n
  have hTc : μ (Ties n)ᶜ = 1 := by
    rw [measure_congr (ae_eq_univ.2 (by rwa [compl_compl])), measure_univ]
  have hdisj : Pairwise (Function.onFun Disjoint fun p : Profile n => Ereg p) := by
    intro p q hpq
    rw [Function.onFun, Set.disjoint_left]
    intro x hp hq
    exact hpq (Ereg_eq_of_mem hp hq)
  have hU : (⋃ p, Ereg p) = (Ties n)ᶜ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_compl_iff]
    constructor
    · rintro ⟨p, hp⟩; exact not_ties_of_Ereg hp
    · intro hx; exact exists_Ereg x hx
  have hsum : c * (Fintype.card (Profile n) : ℝ≥0∞) = 1 := by
    have h1 : μ (⋃ p, Ereg p) = ∑ p, μ (Ereg p) := by
      rw [measure_iUnion hdisj measurableSet_Ereg, tsum_fintype]
    rw [hU, hTc] at h1
    simp only [hE, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    rw [h1, mul_comm]
  have hcinv : c = (Fintype.card (Profile n) : ℝ≥0∞)⁻¹ := ENNReal.eq_inv_of_mul_eq_one_left hsum
  have hA : μ {x | t ≤ ((Nat.card {m : Matching n // ∀ i j, ¬ (m i ≠ j ∧
        x (.inl i) j < x (.inl i) (m i) ∧ x (.inr j) i < x (.inr j) (m.symm j))} : ℕ) : ℝ)} =
      μ (⋃ p ∈ Finset.univ.filter (fun p : Profile n => t ≤ (numStableMatchings p : ℝ)),
        Ereg p) := by
    rw [← measure_inter_conull (t := (Ties n)ᶜ) (by rwa [compl_compl])]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion,
      Finset.mem_filter, Finset.mem_univ, true_and, exists_prop]
    constructor
    · rintro ⟨ht, hx⟩
      obtain ⟨p, hp⟩ := exists_Ereg x hx
      exact ⟨p, by rwa [← S_eq hp], hp⟩
    · rintro ⟨p, ht, hp⟩
      exact ⟨by rwa [S_eq hp], not_ties_of_Ereg hp⟩
  rw [hA, measure_biUnion_finset (fun p _ q _ hpq => hdisj hpq)
    (fun p _ => measurableSet_Ereg p)]
  simp only [hE, Finset.sum_const, nsmul_eq_mul]
  rw [uniformProfile, PMF.toMeasure_uniformOfFintype_apply _ (MeasurableSpace.measurableSet_top),
    hcinv, div_eq_mul_inv]
  congr 2
  rw [Fintype.card_subtype]
  rfl

end OMA.Helpers

theorem OMA.solution : OMA.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1.H1 := by
  intro n t
  exact OMA.Helpers.main_eq n t
