import FormalConjectures.ErdosProblems.«1129»

/-!
# Erdős 1129: all optimal free interpolation nodes

Own formalisation of the theorem of Kilgore and de Boor–Pinkus (conjectures of Bernstein and
Erdős) together with the description of all minimisers of the Lebesgue constant among arbitrary
node sets in `[-1, 1]`.

Outline (nodes `x 0 < ... < x N`, gaps `i : Fin N`, `λ_i = gapMax x (i + 1)`):

* `Fp x i` is the polynomial of degree `≤ N` with the values `eps i k = ±1` at the nodes; it equals
  the Lebesgue function on the `i`-th gap (`lebesgue_eq_Fp`).
* `root_structure`: a polynomial of degree `≤ N` with the sign pattern `eps i` at the nodes is an
  affine factor without zero in the node hull times one linear factor per gap `≠ i`.  Hence the
  maximiser `tau x i` of each gap is unique and interior (`Fp_midpoint_lt`, `tau_unique`).
* `key_sign`: the sign of `F_i'(tau_j)`, obtained by applying `root_structure` to
  `F_i - c F_j` with `c = F_i(tau_j) / F_j(tau_j)`, `|c| < 1` (this replaces the interlacing
  analysis of Kilgore and of de Boor–Pinkus).
* `positivity_lemma` and `app3`: a nonzero variation of the interior nodes cannot decrease all
  `λ_i` to first order.
* `danskin`, `hasStrictFDerivAt_gap`: `λ_i` is strictly differentiable with
  `∂λ_i/∂x_k = -F_i'(x_k) ℓ_k(tau_i)`.
* `Gam x = (x 0, (λ_k - λ_{k-1})_k, log (x N - x 0))` is a local homeomorphism (`Gam_strict`),
  proper (`Gam_gap_bound`, `Gam_isProperMap`), hence a homeomorphism onto the whole space
  (`hadamard_abstract`, `Gam_homeo`).
* `no_domination`: two node vectors with the same end nodes and `λ(s) ≤ λ(t)` coincide
  (monotonicity along the preimage of a segment, `local_antichain`).
* `main_succ`, `main_zero`, `main_one`: the statement.
-/

open Topology Set Filter Polynomial Finset

namespace OMA.Helpers

open Erdos1129


/-- Abstract Hadamard: a closed local homeomorphism with finite fibres from a connected Hausdorff
space onto a simply connected, locally path connected space is injective with a continuous
inverse. -/
theorem hadamard_abstract {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space E]
    [ConnectedSpace E] [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (f : E → X) (hloc : IsLocalHomeomorph f) (hclosed : IsClosedMap f)
    (hfin : ∀ x, (f ⁻¹' {x}).Finite) :
    ∃ g : X → E, Continuous g ∧ (∀ e, g (f e) = e) ∧ (∀ x, f (g x) = x) := by
  have hcovOn : IsCoveringMapOn f Set.univ :=
    hclosed.isCoveringMapOn_of_isLocalHomeomorphOn (fun x _ => hfin x)
      (by simpa [← isLocalHomeomorph_iff_isLocalHomeomorphOn_univ] using hloc)
  have hcov : IsCoveringMap f := isCoveringMap_iff_isCoveringMapOn_univ.mpr hcovOn
  obtain ⟨e₀⟩ := (inferInstance : Nonempty E)
  obtain ⟨F, ⟨hF0, hFl⟩, -⟩ :=
    hcov.existsUnique_continuousMap_lifts (ContinuousMap.id X) (f e₀) e₀ rfl
  refine ⟨F, F.continuous, ?_, fun x => congrFun hFl x⟩
  have h := hcov.eq_of_comp_eq (g₁ := F ∘ f) (g₂ := id) (F.continuous.comp hcov.continuous)
    continuous_id (by
      funext e
      exact congrFun hFl (f e)) e₀ hF0
  exact fun e => congrFun h e

/-- IFT on an open subtype. -/
theorem isLocalHomeomorph_of_strict {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (U : TopologicalSpace.Opens E) (f : E → E)
    (h : ∀ x ∈ U, ∃ f' : E ≃L[ℝ] E, HasStrictFDerivAt f (f' : E →L[ℝ] E) x) :
    IsLocalHomeomorph (fun x : U => f x) := by
  refine IsLocalHomeomorph.mk _ fun x => ?_
  obtain ⟨f', hf'⟩ := h x x.2
  have hne : Nonempty U := ⟨x⟩
  refine ⟨(hf'.toOpenPartialHomeomorph f).subtypeRestr hne, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact hf'.mem_toOpenPartialHomeomorph_source
  · intro y _
    rfl

/-- injective linear endomorphism of a finite-dimensional space gives a continuous linear equiv -/
noncomputable def clEquivOfInjective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (A : E →L[ℝ] E) (hA : Function.Injective A) : E ≃L[ℝ] E :=
  (LinearEquiv.ofInjectiveEndo (A : E →ₗ[ℝ] E) hA).toContinuousLinearEquiv

theorem clEquivOfInjective_coe {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (A : E →L[ℝ] E) (hA : Function.Injective A) :
    ((clEquivOfInjective A hA : E ≃L[ℝ] E) : E →L[ℝ] E) = A := by
  ext x
  rfl


/-- The set of strictly monotone node vectors is open and convex. -/
theorem isOpen_strictMono (n : ℕ) : IsOpen {x : Fin n → ℝ | StrictMono x} := by
  have : {x : Fin n → ℝ | StrictMono x} = ⋂ i : Fin n, ⋂ j : Fin n, {x | i < j → x i < x j} := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter]
    exact ⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩
  rw [this]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  by_cases hij : i < j
  · simp only [hij, forall_const]
    exact isOpen_lt (continuous_apply i) (continuous_apply j)
  · simp [hij]

theorem convex_strictMono (n : ℕ) : Convex ℝ {x : Fin n → ℝ | StrictMono x} := by
  intro x hx y hy a b ha hb hab i j hij
  have h1 := hx hij
  have h2 := hy hij
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases ha.lt_or_eq with ha' | ha'
  · nlinarith
  · have hb1 : b = 1 := by linarith
    subst hb1
    rw [← ha']
    simpa using h2

/-- Danskin envelope lemma: a sup over a compact interval with a unique maximiser is strictly
differentiable, with derivative the partial derivative at the maximiser. -/
theorem danskin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : E × ℝ → ℝ) (x₀ : E) (u₀ : ℝ) (a b : ℝ) (hu₀ : u₀ ∈ Icc a b)
    (D : E × ℝ →L[ℝ] ℝ)
    (hD : HasStrictFDerivAt Φ D (x₀, u₀))
    (hcont : ∀ u ∈ Icc a b, ContinuousAt Φ (x₀, u))
    (hcont' : ∀ᶠ x in 𝓝 x₀, ContinuousOn (fun u => Φ (x, u)) (Icc a b))
    (huniq : ∀ u ∈ Icc a b, u ≠ u₀ → Φ (x₀, u) < Φ (x₀, u₀)) :
    HasStrictFDerivAt (fun x => sSup ((fun u => Φ (x, u)) '' Icc a b))
      (D.comp (ContinuousLinearMap.inl ℝ E ℝ)) x₀ := by
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have h2 := hasStrictFDerivAt_iff_isLittleO.mp hD
  rw [Asymptotics.isLittleO_iff] at h2
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp (h2 hc)
  -- maximisers are close to u₀
  have h3 : ∀ᶠ x in 𝓝 x₀, ∀ u ∈ Icc a b,
      (∀ u' ∈ Icc a b, Φ (x, u') ≤ Φ (x, u)) → dist u u₀ < δ := by
    set K' : Set ℝ := Icc a b \ Metric.ball u₀ δ with hK'
    have hK'c : IsCompact K' := isCompact_Icc.diff Metric.isOpen_ball
    have hΦ0 : ContinuousOn (fun u => Φ (x₀, u)) (Icc a b) := fun u hu =>
      ((hcont u hu).comp (f := fun u : ℝ => (x₀, u)) (by fun_prop)).continuousWithinAt
    rcases K'.eq_empty_or_nonempty with hem | hne
    · refine Eventually.of_forall fun x u hu _ => ?_
      by_contra hcon
      have : u ∈ K' := ⟨hu, by simpa [Metric.mem_ball] using hcon⟩
      rw [hem] at this
      exact this
    · obtain ⟨us, hus, husmax⟩ := hK'c.exists_isMaxOn hne (hΦ0.mono sdiff_subset)
      have hlt : Φ (x₀, us) < Φ (x₀, u₀) := by
        refine huniq us hus.1 ?_
        rintro rfl
        exact hus.2 (Metric.mem_ball_self hδ)
      set η := (Φ (x₀, us) + Φ (x₀, u₀)) / 2 with hη
      have hA : ∀ᶠ x in 𝓝 x₀, ∀ u ∈ K', Φ (x, u) < η := by
        refine hK'c.eventually_forall_of_forall_eventually fun u hu => ?_
        have hle : Φ (x₀, u) ≤ Φ (x₀, us) := husmax hu
        have : Φ (x₀, u) < η := by rw [hη]; linarith
        exact (hcont u hu.1).eventually (gt_mem_nhds this)
      have hB : ∀ᶠ x in 𝓝 x₀, η < Φ (x, u₀) := by
        have hc0 : ContinuousAt (fun x : E => Φ (x, u₀)) x₀ :=
          (hcont u₀ hu₀).comp (f := fun x : E => (x, u₀)) (by fun_prop)
        have : η < Φ (x₀, u₀) := by rw [hη]; linarith
        exact hc0.eventually (lt_mem_nhds this)
      filter_upwards [hA, hB] with x hxA hxB u hu hmax
      by_contra hcon
      have huK : u ∈ K' := ⟨hu, by simpa [Metric.mem_ball] using hcon⟩
      have := hxA u huK
      have := hmax u₀ hu₀
      linarith
  -- maximisers exist
  have hmax : ∀ᶠ x in 𝓝 x₀, ∃ u ∈ Icc a b, (∀ u' ∈ Icc a b, Φ (x, u') ≤ Φ (x, u)) ∧
      sSup ((fun u => Φ (x, u)) '' Icc a b) = Φ (x, u) := by
    filter_upwards [hcont'] with x hx
    obtain ⟨u, hu, humax⟩ := isCompact_Icc.exists_isMaxOn ⟨u₀, hu₀⟩ hx
    refine ⟨u, hu, fun u' hu' => humax hu', ?_⟩
    refine IsGreatest.csSup_eq ⟨⟨u, hu, rfl⟩, ?_⟩
    rintro _ ⟨u', hu', rfl⟩
    exact humax hu'
  have hball : ∀ᶠ x in 𝓝 x₀, dist x x₀ < δ := Metric.ball_mem_nhds x₀ hδ
  have hall := h3.and (hmax.and hball)
  have hprod := hall.prod_nhds hall
  filter_upwards [hprod] with p hp
  obtain ⟨⟨h3x, ⟨u, hu, humax, hsup⟩, hbx⟩, ⟨h3y, ⟨w, hw, hwmax, hsup'⟩, hby⟩⟩ := hp
  have hdu : dist u u₀ < δ := h3x u hu humax
  have hdw : dist w u₀ < δ := h3y w hw hwmax
  -- the two key estimates
  have key : ∀ v : ℝ, dist v u₀ < δ →
      ‖Φ (p.1, v) - Φ (p.2, v) - D ((p.1, v) - (p.2, v))‖ ≤ c * ‖(p.1, v) - (p.2, v)‖ := by
    intro v hv
    have := @hδ' ((p.1, v), (p.2, v)) (by
      rw [Prod.dist_eq, Prod.dist_eq, Prod.dist_eq]
      simp only [max_lt_iff]
      exact ⟨⟨hbx, hv⟩, ⟨hby, hv⟩⟩)
    simpa using this
  have hsub : ∀ v : ℝ, ((p.1, v) : E × ℝ) - (p.2, v) = (p.1 - p.2, 0) := by
    intro v; ext <;> simp
  have hnorm : ‖((p.1 - p.2, (0:ℝ)) : E × ℝ)‖ = ‖p.1 - p.2‖ := by
    simp [Prod.norm_def]
  have k1 := key u hdu
  have k2 := key w hdw
  rw [hsub, hnorm] at k1 k2
  rw [Real.norm_eq_abs, abs_le] at k1 k2
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inl_apply]
  rw [hsup, hsup', Real.norm_eq_abs, abs_le]
  have e1 : Φ (p.2, u) ≤ Φ (p.2, w) := hwmax u hu
  have e2 : Φ (p.1, w) ≤ Φ (p.1, u) := humax w hw
  constructor <;> linarith [k1.1, k1.2, k2.1, k2.2]

/-- Positivity lemma (replaces the linear-independence part of Kilgore's argument). -/
theorem positivity_lemma {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (τ : ι → ℝ) (hτ : Function.Injective τ) (g : ι → ℝ[X])
    (hdeg : ∀ i, (g i).degree < ((Fintype.card ι - 1 : ℕ) : WithBot ℕ))
    (hsign : ∀ i j, i ≠ j → (g i).eval (τ j) * ∏ k ∈ univ.erase j, (τ j - τ k) < 0)
    (φ : ℝ[X] →ₗ[ℝ] ℝ) (hφ : ∀ i, φ (g i) ≤ 0) :
    ∀ P : ℝ[X], P.degree < ((Fintype.card ι - 1 : ℕ) : WithBot ℕ) → φ P = 0 := by
  classical
  have hinj : Set.InjOn τ (univ : Finset ι) := hτ.injOn
  have hcard : (univ : Finset ι).card = Fintype.card ι := Finset.card_univ
  have hpos : 0 < Fintype.card ι := Fintype.card_pos
  set π : ι → ℝ := fun j => ∏ k ∈ univ.erase j, (τ j - τ k) with hπ
  have hπne : ∀ j, π j ≠ 0 := by
    intro j
    rw [hπ]
    refine Finset.prod_ne_zero_iff.mpr fun k hk => ?_
    exact sub_ne_zero.mpr fun h => (Finset.ne_of_mem_erase hk) (hτ h).symm
  set c : ι → ℝ := fun j => φ (Lagrange.basis univ τ j) with hc
  -- representation of φ on low-degree polynomials
  have hlt : ∀ P : ℝ[X], P.degree < ((Fintype.card ι - 1 : ℕ) : WithBot ℕ) →
      P.degree < ((univ : Finset ι).card : WithBot ℕ) := by
    intro P hP
    rw [hcard]
    refine lt_of_lt_of_le hP ?_
    exact_mod_cast Nat.sub_le _ _
  have hrep : ∀ P : ℝ[X], P.degree < ((Fintype.card ι - 1 : ℕ) : WithBot ℕ) →
      φ P = ∑ j, P.eval (τ j) * c j := by
    intro P hP
    conv_lhs => rw [Lagrange.eq_interpolate hinj (hlt P hP), Lagrange.interpolate_apply]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_C_mul, map_smul, smul_eq_mul]
  have hrel : ∀ P : ℝ[X], P.degree < ((Fintype.card ι - 1 : ℕ) : WithBot ℕ) →
      ∑ j, P.eval (τ j) / π j = 0 := by
    intro P hP
    have h := Lagrange.coeff_eq_sum hinj (hlt P hP)
    rw [hcard] at h
    rw [← h]
    exact coeff_eq_zero_of_degree_lt hP
  -- choose the maximal ratio
  obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image (univ : Finset ι) (fun j => c j * π j)
    Finset.univ_nonempty
  set s := c j0 * π j0 with hs
  have hterm : ∀ j, 0 ≤ (g j0).eval (τ j) / π j * (c j * π j - s) := by
    intro j
    by_cases hj : j = j0
    · subst hj; simp [hs]
    · have h1 : (g j0).eval (τ j) / π j < 0 := by
        have := hsign j0 j (Ne.symm hj)
        rw [div_neg_iff]
        rcases lt_or_gt_of_ne (hπne j) with h | h
        · left; exact ⟨by nlinarith, h⟩
        · right; exact ⟨by nlinarith, h⟩
      have h2 : c j * π j - s ≤ 0 := sub_nonpos.mpr (hj0 j (Finset.mem_univ j))
      exact mul_nonneg_of_nonpos_of_nonpos h1.le h2
  have hsum : ∑ j, (g j0).eval (τ j) / π j * (c j * π j - s) = φ (g j0) := by
    rw [hrep _ (hdeg j0)]
    have h0 := hrel _ (hdeg j0)
    have : ∑ j, (g j0).eval (τ j) / π j * (c j * π j - s) =
        ∑ j, (g j0).eval (τ j) * c j - s * ∑ j, (g j0).eval (τ j) / π j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp [hπne j]
    rw [this, h0, mul_zero, sub_zero]
  have hzero : ∀ j, (g j0).eval (τ j) / π j * (c j * π j - s) = 0 := by
    have hle : ∑ j, (g j0).eval (τ j) / π j * (c j * π j - s) ≤ 0 := hsum ▸ hφ j0
    have heq : ∑ j, (g j0).eval (τ j) / π j * (c j * π j - s) = 0 :=
      le_antisymm hle (Finset.sum_nonneg fun j _ => hterm j)
    intro j
    exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hterm j).mp heq j (Finset.mem_univ j)
  have hcs : ∀ j, c j = s / π j := by
    intro j
    by_cases hj : j = j0
    · subst hj; rw [hs]; field_simp [hπne j]
    · have h1 : (g j0).eval (τ j) / π j ≠ 0 := by
        have := hsign j0 j (Ne.symm hj)
        refine div_ne_zero ?_ (hπne j)
        intro h0; rw [h0, zero_mul] at this; exact lt_irrefl _ this
      have := (mul_eq_zero.mp (hzero j)).resolve_left h1
      field_simp [hπne j]
      linarith
  intro P hP
  rw [hrep P hP]
  have : ∑ j, P.eval (τ j) * c j = s * ∑ j, P.eval (τ j) / π j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcs j]; ring
  rw [this, hrel P hP, mul_zero]

/-- one-dimensional lemma: a continuous function that locally strictly decreases to the right
has `D 1 < D 0`. -/
theorem lt_of_locally_decreasing (D : ℝ → ℝ) (hD : ContinuousOn D (Icc 0 1))
    (hloc : ∀ θ₀ ∈ Ico (0:ℝ) 1, ∃ η > 0, ∀ θ, θ₀ < θ → θ < θ₀ + η → θ ≤ 1 → D θ < D θ₀) :
    D 1 < D 0 := by
  obtain ⟨θm, hθm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one) hD
  have key : ∀ θ₀ ∈ Ico (0:ℝ) 1, ∃ θ ∈ Icc (0:ℝ) 1, D θ < D θ₀ := by
    intro θ₀ hθ₀
    obtain ⟨η, hη, h⟩ := hloc θ₀ hθ₀
    refine ⟨min (θ₀ + η / 2) 1, ⟨le_min (by linarith [hθ₀.1]) zero_le_one, min_le_right _ _⟩, ?_⟩
    refine h _ (lt_min (by linarith) hθ₀.2) ?_ (min_le_right _ _)
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have h1 : θm = 1 := by
    by_contra hne
    have hθm' : θm ∈ Ico (0:ℝ) 1 := ⟨hθm.1, lt_of_le_of_ne hθm.2 hne⟩
    obtain ⟨θ, hθ, hlt⟩ := key θm hθm'
    exact absurd (hmin hθ) (not_le.mpr hlt)
  obtain ⟨θ, hθ, hlt⟩ := key 0 ⟨le_rfl, zero_lt_one⟩
  have := hmin hθ
  rw [h1] at this
  exact lt_of_le_of_lt this hlt



variable {N : ℕ}

theorem continuous_lebesgue {n : ℕ} (x : Fin n → ℝ) : Continuous (lebesgueFunction x) := by
  unfold lebesgueFunction
  exact continuous_finsetSum _ fun k _ => (Polynomial.continuous _).abs

/-- explicit product formula for the evaluation of a Lagrange basis polynomial -/
theorem basis_eval_eq {n : ℕ} (x : Fin n → ℝ) (k : Fin n) (y : ℝ) :
    (Lagrange.basis univ x k).eval y = ∏ l ∈ univ.erase k, ((x k - x l)⁻¹ * (y - x l)) := by
  simp only [Lagrange.basis, Lagrange.basisDivisor, eval_prod, eval_mul, eval_C, eval_sub, eval_X]

/-- the sign pattern of the Lagrange basis on the `i`-th gap -/
noncomputable def eps (i : Fin N) (k : Fin (N + 1)) : ℝ :=
  if k.val ≤ i.val then (-1) ^ (i.val - k.val) else (-1) ^ (k.val - i.val - 1)

theorem eps_eq_or (i : Fin N) (k : Fin (N + 1)) : eps i k = 1 ∨ eps i k = -1 := by
  unfold eps; split_ifs <;> exact neg_one_pow_eq_or ℝ _

theorem eps_mul_self (i : Fin N) (k : Fin (N + 1)) : eps i k * eps i k = 1 := by
  rcases eps_eq_or i k with h | h <;> rw [h] <;> norm_num

theorem eps_castSucc (i : Fin N) : eps i i.castSucc = 1 := by
  simp [eps]

theorem eps_succ (i : Fin N) : eps i i.succ = 1 := by
  simp [eps]

theorem eps_consec {i r : Fin N} (h : r ≠ i) : eps i r.castSucc * eps i r.succ = -1 := by
  unfold eps
  have hne : r.val ≠ i.val := fun h' => h (Fin.ext h')
  simp only [Fin.val_castSucc, Fin.val_succ]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [if_pos (by omega), if_pos (by omega)]
    have : i.val - r.val = (i.val - (r.val + 1)) + 1 := by omega
    rw [this, pow_succ]
    have h2 := neg_one_pow_eq_or ℝ (i.val - (r.val + 1))
    rcases h2 with h2 | h2 <;> rw [h2] <;> norm_num
  · rw [if_neg (by omega), if_neg (by omega)]
    have : r.val + 1 - i.val - 1 = (r.val - i.val - 1) + 1 := by omega
    rw [this, pow_succ]
    have h2 := neg_one_pow_eq_or ℝ (r.val - i.val - 1)
    rcases h2 with h2 | h2 <;> rw [h2] <;> norm_num

/-- the polynomial that coincides with the Lebesgue function on the `i`-th gap -/
noncomputable def Fp (x : Fin (N + 1) → ℝ) (i : Fin N) : ℝ[X] :=
  Lagrange.interpolate univ x (eps i)

theorem Fp_eval_node {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (i : Fin N) (k : Fin (N + 1)) :
    (Fp x i).eval (x k) = eps i k :=
  Lagrange.eval_interpolate_at_node _ hx.injective.injOn (mem_univ k)

theorem Fp_degree_lt {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (i : Fin N) :
    (Fp x i).degree < ((N + 1 : ℕ) : WithBot ℕ) := by
  have := Lagrange.degree_interpolate_lt (eps i) (s := univ) (v := x) hx.injective.injOn
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact this

theorem Fp_eval (x : Fin (N + 1) → ℝ) (i : Fin N) (y : ℝ) :
    (Fp x i).eval y = ∑ k, eps i k * (Lagrange.basis univ x k).eval y := by
  simp [Fp, Lagrange.interpolate_apply, eval_finsetSum]

/-- sign of the product of two consecutive basis polynomials -/
theorem basis_consec_sign {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (r : Fin N) {y : ℝ}
    (hy : ∀ k, y ≠ x k) :
    (Lagrange.basis univ x r.castSucc).eval y * (Lagrange.basis univ x r.succ).eval y *
      ((y - x r.castSucc) * (y - x r.succ)) < 0 := by
  have hab : r.castSucc ≠ r.succ := (Fin.castSucc_lt_succ).ne
  have hlt : x r.castSucc < x r.succ := hx Fin.castSucc_lt_succ
  have hb : r.succ ∈ univ.erase r.castSucc := mem_erase.mpr ⟨hab.symm, mem_univ _⟩
  have ha : r.castSucc ∈ univ.erase r.succ := mem_erase.mpr ⟨hab, mem_univ _⟩
  rw [basis_eval_eq, basis_eval_eq, ← Finset.mul_prod_erase _ _ hb, ← Finset.mul_prod_erase _ _ ha,
    Finset.erase_right_comm (a := r.succ) (b := r.castSucc)]
  set S := (univ.erase r.castSucc).erase r.succ with hS
  have hpos : 0 < (∏ l ∈ S, ((x r.castSucc - x l)⁻¹ * (y - x l))) *
      (∏ l ∈ S, ((x r.succ - x l)⁻¹ * (y - x l))) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_pos fun l hl => ?_
    have hl1 : l ≠ r.succ := (mem_erase.mp hl).1
    have hl2 : l ≠ r.castSucc := (mem_erase.mp (mem_erase.mp hl).2).1
    have hyl : y - x l ≠ 0 := sub_ne_zero.mpr (hy l)
    have hsq : 0 < (y - x l) * (y - x l) := mul_self_pos.mpr hyl
    have hprod : 0 < (x r.castSucc - x l) * (x r.succ - x l) := by
      have hlv1 : l.val ≠ r.val + 1 := fun h => hl1 (Fin.ext (by simpa using h))
      have hlv2 : l.val ≠ r.val := fun h => hl2 (Fin.ext (by simpa using h))
      rcases lt_or_gt_of_ne hlv2 with h | h
      · have h1 : x l < x r.castSucc := hx (by rw [Fin.lt_def]; simpa using h)
        nlinarith
      · have h1 : x r.succ < x l := hx (by rw [Fin.lt_def]; simp; omega)
        nlinarith
    have : (x r.castSucc - x l)⁻¹ * (y - x l) * ((x r.succ - x l)⁻¹ * (y - x l)) =
        ((x r.castSucc - x l) * (x r.succ - x l))⁻¹ * ((y - x l) * (y - x l)) := by
      rw [mul_inv]; ring
    rw [this]
    exact mul_pos (inv_pos.mpr hprod) hsq
  have hya : y - x r.castSucc ≠ 0 := sub_ne_zero.mpr (hy _)
  have hyb : y - x r.succ ≠ 0 := sub_ne_zero.mpr (hy _)
  have hc : (x r.castSucc - x r.succ)⁻¹ * (x r.succ - x r.castSucc)⁻¹ < 0 := by
    have h1 : (x r.castSucc - x r.succ)⁻¹ < 0 := inv_lt_zero.mpr (by linarith)
    have h2 : 0 < (x r.succ - x r.castSucc)⁻¹ := inv_pos.mpr (by linarith)
    exact mul_neg_of_neg_of_pos h1 h2
  have hsq : 0 < ((y - x r.castSucc) * (y - x r.succ)) ^ 2 := by positivity
  set A := ∏ l ∈ S, ((x r.castSucc - x l)⁻¹ * (y - x l)) with hA
  set B := ∏ l ∈ S, ((x r.succ - x l)⁻¹ * (y - x l)) with hB
  have key : (x r.castSucc - x r.succ)⁻¹ * (y - x r.succ) * A *
      ((x r.succ - x r.castSucc)⁻¹ * (y - x r.castSucc) * B) *
      ((y - x r.castSucc) * (y - x r.succ)) =
      ((x r.castSucc - x r.succ)⁻¹ * (x r.succ - x r.castSucc)⁻¹) * (A * B) *
        ((y - x r.castSucc) * (y - x r.succ)) ^ 2 := by ring
  rw [key]
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hc hpos) hsq

/-- Lemma Sign: on the open gap `i`, `eps i k * ℓ_k > 0`. -/
theorem eps_mul_basis_pos {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (i : Fin N) {y : ℝ}
    (hy : y ∈ Ioo (x i.castSucc) (x i.succ)) (k : Fin (N + 1)) :
    0 < eps i k * (Lagrange.basis univ x k).eval y := by
  -- y is not a node
  have hyn : ∀ k, y ≠ x k := by
    intro k hk
    rcases le_or_gt k.val i.val with h | h
    · have : x k ≤ x i.castSucc := hx.monotone (by rw [Fin.le_def]; simpa using h)
      linarith [hy.1]
    · have : x i.succ ≤ x k := hx.monotone (by rw [Fin.le_def]; simp; omega)
      linarith [hy.2]
  set s : Fin (N + 1) → ℝ := fun k => eps i k * (Lagrange.basis univ x k).eval y with hs
  -- consecutive products are positive
  have hcons : ∀ r : Fin N, 0 < s r.castSucc * s r.succ := by
    intro r
    have h1 := basis_consec_sign hx r hyn
    by_cases hr : r = i
    · subst hr
      have h2 : (y - x r.castSucc) * (y - x r.succ) < 0 :=
        mul_neg_of_pos_of_neg (by linarith [hy.1]) (by linarith [hy.2])
      simp only [hs, eps_castSucc, eps_succ, one_mul]
      nlinarith
    · have h2 : 0 < (y - x r.castSucc) * (y - x r.succ) := by
        have hne : r.val ≠ i.val := fun h' => hr (Fin.ext h')
        rcases lt_or_gt_of_ne hne with h | h
        · have : x r.succ ≤ x i.castSucc := hx.monotone (by rw [Fin.le_def]; simp; omega)
          have hlt : x r.castSucc < x r.succ := hx Fin.castSucc_lt_succ
          exact mul_pos (by linarith [hy.1]) (by linarith [hy.1])
        · have : x i.succ ≤ x r.castSucc := hx.monotone (by rw [Fin.le_def]; simp; omega)
          have hlt : x r.castSucc < x r.succ := hx Fin.castSucc_lt_succ
          exact mul_pos_of_neg_of_neg (by linarith [hy.2]) (by linarith [hy.2])
      have h3 := eps_consec hr
      have : s r.castSucc * s r.succ = (eps i r.castSucc * eps i r.succ) *
          ((Lagrange.basis univ x r.castSucc).eval y * (Lagrange.basis univ x r.succ).eval y) := by
        simp only [hs]; ring
      rw [this, h3]
      nlinarith
  -- all have the sign of s 0
  have hall : ∀ k : Fin (N + 1), 0 < s 0 * s k := by
    intro k
    induction k using Fin.induction with
    | zero =>
      have := hcons ⟨0, by
        rcases Nat.eq_zero_or_pos N with h | h
        · exact absurd i.2 (by omega)
        · exact h⟩
      have h0 : s 0 ≠ 0 := by
        intro h0
        have h00 : s (Fin.castSucc ⟨0, by
          rcases Nat.eq_zero_or_pos N with h | h
          · exact absurd i.2 (by omega)
          · exact h⟩) = 0 := h0
        rw [h00, zero_mul] at this
        exact lt_irrefl _ this
      exact mul_self_pos.mpr h0
    | succ r ih =>
      have h1 := hcons r
      have hne : s r.castSucc ≠ 0 := by
        intro h0; rw [h0, mul_zero] at ih; exact lt_irrefl _ ih
      have hsq : 0 < s r.castSucc * s r.castSucc := mul_self_pos.mpr hne
      by_contra hcon
      push Not at hcon
      nlinarith
  -- anchor: s i.castSucc > 0
  have hanchor : 0 < s i.castSucc := by
    simp only [hs, eps_castSucc, one_mul]
    rw [basis_eval_eq]
    refine Finset.prod_pos fun l hl => ?_
    have hl1 : l ≠ i.castSucc := (mem_erase.mp hl).1
    have hlv : l.val ≠ i.val := fun h => hl1 (Fin.ext (by simpa using h))
    rcases lt_or_gt_of_ne hlv with h | h
    · have h1 : x l < x i.castSucc := hx (by rw [Fin.lt_def]; simpa using h)
      exact mul_pos (inv_pos.mpr (by linarith)) (by linarith [hy.1])
    · have h1 : x i.succ ≤ x l := hx.monotone (by rw [Fin.le_def]; simp; omega)
      have h2 : x i.castSucc < x i.succ := hx Fin.castSucc_lt_succ
      exact mul_pos_of_neg_of_neg (inv_lt_zero.mpr (by linarith)) (by linarith [hy.2])
  have h0 : 0 < s 0 := by
    have := hall i.castSucc
    by_contra hcon
    push Not at hcon
    nlinarith
  have := hall k
  by_contra hcon
  push Not at hcon
  nlinarith

theorem abs_basis_eq {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (i : Fin N) {y : ℝ}
    (hy : y ∈ Ioo (x i.castSucc) (x i.succ)) (k : Fin (N + 1)) :
    |(Lagrange.basis univ x k).eval y| = eps i k * (Lagrange.basis univ x k).eval y := by
  have h := eps_mul_basis_pos hx i hy k
  rcases eps_eq_or i k with he | he
  · rw [he, one_mul] at h ⊢; exact abs_of_pos h
  · rw [he] at h ⊢
    rw [abs_of_neg (by linarith)]; ring

theorem lebesgue_eq_Fp {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (i : Fin N) {y : ℝ}
    (hy : y ∈ Icc (x i.castSucc) (x i.succ)) : lebesgueFunction x y = (Fp x i).eval y := by
  have hlt : x i.castSucc < x i.succ := hx Fin.castSucc_lt_succ
  have hEq : EqOn (lebesgueFunction x) (fun y => (Fp x i).eval y) (Ioo (x i.castSucc) (x i.succ)) := by
    intro z hz
    simp only [Fp_eval]
    unfold lebesgueFunction
    exact Finset.sum_congr rfl fun k _ => abs_basis_eq hx i hz k
  have := hEq.of_subset_closure (continuous_lebesgue x).continuousOn
    (Polynomial.continuous _).continuousOn Ioo_subset_Icc_self (by rw [closure_Ioo hlt.ne])
  exact this hy

theorem abs_Fp_le (x : Fin (N + 1) → ℝ) (i : Fin N) (y : ℝ) :
    |(Fp x i).eval y| ≤ lebesgueFunction x y := by
  rw [Fp_eval]
  unfold lebesgueFunction
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  rw [abs_mul]
  rcases eps_eq_or i k with he | he <;> rw [he] <;> simp

theorem one_le_lebesgue {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (y : ℝ) :
    1 ≤ lebesgueFunction x y := by
  have h := Lagrange.sum_basis (s := univ) (v := x) hx.injective.injOn univ_nonempty
  have h1 : (∑ k, (Lagrange.basis univ x k).eval y) = 1 := by
    rw [← eval_finsetSum, h, eval_one]
  unfold lebesgueFunction
  calc (1 : ℝ) = |∑ k, (Lagrange.basis univ x k).eval y| := by rw [h1, abs_one]
    _ ≤ _ := Finset.abs_sum_le_sum_abs _ _

theorem exists_gap (hN : 0 < N) {x : Fin (N + 1) → ℝ} (_hx : StrictMono x) {y : ℝ} (h0 : x 0 ≤ y)
    (h1 : y ≤ x (Fin.last N)) : ∃ i : Fin N, y ∈ Icc (x i.castSucc) (x i.succ) := by
  by_contra hcon
  push Not at hcon
  have key : ∀ k : Fin (N + 1), x k ≤ y := by
    intro k
    induction k using Fin.induction with
    | zero => exact h0
    | succ r ih =>
      by_contra hlt
      push Not at hlt
      exact hcon r ⟨ih, hlt.le⟩
  have hlast := key (Fin.last N)
  have hy : y = x (Fin.last N) := le_antisymm h1 hlast
  refine hcon ⟨N - 1, by omega⟩ ⟨key _, ?_⟩
  rw [hy]
  refine le_of_eq (congrArg x (Fin.ext ?_))
  simp
  omega


/-- the sign condition gives a root in every gap other than the `i`-th -/
theorem exists_root_in_gap {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (i : Fin N) (P : ℝ[X])
    (hsign : ∀ k, 0 < eps i k * P.eval (x k)) {r : Fin N} (hr : r ≠ i) :
    ∃ z ∈ Ioo (x r.castSucc) (x r.succ), P.eval z = 0 := by
  have hlt : x r.castSucc < x r.succ := hx Fin.castSucc_lt_succ
  have h1 := hsign r.castSucc
  have h2 := hsign r.succ
  have h3 := eps_consec hr
  have hneg : P.eval (x r.castSucc) * P.eval (x r.succ) < 0 := by
    nlinarith [mul_pos h1 h2]
  have hcont : ContinuousOn (fun y => P.eval y) (Icc (x r.castSucc) (x r.succ)) :=
    (Polynomial.continuous P).continuousOn
  have hne : P.eval (x r.castSucc) ≠ 0 := by
    intro h; rw [h, zero_mul] at hneg; exact lt_irrefl _ hneg
  rcases lt_or_gt_of_ne hne with ha | ha
  · have hb : 0 < P.eval (x r.succ) := by nlinarith
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo hlt.le hcont ⟨ha, hb⟩
    exact ⟨z, hz, hz0⟩
  · have hb : P.eval (x r.succ) < 0 := by nlinarith
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo' hlt.le hcont ⟨hb, ha⟩
    exact ⟨z, hz, hz0⟩

/-- Root structure: a polynomial of degree `≤ N` with the sign pattern `eps i` at the nodes
factors as an affine polynomial without zero in the node hull times the linear factors of one
root in every gap other than the `i`-th. -/
theorem root_structure {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (i : Fin N) (P : ℝ[X])
    (hdeg : P.natDegree ≤ N) (hsign : ∀ k, 0 < eps i k * P.eval (x k)) (ρ : Fin N → ℝ)
    (hρ : ∀ r, r ≠ i → ρ r ∈ Ioo (x r.castSucc) (x r.succ) ∧ P.eval (ρ r) = 0) :
    ∃ h : ℝ[X], h.natDegree ≤ 1 ∧ P = h * ∏ r ∈ univ.erase i, (X - C (ρ r)) ∧
      ∀ y ∈ Icc (x 0) (x (Fin.last N)), ∀ y' ∈ Icc (x 0) (x (Fin.last N)),
        0 < h.eval y * h.eval y' := by
  classical
  have hN : 0 < N := i.pos
  have hρlt : ∀ r r' : Fin N, r ≠ i → r' ≠ i → r < r' → ρ r < ρ r' := by
    intro r r' hr hr' hlt
    have h1 := (hρ r hr).1.2
    have h2 := (hρ r' hr').1.1
    have h3 : x r.succ ≤ x r'.castSucc := hx.monotone (by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; exact hlt)
    linarith
  have hρne : ∀ r r' : Fin N, r ≠ i → r' ≠ i → r ≠ r' → ρ r ≠ ρ r' := by
    intro r r' hr hr' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hρlt r r' hr hr' h).ne
    · exact (hρlt r' r hr' hr h).ne'
  set Q : ℝ[X] := ∏ r ∈ univ.erase i, (X - C (ρ r)) with hQ
  have hdvd : Q ∣ P := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro r hr r' hr' hne
      exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr
        (hρne r r' (ne_of_mem_erase hr) (ne_of_mem_erase hr') hne)).isUnit
    · intro r hr
      exact dvd_iff_isRoot.mpr (hρ r (ne_of_mem_erase hr)).2
  obtain ⟨h, hh⟩ := hdvd
  have hP0 : P ≠ 0 := by
    intro h0
    have := hsign 0
    rw [h0, eval_zero, mul_zero] at this
    exact lt_irrefl _ this
  have hQ0 : Q ≠ 0 := fun h0 => hP0 (by rw [hh, h0, zero_mul])
  have hh0 : h ≠ 0 := fun h0 => hP0 (by rw [hh, h0, mul_zero])
  have hQdeg : Q.natDegree = N - 1 := by
    rw [hQ, natDegree_finsetProd_X_sub_C_eq_card, card_erase_of_mem (mem_univ i), card_univ,
      Fintype.card_fin]
  have hhdeg : h.natDegree ≤ 1 := by
    have := natDegree_mul hQ0 hh0
    rw [← hh, hQdeg] at this
    omega
  refine ⟨h, hhdeg, by rw [hh, mul_comm], ?_⟩
  have hQeval : ∀ y, Q.eval y = ∏ r ∈ univ.erase i, (y - ρ r) := by
    intro y; simp [hQ, eval_prod]
  -- consecutive nodes
  have hcons : ∀ k : Fin N, 0 < h.eval (x k.castSucc) * h.eval (x k.succ) := by
    intro k
    have hPk : P.eval (x k.castSucc) * P.eval (x k.succ) =
        (Q.eval (x k.castSucc) * Q.eval (x k.succ)) *
          (h.eval (x k.castSucc) * h.eval (x k.succ)) := by
      rw [hh, eval_mul, eval_mul]; ring
    have hpair : ∀ r : Fin N, r ≠ i → r ≠ k →
        0 < (x k.castSucc - ρ r) * (x k.succ - ρ r) := by
      intro r hr hrk
      have hlt : x k.castSucc < x k.succ := hx Fin.castSucc_lt_succ
      have hne : r.val ≠ k.val := fun h' => hrk (Fin.ext h')
      rcases lt_or_gt_of_ne hne with h' | h'
      · have h3 : x r.succ ≤ x k.castSucc := hx.monotone (by
          rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; omega)
        have := (hρ r hr).1.2
        exact mul_pos (by linarith) (by linarith)
      · have h3 : x k.succ ≤ x r.castSucc := hx.monotone (by
          rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; omega)
        have := (hρ r hr).1.1
        exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
    have h1 := hsign k.castSucc
    have h2 := hsign k.succ
    by_cases hk : k = i
    · subst hk
      have hQpos : 0 < Q.eval (x k.castSucc) * Q.eval (x k.succ) := by
        rw [hQeval, hQeval, ← Finset.prod_mul_distrib]
        exact Finset.prod_pos fun r hr => hpair r (ne_of_mem_erase hr) (ne_of_mem_erase hr)
      rw [eps_castSucc, one_mul] at h1
      rw [eps_succ, one_mul] at h2
      have hPpos : 0 < P.eval (x k.castSucc) * P.eval (x k.succ) := mul_pos h1 h2
      rw [hPk] at hPpos
      by_contra hcon
      push Not at hcon
      nlinarith
    · have hkmem : k ∈ univ.erase i := mem_erase.mpr ⟨hk, mem_univ _⟩
      have hQneg : Q.eval (x k.castSucc) * Q.eval (x k.succ) < 0 := by
        rw [hQeval, hQeval, ← Finset.prod_mul_distrib, ← Finset.mul_prod_erase _ _ hkmem]
        have hkk : (x k.castSucc - ρ k) * (x k.succ - ρ k) < 0 := by
          have := (hρ k hk).1
          exact mul_neg_of_neg_of_pos (by linarith [this.1]) (by linarith [this.2])
        refine mul_neg_of_neg_of_pos hkk (Finset.prod_pos fun r hr => ?_)
        exact hpair r (ne_of_mem_erase (mem_of_mem_erase hr)) (ne_of_mem_erase hr)
      have hPneg : P.eval (x k.castSucc) * P.eval (x k.succ) < 0 := by
        have h3 := eps_consec hk
        nlinarith [mul_pos h1 h2]
      rw [hPk] at hPneg
      by_contra hcon
      push Not at hcon
      nlinarith
  -- h is affine
  have haff : ∀ y, h.eval y = h.coeff 1 * y + h.coeff 0 := by
    intro y
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hhdeg]
    simp
  -- all nodes have the sign of node 0
  have hnodes : ∀ k : Fin (N + 1), 0 < h.eval (x 0) * h.eval (x k) := by
    intro k
    induction k using Fin.induction with
    | zero =>
      have h1 := hcons ⟨0, hN⟩
      have h0 : h.eval (x 0) ≠ 0 := by
        intro h0
        have h00 : h.eval (x (Fin.castSucc (⟨0, hN⟩ : Fin N))) = 0 := h0
        rw [h00, zero_mul] at h1
        exact lt_irrefl _ h1
      exact mul_self_pos.mpr h0
    | succ r ih =>
      have h1 := hcons r
      have hne : h.eval (x r.castSucc) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at ih; exact lt_irrefl _ ih
      have hsq : 0 < h.eval (x r.castSucc) * h.eval (x r.castSucc) := mul_self_pos.mpr hne
      by_contra hcon
      push Not at hcon
      nlinarith
  have hgap : ∀ y ∈ Icc (x 0) (x (Fin.last N)), 0 < h.eval (x 0) * h.eval y := by
    intro y hy
    obtain ⟨k, hk⟩ := exists_gap hN hx hy.1 hy.2
    have h2 := hnodes k.castSucc
    have h3 := hnodes k.succ
    have hlt : x k.castSucc < x k.succ := hx Fin.castSucc_lt_succ
    have hid : (x k.succ - x k.castSucc) * h.eval y =
        (x k.succ - y) * h.eval (x k.castSucc) + (y - x k.castSucc) * h.eval (x k.succ) := by
      rw [haff y, haff (x k.castSucc), haff (x k.succ)]; ring
    have hid2 : (x k.succ - x k.castSucc) * (h.eval (x 0) * h.eval y) =
        (x k.succ - y) * (h.eval (x 0) * h.eval (x k.castSucc)) +
          (y - x k.castSucc) * (h.eval (x 0) * h.eval (x k.succ)) := by
      linear_combination (h.eval (x 0)) * hid
    have hpos : 0 < (x k.succ - y) * (h.eval (x 0) * h.eval (x k.castSucc)) +
          (y - x k.castSucc) * (h.eval (x 0) * h.eval (x k.succ)) := by
      rcases hk.1.lt_or_eq with hlt1 | heq1
      · have : 0 ≤ (x k.succ - y) * (h.eval (x 0) * h.eval (x k.castSucc)) :=
          mul_nonneg (by linarith [hk.2]) h2.le
        have : 0 < (y - x k.castSucc) * (h.eval (x 0) * h.eval (x k.succ)) :=
          mul_pos (by linarith) h3
        linarith
      · have : 0 < (x k.succ - y) * (h.eval (x 0) * h.eval (x k.castSucc)) :=
          mul_pos (by linarith) h2
        have : 0 ≤ (y - x k.castSucc) * (h.eval (x 0) * h.eval (x k.succ)) :=
          mul_nonneg (by linarith) h3.le
        linarith
    rw [← hid2] at hpos
    exact (pos_iff_pos_of_mul_pos hpos).mp (by linarith)
  intro y hy y' hy'
  have h1 := hgap y hy
  have h2 := hgap y' hy'
  have h0 : h.eval (x 0) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h1; exact lt_irrefl _ h1
  have hsq : 0 < h.eval (x 0) * h.eval (x 0) := mul_self_pos.mpr h0
  by_contra hcon
  push Not at hcon
  nlinarith [mul_pos h1 h2]

theorem Fp_sign {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (i : Fin N) (k : Fin (N + 1)) :
    0 < eps i k * (Fp x i).eval (x k) := by
  rw [Fp_eval_node hx, eps_mul_self]; exact one_pos

theorem Fp_natDegree_le {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (i : Fin N) :
    (Fp x i).natDegree ≤ N := by
  have h := Fp_degree_lt hx i
  by_cases h0 : Fp x i = 0
  · rw [h0]; simp
  · rw [degree_eq_natDegree h0] at h
    have : (Fp x i).natDegree < N + 1 := by exact_mod_cast h
    omega

/-- the chosen roots in the gaps other than `i` -/
theorem exists_roots {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (i : Fin N) (P : ℝ[X])
    (hsign : ∀ k, 0 < eps i k * P.eval (x k)) :
    ∃ ρ : Fin N → ℝ, ∀ r, r ≠ i → ρ r ∈ Ioo (x r.castSucc) (x r.succ) ∧ P.eval (ρ r) = 0 := by
  classical
  refine ⟨fun r => if h : r = i then 0 else (exists_root_in_gap hx i P hsign h).choose,
    fun r hr => ?_⟩
  simp only [dif_neg hr]
  exact (exists_root_in_gap hx i P hsign hr).choose_spec

/-- strict log-concavity in midpoint form -/
theorem Fp_midpoint_lt {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (hN : 2 ≤ N) (i : Fin N)
    {a b : ℝ} (ha : a ∈ Icc (x i.castSucc) (x i.succ)) (hb : b ∈ Icc (x i.castSucc) (x i.succ))
    (hab : a ≠ b) :
    (Fp x i).eval a * (Fp x i).eval b < (Fp x i).eval ((a + b) / 2) ^ 2 := by
  classical
  obtain ⟨ρ, hρ⟩ := exists_roots hx i (Fp x i) (Fp_sign hx i)
  obtain ⟨h, hhdeg, hfac, hhsign⟩ :=
    root_structure hx i (Fp x i) (Fp_natDegree_le hx i) (Fp_sign hx i) ρ hρ
  have hhull : ∀ y ∈ Icc (x i.castSucc) (x i.succ), y ∈ Icc (x 0) (x (Fin.last N)) := by
    intro y hy
    exact ⟨(hx.monotone (Fin.zero_le _)).trans hy.1, hy.2.trans (hx.monotone (Fin.le_last _))⟩
  have hm : (a + b) / 2 ∈ Icc (x i.castSucc) (x i.succ) :=
    ⟨by linarith [ha.1, hb.1], by linarith [ha.2, hb.2]⟩
  have heval : ∀ y, (Fp x i).eval y = h.eval y * ∏ r ∈ univ.erase i, (y - ρ r) := by
    intro y
    conv_lhs => rw [hfac]
    simp [eval_prod]
  have haff : ∀ y, h.eval y = h.coeff 1 * y + h.coeff 0 := by
    intro y
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hhdeg]
    simp
  have hh1 : 0 < h.eval a * h.eval b := hhsign a (hhull a ha) b (hhull b hb)
  have hh2 : h.eval a * h.eval b ≤ h.eval ((a + b) / 2) ^ 2 := by
    rw [haff a, haff b, haff ((a + b) / 2)]
    nlinarith [sq_nonneg (h.coeff 1 * a - h.coeff 1 * b)]
  have hne : (univ.erase i).Nonempty := by
    rw [← Finset.card_pos, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
    omega
  have hfac1 : ∀ r ∈ univ.erase i, 0 < (a - ρ r) * (b - ρ r) := by
    intro r hr
    have hri : r ≠ i := ne_of_mem_erase hr
    have hne : r.val ≠ i.val := fun h' => hri (Fin.ext h')
    rcases lt_or_gt_of_ne hne with h' | h'
    · have h3 : x r.succ ≤ x i.castSucc := hx.monotone (by
        rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; omega)
      have := (hρ r hri).1.2
      exact mul_pos (by linarith [ha.1]) (by linarith [hb.1])
    · have h3 : x i.succ ≤ x r.castSucc := hx.monotone (by
        rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; omega)
      have := (hρ r hri).1.1
      exact mul_pos_of_neg_of_neg (by linarith [ha.2]) (by linarith [hb.2])
  have hfac2 : ∀ r ∈ univ.erase i, (a - ρ r) * (b - ρ r) < ((a + b) / 2 - ρ r) ^ 2 := by
    intro r _
    have : 0 < (a - b) ^ 2 := by
      have : a - b ≠ 0 := sub_ne_zero.mpr hab
      positivity
    nlinarith
  have hprod := Finset.prod_lt_prod_of_nonempty hfac1 hfac2 hne
  have hprodpos : 0 < ∏ r ∈ univ.erase i, (a - ρ r) * (b - ρ r) := Finset.prod_pos hfac1
  rw [heval a, heval b, heval ((a + b) / 2)]
  have e1 : (h.eval a * (∏ r ∈ univ.erase i, (a - ρ r))) *
      (h.eval b * (∏ r ∈ univ.erase i, (b - ρ r))) =
      (h.eval a * h.eval b) * (∏ r ∈ univ.erase i, ((a - ρ r) * (b - ρ r))) := by
    rw [Finset.prod_mul_distrib]; ring
  have e2 : (h.eval ((a + b) / 2) * (∏ r ∈ univ.erase i, ((a + b) / 2 - ρ r))) ^ 2 =
      h.eval ((a + b) / 2) ^ 2 * (∏ r ∈ univ.erase i, ((a + b) / 2 - ρ r) ^ 2) := by
    rw [mul_pow, Finset.prod_pow]
  rw [e1, e2]
  calc (h.eval a * h.eval b) * (∏ r ∈ univ.erase i, ((a - ρ r) * (b - ρ r)))
      < (h.eval a * h.eval b) * (∏ r ∈ univ.erase i, ((a + b) / 2 - ρ r) ^ 2) :=
        mul_lt_mul_of_pos_left hprod hh1
    _ ≤ h.eval ((a + b) / 2) ^ 2 * (∏ r ∈ univ.erase i, ((a + b) / 2 - ρ r) ^ 2) :=
        mul_le_mul_of_nonneg_right hh2 (le_of_lt (lt_trans hprodpos hprod))

/-- the maximiser of the Lebesgue function on the `i`-th gap -/
noncomputable def tau (x : Fin (N + 1) → ℝ) (i : Fin N) : ℝ :=
  Classical.epsilon fun t => t ∈ Icc (x i.castSucc) (x i.succ) ∧
      ∀ y ∈ Icc (x i.castSucc) (x i.succ), (Fp x i).eval y ≤ (Fp x i).eval t

theorem tau_spec {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (i : Fin N) :
    tau x i ∈ Icc (x i.castSucc) (x i.succ) ∧
      ∀ y ∈ Icc (x i.castSucc) (x i.succ), (Fp x i).eval y ≤ (Fp x i).eval (tau x i) := by
  have hlt : x i.castSucc < x i.succ := hx Fin.castSucc_lt_succ
  have hex : ∃ t, t ∈ Icc (x i.castSucc) (x i.succ) ∧
      ∀ y ∈ Icc (x i.castSucc) (x i.succ), (Fp x i).eval y ≤ (Fp x i).eval t := by
    obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hlt.le)
      (Polynomial.continuous (Fp x i)).continuousOn
    exact ⟨t, ht, fun y hy => hmax hy⟩
  exact Classical.epsilon_spec hex

theorem Fp_tau_ge_one {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (i : Fin N) :
    1 ≤ (Fp x i).eval (tau x i) := by
  rw [← lebesgue_eq_Fp hx i (tau_spec hx i).1]
  exact one_le_lebesgue hx _

theorem tau_unique {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (hN : 2 ≤ N) (i : Fin N) {t : ℝ}
    (ht : t ∈ Icc (x i.castSucc) (x i.succ))
    (hmax : ∀ y ∈ Icc (x i.castSucc) (x i.succ), (Fp x i).eval y ≤ (Fp x i).eval t) :
    t = tau x i := by
  by_contra hne
  obtain ⟨hτ, hτmax⟩ := tau_spec hx i
  have hm : (t + tau x i) / 2 ∈ Icc (x i.castSucc) (x i.succ) :=
    ⟨by linarith [ht.1, hτ.1], by linarith [ht.2, hτ.2]⟩
  have h1 := Fp_midpoint_lt hx hN i ht hτ hne
  have h2 : (Fp x i).eval t = (Fp x i).eval (tau x i) := le_antisymm (hτmax t ht) (hmax _ hτ)
  have h3 := hτmax _ hm
  have h4 : 1 ≤ (Fp x i).eval ((t + tau x i) / 2) := by
    rw [← lebesgue_eq_Fp hx i hm]; exact one_le_lebesgue hx _
  have h5 := Fp_tau_ge_one hx i
  rw [h2] at h1
  nlinarith

theorem tau_mem_Ioo {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (hN : 2 ≤ N) (i : Fin N) :
    tau x i ∈ Ioo (x i.castSucc) (x i.succ) ∧ 1 < (Fp x i).eval (tau x i) := by
  have hlt : x i.castSucc < x i.succ := hx Fin.castSucc_lt_succ
  obtain ⟨hτ, hτmax⟩ := tau_spec hx i
  have ha : x i.castSucc ∈ Icc (x i.castSucc) (x i.succ) := left_mem_Icc.mpr hlt.le
  have hb : x i.succ ∈ Icc (x i.castSucc) (x i.succ) := right_mem_Icc.mpr hlt.le
  have hm : (x i.castSucc + x i.succ) / 2 ∈ Icc (x i.castSucc) (x i.succ) :=
    ⟨by linarith, by linarith⟩
  have h1 := Fp_midpoint_lt hx hN i ha hb hlt.ne
  rw [Fp_eval_node hx, Fp_eval_node hx, eps_castSucc, eps_succ] at h1
  have h4 : 1 ≤ (Fp x i).eval ((x i.castSucc + x i.succ) / 2) := by
    rw [← lebesgue_eq_Fp hx i hm]; exact one_le_lebesgue hx _
  have h5 : 1 < (Fp x i).eval ((x i.castSucc + x i.succ) / 2) := by nlinarith
  have h6 : 1 < (Fp x i).eval (tau x i) := lt_of_lt_of_le h5 (hτmax _ hm)
  refine ⟨⟨lt_of_le_of_ne hτ.1 ?_, lt_of_le_of_ne hτ.2 ?_⟩, h6⟩
  · intro h
    rw [← h, Fp_eval_node hx, eps_castSucc] at h6
    exact lt_irrefl _ h6
  · intro h
    rw [h, Fp_eval_node hx, eps_succ] at h6
    exact lt_irrefl _ h6

theorem Fp_deriv_tau {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (hN : 2 ≤ N) (i : Fin N) :
    (derivative (Fp x i)).eval (tau x i) = 0 := by
  obtain ⟨hτ, hτmax⟩ := tau_spec hx i
  have hio := (tau_mem_Ioo hx hN i).1
  have hmax : IsMaxOn (fun y => (Fp x i).eval y) (Icc (x i.castSucc) (x i.succ)) (tau x i) :=
    fun y hy => hτmax y hy
  have hloc : IsLocalMax (fun y => (Fp x i).eval y) (tau x i) :=
    hmax.isLocalMax (Icc_mem_nhds hio.1 hio.2)
  exact hloc.hasDerivAt_eq_zero ((Fp x i).hasDerivAt (tau x i))

theorem gapMax_eq_sSup (x : Fin (N + 1) → ℝ) (i : Fin N) :
    gapMax x (i.val + 1) = sSup (lebesgueFunction x '' Icc (x i.castSucc) (x i.succ)) := by
  unfold gapMax extendedNodes
  have h1 : 1 ≤ i.val + 1 ∧ i.val + 1 ≤ N + 1 := ⟨by omega, by omega⟩
  have h2 : 1 ≤ i.val + 1 + 1 ∧ i.val + 1 + 1 ≤ N + 1 := ⟨by omega, by omega⟩
  rw [dif_pos h1, dif_pos h2]
  rfl

theorem gapMax_eq_tau {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (i : Fin N) :
    gapMax x (i.val + 1) = (Fp x i).eval (tau x i) := by
  obtain ⟨hτ, hτmax⟩ := tau_spec hx i
  rw [gapMax_eq_sSup]
  refine IsGreatest.csSup_eq ⟨⟨tau x i, hτ, lebesgue_eq_Fp hx i hτ⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [lebesgue_eq_Fp hx i hy]
  exact hτmax y hy

/-- `|F_i| < F_j` on the open gap `j ≠ i` -/
theorem abs_Fp_lt {x : Fin (N + 1) → ℝ} (hx : StrictMono x) {i j : Fin N} (hij : i ≠ j) {t : ℝ}
    (ht : t ∈ Ioo (x j.castSucc) (x j.succ)) :
    |(Fp x i).eval t| < (Fp x j).eval t := by
  rw [abs_lt]
  have hpos : ∀ k, 0 < eps j k * (Lagrange.basis univ x k).eval t := eps_mul_basis_pos hx j ht
  have hc := eps_consec (i := j) (r := i) hij
  have h1 := eps_castSucc i
  have h2 := eps_succ i
  have hsub : (Fp x j).eval t - (Fp x i).eval t =
      ∑ k, (1 - eps i k * eps j k) * (eps j k * (Lagrange.basis univ x k).eval t) := by
    rw [Fp_eval, Fp_eval, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := eps_mul_self j k
    linear_combination (eps i k * (Lagrange.basis univ x k).eval t) * this
  have hadd : (Fp x j).eval t + (Fp x i).eval t =
      ∑ k, (1 + eps i k * eps j k) * (eps j k * (Lagrange.basis univ x k).eval t) := by
    rw [Fp_eval, Fp_eval, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := eps_mul_self j k
    linear_combination (-(eps i k * (Lagrange.basis univ x k).eval t)) * this
  have hnn1 : ∀ k, 0 ≤ 1 - eps i k * eps j k := by
    intro k
    rcases eps_eq_or i k with h | h <;> rcases eps_eq_or j k with h' | h' <;> rw [h, h'] <;> norm_num
  have hnn2 : ∀ k, 0 ≤ 1 + eps i k * eps j k := by
    intro k
    rcases eps_eq_or i k with h | h <;> rcases eps_eq_or j k with h' | h' <;> rw [h, h'] <;> norm_num
  have hsubpos : 0 < (Fp x j).eval t - (Fp x i).eval t := by
    rw [hsub]
    refine Finset.sum_pos' (fun k _ => mul_nonneg (hnn1 k) (hpos k).le) ?_
    rcases eps_eq_or j i.castSucc with h | h
    · have h' : eps j i.succ = -1 := by rw [h] at hc; linarith
      exact ⟨i.succ, mem_univ _, mul_pos (by rw [h2, h']; norm_num) (hpos _)⟩
    · exact ⟨i.castSucc, mem_univ _, mul_pos (by rw [h1, h]; norm_num) (hpos _)⟩
  have haddpos : 0 < (Fp x j).eval t + (Fp x i).eval t := by
    rw [hadd]
    refine Finset.sum_pos' (fun k _ => mul_nonneg (hnn2 k) (hpos k).le) ?_
    rcases eps_eq_or j i.castSucc with h | h
    · exact ⟨i.castSucc, mem_univ _, mul_pos (by rw [h1, h]; norm_num) (hpos _)⟩
    · have h' : eps j i.succ = 1 := by rw [h] at hc; linarith
      exact ⟨i.succ, mem_univ _, mul_pos (by rw [h2, h']; norm_num) (hpos _)⟩
  constructor <;> linarith

/-- Key sign lemma (replaces the interlacing analysis of Kilgore and de Boor–Pinkus):
the sign of `F_i'` at the maximiser of another gap. -/
theorem key_sign {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (hN : 2 ≤ N) {i j : Fin N}
    (hij : i ≠ j) :
    (Lagrange.nodal univ x).eval (tau x i) * (derivative (Fp x i)).eval (tau x j) *
      ∏ k ∈ (univ.erase i).erase j, (tau x j - tau x k) < 0 := by
  classical
  set s := tau x i with hs
  set t := tau x j with ht
  have hsio := (tau_mem_Ioo hx hN i).1
  have htio := (tau_mem_Ioo hx hN j).1
  have hGpos : 1 ≤ (Fp x j).eval t := Fp_tau_ge_one hx j
  have habs := abs_Fp_lt hx hij htio
  set c := (Fp x i).eval t / (Fp x j).eval t with hc
  have hG0 : (Fp x j).eval t ≠ 0 := by linarith
  have hcabs : |c| < 1 := by
    rw [hc, abs_div, abs_of_pos (by linarith : (0:ℝ) < (Fp x j).eval t), div_lt_one (by linarith)]
    exact habs
  set P : ℝ[X] := Fp x i - C c * Fp x j with hP
  have hPdeg : P.natDegree ≤ N := by
    refine (natDegree_sub_le _ _).trans (max_le (Fp_natDegree_le hx i) ?_)
    exact (natDegree_C_mul_le _ _).trans (Fp_natDegree_le hx j)
  have hPsign : ∀ k, 0 < eps i k * P.eval (x k) := by
    intro k
    simp only [hP, eval_sub, eval_mul, eval_C, Fp_eval_node hx]
    have h1 := eps_mul_self i k
    have h2 : |eps i k * eps j k| = 1 := by
      rcases eps_eq_or i k with h | h <;> rcases eps_eq_or j k with h' | h' <;> rw [h, h'] <;> norm_num
    have h3 : |c * (eps i k * eps j k)| < 1 := by rw [abs_mul, h2, mul_one]; exact hcabs
    have h4 := (abs_lt.mp h3).2
    nlinarith
  have hPt : P.eval t = 0 := by
    simp only [hP, eval_sub, eval_mul, eval_C, hc]
    field_simp
    ring
  -- roots
  obtain ⟨ρ₀, hρ₀⟩ := exists_roots hx i P hPsign
  set ρ : Fin N → ℝ := Function.update ρ₀ j t with hρdef
  have hρj : ρ j = t := by simp [hρdef]
  have hρ : ∀ r, r ≠ i → ρ r ∈ Ioo (x r.castSucc) (x r.succ) ∧ P.eval (ρ r) = 0 := by
    intro r hr
    by_cases hrj : r = j
    · subst hrj; rw [hρj]; exact ⟨htio, hPt⟩
    · rw [hρdef, Function.update_of_ne hrj]; exact hρ₀ r hr
  obtain ⟨h, hhdeg, hfac, hhsign⟩ := root_structure hx i P hPdeg hPsign ρ hρ
  -- derivative at t
  have hjmem : j ∈ univ.erase i := mem_erase.mpr ⟨hij.symm, mem_univ _⟩
  set R : ℝ[X] := h * ∏ r ∈ (univ.erase i).erase j, (X - C (ρ r)) with hR
  have hPR : P = (X - C t) * R := by
    rw [hfac, hR, ← Finset.mul_prod_erase _ _ hjmem, hρj]; ring
  have hderP : (derivative P).eval t = R.eval t := by
    rw [hPR, derivative_mul]
    simp
  have hderP' : (derivative P).eval t = (derivative (Fp x i)).eval t := by
    simp only [hP, derivative_sub, derivative_mul, derivative_C, eval_sub, eval_mul,
      eval_C, zero_mul, zero_add]
    rw [Fp_deriv_tau hx hN j]; ring
  have hFder : (derivative (Fp x i)).eval t =
      h.eval t * ∏ r ∈ (univ.erase i).erase j, (t - ρ r) := by
    rw [← hderP', hderP, hR]; simp [eval_prod]
  -- positivity of the paired product
  have hpair : 0 < ∏ r ∈ (univ.erase i).erase j, ((t - ρ r) * (t - tau x r)) := by
    refine Finset.prod_pos fun r hr => ?_
    have hrj : r ≠ j := ne_of_mem_erase hr
    have hri : r ≠ i := ne_of_mem_erase (mem_of_mem_erase hr)
    have h1 := (hρ r hri).1
    have h2 := (tau_spec hx r).1
    have hne : r.val ≠ j.val := fun h' => hrj (Fin.ext h')
    rcases lt_or_gt_of_ne hne with h' | h'
    · have h3 : x r.succ ≤ x j.castSucc := hx.monotone (by
        rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; omega)
      exact mul_pos (by linarith [h1.2, htio.1]) (by linarith [h2.2, htio.1])
    · have h3 : x j.succ ≤ x r.castSucc := hx.monotone (by
        rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; omega)
      exact mul_pos_of_neg_of_neg (by linarith [h1.1, htio.2]) (by linarith [h2.1, htio.2])
  -- sign of h versus sign of the nodal polynomial at s
  have hhull : ∀ r : Fin N, ∀ y ∈ Icc (x r.castSucc) (x r.succ), y ∈ Icc (x 0) (x (Fin.last N)) := by
    intro r y hy
    exact ⟨(hx.monotone (Fin.zero_le _)).trans hy.1, hy.2.trans (hx.monotone (Fin.le_last _))⟩
  have hlastmem : x (Fin.last N) ∈ Icc (x 0) (x (Fin.last N)) :=
    ⟨hx.monotone (Fin.zero_le _), le_rfl⟩
  have hht : 0 < h.eval t * h.eval (x (Fin.last N)) :=
    hhsign t (hhull j t (Ioo_subset_Icc_self htio)) _ hlastmem
  have hQlast : 0 < ∏ r ∈ univ.erase i, (x (Fin.last N) - ρ r) := by
    refine Finset.prod_pos fun r hr => ?_
    have h1 := (hρ r (ne_of_mem_erase hr)).1.2
    have h3 : x r.succ ≤ x (Fin.last N) := hx.monotone (Fin.le_last _)
    linarith
  have hPlast : P.eval (x (Fin.last N)) =
      h.eval (x (Fin.last N)) * ∏ r ∈ univ.erase i, (x (Fin.last N) - ρ r) := by
    conv_lhs => rw [hfac]
    simp [eval_prod]
  have hh_last : 0 < eps i (Fin.last N) * h.eval (x (Fin.last N)) := by
    have := hPsign (Fin.last N)
    rw [hPlast, ← mul_assoc] at this
    exact (pos_iff_pos_of_mul_pos this).mpr hQlast
  -- nodal polynomial at s
  have hsne : s ≠ x (Fin.last N) := by
    have h3 : x i.succ ≤ x (Fin.last N) := hx.monotone (Fin.le_last _)
    linarith [hsio.2]
  have hbasis := Lagrange.eval_basis_not_at_node (s := univ) (v := x) (mem_univ (Fin.last N)) hsne
  have hw : 0 < Lagrange.nodalWeight univ x (Fin.last N) := by
    unfold Lagrange.nodalWeight
    refine Finset.prod_pos fun l hl => inv_pos.mpr ?_
    have : l < Fin.last N := lt_of_le_of_ne (Fin.le_last l) (ne_of_mem_erase hl)
    linarith [hx this]
  have hκ : Lagrange.nodalWeight univ x (Fin.last N) * (s - x (Fin.last N))⁻¹ < 0 := by
    refine mul_neg_of_pos_of_neg hw (inv_lt_zero.mpr ?_)
    have h3 : x i.succ ≤ x (Fin.last N) := hx.monotone (Fin.le_last _)
    linarith [hsio.2]
  have hsign_s := eps_mul_basis_pos hx i hsio (Fin.last N)
  rw [hbasis] at hsign_s
  -- eps * ω(s) < 0
  have hω : eps i (Fin.last N) * (Lagrange.nodal univ x).eval s < 0 := by
    by_contra hcon
    push Not at hcon
    have : eps i (Fin.last N) * ((Lagrange.nodal univ x).eval s *
        (Lagrange.nodalWeight univ x (Fin.last N) * (s - x (Fin.last N))⁻¹)) =
        (eps i (Fin.last N) * (Lagrange.nodal univ x).eval s) *
        (Lagrange.nodalWeight univ x (Fin.last N) * (s - x (Fin.last N))⁻¹) := by ring
    rw [this] at hsign_s
    nlinarith
  have heps := eps_mul_self i (Fin.last N)
  have hωh : (Lagrange.nodal univ x).eval s * h.eval t < 0 := by
    -- (eps ω)(eps h_last) < 0 gives ω h_last < 0; with h_t h_last > 0
    have h1 : (Lagrange.nodal univ x).eval s * h.eval (x (Fin.last N)) < 0 := by
      have := mul_neg_of_neg_of_pos hω hh_last
      have e : eps i (Fin.last N) * (Lagrange.nodal univ x).eval s *
          (eps i (Fin.last N) * h.eval (x (Fin.last N))) =
          (eps i (Fin.last N) * eps i (Fin.last N)) *
          ((Lagrange.nodal univ x).eval s * h.eval (x (Fin.last N))) := by ring
      rw [e, heps, one_mul] at this
      exact this
    have hl0 : h.eval (x (Fin.last N)) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hht; exact lt_irrefl _ hht
    have hsq : 0 < h.eval (x (Fin.last N)) * h.eval (x (Fin.last N)) := mul_self_pos.mpr hl0
    by_contra hcon
    push Not at hcon
    nlinarith [mul_nonneg hcon hht.le]
  rw [hFder]
  have e : (Lagrange.nodal univ x).eval s * (h.eval t * ∏ r ∈ (univ.erase i).erase j, (t - ρ r)) *
      ∏ k ∈ (univ.erase i).erase j, (t - tau x k) =
      ((Lagrange.nodal univ x).eval s * h.eval t) *
        ∏ r ∈ (univ.erase i).erase j, ((t - ρ r) * (t - tau x r)) := by
    rw [Finset.prod_mul_distrib]; ring
  rw [e]
  exact mul_neg_of_neg_of_pos hωh hpair

/-- the maximiser is not a node -/
theorem tau_ne_node {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (hN : 2 ≤ N) (i : Fin N)
    (k : Fin (N + 1)) : tau x i ≠ x k := by
  have hio := (tau_mem_Ioo hx hN i).1
  intro hk
  rcases le_or_gt k.val i.val with h | h
  · have : x k ≤ x i.castSucc := hx.monotone (by rw [Fin.le_def]; simpa using h)
    linarith [hio.1]
  · have : x i.succ ≤ x k := hx.monotone (by
      rw [Fin.le_def]; simp only [Fin.val_succ]; omega)
    linarith [hio.2]

theorem tau_strictMono {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (hN : 2 ≤ N) :
    StrictMono (tau x) := by
  intro i j hij
  have h1 := (tau_mem_Ioo hx hN i).1.2
  have h2 := (tau_mem_Ioo hx hN j).1.1
  have h3 : x i.succ ≤ x j.castSucc := hx.monotone (by
    rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; exact hij)
  linarith

/-- coefficient of the differential of the `i`-th gap maximum with respect to the node `k` -/
noncomputable def Acoef (x : Fin (N + 1) → ℝ) (i : Fin N) (k : Fin (N + 1)) : ℝ :=
  -((derivative (Fp x i)).eval (x k) * (Lagrange.basis univ x k).eval (tau x i))

/-- First-order non-domination: a nonzero variation of the interior nodes cannot make all
gap maxima decrease (to first order). -/
theorem app3 {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (hN : 2 ≤ N) (v : Fin (N + 1) → ℝ)
    (h0 : v 0 = 0) (hl : v (Fin.last N) = 0)
    (hle : ∀ i : Fin N, ∑ k, v k * Acoef x i k ≤ 0) : v = 0 := by
  classical
  have : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  set q : Fin N → ℝ[X] := fun i => derivative (Fp x i) /ₘ (X - C (tau x i)) with hq
  have hqmul : ∀ i, (X - C (tau x i)) * q i = derivative (Fp x i) := fun i =>
    mul_divByMonic_eq_iff_isRoot.mpr (Fp_deriv_tau hx hN i)
  set g : Fin N → ℝ[X] := fun i => C ((Lagrange.nodal univ x).eval (tau x i)) * q i with hg
  have hcardN : Fintype.card (Fin N) = N := Fintype.card_fin N
  have hdeg : ∀ i, (g i).degree < ((Fintype.card (Fin N) - 1 : ℕ) : WithBot ℕ) := by
    intro i
    have h1 : (derivative (Fp x i)).natDegree ≤ N - 1 :=
      (natDegree_derivative_le _).trans (Nat.sub_le_sub_right (Fp_natDegree_le hx i) 1)
    have h2 : (q i).natDegree ≤ N - 2 := by
      simp only [hq]
      rw [natDegree_divByMonic _ (monic_X_sub_C _), natDegree_X_sub_C]
      omega
    have h3 : (g i).natDegree ≤ N - 2 := (natDegree_C_mul_le _ _).trans h2
    refine lt_of_le_of_lt (degree_le_of_natDegree_le h3) ?_
    rw [hcardN]
    exact_mod_cast (by omega : N - 2 < N - 1)
  have hτinj : Function.Injective (tau x) := (tau_strictMono hx hN).injective
  have hsign : ∀ i j, i ≠ j →
      (g i).eval (tau x j) * ∏ k ∈ univ.erase j, (tau x j - tau x k) < 0 := by
    intro i j hij
    have hi : i ∈ univ.erase j := mem_erase.mpr ⟨hij, mem_univ _⟩
    have hks := key_sign hx hN hij
    have hder : (derivative (Fp x i)).eval (tau x j) =
        (tau x j - tau x i) * (q i).eval (tau x j) := by
      rw [← hqmul i]; simp
    rw [← Finset.mul_prod_erase _ _ hi, Finset.erase_right_comm]
    simp only [hg, eval_mul, eval_C]
    rw [hder] at hks
    linarith [hks]
  set φ : ℝ[X] →ₗ[ℝ] ℝ :=
    ∑ k, (v k * Lagrange.nodalWeight univ x k) • Polynomial.leval (x k) with hφ
  have hφapply : ∀ P : ℝ[X], φ P = ∑ k, v k * Lagrange.nodalWeight univ x k * P.eval (x k) := by
    intro P
    simp [hφ, Polynomial.leval]
  have hφg : ∀ i, φ (g i) = ∑ k, v k * Acoef x i k := by
    intro i
    rw [hφapply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hne : tau x i ≠ x k := tau_ne_node hx hN i k
    have hb := Lagrange.eval_basis_not_at_node (s := univ) (v := x) (mem_univ k) hne
    have hder : (derivative (Fp x i)).eval (x k) = (x k - tau x i) * (q i).eval (x k) := by
      rw [← hqmul i]; simp
    have hne' : tau x i - x k ≠ 0 := sub_ne_zero.mpr hne
    simp only [Acoef, hg, eval_mul, eval_C]
    rw [hb, hder]
    field_simp
    ring
  have hzero := positivity_lemma (tau x) hτinj g hdeg hsign φ (fun i => by rw [hφg]; exact hle i)
  -- test polynomials
  funext k₀
  by_cases hk0 : k₀ = 0
  · rw [hk0, h0]; rfl
  by_cases hkl : k₀ = Fin.last N
  · rw [hkl, hl]; rfl
  set S : Finset (Fin (N + 1)) := ((univ.erase 0).erase (Fin.last N)).erase k₀ with hS
  set P : ℝ[X] := ∏ l ∈ S, (X - C (x l)) with hP
  have h0l : (0 : Fin (N + 1)) ≠ Fin.last N := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  have hScard : S.card = N - 2 := by
    rw [hS, card_erase_of_mem, card_erase_of_mem, card_erase_of_mem (mem_univ _), card_univ,
      Fintype.card_fin]
    · omega
    · exact mem_erase.mpr ⟨Ne.symm h0l, mem_univ _⟩
    · exact mem_erase.mpr ⟨hkl, mem_erase.mpr ⟨hk0, mem_univ _⟩⟩
  have hPdeg : P.degree < ((Fintype.card (Fin N) - 1 : ℕ) : WithBot ℕ) := by
    have : P.natDegree = N - 2 := by rw [hP, natDegree_finsetProd_X_sub_C_eq_card, hScard]
    refine lt_of_le_of_lt (degree_le_of_natDegree_le this.le) ?_
    rw [hcardN]
    exact_mod_cast (by omega : N - 2 < N - 1)
  have hPz := hzero P hPdeg
  rw [hφapply] at hPz
  have hPeval : ∀ y, P.eval y = ∏ l ∈ S, (y - x l) := by
    intro y; simp [hP, eval_prod]
  rw [Finset.sum_eq_single k₀] at hPz
  · have hw : Lagrange.nodalWeight univ x k₀ ≠ 0 :=
      Lagrange.nodalWeight_ne_zero hx.injective.injOn (mem_univ _)
    have hPk : P.eval (x k₀) ≠ 0 := by
      rw [hPeval]
      refine Finset.prod_ne_zero_iff.mpr fun l hl => sub_ne_zero.mpr fun h => ?_
      exact (ne_of_mem_erase hl) (hx.injective h).symm
    have := mul_eq_zero.mp hPz
    rcases this with h | h
    · rcases mul_eq_zero.mp h with h | h
      · simpa using h
      · exact absurd h hw
    · exact absurd h hPk
  · intro k _ hk
    by_cases hk0' : k = 0
    · rw [hk0', h0]; ring
    by_cases hkl' : k = Fin.last N
    · rw [hkl', hl]; ring
    have hkS : k ∈ S := mem_erase.mpr ⟨hk, mem_erase.mpr ⟨hkl', mem_erase.mpr ⟨hk0', mem_univ _⟩⟩⟩
    have : P.eval (x k) = 0 := by
      rw [hPeval]; exact Finset.prod_eq_zero hkS (sub_self _)
    rw [this, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- joint smoothness of the Lagrange basis in (nodes, evaluation point) -/
theorem contDiffAt_basisEval {n : ℕ} (k : Fin n) (x₀ : Fin n → ℝ) (hx₀ : Function.Injective x₀)
    (y₀ : ℝ) :
    ContDiffAt ℝ ⊤ (fun p : (Fin n → ℝ) × ℝ => (Lagrange.basis univ p.1 k).eval p.2) (x₀, y₀) := by
  simp only [basis_eval_eq]
  refine contDiffAt_prod fun l hl => ?_
  have hne : x₀ k - x₀ l ≠ 0 := sub_ne_zero.mpr fun h => (Finset.ne_of_mem_erase hl) (hx₀ h).symm
  have h1 : ContDiffAt ℝ ⊤ (fun p : (Fin n → ℝ) × ℝ => p.1 k - p.1 l) (x₀, y₀) := by fun_prop
  have h2 : ContDiffAt ℝ ⊤ (fun p : (Fin n → ℝ) × ℝ => p.2 - p.1 l) (x₀, y₀) := by fun_prop
  exact (h1.inv hne).mul h2

/-- the parametrised gap function -/
noncomputable def Phi {n : ℕ} (ε : Fin n → ℝ) (a b : Fin n) (p : (Fin n → ℝ) × ℝ) : ℝ :=
  ∑ k, ε k * (Lagrange.basis univ p.1 k).eval (p.1 a + p.2 * (p.1 b - p.1 a))

theorem contDiffAt_Phi {n : ℕ} (ε : Fin n → ℝ) (a b : Fin n) (x₀ : Fin n → ℝ)
    (hx₀ : Function.Injective x₀) (u₀ : ℝ) :
    ContDiffAt ℝ ⊤ (Phi ε a b) (x₀, u₀) := by
  unfold Phi
  refine ContDiffAt.sum fun k _ => contDiffAt_const.mul ?_
  have hg : ContDiffAt ℝ ⊤ (fun p : (Fin n → ℝ) × ℝ => (p.1, p.1 a + p.2 * (p.1 b - p.1 a)))
      (x₀, u₀) := by fun_prop
  exact (contDiffAt_basisEval k x₀ hx₀ (x₀ a + u₀ * (x₀ b - x₀ a))).comp (x₀, u₀) hg

theorem image_param (g : ℝ → ℝ) {α β : ℝ} (hαβ : α < β) :
    (fun u => g (α + u * (β - α))) '' Icc 0 1 = g '' Icc α β := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨α + u * (β - α), ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    have hpos : 0 < β - α := by linarith
    refine ⟨(y - α) / (β - α), ⟨div_nonneg (by linarith [hy.1]) hpos.le,
      (div_le_one hpos).mpr (by linarith [hy.2])⟩, ?_⟩
    simp only
    congr 1
    field_simp
    ring

theorem gap_as_sup {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (i : Fin N) :
    gapMax x (i.val + 1) =
      sSup ((fun u => Phi (eps i) i.castSucc i.succ (x, u)) '' Icc 0 1) := by
  have hlt : x i.castSucc < x i.succ := hx Fin.castSucc_lt_succ
  rw [gapMax_eq_sSup]
  have h1 : lebesgueFunction x '' Icc (x i.castSucc) (x i.succ) =
      (fun y => (Fp x i).eval y) '' Icc (x i.castSucc) (x i.succ) :=
    Set.image_congr fun y hy => lebesgue_eq_Fp hx i hy
  have h2 : (fun u => Phi (eps i) i.castSucc i.succ (x, u)) =
      fun u => (fun y => (Fp x i).eval y) (x i.castSucc + u * (x i.succ - x i.castSucc)) := by
    funext u
    simp only [Phi, Fp_eval]
  rw [h1, h2]
  exact congrArg sSup (image_param (fun y => (Fp x i).eval y) hlt).symm

/-- moving one node: exact difference formula for the interpolant of fixed data -/
theorem interp_shift {x₀ x' : Fin (N + 1) → ℝ} (hx₀ : StrictMono x₀) (hx' : StrictMono x')
    (i : Fin N) (k : Fin (N + 1)) (hk : ∀ l, l ≠ k → x' l = x₀ l) :
    Fp x' i = Fp x₀ i +
      C ((Fp x₀ i).eval (x₀ k) - (Fp x₀ i).eval (x' k)) * Lagrange.basis univ x' k := by
  classical
  have hdeg : (Fp x₀ i).degree < ((univ : Finset (Fin (N + 1))).card : WithBot ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin]; exact Fp_degree_lt hx₀ i
  have e1 : Fp x₀ i = Lagrange.interpolate univ x' (fun l => (Fp x₀ i).eval (x' l)) :=
    Lagrange.eq_interpolate hx'.injective.injOn hdeg
  have e2 : Fp x' i - Fp x₀ i =
      Lagrange.interpolate univ x' (eps i - fun l => (Fp x₀ i).eval (x' l)) := by
    rw [map_sub, ← e1]; rfl
  have e3 : Fp x' i - Fp x₀ i =
      C ((Fp x₀ i).eval (x₀ k) - (Fp x₀ i).eval (x' k)) * Lagrange.basis univ x' k := by
    rw [e2, Lagrange.interpolate_apply, Finset.sum_eq_single k]
    · simp only [Pi.sub_apply]
      rw [Fp_eval_node hx₀]
    · intro l _ hl
      simp only [Pi.sub_apply]
      rw [hk l hl, Fp_eval_node hx₀, sub_self, map_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [← e3]; ring

/-- The gap maximum is strictly differentiable in the nodes, with the classical formula
`∂λ_i/∂x_k = -F_i'(x_k) ℓ_k(τ_i)`. -/
theorem hasStrictFDerivAt_gap {x₀ : Fin (N + 1) → ℝ} (hx₀ : StrictMono x₀) (hN : 2 ≤ N)
    (i : Fin N) :
    ∃ A : (Fin (N + 1) → ℝ) →L[ℝ] ℝ,
      HasStrictFDerivAt (fun x : Fin (N + 1) → ℝ => gapMax x (i.val + 1)) A x₀ ∧
      ∀ v, A v = ∑ k, v k * Acoef x₀ i k := by
  classical
  have hlt : x₀ i.castSucc < x₀ i.succ := hx₀ Fin.castSucc_lt_succ
  set Φ := Phi (eps i) i.castSucc i.succ with hΦ
  set τ₀ := tau x₀ i with hτ₀
  obtain ⟨hτmem, hτmax⟩ := tau_spec hx₀ i
  set u₀ := (τ₀ - x₀ i.castSucc) / (x₀ i.succ - x₀ i.castSucc) with hu₀
  have hpos : 0 < x₀ i.succ - x₀ i.castSucc := by linarith
  have hu₀mem : u₀ ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg (by linarith [hτmem.1]) hpos.le, (div_le_one hpos).mpr (by linarith [hτmem.2])⟩
  have hyu₀ : x₀ i.castSucc + u₀ * (x₀ i.succ - x₀ i.castSucc) = τ₀ := by
    rw [hu₀]; field_simp; ring
  have hΦF : ∀ (x : Fin (N + 1) → ℝ) (u : ℝ),
      Φ (x, u) = (Fp x i).eval (x i.castSucc + u * (x i.succ - x i.castSucc)) := by
    intro x u; rw [Fp_eval]; rfl
  have hCD : ∀ u, ContDiffAt ℝ ⊤ Φ (x₀, u) := fun u =>
    contDiffAt_Phi (eps i) i.castSucc i.succ x₀ hx₀.injective u
  have hD := (hCD u₀).hasStrictFDerivAt (by simp)
  have hcont : ∀ u ∈ Icc (0:ℝ) 1, ContinuousAt Φ (x₀, u) := fun u _ => (hCD u).continuousAt
  have hcont' : ∀ᶠ x in 𝓝 x₀, ContinuousOn (fun u => Φ (x, u)) (Icc 0 1) := by
    refine Eventually.of_forall fun x => ?_
    have : (fun u => Φ (x, u)) =
        fun u => (Fp x i).eval (x i.castSucc + u * (x i.succ - x i.castSucc)) :=
      funext fun u => hΦF x u
    rw [this]
    exact ((Polynomial.continuous _).comp (by fun_prop)).continuousOn
  have huniq : ∀ u ∈ Icc (0:ℝ) 1, u ≠ u₀ → Φ (x₀, u) < Φ (x₀, u₀) := by
    intro u hu hne
    rw [hΦF, hΦF, hyu₀]
    set y := x₀ i.castSucc + u * (x₀ i.succ - x₀ i.castSucc) with hy
    have hymem : y ∈ Icc (x₀ i.castSucc) (x₀ i.succ) :=
      ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
    by_contra hcon
    push Not at hcon
    have hyτ : y = τ₀ := tau_unique hx₀ hN i hymem (fun z hz => (hτmax z hz).trans hcon)
    apply hne
    rw [hu₀, ← hyτ, hy]
    field_simp
    ring
  have hdan := danskin Φ x₀ u₀ 0 1 hu₀mem (fderiv ℝ Φ (x₀, u₀)) hD hcont hcont' huniq
  have hev : (fun x => sSup ((fun u => Φ (x, u)) '' Icc 0 1)) =ᶠ[𝓝 x₀]
      fun x => gapMax x (i.val + 1) := by
    filter_upwards [(isOpen_strictMono (N + 1)).mem_nhds hx₀] with x hx
    exact (gap_as_sup hx i).symm
  refine ⟨(fderiv ℝ Φ (x₀, u₀)).comp (ContinuousLinearMap.inl ℝ _ ℝ),
    hdan.congr_of_eventuallyEq hev, ?_⟩
  -- identification of the partial derivatives
  have key : ∀ k : Fin (N + 1),
      (fderiv ℝ Φ (x₀, u₀)) ((fun j => if k = j then (1:ℝ) else 0), (0:ℝ)) = Acoef x₀ i k := by
    intro k
    set e : Fin (N + 1) → ℝ := fun j => if k = j then (1:ℝ) else 0 with he
    have hγ : HasDerivAt (fun s : ℝ => ((x₀ + s • e, u₀) : (Fin (N + 1) → ℝ) × ℝ)) (e, 0) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => x₀ + s • e) e 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).smul_const e).const_add x₀
      exact h1.prodMk (hasDerivAt_const 0 u₀)
    have hF : HasFDerivAt Φ (fderiv ℝ Φ (x₀, u₀)) ((x₀ + (0:ℝ) • e, u₀)) := by
      simpa using hD.hasFDerivAt
    have hψ0 := HasFDerivAt.comp_hasDerivAt (0:ℝ) hF hγ
    have hψ : HasDerivAt (fun s : ℝ => Φ (x₀ + s • e, u₀)) ((fderiv ℝ Φ (x₀, u₀)) (e, 0)) 0 :=
      hψ0
    -- explicit computation
    set F₀ := Fp x₀ i with hF₀
    set κ : ℝ := e i.castSucc + u₀ * (e i.succ - e i.castSucc) with hκ
    have hyfun : (fun s : ℝ => (x₀ + s • e) i.castSucc +
        u₀ * ((x₀ + s • e) i.succ - (x₀ + s • e) i.castSucc)) = fun s => τ₀ + s * κ := by
      funext s
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hκ]
      rw [← hyu₀]; ring
    have hy : HasDerivAt (fun s : ℝ => τ₀ + s * κ) κ 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const κ).const_add τ₀
    have h1 : HasDerivAt (fun s : ℝ => F₀.eval (τ₀ + s * κ)) 0 0 := by
      have hF0' : HasDerivAt (fun y => F₀.eval y) ((derivative F₀).eval τ₀)
          ((fun s : ℝ => τ₀ + s * κ) 0) := by
        simpa using F₀.hasDerivAt τ₀
      have hc := hF0'.comp (0:ℝ) hy
      have hz : (derivative F₀).eval τ₀ * κ = 0 := by
        rw [hF₀, hτ₀, Fp_deriv_tau hx₀ hN i, zero_mul]
      rw [hz] at hc
      exact hc
    have h2 : HasDerivAt (fun s : ℝ => F₀.eval (x₀ k) - F₀.eval (x₀ k + s))
        (-(derivative F₀).eval (x₀ k)) 0 := by
      have hc := HasDerivAt.comp_const_add (x₀ k) (0:ℝ) (F₀.hasDerivAt (x₀ k + 0))
      rw [add_zero] at hc
      exact hc.const_sub (F₀.eval (x₀ k))
    set B : ℝ → ℝ := fun s => (Lagrange.basis univ (x₀ + s • e) k).eval (τ₀ + s * κ) with hB
    have hBdiff : DifferentiableAt ℝ B 0 := by
      have hc : ContDiffAt ℝ ⊤ (fun p : (Fin (N + 1) → ℝ) × ℝ => (Lagrange.basis univ p.1 k).eval p.2)
          ((fun s : ℝ => ((x₀ + s • e, τ₀ + s * κ) : (Fin (N + 1) → ℝ) × ℝ)) 0) := by
        simpa using contDiffAt_basisEval k x₀ hx₀.injective τ₀
      have hcurve : DifferentiableAt ℝ
          (fun s : ℝ => ((x₀ + s • e, τ₀ + s * κ) : (Fin (N + 1) → ℝ) × ℝ)) 0 := by fun_prop
      exact (hc.differentiableAt (by simp)).comp (0:ℝ) hcurve
    have h3 := h2.mul hBdiff.hasDerivAt
    have h4 := h1.add h3
    have hval : (0:ℝ) + (-(derivative F₀).eval (x₀ k) * B 0 +
        (F₀.eval (x₀ k) - F₀.eval (x₀ k + 0)) * deriv B 0) = Acoef x₀ i k := by
      simp only [hB, Acoef, add_zero, sub_self, zero_mul, zero_smul, zero_add]
      ring
    rw [hval] at h4
    have hev' : (fun s : ℝ => Φ (x₀ + s • e, u₀)) =ᶠ[𝓝 (0:ℝ)]
        fun s => F₀.eval (τ₀ + s * κ) + (F₀.eval (x₀ k) - F₀.eval (x₀ k + s)) * B s := by
      have hcts : ContinuousAt (fun s : ℝ => x₀ + s • e) 0 := by fun_prop
      have hmem : ∀ᶠ s in 𝓝 (0:ℝ), StrictMono (x₀ + s • e) := by
        have h0 : ∀ᶠ y in 𝓝 x₀, StrictMono y := (isOpen_strictMono (N + 1)).mem_nhds hx₀
        refine hcts.eventually ?_
        simpa using h0
      filter_upwards [hmem] with s hs
      have hshift := interp_shift hx₀ hs i k (by
        intro l hl
        simp [he, Ne.symm hl])
      have hk' : (x₀ + s • e) k = x₀ k + s := by simp [he]
      have hys : (x₀ + s • e) i.castSucc +
          u₀ * ((x₀ + s • e) i.succ - (x₀ + s • e) i.castSucc) = τ₀ + s * κ := congrFun hyfun s
      rw [hΦF, hshift, hk', hys]
      simp only [eval_add, eval_mul, eval_C, hB]
      rfl
    exact hψ.unique (h4.congr_of_eventuallyEq hev')
  intro v
  have hlin := LinearMap.pi_apply_eq_sum_univ
    (((fderiv ℝ Φ (x₀, u₀)).comp (ContinuousLinearMap.inl ℝ (Fin (N + 1) → ℝ) ℝ) :
      (Fin (N + 1) → ℝ) →L[ℝ] ℝ) : (Fin (N + 1) → ℝ) →ₗ[ℝ] ℝ) v
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.inl_apply, smul_eq_mul] at hlin
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, hlin]
  exact Finset.sum_congr rfl fun k _ => by rw [key k]

/-- the equioscillation map, completed by the first node and the logarithm of the diameter -/
noncomputable def Gam (x : Fin (N + 1) → ℝ) : Fin (N + 1) → ℝ := fun k =>
  if k = 0 then x 0
  else if k = Fin.last N then Real.log (x (Fin.last N) - x 0)
  else gapMax x (k.val + 1) - gapMax x k.val

theorem Gam_zero (x : Fin (N + 1) → ℝ) : Gam x 0 = x 0 := by simp [Gam]

theorem Gam_last (hN : 1 ≤ N) (x : Fin (N + 1) → ℝ) :
    Gam x (Fin.last N) = Real.log (x (Fin.last N) - x 0) := by
  have h : Fin.last N ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  simp [Gam, h]

theorem Gam_interior (x : Fin (N + 1) → ℝ) {j : ℕ} (hj : j + 1 < N) :
    Gam x ⟨j + 1, by omega⟩ = gapMax x (j + 1 + 1) - gapMax x (j + 1) := by
  have h0 : (⟨j + 1, by omega⟩ : Fin (N + 1)) ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp at this
  have hl : (⟨j + 1, by omega⟩ : Fin (N + 1)) ≠ Fin.last N := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  simp [Gam, h0, hl]

/-- the differentials of the gap maxima, with a junk value outside the range of gaps -/
theorem exists_gap_derivs {x₀ : Fin (N + 1) → ℝ} (hx₀ : StrictMono x₀) (hN : 2 ≤ N) :
    ∃ A : ℕ → ((Fin (N + 1) → ℝ) →L[ℝ] ℝ),
      (∀ j, j < N → HasStrictFDerivAt (fun x : Fin (N + 1) → ℝ => gapMax x (j + 1)) (A j) x₀) ∧
      ∀ (i : Fin N) v, A i.val v = ∑ k, v k * Acoef x₀ i k := by
  classical
  choose A hA hA' using fun i : Fin N => hasStrictFDerivAt_gap hx₀ hN i
  refine ⟨fun j => if h : j < N then A ⟨j, h⟩ else 0, ?_, ?_⟩
  · intro j hj
    simp only [dif_pos hj]
    exact hA ⟨j, hj⟩
  · intro i v
    simp only [dif_pos i.2]
    exact hA' i v

/-- `Gam` is strictly differentiable with invertible differential on strictly monotone nodes. -/
theorem Gam_strict {x₀ : Fin (N + 1) → ℝ} (hx₀ : StrictMono x₀) (hN : 2 ≤ N) :
    ∃ D : (Fin (N + 1) → ℝ) ≃L[ℝ] (Fin (N + 1) → ℝ),
      HasStrictFDerivAt Gam (D : (Fin (N + 1) → ℝ) →L[ℝ] (Fin (N + 1) → ℝ)) x₀ := by
  classical
  obtain ⟨A, hA, hA'⟩ := exists_gap_derivs hx₀ hN
  have h0l : (0 : Fin (N + 1)) < Fin.last N := Fin.pos_iff_ne_zero.mpr (by
    intro h; have := congrArg Fin.val h; simp at this; omega)
  have hW : 0 < x₀ (Fin.last N) - x₀ 0 := by linarith [hx₀ h0l]
  set pr : Fin (N + 1) → ((Fin (N + 1) → ℝ) →L[ℝ] ℝ) := fun k =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (N + 1) => ℝ) k with hpr
  set φ : Fin (N + 1) → ((Fin (N + 1) → ℝ) →L[ℝ] ℝ) := fun k =>
    if k = 0 then pr 0
    else if k = Fin.last N then (x₀ (Fin.last N) - x₀ 0)⁻¹ • (pr (Fin.last N) - pr 0)
    else A k.val - A (k.val - 1) with hφ
  have hder : HasStrictFDerivAt Gam (ContinuousLinearMap.pi φ) x₀ := by
    show HasStrictFDerivAt (fun (x : Fin (N + 1) → ℝ) (k : Fin (N + 1)) => Gam x k)
      (ContinuousLinearMap.pi φ) x₀
    rw [hasStrictFDerivAt_pi]
    intro k
    by_cases hk0 : k = 0
    · subst hk0
      have e : (fun x : Fin (N + 1) → ℝ => Gam x 0) = fun x => x 0 := funext fun x => Gam_zero x
      rw [e]
      simp only [hφ, if_true]
      exact hasStrictFDerivAt_apply 0 x₀
    by_cases hkl : k = Fin.last N
    · subst hkl
      have e : (fun x : Fin (N + 1) → ℝ => Gam x (Fin.last N)) =
          fun x => Real.log (x (Fin.last N) - x 0) := funext fun x => Gam_last (by omega) x
      rw [e]
      simp only [hφ, if_neg hk0, if_true]
      have h1 : HasStrictFDerivAt (fun x : Fin (N + 1) → ℝ => x (Fin.last N) - x 0)
          (pr (Fin.last N) - pr 0) x₀ :=
        (hasStrictFDerivAt_apply (Fin.last N) x₀).sub (hasStrictFDerivAt_apply 0 x₀)
      exact h1.log hW.ne'
    · have hkpos : 0 < k.val := Nat.pos_of_ne_zero fun h => hk0 (Fin.ext h)
      have hklt : k.val < N := lt_of_le_of_ne (Nat.lt_succ_iff.mp k.2) fun h => hkl (Fin.ext h)
      have e : (fun x : Fin (N + 1) → ℝ => Gam x k) =
          fun x => gapMax x (k.val + 1) - gapMax x (k.val - 1 + 1) := by
        funext x
        simp only [Gam, if_neg hk0, if_neg hkl]
        rw [Nat.sub_add_cancel hkpos]
      rw [e]
      simp only [hφ, if_neg hk0, if_neg hkl]
      exact (hA k.val hklt).sub (hA (k.val - 1) (by omega))
  have hinj : Function.Injective (ContinuousLinearMap.pi φ) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hcomp : ∀ k, φ k v = 0 := fun k => by
      have := congrFun hv k
      simpa using this
    have hv0 : v 0 = 0 := by
      have := hcomp 0
      simpa [hφ, hpr] using this
    have hvl : v (Fin.last N) = 0 := by
      have := hcomp (Fin.last N)
      simp only [hφ, hpr, if_neg (ne_of_gt h0l), if_true, _root_.smul_apply,
        _root_.sub_apply, ContinuousLinearMap.proj_apply, smul_eq_mul] at this
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (inv_ne_zero hW.ne')
      · linarith
    -- all gap differentials agree on v
    have hstep : ∀ j, j + 1 < N → A (j + 1) v = A j v := by
      intro j hj
      have hk0 : (⟨j + 1, by omega⟩ : Fin (N + 1)) ≠ 0 := by
        intro h; have := congrArg Fin.val h; simp at this
      have hkl : (⟨j + 1, by omega⟩ : Fin (N + 1)) ≠ Fin.last N := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      have := hcomp ⟨j + 1, by omega⟩
      simp only [hφ, if_neg hk0, if_neg hkl, _root_.sub_apply,
        Nat.add_sub_cancel] at this
      linarith
    have hall : ∀ j, j < N → A j v = A 0 v := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro hj
        rw [hstep j hj, ih (by omega)]
    have hsum : ∀ i : Fin N, ∑ k, v k * Acoef x₀ i k = A 0 v := by
      intro i
      rw [← hA' i v, hall i.val i.2]
    rcases le_total (A 0 v) 0 with hc | hc
    · exact app3 hx₀ hN v hv0 hvl fun i => by rw [hsum i]; exact hc
    · have hneg : -v = 0 := by
        refine app3 hx₀ hN (-v) (by simp [hv0]) (by simp [hvl]) fun i => ?_
        have : ∑ k, (-v) k * Acoef x₀ i k = -∑ k, v k * Acoef x₀ i k := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun k _ => by simp
        rw [this, hsum i]
        linarith
      simpa using hneg
  refine ⟨clEquivOfInjective _ hinj, ?_⟩
  rw [clEquivOfInjective_coe]
  exact hder

/-- the open set of strictly increasing node vectors -/
def Omega (N : ℕ) : TopologicalSpace.Opens (Fin (N + 1) → ℝ) :=
  ⟨{x | StrictMono x}, isOpen_strictMono (N + 1)⟩

theorem Gam_isLocalHomeomorph (hN : 2 ≤ N) :
    IsLocalHomeomorph (fun x : Omega N => Gam (x : Fin (N + 1) → ℝ)) :=
  isLocalHomeomorph_of_strict (Omega N) Gam fun _ hx => Gam_strict hx hN

theorem Gam_continuous (hN : 2 ≤ N) :
    Continuous (fun x : Omega N => Gam (x : Fin (N + 1) → ℝ)) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨D, hD⟩ := Gam_strict (x₀ := (x : Fin (N + 1) → ℝ)) x.2 hN
  exact hD.hasFDerivAt.continuousAt.comp continuous_subtype_val.continuousAt

theorem abs_basis_eval {n : ℕ} (x : Fin n → ℝ) (k : Fin n) (y : ℝ) :
    |(Lagrange.basis univ x k).eval y| = ∏ l ∈ univ.erase k, (|x k - x l|⁻¹ * |y - x l|) := by
  rw [basis_eval_eq, Finset.abs_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [abs_mul, abs_inv]

theorem le_gapMax (x : Fin (N + 1) → ℝ) (i : Fin N) {y : ℝ}
    (hy : y ∈ Icc (x i.castSucc) (x i.succ)) : lebesgueFunction x y ≤ gapMax x (i.val + 1) := by
  rw [gapMax_eq_sSup]
  exact le_csSup (isCompact_Icc.image (continuous_lebesgue x)).bddAbove ⟨y, hy, rfl⟩

/-- The Lebesgue function on a short gap is small compared with its value at the midpoint of the
longest gap (quantitative form of Lemma 4 of de Boor–Pinkus). -/
theorem lebesgue_small_gap {x : Fin (N + 1) → ℝ} (hx : StrictMono x) (hN : 1 ≤ N) (a b : Fin N)
    (ha : ∀ i : Fin N, x i.succ - x i.castSucc ≤ x a.succ - x a.castSucc) {y : ℝ}
    (hy : y ∈ Icc (x b.castSucc) (x b.succ)) :
    lebesgueFunction x y ≤
      (2 * (N : ℝ)) ^ N * ((x b.succ - x b.castSucc) / (x (Fin.last N) - x 0)) *
        lebesgueFunction x ((x a.castSucc + x a.succ) / 2) := by
  classical
  set Δa := x a.succ - x a.castSucc with hΔa
  set Δb := x b.succ - x b.castSucc with hΔb
  set W := x (Fin.last N) - x 0 with hW
  set M := (x a.castSucc + x a.succ) / 2 with hM
  have hΔa0 : 0 < Δa := by have := hx (Fin.castSucc_lt_succ (i := a)); linarith
  have hΔb0 : 0 < Δb := by have := hx (Fin.castSucc_lt_succ (i := b)); linarith
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hsteps : ∀ k : Fin (N + 1), x k - x 0 ≤ k.val * Δa := by
    intro k
    induction k using Fin.induction with
    | zero => simp
    | succ r ih =>
      have := ha r
      have e : ((r.succ : Fin (N + 1)).val : ℝ) = (r.castSucc.val : ℝ) + 1 := by simp
      rw [e]
      nlinarith
  have hWle : W ≤ N * Δa := by
    have := hsteps (Fin.last N)
    simpa [hW] using this
  have hW0 : 0 < W := by
    have : (0 : Fin (N + 1)) < Fin.last N := Fin.pos_iff_ne_zero.mpr (by
      intro h; have := congrArg Fin.val h; simp at this; omega)
    have := hx this
    linarith
  have hMl : ∀ l : Fin (N + 1), Δa / 2 ≤ |M - x l| := by
    intro l
    rcases le_or_gt l.val a.val with h | h
    · have : x l ≤ x a.castSucc := hx.monotone (by rw [Fin.le_def]; simpa using h)
      rw [abs_of_nonneg (by rw [hM]; linarith)]
      rw [hM]; linarith
    · have : x a.succ ≤ x l := hx.monotone (by
        rw [Fin.le_def]; simp only [Fin.val_succ]; omega)
      rw [abs_of_nonpos (by rw [hM]; linarith)]
      rw [hM]; linarith
  have hy0 : x 0 ≤ y := (hx.monotone (Fin.zero_le _)).trans hy.1
  have hy1 : y ≤ x (Fin.last N) := hy.2.trans (hx.monotone (Fin.le_last _))
  have hyW : ∀ l : Fin (N + 1), |y - x l| ≤ W := by
    intro l
    have h1 : x 0 ≤ x l := hx.monotone (Fin.zero_le _)
    have h2 : x l ≤ x (Fin.last N) := hx.monotone (Fin.le_last _)
    rw [abs_le]; constructor <;> linarith
  have hyb1 : |y - x b.castSucc| ≤ Δb := by
    rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
  have hyb2 : |y - x b.succ| ≤ Δb := by
    rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
  set c : Fin (N + 1) → ℝ := fun l => |y - x l| / |M - x l| with hc
  have hMpos : ∀ l, 0 < |M - x l| := fun l => lt_of_lt_of_le (by linarith) (hMl l)
  have hc0 : ∀ l, 0 ≤ c l := fun l => div_nonneg (abs_nonneg _) (hMpos l).le
  have hc1 : ∀ l, c l ≤ 2 * N := by
    intro l
    rw [hc, div_le_iff₀ (hMpos l)]
    have := hMl l
    have := hyW l
    nlinarith
  have hc2 : ∀ l, |y - x l| ≤ Δb → c l ≤ 2 * N * (Δb / W) := by
    intro l hl
    rw [hc, div_le_iff₀ (hMpos l)]
    have h1 := hMl l
    have h2 : Δb / W * W = Δb := div_mul_cancel₀ _ hW0.ne'
    have h3 : 0 ≤ Δb / W := div_nonneg hΔb0.le hW0.le
    -- Δb ≤ (Δb/W) * N * Δa
    have h4 : Δb ≤ Δb / W * (N * Δa) := by
      calc Δb = Δb / W * W := h2.symm
        _ ≤ Δb / W * (N * Δa) := mul_le_mul_of_nonneg_left hWle h3
    nlinarith
  have hterm : ∀ k : Fin (N + 1), |(Lagrange.basis univ x k).eval y| ≤
      (2 * (N : ℝ)) ^ N * (Δb / W) * |(Lagrange.basis univ x k).eval M| := by
    intro k
    rw [abs_basis_eval, abs_basis_eval]
    have hsplit : ∏ l ∈ univ.erase k, (|x k - x l|⁻¹ * |y - x l|) =
        (∏ l ∈ univ.erase k, c l) * ∏ l ∈ univ.erase k, (|x k - x l|⁻¹ * |M - x l|) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun l _ => ?_
      have := (hMpos l).ne'
      simp only [hc]
      field_simp
    rw [hsplit]
    have hnn : 0 ≤ ∏ l ∈ univ.erase k, (|x k - x l|⁻¹ * |M - x l|) :=
      Finset.prod_nonneg fun l _ => mul_nonneg (inv_nonneg.mpr (abs_nonneg _)) (abs_nonneg _)
    refine mul_le_mul_of_nonneg_right ?_ hnn
    -- the product of the ratios
    set ls : Fin (N + 1) := if k = b.castSucc then b.succ else b.castSucc with hls
    have hlsk : ls ≠ k := by
      rw [hls]
      split_ifs with h
      · rw [h]; exact (Fin.castSucc_lt_succ).ne'
      · exact fun h' => h h'.symm
    have hlsb : |y - x ls| ≤ Δb := by
      rw [hls]; split_ifs
      · exact hyb2
      · exact hyb1
    have hmem : ls ∈ univ.erase k := mem_erase.mpr ⟨hlsk, mem_univ _⟩
    rw [← Finset.mul_prod_erase _ _ hmem]
    have hcard : ((univ.erase k).erase ls).card = N - 1 := by
      rw [card_erase_of_mem hmem, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
      omega
    have hrest : ∏ l ∈ (univ.erase k).erase ls, c l ≤ (2 * (N : ℝ)) ^ (N - 1) := by
      calc ∏ l ∈ (univ.erase k).erase ls, c l
          ≤ ∏ _l ∈ (univ.erase k).erase ls, (2 * (N : ℝ)) :=
            Finset.prod_le_prod (fun l _ => hc0 l) (fun l _ => hc1 l)
        _ = (2 * (N : ℝ)) ^ (N - 1) := by rw [Finset.prod_const, hcard]
    have hrest0 : 0 ≤ ∏ l ∈ (univ.erase k).erase ls, c l :=
      Finset.prod_nonneg fun l _ => hc0 l
    have h2N : (0:ℝ) ≤ 2 * N := by positivity
    have hpow : (2 * (N : ℝ)) ^ N = 2 * N * (2 * (N : ℝ)) ^ (N - 1) := by
      have h := pow_sub_one_mul (show N ≠ 0 by omega) (2 * (N : ℝ))
      rw [← h]; ring
    calc c ls * ∏ l ∈ (univ.erase k).erase ls, c l
        ≤ (2 * N * (Δb / W)) * (2 * (N : ℝ)) ^ (N - 1) :=
          mul_le_mul (hc2 ls hlsb) hrest hrest0
            (mul_nonneg h2N (div_nonneg hΔb0.le hW0.le))
      _ = (2 * (N : ℝ)) ^ N * (Δb / W) := by rw [hpow]; ring
  unfold lebesgueFunction
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => hterm k

/-- Properness estimate: bounded `Gam` forces all gaps to be bounded below. -/
theorem Gam_gap_bound (hN : 2 ≤ N) (R : ℝ) (hR : 0 ≤ R) :
    ∃ δ > 0, ∀ x : Fin (N + 1) → ℝ, StrictMono x → (∀ k, |Gam x k| ≤ R) →
      ∀ i : Fin N, δ ≤ x i.succ - x i.castSucc := by
  classical
  set C : ℝ := (2 * (N : ℝ)) ^ N with hC
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hC0 : 0 < C := by positivity
  set T : ℝ := 2 * N * R with hT
  have hT0 : 0 ≤ T := by positivity
  refine ⟨Real.exp (-R) / (2 * C * (T + 1)), by positivity, ?_⟩
  intro x hx hG b
  by_contra hlt
  push Not at hlt
  have h0l : (0 : Fin (N + 1)) < Fin.last N := Fin.pos_iff_ne_zero.mpr (by
    intro h; have := congrArg Fin.val h; simp at this; omega)
  set W := x (Fin.last N) - x 0 with hW
  have hW0 : 0 < W := by have := hx h0l; linarith
  have hWexp : Real.exp (-R) ≤ W := by
    have h1 := hG (Fin.last N)
    rw [Gam_last (by omega)] at h1
    have h2 : -R ≤ Real.log W := (abs_le.mp h1).1
    calc Real.exp (-R) ≤ Real.exp (Real.log W) := Real.exp_le_exp.mpr h2
      _ = W := Real.exp_log hW0
  -- telescoping
  have htel : ∀ j, j < N → |gapMax x (j + 1) - gapMax x (0 + 1)| ≤ j * R := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h1 := hG ⟨j + 1, by omega⟩
      rw [Gam_interior x hj] at h1
      have h2 := ih (by omega)
      have e : gapMax x (j + 1 + 1) - gapMax x (0 + 1) =
          (gapMax x (j + 1 + 1) - gapMax x (j + 1)) + (gapMax x (j + 1) - gapMax x (0 + 1)) := by
        ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      push_cast
      linarith
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image (univ : Finset (Fin N))
    (fun i => x i.succ - x i.castSucc) ⟨b, mem_univ _⟩
  have ha' : ∀ i : Fin N, x i.succ - x i.castSucc ≤ x a.succ - x a.castSucc :=
    fun i => ha i (mem_univ _)
  set lamA := gapMax x (a.val + 1) with hlamA
  set lamB := gapMax x (b.val + 1) with hlamB
  set Δb := x b.succ - x b.castSucc with hΔb
  have hΔb0 : 0 < Δb := by have := hx (Fin.castSucc_lt_succ (i := b)); linarith
  have hAB : lamA ≤ lamB + T := by
    have h1 := htel a.val a.2
    have h2 := htel b.val b.2
    have h3 : (a.val : ℝ) ≤ N := by exact_mod_cast a.2.le
    have h4 : (b.val : ℝ) ≤ N := by exact_mod_cast b.2.le
    have h5 := (abs_le.mp h1).2
    have h6 := (abs_le.mp h2).1
    rw [hT]
    nlinarith
  have hltab : x b.castSucc < x b.succ := hx Fin.castSucc_lt_succ
  have hlta : x a.castSucc < x a.succ := hx Fin.castSucc_lt_succ
  have hB1 : 1 ≤ lamB :=
    (one_le_lebesgue hx _).trans (le_gapMax x b (left_mem_Icc.mpr hltab.le))
  have hMA : lebesgueFunction x ((x a.castSucc + x a.succ) / 2) ≤ lamA :=
    le_gapMax x a ⟨by linarith, by linarith⟩
  set κ := C * (Δb / W) with hκ
  have hκ0 : 0 ≤ κ := mul_nonneg hC0.le (div_nonneg hΔb0.le hW0.le)
  have hBA : lamB ≤ κ * lamA := by
    rw [hlamB, gapMax_eq_sSup]
    refine csSup_le ⟨_, ⟨x b.castSucc, left_mem_Icc.mpr hltab.le, rfl⟩⟩ ?_
    rintro _ ⟨y, hy, rfl⟩
    exact (lebesgue_small_gap hx (by omega) a b ha' hy).trans
      (mul_le_mul_of_nonneg_left hMA hκ0)
  have hκlt : κ * (2 * (T + 1)) < 1 := by
    have h1 : Δb * (2 * C * (T + 1)) < Real.exp (-R) := by
      rwa [lt_div_iff₀ (by positivity)] at hlt
    have h2 : Δb * (2 * C * (T + 1)) < W := lt_of_lt_of_le h1 hWexp
    have h3 : κ * (2 * (T + 1)) = Δb * (2 * C * (T + 1)) / W := by
      rw [hκ]; field_simp
    rw [h3, div_lt_one hW0]
    exact h2
  have hA1 : 0 ≤ lamB + T := by linarith
  have h7 : lamB ≤ κ * (lamB + T) := hBA.trans (mul_le_mul_of_nonneg_left hAB hκ0)
  have h8 : lamB * (2 * (T + 1)) ≤ κ * (2 * (T + 1)) * (lamB + T) := by nlinarith
  have h9 : κ * (2 * (T + 1)) * (lamB + T) ≤ 1 * (lamB + T) :=
    mul_le_mul_of_nonneg_right hκlt.le hA1
  nlinarith

theorem Gam_isProperMap (hN : 2 ≤ N) :
    IsProperMap (fun x : Omega N => Gam (x : Fin (N + 1) → ℝ)) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨Gam_continuous hN, fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Fin (N + 1) → ℝ)
  set R' := max R 0 with hR'
  have hR'0 : 0 ≤ R' := le_max_right _ _
  have hKb : ∀ p ∈ K, ∀ k, |p k| ≤ R' := by
    intro p hp k
    have h1 : ‖p‖ ≤ R := by simpa using hR hp
    have h2 : ‖p k‖ ≤ ‖p‖ := norm_le_pi_norm p k
    rw [Real.norm_eq_abs] at h2
    exact h2.trans (h1.trans (le_max_left _ _))
  obtain ⟨δ, hδ, hgap⟩ := Gam_gap_bound hN R' hR'0
  have h0l : (0 : Fin (N + 1)) < Fin.last N := Fin.pos_iff_ne_zero.mpr (by
    intro h; have := congrArg Fin.val h; simp at this; omega)
  set Cset : Set (Fin (N + 1) → ℝ) :=
    {x | (∀ i : Fin N, δ ≤ x i.succ - x i.castSucc) ∧ |x 0| ≤ R' ∧
      x (Fin.last N) - x 0 ≤ Real.exp R'} with hCset
  have hCmono : ∀ x ∈ Cset, StrictMono x := by
    intro x hx
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    have := hx.1 i
    linarith
  have hCclosed : IsClosed Cset := by
    have h1 : IsClosed {x : Fin (N + 1) → ℝ | ∀ i : Fin N, δ ≤ x i.succ - x i.castSucc} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)
    have h2 : IsClosed {x : Fin (N + 1) → ℝ | |x 0| ≤ R'} :=
      isClosed_le (by fun_prop) continuous_const
    have h3 : IsClosed {x : Fin (N + 1) → ℝ | x (Fin.last N) - x 0 ≤ Real.exp R'} :=
      isClosed_le (by fun_prop) continuous_const
    exact h1.inter (h2.inter h3)
  have hCbdd : Bornology.IsBounded Cset := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin (N + 1) → ℝ))
      (r := R' + Real.exp R')).subset fun x hx => ?_
    have hmono := (hCmono x hx).monotone
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    have h1 : x 0 ≤ x k := hmono (Fin.zero_le _)
    have h2 : x k ≤ x (Fin.last N) := hmono (Fin.le_last _)
    have h3 := abs_le.mp hx.2.1
    have h4 := hx.2.2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [Real.exp_pos R']
  have hcontOn : ContinuousOn Gam Cset := by
    intro x hx
    obtain ⟨D, hD⟩ := Gam_strict (hCmono x hx) hN
    exact hD.hasFDerivAt.continuousAt.continuousWithinAt
  have hclosed : IsClosed (Cset ∩ Gam ⁻¹' K) :=
    hcontOn.preimage_isClosed_of_isClosed hCclosed hK.isClosed
  have hcompact : IsCompact (Cset ∩ Gam ⁻¹' K) :=
    Metric.isCompact_of_isClosed_isBounded hclosed (hCbdd.subset inter_subset_left)
  rw [Subtype.isCompact_iff]
  convert hcompact using 1
  ext x
  constructor
  · rintro ⟨⟨x', hx'⟩, hxK, rfl⟩
    have hxK' : Gam x' ∈ K := hxK
    have hb := hKb _ hxK'
    refine ⟨⟨hgap x' hx' hb, ?_, ?_⟩, hxK'⟩
    · have := hb 0; rwa [Gam_zero] at this
    · have h1 := hb (Fin.last N)
      rw [Gam_last (by omega)] at h1
      have hW0 : 0 < x' (Fin.last N) - x' 0 := by have := hx' h0l; linarith
      calc x' (Fin.last N) - x' 0 = Real.exp (Real.log (x' (Fin.last N) - x' 0)) :=
            (Real.exp_log hW0).symm
        _ ≤ Real.exp R' := Real.exp_le_exp.mpr (abs_le.mp h1).2
  · rintro ⟨hxC, hxK⟩
    exact ⟨⟨x, hCmono x hxC⟩, hxK, rfl⟩

/-- `Gam` is a homeomorphism from the strictly increasing node vectors onto the whole space
(Hadamard's global inverse function theorem, through covering space theory). -/
theorem Gam_homeo (hN : 2 ≤ N) :
    ∃ g : (Fin (N + 1) → ℝ) → Omega N, Continuous g ∧
      (∀ e : Omega N, g (Gam (e : Fin (N + 1) → ℝ)) = e) ∧
      ∀ p, Gam ((g p : Omega N) : Fin (N + 1) → ℝ) = p := by
  have hproper := Gam_isProperMap hN
  have hloc := Gam_isLocalHomeomorph hN
  have hconn : ConnectedSpace (Omega N) := by
    have hconv : Convex ℝ {x : Fin (N + 1) → ℝ | StrictMono x} := convex_strictMono (N + 1)
    have hne : {x : Fin (N + 1) → ℝ | StrictMono x}.Nonempty :=
      ⟨fun k => (k.val : ℝ), fun i j hij => by
        have : i.val < j.val := hij
        show ((i.val : ℕ) : ℝ) < ((j.val : ℕ) : ℝ)
        exact_mod_cast this⟩
    exact isConnected_iff_connectedSpace.mp (hconv.isConnected hne)
  refine hadamard_abstract _ hloc hproper.isClosedMap fun p => ?_
  have hc : IsCompact ((fun x : Omega N => Gam (x : Fin (N + 1) → ℝ)) ⁻¹' {p}) :=
    hproper.isCompact_preimage isCompact_singleton
  refine hc.finite (IsDiscrete.of_openPartialHomeomorph _ subset_rfl fun e _ => ?_)
  obtain ⟨φ, hφ, hφe⟩ := hloc e
  exact ⟨φ, hφ, hφe.symm⟩

/-- Local non-domination: near a node vector, no other node vector with the same end nodes has
all gap maxima at least as large. -/
theorem local_antichain {x₀ : Fin (N + 1) → ℝ} (hx₀ : StrictMono x₀) (hN : 2 ≤ N) :
    ∃ ε > 0, ∀ z : Fin (N + 1) → ℝ, z 0 = x₀ 0 → z (Fin.last N) = x₀ (Fin.last N) → z ≠ x₀ →
      dist z x₀ < ε → ∃ i : Fin N, gapMax z (i.val + 1) < gapMax x₀ (i.val + 1) := by
  classical
  obtain ⟨A, hA, hA'⟩ := exists_gap_derivs hx₀ hN
  have hNpos : 0 < N := by omega
  have hne : (univ : Finset (Fin N)).Nonempty := ⟨⟨0, hNpos⟩, mem_univ _⟩
  -- a negative direction exists for every nonzero admissible variation
  have hneg : ∀ v : Fin (N + 1) → ℝ, v 0 = 0 → v (Fin.last N) = 0 → v ≠ 0 →
      ∃ i : Fin N, A i.val v < 0 := by
    intro v hv0 hvl hv
    by_contra hcon
    push Not at hcon
    apply hv
    have : -v = 0 := by
      refine app3 hx₀ hN (-v) (by simp [hv0]) (by simp [hvl]) fun i => ?_
      have e : ∑ k, (-v) k * Acoef x₀ i k = -∑ k, v k * Acoef x₀ i k := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun k _ => by simp
      rw [e, ← hA' i v]
      linarith [hcon i]
    simpa using this
  -- uniform constant by compactness of the unit sphere
  set S : Set (Fin (N + 1) → ℝ) := {v | ‖v‖ = 1 ∧ v 0 = 0 ∧ v (Fin.last N) = 0} with hS
  have hScompact : IsCompact S := by
    have hcl : IsClosed S := by
      have h1 : IsClosed {v : Fin (N + 1) → ℝ | ‖v‖ = 1} := isClosed_eq continuous_norm continuous_const
      have h2 : IsClosed {v : Fin (N + 1) → ℝ | v 0 = 0} := isClosed_eq (by fun_prop) continuous_const
      have h3 : IsClosed {v : Fin (N + 1) → ℝ | v (Fin.last N) = 0} :=
        isClosed_eq (by fun_prop) continuous_const
      exact h1.inter (h2.inter h3)
    refine Metric.isCompact_of_isClosed_isBounded hcl ?_
    refine (Metric.isBounded_closedBall (x := (0 : Fin (N + 1) → ℝ)) (r := 1)).subset fun v hv => ?_
    rw [mem_closedBall_zero_iff]
    exact hv.1.le
  set f : (Fin (N + 1) → ℝ) → ℝ := fun v => ∑ i : Fin N, max (-(A i.val v)) 0 with hf
  have hfcont : Continuous f := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((A i.val).continuous.neg).max continuous_const
  have hfpos : ∀ v ∈ S, 0 < f v := by
    intro v hv
    have hv0 : v ≠ 0 := by
      intro h
      have h1 := hv.1
      rw [h, norm_zero] at h1
      exact zero_ne_one h1
    obtain ⟨i, hi⟩ := hneg v hv.2.1 hv.2.2 hv0
    refine Finset.sum_pos' (fun j _ => le_max_right _ _) ⟨i, mem_univ _, ?_⟩
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hc : ∃ c > 0, ∀ v ∈ S, ∃ i : Fin N, A i.val v ≤ -c := by
    rcases S.eq_empty_or_nonempty with hem | hSne
    · exact ⟨1, one_pos, fun v hv => by rw [hem] at hv; exact absurd hv (Set.notMem_empty v)⟩
    · obtain ⟨v₀, hv₀, hmin⟩ := hScompact.exists_isMinOn hSne hfcont.continuousOn
      have hm := hfpos v₀ hv₀
      refine ⟨f v₀ / N, by positivity, fun v hv => ?_⟩
      have h1 : f v₀ ≤ f v := hmin hv
      have h2 : ∑ _i : Fin N, f v₀ / N ≤ ∑ i : Fin N, max (-(A i.val v)) 0 := by
        rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        have : (N : ℝ) * (f v₀ / N) = f v₀ := by
          field_simp
        rw [this]; exact h1
      obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le hne h2
      refine ⟨i, ?_⟩
      have hpos : 0 < f v₀ / N := by positivity
      rcases le_max_iff.mp hi with h | h
      · linarith
      · linarith
  obtain ⟨c, hc0, hcS⟩ := hc
  have hcV : ∀ v : Fin (N + 1) → ℝ, v 0 = 0 → v (Fin.last N) = 0 → v ≠ 0 →
      ∃ i : Fin N, A i.val v ≤ -c * ‖v‖ := by
    intro v hv0 hvl hv
    have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hmem : (‖v‖⁻¹ • v) ∈ S := by
      refine ⟨?_, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnorm.ne']
      · simp [hv0]
      · simp [hvl]
    obtain ⟨i, hi⟩ := hcS _ hmem
    refine ⟨i, ?_⟩
    rw [map_smul, smul_eq_mul] at hi
    have : A i.val v = ‖v‖ * (‖v‖⁻¹ * A i.val v) := by field_simp
    rw [this]
    nlinarith
  -- differentiability
  have hev : ∀ᶠ z in 𝓝 x₀, ∀ i : Fin N,
      ‖gapMax z (i.val + 1) - gapMax x₀ (i.val + 1) - A i.val (z - x₀)‖ ≤ c / 2 * ‖z - x₀‖ := by
    rw [Filter.eventually_all]
    intro i
    exact (hA i.val i.2).hasFDerivAt.isLittleO.def (half_pos hc0)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε, hε, fun z hz0 hzl hzne hdist => ?_⟩
  have hv : z - x₀ ≠ 0 := sub_ne_zero.mpr hzne
  obtain ⟨i, hi⟩ := hcV (z - x₀) (by simp [hz0]) (by simp [hzl]) hv
  refine ⟨i, ?_⟩
  have h1 := hball hdist i
  rw [Real.norm_eq_abs, abs_le] at h1
  have hnorm : 0 < ‖z - x₀‖ := norm_pos_iff.mpr hv
  nlinarith [h1.2]

theorem gap_continuousAt {x₀ : Fin (N + 1) → ℝ} (hx₀ : StrictMono x₀) (hN : 2 ≤ N) {j : ℕ}
    (hj : j < N) : ContinuousAt (fun x : Fin (N + 1) → ℝ => gapMax x (j + 1)) x₀ := by
  obtain ⟨A, hA, -⟩ := exists_gap_derivs hx₀ hN
  exact (hA j hj).hasFDerivAt.continuousAt

/-- Global non-domination (Theorem 2 of de Boor–Pinkus) for at least three nodes. -/
theorem no_domination_two (hN : 2 ≤ N) {s t : Fin (N + 1) → ℝ} (hs : StrictMono s)
    (ht : StrictMono t) (h0 : s 0 = t 0) (hl : s (Fin.last N) = t (Fin.last N))
    (hle : ∀ i : Fin N, gapMax s (i.val + 1) ≤ gapMax t (i.val + 1)) : s = t := by
  classical
  obtain ⟨g, hg, hgl, hgr⟩ := Gam_homeo hN
  by_contra hne
  set p := Gam s with hp
  set p' := Gam t with hp'
  have hgs : ((g p : Omega N) : Fin (N + 1) → ℝ) = s := by
    have := hgl ⟨s, hs⟩
    exact congrArg Subtype.val this
  have hgt : ((g p' : Omega N) : Fin (N + 1) → ℝ) = t := by
    have := hgl ⟨t, ht⟩
    exact congrArg Subtype.val this
  have hpp : p' - p ≠ 0 := by
    intro h
    apply hne
    have : p' = p := sub_eq_zero.mp h
    rw [← hgs, ← hgt, this]
  set c : ℝ → (Fin (N + 1) → ℝ) :=
    fun θ => ((g (p + θ • (p' - p)) : Omega N) : Fin (N + 1) → ℝ) with hc
  have hcmono : ∀ θ, StrictMono (c θ) := fun θ => (g (p + θ • (p' - p))).2
  have hcG : ∀ θ, Gam (c θ) = p + θ • (p' - p) := fun θ => hgr _
  have hc0 : c 0 = s := by
    simp only [hc, zero_smul, add_zero]; exact hgs
  have hc1 : c 1 = t := by
    simp only [hc, one_smul, add_sub_cancel]; exact hgt
  have hccont : Continuous c :=
    continuous_subtype_val.comp (hg.comp (by fun_prop))
  have h0l : (0 : Fin (N + 1)) < Fin.last N := Fin.pos_iff_ne_zero.mpr (by
    intro h; have := congrArg Fin.val h; simp at this; omega)
  have hce0 : ∀ θ, c θ 0 = s 0 := by
    intro θ
    have h1 := congrFun (hcG θ) 0
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hp, hp', Gam_zero] at h1
    rw [h1, h0]; ring
  have hcel : ∀ θ, c θ (Fin.last N) = s (Fin.last N) := by
    intro θ
    have h1 := congrFun (hcG θ) (Fin.last N)
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hp, hp',
      Gam_last (by omega : 1 ≤ N)] at h1
    rw [← hl, ← h0, sub_self, mul_zero, add_zero, hce0 θ] at h1
    have hpos1 : 0 < c θ (Fin.last N) - s 0 := by
      have := hcmono θ h0l
      rw [hce0 θ] at this
      linarith
    have hpos2 : 0 < s (Fin.last N) - s 0 := by have := hs h0l; linarith
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr hpos1) (Set.mem_Ioi.mpr hpos2) h1
    linarith
  set D : ℝ → ℝ := fun θ =>
    gapMax (c θ) (0 + 1) - ((1 - θ) * gapMax s (0 + 1) + θ * gapMax t (0 + 1)) with hD
  have hDi : ∀ θ, ∀ j, j < N →
      gapMax (c θ) (j + 1) - ((1 - θ) * gapMax s (j + 1) + θ * gapMax t (j + 1)) = D θ := by
    intro θ j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have h1 := congrFun (hcG θ) ⟨j + 1, by omega⟩
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hp, hp'] at h1
      rw [Gam_interior _ hj, Gam_interior s hj, Gam_interior t hj] at h1
      have h2 := ih (by omega)
      linear_combination h1 + h2
  have hDcont : ContinuousOn D (Icc 0 1) := by
    refine Continuous.continuousOn ?_
    have h1 : Continuous fun θ => gapMax (c θ) (0 + 1) := by
      rw [continuous_iff_continuousAt]
      intro θ
      exact ContinuousAt.comp (f := c) (g := fun x : Fin (N + 1) → ℝ => gapMax x (0 + 1))
        (gap_continuousAt (hcmono θ) hN (by omega)) hccont.continuousAt
    simp only [hD]
    fun_prop
  have hloc : ∀ θ₀ ∈ Ico (0:ℝ) 1, ∃ η > 0, ∀ θ, θ₀ < θ → θ < θ₀ + η → θ ≤ 1 → D θ < D θ₀ := by
    intro θ₀ _
    obtain ⟨ε, hε, hLA⟩ := local_antichain (hcmono θ₀) hN
    obtain ⟨η, hη, hηc⟩ := Metric.continuousAt_iff.mp hccont.continuousAt ε hε
    refine ⟨η, hη, fun θ hθ1 hθ2 _ => ?_⟩
    have hdist : dist (c θ) (c θ₀) < ε := by
      apply hηc
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have hneq : c θ ≠ c θ₀ := by
      intro h
      have h1 := hcG θ
      rw [h, hcG θ₀] at h1
      have h2 : (θ - θ₀) • (p' - p) = 0 := by
        rw [sub_smul]
        have := add_left_cancel h1
        rw [this, sub_self]
      rcases smul_eq_zero.mp h2 with h3 | h3
      · linarith
      · exact hpp h3
    obtain ⟨i, hi⟩ := hLA (c θ) (by rw [hce0, hce0]) (by rw [hcel, hcel]) hneq hdist
    have e1 := hDi θ i.val i.2
    have e2 := hDi θ₀ i.val i.2
    have h3 := hle i
    nlinarith
  have hfinal := lt_of_locally_decreasing D hDcont hloc
  have hD0 : D 0 = 0 := by simp only [hD, hc0]; ring
  have hD1 : D 1 = 0 := by simp only [hD, hc1]; ring
  rw [hD0, hD1] at hfinal
  exact lt_irrefl _ hfinal

/-- existence of an equioscillating node vector with prescribed end nodes -/
theorem exists_equi_two (hN : 2 ≤ N) (a b : ℝ) (hab : a < b) :
    ∃ e : Fin (N + 1) → ℝ, StrictMono e ∧ e 0 = a ∧ e (Fin.last N) = b ∧
      ∀ i j : Fin N, gapMax e (i.val + 1) = gapMax e (j.val + 1) := by
  classical
  obtain ⟨g, -, -, hgr⟩ := Gam_homeo hN
  set p : Fin (N + 1) → ℝ := fun k =>
    if k = 0 then a else if k = Fin.last N then Real.log (b - a) else 0 with hp
  set e : Fin (N + 1) → ℝ := ((g p : Omega N) : Fin (N + 1) → ℝ) with he
  have hemono : StrictMono e := (g p).2
  have hG : Gam e = p := hgr p
  have h0l : (0 : Fin (N + 1)) < Fin.last N := Fin.pos_iff_ne_zero.mpr (by
    intro h; have := congrArg Fin.val h; simp at this; omega)
  have he0 : e 0 = a := by
    have := congrFun hG 0
    rw [Gam_zero] at this
    simpa [hp] using this
  have hel : e (Fin.last N) = b := by
    have h1 := congrFun hG (Fin.last N)
    rw [Gam_last (by omega)] at h1
    simp only [hp, if_neg (ne_of_gt h0l), if_true] at h1
    have hpos1 : 0 < e (Fin.last N) - e 0 := by have := hemono h0l; linarith
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr hpos1) (Set.mem_Ioi.mpr (by linarith : 0 < b - a)) h1
    linarith
  have hstep : ∀ j, j + 1 < N → gapMax e (j + 1 + 1) = gapMax e (j + 1) := by
    intro j hj
    have h1 := congrFun hG ⟨j + 1, by omega⟩
    rw [Gam_interior _ hj] at h1
    have hk0 : (⟨j + 1, by omega⟩ : Fin (N + 1)) ≠ 0 := by
      intro h; have := congrArg Fin.val h; simp at this
    have hkl : (⟨j + 1, by omega⟩ : Fin (N + 1)) ≠ Fin.last N := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    simp only [hp, if_neg hk0, if_neg hkl] at h1
    linarith
  have hall : ∀ j, j < N → gapMax e (j + 1) = gapMax e (0 + 1) := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [hstep j hj, ih (by omega)]
  exact ⟨e, hemono, he0, hel, fun i j => by rw [hall i.val i.2, hall j.val j.2]⟩

/-- Global non-domination for at least two nodes. -/
theorem no_domination (hN : 1 ≤ N) {s t : Fin (N + 1) → ℝ} (hs : StrictMono s) (ht : StrictMono t)
    (h0 : s 0 = t 0) (hl : s (Fin.last N) = t (Fin.last N))
    (hle : ∀ i : Fin N, gapMax s (i.val + 1) ≤ gapMax t (i.val + 1)) : s = t := by
  rcases (by omega : N = 1 ∨ 2 ≤ N) with h1 | h2
  · subst h1
    funext k
    rcases Fin.eq_zero_or_eq_succ k with h | ⟨j, rfl⟩
    · rw [h]; exact h0
    · have : j = 0 := Subsingleton.elim _ _
      subst this
      exact hl
  · exact no_domination_two h2 hs ht h0 hl hle

theorem exists_equi (hN : 1 ≤ N) (a b : ℝ) (hab : a < b) :
    ∃ e : Fin (N + 1) → ℝ, StrictMono e ∧ e 0 = a ∧ e (Fin.last N) = b ∧
      ∀ i j : Fin N, gapMax e (i.val + 1) = gapMax e (j.val + 1) := by
  rcases (by omega : N = 1 ∨ 2 ≤ N) with h1 | h2
  · subst h1
    refine ⟨![a, b], ?_, rfl, rfl, fun i j => by rw [Subsingleton.elim i j]⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · exact exists_equi_two h2 a b hab

theorem lebesgue_le_left {x : Fin (N + 1) → ℝ} (hx : StrictMono x) {y z : ℝ} (hzy : z ≤ y)
    (hy : y ≤ x 0) : lebesgueFunction x y ≤ lebesgueFunction x z := by
  unfold lebesgueFunction
  refine Finset.sum_le_sum fun k _ => ?_
  rw [abs_basis_eval, abs_basis_eval]
  refine Finset.prod_le_prod
    (fun l _ => mul_nonneg (inv_nonneg.mpr (abs_nonneg _)) (abs_nonneg _)) fun l _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (abs_nonneg _))
  have h1 : x 0 ≤ x l := hx.monotone (Fin.zero_le _)
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  linarith

theorem lebesgue_le_right {x : Fin (N + 1) → ℝ} (hx : StrictMono x) {y z : ℝ}
    (hy : x (Fin.last N) ≤ y) (hyz : y ≤ z) : lebesgueFunction x y ≤ lebesgueFunction x z := by
  unfold lebesgueFunction
  refine Finset.sum_le_sum fun k _ => ?_
  rw [abs_basis_eval, abs_basis_eval]
  refine Finset.prod_le_prod
    (fun l _ => mul_nonneg (inv_nonneg.mpr (abs_nonneg _)) (abs_nonneg _)) fun l _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (abs_nonneg _))
  have h1 : x l ≤ x (Fin.last N) := hx.monotone (Fin.le_last _)
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  linarith

theorem lebesgue_affine {n : ℕ} (x : Fin n → ℝ) (c d : ℝ) (hc : c ≠ 0) (y : ℝ) :
    lebesgueFunction (fun k => c * x k + d) (c * y + d) = lebesgueFunction x y := by
  unfold lebesgueFunction
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [basis_eval_eq, basis_eval_eq]
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  have e1 : c * x k + d - (c * x l + d) = c * (x k - x l) := by ring
  have e2 : c * y + d - (c * x l + d) = c * (y - x l) := by ring
  rw [e1, e2, mul_inv]
  have : c⁻¹ * (x k - x l)⁻¹ * (c * (y - x l)) = (c⁻¹ * c) * ((x k - x l)⁻¹ * (y - x l)) := by
    ring
  rw [this, inv_mul_cancel₀ hc, one_mul]

theorem gapMax_affine (x : Fin (N + 1) → ℝ) (c d : ℝ) (hc : 0 < c) (i : Fin N) :
    gapMax (fun k => c * x k + d) (i.val + 1) = gapMax x (i.val + 1) := by
  rw [gapMax_eq_sSup, gapMax_eq_sSup]
  congr 1
  ext z
  constructor
  · rintro ⟨y', hy', rfl⟩
    have h1 : c * x i.castSucc + d ≤ y' := hy'.1
    have h2 : y' ≤ c * x i.succ + d := hy'.2
    refine ⟨(y' - d) / c, ⟨?_, ?_⟩, ?_⟩
    · rw [le_div_iff₀ hc]; linarith
    · rw [div_le_iff₀ hc]; linarith
    · have := lebesgue_affine x c d hc.ne' ((y' - d) / c)
      rw [← this]
      congr 1
      field_simp
      ring
  · rintro ⟨y, hy, rfl⟩
    refine ⟨c * y + d, ⟨?_, ?_⟩, lebesgue_affine x c d hc.ne' y⟩
    · show c * x i.castSucc + d ≤ c * y + d
      nlinarith [hy.1]
    · show c * y + d ≤ c * x i.succ + d
      nlinarith [hy.2]

theorem lebesgue_le_lebesgueConstant {n : ℕ} (x : Fin n → ℝ) {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    lebesgueFunction x y ≤ lebesgueConstant x :=
  le_csSup (isCompact_Icc.image (continuous_lebesgue x)).bddAbove ⟨y, hy, rfl⟩

theorem gapMax_le_lebesgueConstant {x : Fin (N + 1) → ℝ} (hx : IsNodeSet x) (i : Fin N) :
    gapMax x (i.val + 1) ≤ lebesgueConstant x := by
  rw [gapMax_eq_sSup]
  have hlt : x i.castSucc < x i.succ := hx.1 (Fin.castSucc_lt_succ)
  refine csSup_le ⟨_, ⟨x i.castSucc, left_mem_Icc.mpr hlt.le, rfl⟩⟩ ?_
  rintro _ ⟨y, hy, rfl⟩
  exact lebesgue_le_lebesgueConstant x ⟨(hx.2 _).1.trans hy.1, hy.2.trans (hx.2 _).2⟩

theorem lebesgueConstant_le (hN : 0 < N) {x : Fin (N + 1) → ℝ} (hx : IsNodeSet x) {c : ℝ}
    (hg : ∀ i : Fin N, gapMax x (i.val + 1) ≤ c) (hl : lebesgueFunction x (-1) ≤ c)
    (hr : lebesgueFunction x 1 ≤ c) : lebesgueConstant x ≤ c := by
  refine csSup_le ⟨_, ⟨-1, ⟨le_rfl, by norm_num⟩, rfl⟩⟩ ?_
  rintro _ ⟨y, hy, rfl⟩
  rcases le_total y (x 0) with h | h
  · exact (lebesgue_le_left hx.1 hy.1 h).trans hl
  rcases le_total (x (Fin.last N)) y with h' | h'
  · exact (lebesgue_le_right hx.1 h' hy.2).trans hr
  obtain ⟨i, hi⟩ := exists_gap hN hx.1 h h'
  exact (le_gapMax x i hi).trans (hg i)

theorem strictMono_affine {x : Fin (N + 1) → ℝ} (hx : StrictMono x) {c : ℝ} (hc : 0 < c) (d : ℝ) :
    StrictMono (fun k => c * x k + d) := by
  intro i j hij
  have := hx hij
  simp only
  nlinarith

theorem equioscillates_iff (x : Fin (N + 1) → ℝ) :
    Equioscillates x ↔ ∀ i j : Fin N, gapMax x (i.val + 1) = gapMax x (j.val + 1) := by
  unfold Equioscillates
  constructor
  · intro h i j
    exact h _ (by simp) _ (by simp)
  · intro h i hi j hj
    simp only [Finset.mem_Icc, Nat.add_sub_cancel] at hi hj
    have := h ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
    simpa [Nat.sub_add_cancel hi.1, Nat.sub_add_cancel hj.1] using this

/-- The theorem for at least two nodes. -/
theorem main_succ (hN : 1 ≤ N) :
    {x : Fin (N + 1) → ℝ | IsMinimiser x} = erdos_1129.answer (N + 1) := by
  have hpos : 0 < N := hN
  ext x
  simp only [erdos_1129.answer, Set.mem_ofPred_eq]
  have g1 : ∀ z : Fin (N + 1) → ℝ, gapMax z 1 = gapMax z ((⟨0, hpos⟩ : Fin N).val + 1) := by
    intro z; rfl
  constructor
  · -- minimiser ⟹ answer
    rintro ⟨hx, hmin⟩
    have hlt : x 0 < x (Fin.last N) := hx.1 (Fin.pos_iff_ne_zero.mpr (by
      intro h; have := congrArg Fin.val h; simp at this; omega))
    obtain ⟨e, he, he0, hel, heq⟩ := exists_equi hN (x 0) (x (Fin.last N)) hlt
    -- canonical rescale of e
    have hW : 0 < e (Fin.last N) - e 0 := by rw [he0, hel]; linarith
    set c : ℝ := 2 / (e (Fin.last N) - e 0) with hc
    have hcpos : 0 < c := by positivity
    set d : ℝ := -1 - c * e 0 with hd
    set e' : Fin (N + 1) → ℝ := fun k => c * e k + d with he'
    have he'mono : StrictMono e' := strictMono_affine he hcpos d
    have he'0 : e' 0 = -1 := by simp only [he', hd]; ring
    have he'l : e' (Fin.last N) = 1 := by
      simp only [he', hd, hc]; field_simp; ring
    have he'node : IsNodeSet e' := by
      refine ⟨he'mono, fun k => ⟨?_, ?_⟩⟩
      · rw [← he'0]; exact he'mono.monotone (Fin.zero_le k)
      · rw [← he'l]; exact he'mono.monotone (Fin.le_last k)
    have hgap' : ∀ i : Fin N, gapMax e' (i.val + 1) = gapMax e (i.val + 1) :=
      fun i => gapMax_affine e c d hcpos i
    set lam := gapMax e 1 with hlam
    have hall : ∀ i : Fin N, gapMax e (i.val + 1) = lam := fun i => by
      rw [hlam, g1]; exact heq i _
    have hC' : lebesgueConstant e' ≤ lam := by
      refine lebesgueConstant_le hpos he'node (fun i => by rw [hgap', hall]) ?_ ?_
      · have := le_gapMax e' ⟨0, hpos⟩ (y := -1) (by
          refine ⟨?_, ?_⟩
          · rw [← he'0]; exact le_of_eq (by congr 1)
          · rw [← he'0]; exact he'mono.monotone (Fin.zero_le _))
        rwa [hgap', hall] at this
      · have := le_gapMax e' ⟨N - 1, by omega⟩ (y := 1) (by
          refine ⟨?_, ?_⟩
          · rw [← he'l]; exact he'mono.monotone (Fin.le_last _)
          · rw [← he'l]; exact le_of_eq (by congr 1; ext; simp; omega))
        rwa [hgap', hall] at this
    have hCx : lebesgueConstant x ≤ lam := (hmin e' he'node).trans hC'
    have hxe : x = e := by
      refine no_domination hN hx.1 he he0.symm hel.symm fun i => ?_
      rw [hall]
      exact (gapMax_le_lebesgueConstant hx i).trans hCx
    refine ⟨hx, ?_, ?_, ?_⟩
    · rw [equioscillates_iff, hxe]; exact heq
    · rw [hxe] at hCx ⊢
      exact (lebesgue_le_lebesgueConstant e ⟨le_rfl, by norm_num⟩).trans hCx
    · rw [hxe] at hCx ⊢
      exact (lebesgue_le_lebesgueConstant e ⟨by norm_num, le_rfl⟩).trans hCx
  · -- answer ⟹ minimiser
    rintro ⟨hx, heq, hL, hR⟩
    rw [equioscillates_iff] at heq
    refine ⟨hx, fun y hy => ?_⟩
    set lam := gapMax x 1 with hlam
    have hall : ∀ i : Fin N, gapMax x (i.val + 1) = lam := fun i => by
      rw [hlam, g1]; exact heq i _
    have hCx : lebesgueConstant x ≤ lam :=
      lebesgueConstant_le hpos hx (fun i => (hall i).le) hL hR
    refine hCx.trans ?_
    by_contra hcon
    push Not at hcon
    have hlast : (0 : Fin (N + 1)) < Fin.last N := Fin.pos_iff_ne_zero.mpr (by
      intro h; have := congrArg Fin.val h; simp at this; omega)
    have hxlt : x 0 < x (Fin.last N) := hx.1 hlast
    have hylt : y 0 < y (Fin.last N) := hy.1 hlast
    set c : ℝ := (x (Fin.last N) - x 0) / (y (Fin.last N) - y 0) with hc
    have hcpos : 0 < c := div_pos (by linarith) (by linarith)
    set d : ℝ := x 0 - c * y 0 with hd
    set y' : Fin (N + 1) → ℝ := fun k => c * y k + d with hy'
    have hy'mono : StrictMono y' := strictMono_affine hy.1 hcpos d
    have hy'0 : y' 0 = x 0 := by simp only [hy', hd]; ring
    have hy'l : y' (Fin.last N) = x (Fin.last N) := by
      simp only [hy', hd, hc]
      have : y (Fin.last N) - y 0 ≠ 0 := by linarith
      field_simp
      ring
    have hgap' : ∀ i : Fin N, gapMax y' (i.val + 1) = gapMax y (i.val + 1) :=
      fun i => gapMax_affine y c d hcpos i
    have hyx : y' = x := by
      refine no_domination hN hy'mono hx.1 hy'0 hy'l fun i => ?_
      rw [hgap', hall]
      exact ((gapMax_le_lebesgueConstant hy i).trans hcon.le)
    have h1 := gapMax_le_lebesgueConstant hy ⟨0, hpos⟩
    rw [← hgap', hyx, hall] at h1
    linarith


theorem main_zero : {x : Fin 0 → ℝ | IsMinimiser x} = erdos_1129.answer 0 := by
  ext x
  simp only [erdos_1129.answer, Set.mem_ofPred_eq]
  have hL : ∀ (z : Fin 0 → ℝ) (t : ℝ), lebesgueFunction z t = 0 := by
    intro z t; simp [lebesgueFunction]
  constructor
  · rintro ⟨hx, -⟩
    refine ⟨hx, ?_, ?_, ?_⟩
    · intro i hi; simp at hi
    · rw [hL]
      unfold gapMax
      refine Real.sSup_nonneg ?_
      rintro _ ⟨y, -, rfl⟩
      rw [hL]
    · rw [hL]
      unfold gapMax
      refine Real.sSup_nonneg ?_
      rintro _ ⟨y, -, rfl⟩
      rw [hL]
  · rintro ⟨hx, -⟩
    exact ⟨hx, fun y _ => le_of_eq (by rw [Subsingleton.elim x y])⟩

theorem main_one : {x : Fin 1 → ℝ | IsMinimiser x} = erdos_1129.answer 1 := by
  ext x
  simp only [erdos_1129.answer, Set.mem_ofPred_eq]
  have hL : ∀ (z : Fin 1 → ℝ) (t : ℝ), lebesgueFunction z t = 1 := by
    intro z t
    simp [lebesgueFunction, Lagrange.basis]
  have hgap : ∀ z : Fin 1 → ℝ, IsNodeSet z → (1 : ℝ) ≤ gapMax z 1 := by
    intro z hz
    unfold gapMax
    have h1 : extendedNodes z 1 = z 0 := by simp [extendedNodes]
    have h2 : extendedNodes z (1 + 1) = 1 := by simp [extendedNodes]
    rw [h1, h2]
    exact le_csSup (isCompact_Icc.image (continuous_lebesgue z)).bddAbove
      ⟨z 0, left_mem_Icc.mpr (hz.2 0).2, hL z _⟩
  constructor
  · rintro ⟨hx, -⟩
    refine ⟨hx, ?_, ?_, ?_⟩
    · intro i hi; simp at hi
    · rw [hL]; exact hgap x hx
    · rw [hL]; exact hgap x hx
  · rintro ⟨hx, -⟩
    refine ⟨hx, fun y _ => le_of_eq ?_⟩
    unfold lebesgueConstant
    have : lebesgueFunction x = lebesgueFunction y := by funext t; rw [hL, hL]
    rw [this]


end OMA.Helpers

theorem OMA.solution : type_of% @Erdos1129.erdos_1129 := by
  intro n
  match n with
  | 0 => exact OMA.Helpers.main_zero
  | 1 => exact OMA.Helpers.main_one
  | (N + 2) => exact OMA.Helpers.main_succ (N := N + 1) (by omega)

