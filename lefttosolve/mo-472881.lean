import OMAStatements.S_mo_472881
import Mathlib

namespace OMA.Helpers

open MvPolynomial

/-- A linear polynomial equal to one at `y` and zero at `z` (when `y ≠ z`). -/
noncomputable def orbitSep472881 {d : ℕ} (y z : Fin d → ℂ) : MvPolynomial (Fin d) ℂ :=
  if h : ∃ i, y i ≠ z i then
    (X h.choose - C (z h.choose)) * C (y h.choose - z h.choose)⁻¹
  else 1

lemma orbitSep472881_ex {d : ℕ} {y z : Fin d → ℂ} (hyz : y ≠ z) : ∃ i, y i ≠ z i := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hyz (funext h)

lemma orbitSep472881_left {d : ℕ} {y z : Fin d → ℂ} (hyz : y ≠ z) :
    eval y (orbitSep472881 y z) = 1 := by
  have h := orbitSep472881_ex hyz
  unfold orbitSep472881
  rw [dif_pos h]
  have h2 := sub_ne_zero.mpr h.choose_spec
  simp only [map_mul, map_sub, eval_X, eval_C]
  exact mul_inv_cancel₀ h2

lemma orbitSep472881_right {d : ℕ} {y z : Fin d → ℂ} (hyz : y ≠ z) :
    eval z (orbitSep472881 y z) = 0 := by
  have h := orbitSep472881_ex hyz
  unfold orbitSep472881
  rw [dif_pos h]
  simp

theorem orbitPart1_472881 {G : Type} [Group G] [Fintype G] {d : ℕ}
    (ρ : Representation ℂ G (Fin d → ℂ)) (H : Subgroup G) (v : Fin d → ℂ)
    (hv : OMA.S_mo_472881.Admissible ρ H v) : ∃ p, OMA.S_mo_472881.Selects ρ H v p := by
  classical
  have hdist : ∀ h ∈ H, ∀ g ∉ H, ρ h v ≠ ρ g v := by
    intro h hh g hg heq
    apply hg
    have h1 : ρ (h⁻¹ * g) v = v := by
      rw [map_mul, Module.End.mul_apply, ← heq, ← Module.End.mul_apply, ← map_mul,
        inv_mul_cancel, map_one, Module.End.one_apply]
    have h2 := H.mul_mem hh (hv _ h1)
    simpa using h2
  let e : G → MvPolynomial (Fin d) ℂ := fun h =>
    ∏ g ∈ Finset.univ.filter (fun g => g ∉ H), orbitSep472881 (ρ h v) (ρ g v)
  refine ⟨1 - ∏ h ∈ Finset.univ.filter (fun h => h ∈ H), (1 - e h), ?_, ?_⟩
  · intro g hg
    simp only [map_sub, map_one, map_prod]
    rw [Finset.prod_eq_zero (i := g) (by simpa using hg)]
    · simp
    · simp only [e, map_prod]
      rw [Finset.prod_eq_one]
      · simp
      intro g' hg'
      exact orbitSep472881_left (hdist g hg g' (by simpa using hg'))
  · intro g hg
    simp only [map_sub, map_one, map_prod]
    rw [Finset.prod_eq_one]
    · simp
    intro h hh
    simp only [e, map_prod]
    rw [Finset.prod_eq_zero (i := g) (by simpa using hg)]
    · simp
    exact orbitSep472881_right (hdist h (by simpa using hh) g hg)


lemma orbitLineEval472881 {d : ℕ} (v : Fin d → ℂ) (q : MvPolynomial (Fin d) ℂ) (t : ℂ) :
    Polynomial.eval t (aeval (fun i => Polynomial.C (v i) * Polynomial.X) q) = eval (t • v) q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.eval_mul, hp, aeval_X, Polynomial.eval_C, Polynomial.eval_X,
      eval_X, Pi.smul_apply, smul_eq_mul]
    ring

lemma orbitEvalSum472881 {d : ℕ} (F : Finset (Fin d →₀ ℕ)) (a : (Fin d →₀ ℕ) → ℂ)
    (y : Fin d → ℂ) :
    eval y (∑ m ∈ F, monomial m (a m)) = ∑ m ∈ F, a m * eval y (monomial m 1) := by
  simp [map_sum, eval_monomial]

theorem orbitPart2_472881 {G : Type} [Group G] {d : ℕ}
    (ρ : Representation ℂ G (Fin d → ℂ)) (H : Subgroup G) (v : Fin d → ℂ)
    (hH : H ≠ ⊤) (hv : OMA.S_mo_472881.Admissible ρ H v) :
    ¬ ∃ p : (Fin d → ℂ) → MvPolynomial (Fin d) ℂ,
      (∀ x, OMA.S_mo_472881.Admissible ρ H x → OMA.S_mo_472881.Selects ρ H x (p x)) ∧
      ∀ m : Fin d →₀ ℕ, ∃ c : MvPolynomial (Fin d) ℂ, ∀ x, OMA.S_mo_472881.Admissible ρ H x →
        MvPolynomial.coeff m (p x) = MvPolynomial.eval x c := by
  classical
  rintro ⟨p, hsel, hcoef⟩
  choose c hc using hcoef
  obtain ⟨g, hg⟩ : ∃ g, g ∉ H := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hH (eq_top_iff.mpr (fun x _ => h x))
  have hadm : ∀ t : ℂ, t ≠ 0 → OMA.S_mo_472881.Admissible ρ H (t • v) := by
    intro t ht k hk
    apply hv k
    rw [map_smul] at hk
    exact smul_right_injective _ ht hk
  let Q : (Fin d →₀ ℕ) → Polynomial ℂ := fun m =>
    aeval (fun i => Polynomial.C (v i) * Polynomial.X) (c m)
  have hQ : ∀ m t, t ≠ 0 → Polynomial.eval t (Q m) = coeff m (p (t • v)) := by
    intro m t ht
    rw [hc m _ (hadm t ht)]
    exact orbitLineEval472881 v (c m) t
  -- the set of roots of the nonzero line polynomials is countable
  let Z : Set ℂ := ⋃ m, {t | Q m ≠ 0 ∧ (Q m).IsRoot t}
  have hZ : Z.Countable := by
    refine Set.countable_iUnion (fun m => ?_)
    by_cases hm : Q m = 0
    · simp [hm]
    · refine (Polynomial.finite_setOfPred_isRoot hm).countable.mono ?_
      intro t ht
      exact ht.2
  have hZ0 : (Z ∪ {0}).Countable := hZ.union (Set.countable_singleton 0)
  obtain ⟨t0, ht0⟩ := (Set.Countable.dense_compl ℂ hZ0).nonempty
  have ht0Z : t0 ∉ Z := fun h => ht0 (Or.inl h)
  have ht00 : t0 ≠ 0 := fun h => ht0 (Or.inr h)
  have hfin : {m | Q m ≠ 0}.Finite := by
    refine (p (t0 • v)).support.finite_toSet.subset ?_
    intro m hm
    simp only [Finset.mem_coe, mem_support_iff]
    rw [← hQ m t0 ht00]
    intro hr
    exact ht0Z (Set.mem_iUnion.mpr ⟨m, hm, hr⟩)
  set F := hfin.toFinset with hF
  have hp : ∀ t : ℂ, t ≠ 0 → p (t • v) = ∑ m ∈ F, monomial m (eval (t • v) (c m)) := by
    intro t ht
    ext n
    rw [coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with hn
    · exact hc n _ (hadm t ht)
    · rw [← hQ n t ht]
      have : Q n = 0 := by
        by_contra h
        exact hn (hfin.mem_toFinset.mpr h)
      rw [this, Polynomial.eval_zero]
  let Φ : ℂ → ℂ := fun t => ∑ m ∈ F, eval (t • v) (c m) * eval (t • v) (monomial m 1)
  let Ψ : ℂ → ℂ := fun t => ∑ m ∈ F, eval (t • v) (c m) * eval (ρ g (t • v)) (monomial m 1)
  have hsm : Continuous fun t : ℂ => t • v := continuous_id.smul continuous_const
  have hρ : Continuous fun t : ℂ => ρ g (t • v) :=
    (LinearMap.continuous_of_finiteDimensional (ρ g)).comp hsm
  have hΦc : Continuous Φ := by
    refine continuous_finsetSum _ (fun m _ => ?_)
    exact ((MvPolynomial.continuous_eval (c m)).comp hsm).mul
      ((MvPolynomial.continuous_eval _).comp hsm)
  have hΨc : Continuous Ψ := by
    refine continuous_finsetSum _ (fun m _ => ?_)
    exact ((MvPolynomial.continuous_eval (c m)).comp hsm).mul
      ((MvPolynomial.continuous_eval _).comp hρ)
  have hΦ : Φ = fun _ => 1 := by
    refine Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hΦc continuous_const ?_
    intro t ht
    have ht' : t ≠ 0 := ht
    have h1 := (hsel _ (hadm t ht')).1 1 H.one_mem
    rw [map_one, Module.End.one_apply, hp t ht', orbitEvalSum472881] at h1
    exact h1
  have hΨ : Ψ = fun _ => 0 := by
    refine Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hΨc continuous_const ?_
    intro t ht
    have ht' : t ≠ 0 := ht
    have h1 := (hsel _ (hadm t ht')).2 g hg
    rw [hp t ht', orbitEvalSum472881] at h1
    exact h1
  have h0 : Φ 0 = Ψ 0 := by
    simp only [Φ, Ψ, zero_smul, map_zero]
  rw [hΦ, hΨ] at h0
  exact one_ne_zero h0

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_mo_472881.main := by
  intro G _ _ d ρ H v _ hH hv
  exact ⟨OMA.Helpers.orbitPart1_472881 ρ H v hv, OMA.Helpers.orbitPart2_472881 ρ H v hH hv⟩
