import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R1

namespace OMA.Helpers

/-- Conjugation by an element of the kernel is the inner automorphism it defines. -/
theorem conjAct_inl {N E G : Type} [Group N] [Group E] [Group G]
    (S : GroupExtension N E G) (a : N) : S.conjAct (S.inl a) = MulAut.conj a := by
  ext m
  apply S.inl_injective
  rw [S.inl_conjAct_comm]
  simp [MulAut.conj_apply]

/-- Two extensions with sections inducing the same outer action and the same factor set are
equivalent. -/
theorem equiv_of_factor {N G E E' : Type} [Group N] [Group G] [Group E] [Group E']
    (S : GroupExtension N E G) (S' : GroupExtension N E' G) (action : G → MulAut N)
    (σ : G → E) (σ' : G → E')
    (hσ : ∀ h, S.rightHom (σ h) = h) (hσ' : ∀ h, S'.rightHom (σ' h) = h)
    (hc : ∀ h, S.conjAct (σ h) = action h) (hc' : ∀ h, S'.conjAct (σ' h) = action h)
    (f : G → G → N)
    (hf : ∀ h k, σ h * σ k = S.inl (f h k) * σ (h * k))
    (hf' : ∀ h k, σ' h * σ' k = S'.inl (f h k) * σ' (h * k)) :
    Nonempty (S.Equiv S') := by
  classical
  have hdec : ∀ e : E, ∃ a : N, e = S.inl a * σ (S.rightHom e) := by
    intro e
    have hmem : e * (σ (S.rightHom e))⁻¹ ∈ S.inl.range := by
      rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, hσ, mul_inv_cancel]
    obtain ⟨a, ha⟩ := hmem
    exact ⟨a, by rw [ha, inv_mul_cancel_right]⟩
  choose ν hν using hdec
  have prod : ∀ (a b : N) (h k : G),
      S.inl a * σ h * (S.inl b * σ k) = S.inl (a * action h b * f h k) * σ (h * k) := by
    intro a b h k
    have sw : σ h * S.inl b = S.inl (S.conjAct (σ h) b) * σ h := by
      rw [S.inl_conjAct_comm]; group
    calc S.inl a * σ h * (S.inl b * σ k) = S.inl a * (σ h * S.inl b) * σ k := by group
      _ = S.inl a * (S.inl (S.conjAct (σ h) b) * σ h) * σ k := by rw [sw]
      _ = S.inl a * S.inl (S.conjAct (σ h) b) * (σ h * σ k) := by group
      _ = S.inl (a * action h b * f h k) * σ (h * k) := by
        rw [hf, hc, map_mul, map_mul]; group
  have prod' : ∀ (a b : N) (h k : G),
      S'.inl a * σ' h * (S'.inl b * σ' k) = S'.inl (a * action h b * f h k) * σ' (h * k) := by
    intro a b h k
    have sw : σ' h * S'.inl b = S'.inl (S'.conjAct (σ' h) b) * σ' h := by
      rw [S'.inl_conjAct_comm]; group
    calc S'.inl a * σ' h * (S'.inl b * σ' k) = S'.inl a * (σ' h * S'.inl b) * σ' k := by group
      _ = S'.inl a * (S'.inl (S'.conjAct (σ' h) b) * σ' h) * σ' k := by rw [sw]
      _ = S'.inl a * S'.inl (S'.conjAct (σ' h) b) * (σ' h * σ' k) := by group
      _ = S'.inl (a * action h b * f h k) * σ' (h * k) := by
        rw [hf', hc', map_mul, map_mul]; group
  have uniq : ∀ (e : E) (a : N), e = S.inl a * σ (S.rightHom e) → ν e = a := by
    intro e a he
    apply S.inl_injective
    exact mul_right_cancel ((hν e).symm.trans he)
  have hone : σ 1 = S.inl (f 1 1) := by
    have := hf 1 1
    rw [mul_one] at this
    exact mul_right_cancel this
  have hone' : σ' 1 = S'.inl (f 1 1) := by
    have := hf' 1 1
    rw [mul_one] at this
    exact mul_right_cancel this
  let φ : E →* E' := MonoidHom.mk' (fun e => S'.inl (ν e) * σ' (S.rightHom e)) (by
    intro e₁ e₂
    have hr : S.rightHom (e₁ * e₂) = S.rightHom e₁ * S.rightHom e₂ := map_mul _ _ _
    have key : ν (e₁ * e₂) = ν e₁ * action (S.rightHom e₁) (ν e₂) *
        f (S.rightHom e₁) (S.rightHom e₂) := by
      apply uniq
      rw [hr, ← prod, ← hν e₁, ← hν e₂]
    show S'.inl (ν (e₁ * e₂)) * σ' (S.rightHom (e₁ * e₂)) =
      S'.inl (ν e₁) * σ' (S.rightHom e₁) * (S'.inl (ν e₂) * σ' (S.rightHom e₂))
    rw [key, hr, prod'])
  refine ⟨GroupExtension.Equiv.ofMonoidHom φ ?_ ?_⟩
  · ext a
    have key : ν (S.inl a) = a * (f 1 1)⁻¹ := by
      apply uniq
      rw [S.rightHom_inl, hone, ← map_mul, inv_mul_cancel_right]
    simp only [MonoidHom.comp_apply, φ, MonoidHom.mk'_apply]
    rw [key, S.rightHom_inl, hone', ← map_mul, inv_mul_cancel_right]
  · ext e
    simp [φ, hσ']

end OMA.Helpers

open CategoryTheory in
theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R1.H1 := by
  intro N H I D S action hact hinj
  classical
  rcases isEmpty_or_nonempty I with hI | ⟨⟨i₀⟩⟩
  · exact ⟨⟨fun i => isEmptyElim i, fun i => isEmptyElim i⟩⟩
  choose e n he hn using hact
  let σ : (i : I) → H → D i := fun i h => (S i).inl (n i h) * e i h
  have hσ : ∀ i h, (S i).rightHom (σ i h) = h := by
    intro i h
    simp [σ, he]
  have hc : ∀ i h, (S i).conjAct (σ i h) = action h := by
    intro i h
    simp only [σ, map_mul, OMA.Helpers.conjAct_inl]
    exact hn i h
  clear_value σ
  have hfex : ∀ i h k, ∃ c : N, σ i h * σ i k = (S i).inl c * σ i (h * k) := by
    intro i h k
    have hmem : σ i h * σ i k * (σ i (h * k))⁻¹ ∈ (S i).inl.range := by
      rw [(S i).range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_mul, map_inv,
        hσ, hσ, hσ, mul_inv_cancel]
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, by rw [hc, inv_mul_cancel_right]⟩
  choose f hf using hfex
  have hconj : ∀ i h k, MulAut.conj (f i h k) = action h * action k * (action (h * k))⁻¹ := by
    intro i h k
    have := congrArg (S i).conjAct (hf i h k)
    rw [map_mul, map_mul, hc, hc, hc, OMA.Helpers.conjAct_inl] at this
    rw [this]
    group
  have hcen : ∀ i h k, (f i₀ h k)⁻¹ * f i h k ∈ Subgroup.center N := by
    intro i h k
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun ψ : MulAut N => ψ g) ((hconj i h k).trans (hconj i₀ h k).symm)
    simp only [MulAut.conj_apply] at h1
    calc g * ((f i₀ h k)⁻¹ * f i h k)
        = (f i₀ h k)⁻¹ * (f i₀ h k * g * (f i₀ h k)⁻¹) * f i h k := by group
      _ = (f i₀ h k)⁻¹ * (f i h k * g * (f i h k)⁻¹) * f i h k := by rw [h1]
      _ = (f i₀ h k)⁻¹ * f i h k * g := by group
  refine ⟨⟨fun i p => ⟨(f i₀ p.1 p.2)⁻¹ * f i p.1 p.2, hcen i p.1 p.2⟩, ?_⟩⟩
  intro i j hij
  have hff : ∀ h k, f i h k = f j h k := by
    intro h k
    have := congrArg (fun F => ((F (h, k) : Subgroup.center N) : N)) hij
    simpa using this
  apply hinj i j
  exact OMA.Helpers.equiv_of_factor (S i) (S j) action (σ i) (σ j) (hσ i) (hσ j) (hc i) (hc j)
    (f i) (hf i) (fun h k => by rw [hff]; exact hf j h k)
