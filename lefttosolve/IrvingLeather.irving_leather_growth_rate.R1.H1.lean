import OMAReductions.R_IrvingLeather_irving_leather_growth_rate_R1

/-!
# Step H1 of the reduction IrvingLeather.irving_leather_growth_rate.R1

Supermultiplicativity of the maximum number of stable matchings. Given profiles `p` on `m` and
`q` on `n` participants per side, put them side by side on `m + n`: every participant ranks the
members of their own block first (in the original order) and the other block afterwards. If `μ`
is stable for `p` and `ν` is stable for `q`, then `μ ⊕ ν` is stable for the combined profile:
a blocking pair inside one block would block `μ` or `ν`, and a man never prefers a woman of the
other block to his own partner. The map `(μ, ν) ↦ μ ⊕ ν` is injective.

Only upstream definitions are used.
-/

namespace OMA.Helpers

open StableMarriage

/-- Ranks for a participant of the first block: own block first, in the order given by `σ`. -/
def ilBlockL {m n : ℕ} (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + n)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr σ (Equiv.refl (Fin n))).trans finSumFinEquiv)

/-- Ranks for a participant of the second block: own block first, in the order given by `τ`. -/
def ilBlockR {m n : ℕ} (τ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (m + n)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr (Equiv.refl (Fin m)) τ).trans
    ((Equiv.sumComm (Fin m) (Fin n)).trans (finSumFinEquiv.trans (finCongr (Nat.add_comm n m)))))

theorem ilBlockL_left {m n : ℕ} (σ : Equiv.Perm (Fin m)) (x : Fin m) :
    ((ilBlockL (n := n) σ) (finSumFinEquiv (Sum.inl x))).val = (σ x).val := by
  simp [ilBlockL]

theorem ilBlockL_right {m n : ℕ} (σ : Equiv.Perm (Fin m)) (y : Fin n) :
    ((ilBlockL (n := n) σ) (finSumFinEquiv (Sum.inr y))).val = m + y.val := by
  simp [ilBlockL]

theorem ilBlockR_left {m n : ℕ} (τ : Equiv.Perm (Fin n)) (x : Fin m) :
    ((ilBlockR (m := m) τ) (finSumFinEquiv (Sum.inl x))).val = n + x.val := by
  simp [ilBlockR]
  omega

theorem ilBlockR_right {m n : ℕ} (τ : Equiv.Perm (Fin n)) (y : Fin n) :
    ((ilBlockR (m := m) τ) (finSumFinEquiv (Sum.inr y))).val = (τ y).val := by
  simp [ilBlockR]

/-- The side-by-side profile. -/
def ilJoin {m n : ℕ} (p : Profile m) (q : Profile n) : Profile (m + n) where
  manRank i := Sum.elim (fun a => ilBlockL (p.manRank a)) (fun b => ilBlockR (q.manRank b))
    (finSumFinEquiv.symm i)
  womanRank i := Sum.elim (fun a => ilBlockL (p.womanRank a)) (fun b => ilBlockR (q.womanRank b))
    (finSumFinEquiv.symm i)

/-- The side-by-side matching. -/
def ilJoinMatching {m n : ℕ} (μ : Matching m) (ν : Matching n) : Matching (m + n) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr μ ν)

theorem ilJoinMatching_left {m n : ℕ} (μ : Matching m) (ν : Matching n) (a : Fin m) :
    ilJoinMatching μ ν (finSumFinEquiv (Sum.inl a)) = finSumFinEquiv (Sum.inl (μ a)) := by
  simp [ilJoinMatching, Equiv.permCongr_apply]

theorem ilJoinMatching_right {m n : ℕ} (μ : Matching m) (ν : Matching n) (b : Fin n) :
    ilJoinMatching μ ν (finSumFinEquiv (Sum.inr b)) = finSumFinEquiv (Sum.inr (ν b)) := by
  simp [ilJoinMatching, Equiv.permCongr_apply]

theorem ilJoinMatching_symm_left {m n : ℕ} (μ : Matching m) (ν : Matching n) (x : Fin m) :
    (ilJoinMatching μ ν).symm (finSumFinEquiv (Sum.inl x)) =
      finSumFinEquiv (Sum.inl (μ.symm x)) := by
  rw [Equiv.symm_apply_eq, ilJoinMatching_left, Equiv.apply_symm_apply]

theorem ilJoinMatching_symm_right {m n : ℕ} (μ : Matching m) (ν : Matching n) (y : Fin n) :
    (ilJoinMatching μ ν).symm (finSumFinEquiv (Sum.inr y)) =
      finSumFinEquiv (Sum.inr (ν.symm y)) := by
  rw [Equiv.symm_apply_eq, ilJoinMatching_right, Equiv.apply_symm_apply]

theorem ilJoin_stable {m n : ℕ} (p : Profile m) (q : Profile n) (μ : Matching m)
    (ν : Matching n) (hμ : IsStable p μ) (hν : IsStable q ν) :
    IsStable (ilJoin p q) (ilJoinMatching μ ν) := by
  intro M W hB
  obtain ⟨sM, rfl⟩ := finSumFinEquiv.surjective M
  obtain ⟨sW, rfl⟩ := finSumFinEquiv.surjective W
  obtain ⟨hne, hman, hwoman⟩ := hB
  rcases sM with a | b <;> rcases sW with x | y
  · -- both in the first block
    rw [ilJoinMatching_left] at hne hman
    rw [ilJoinMatching_symm_left] at hwoman
    simp only [ilJoin, Equiv.symm_apply_apply, Sum.elim_inl] at hman hwoman
    rw [Fin.lt_def, ilBlockL_left, ilBlockL_left] at hman hwoman
    refine hμ a x ⟨fun h => hne (by rw [h]), ?_, ?_⟩
    · exact Fin.lt_def.mpr hman
    · exact Fin.lt_def.mpr hwoman
  · -- man in the first block, woman in the second
    rw [ilJoinMatching_left] at hman
    simp only [ilJoin, Equiv.symm_apply_apply, Sum.elim_inl] at hman
    rw [Fin.lt_def, ilBlockL_right, ilBlockL_left] at hman
    have := ((p.manRank a) (μ a)).isLt
    omega
  · -- man in the second block, woman in the first
    rw [ilJoinMatching_right] at hman
    simp only [ilJoin, Equiv.symm_apply_apply, Sum.elim_inr] at hman
    rw [Fin.lt_def, ilBlockR_left, ilBlockR_right] at hman
    have := ((q.manRank b) (ν b)).isLt
    omega
  · -- both in the second block
    rw [ilJoinMatching_right] at hne hman
    rw [ilJoinMatching_symm_right] at hwoman
    simp only [ilJoin, Equiv.symm_apply_apply, Sum.elim_inr] at hman hwoman
    rw [Fin.lt_def, ilBlockR_right, ilBlockR_right] at hman hwoman
    refine hν b y ⟨fun h => hne (by rw [h]), ?_, ?_⟩
    · exact Fin.lt_def.mpr hman
    · exact Fin.lt_def.mpr hwoman

theorem ilJoinMatching_injective {m n : ℕ} :
    Function.Injective (fun x : Matching m × Matching n => ilJoinMatching x.1 x.2) := by
  rintro ⟨μ, ν⟩ ⟨μ', ν'⟩ h
  simp only at h
  have h1 : μ = μ' := by
    ext a
    have := congrArg (fun ρ : Matching (m + n) => ρ (finSumFinEquiv (Sum.inl a))) h
    simp only [ilJoinMatching_left] at this
    have := finSumFinEquiv.injective this
    rw [Sum.inl.injEq] at this
    rw [this]
  have h2 : ν = ν' := by
    ext b
    have := congrArg (fun ρ : Matching (m + n) => ρ (finSumFinEquiv (Sum.inr b))) h
    simp only [ilJoinMatching_right] at this
    have := finSumFinEquiv.injective this
    rw [Sum.inr.injEq] at this
    rw [this]
  rw [h1, h2]

theorem ilJoin_num {m n : ℕ} (p : Profile m) (q : Profile n) :
    numStableMatchings p * numStableMatchings q ≤ numStableMatchings (ilJoin p q) := by
  classical
  unfold numStableMatchings
  rw [← Fintype.card_prod]
  refine Fintype.card_le_of_injective
    (fun x => ⟨ilJoinMatching x.1.1 x.2.1, ilJoin_stable p q x.1.1 x.2.1 x.1.2 x.2.2⟩) ?_
  rintro ⟨⟨μ, hμ⟩, ⟨ν, hν⟩⟩ ⟨⟨μ', hμ'⟩, ⟨ν', hν'⟩⟩ h
  have h' : ilJoinMatching μ ν = ilJoinMatching μ' ν' := congrArg Subtype.val h
  have := ilJoinMatching_injective (m := m) (n := n) (a₁ := (μ, ν)) (a₂ := (μ', ν')) h'
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  rfl

end OMA.Helpers

open IrvingLeather StableMarriage in
theorem OMA.solution : OMA.R_IrvingLeather_irving_leather_growth_rate_R1.H1 := by
  intro m n
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Profile m))
    Finset.univ_nonempty (fun p : Profile m ↦ numStableMatchings p)
  obtain ⟨q, -, hq⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Profile n))
    Finset.univ_nonempty (fun q : Profile n ↦ numStableMatchings q)
  unfold maxStableMatchings
  rw [hp, hq]
  exact (OMA.Helpers.ilJoin_num p q).trans
    (Finset.le_sup (f := fun r : Profile (m + n) ↦ numStableMatchings r) (Finset.mem_univ _))
