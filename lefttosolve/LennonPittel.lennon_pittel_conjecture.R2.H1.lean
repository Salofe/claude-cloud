import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R2

/-!
# Step H1 of the reduction LennonPittel.lennon_pittel_conjecture.R2

Every complete strict preference profile admits a stable complete matching (Gale and Shapley).

The proof is a deferred acceptance argument on a finite set R of rejected pairs. Under R, each
man proposes to his favourite woman who has not rejected him. The invariant says that every
rejection of a man m by a woman w is justified by a current proposer whom w prefers to m.
While some woman has two proposers, she rejects the worse one; the invariant is preserved and R
grows, so the process stops. At the end no man is rejected by every woman (otherwise every woman
would have a proposer, and by counting so would that man), each woman has at most one proposer,
and the proposals form a bijection without blocking pairs. Only the upstream definitions of
profiles, matchings and stability are used.
-/

namespace OMA.Helpers

open StableMarriage

/-- Under the rejection set R, man m proposes to w: w is his favourite non-rejecting woman. -/
def GSProposes {n : ℕ} (p : Profile n) (R : Finset (Fin n × Fin n)) (m w : Fin n) : Prop :=
  (m, w) ∉ R ∧ ∀ w', (m, w') ∉ R → p.manRank m w ≤ p.manRank m w'

/-- Every rejection of m by w is justified by a better current proposer to w. -/
def GSInv {n : ℕ} (p : Profile n) (R : Finset (Fin n × Fin n)) : Prop :=
  ∀ m w, (m, w) ∈ R → ∃ m', p.womanRank w m' < p.womanRank w m ∧ GSProposes p R m' w

theorem gs_proposes_unique {n : ℕ} {p : Profile n} {R : Finset (Fin n × Fin n)}
    {m w w' : Fin n} (h : GSProposes p R m w) (h' : GSProposes p R m w') : w = w' :=
  (p.manRank m).injective (le_antisymm (h.2 w' h'.1) (h'.2 w h.1))

theorem gs_exists_proposes {n : ℕ} (p : Profile n) (R : Finset (Fin n × Fin n))
    {m w0 : Fin n} (h : (m, w0) ∉ R) : ∃ w, GSProposes p R m w := by
  classical
  have hs : (Finset.univ.filter fun w => (m, w) ∉ R).Nonempty :=
    ⟨w0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  obtain ⟨w, hw, hmin⟩ := Finset.exists_min_image _ (fun w => p.manRank m w) hs
  exact ⟨w, (Finset.mem_filter.mp hw).2,
    fun w' hw' => hmin w' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw'⟩)⟩

theorem gs_proposes_insert {n : ℕ} {p : Profile n} {R : Finset (Fin n × Fin n)}
    {e : Fin n × Fin n} {m w : Fin n} (h : GSProposes p R m w) (hne : (m, w) ≠ e) :
    GSProposes p (insert e R) m w := by
  refine ⟨fun hm => ?_, fun w' hw' => h.2 w' (fun hr => hw' (Finset.mem_insert_of_mem hr))⟩
  rcases Finset.mem_insert.mp hm with he | hr
  · exact hne he
  · exact h.1 hr

theorem gs_inv_insert {n : ℕ} {p : Profile n} {R : Finset (Fin n × Fin n)} (hI : GSInv p R)
    {m w m' : Fin n} (hm : GSProposes p R m w) (hm' : GSProposes p R m' w)
    (hlt : p.womanRank w m' < p.womanRank w m) : GSInv p (insert (m, w) R) := by
  have hne' : (m', w) ≠ (m, w) := by
    intro he
    have : m' = m := congrArg Prod.fst he
    subst this
    exact lt_irrefl _ hlt
  intro m1 w1 h1
  rcases Finset.mem_insert.mp h1 with he | hr
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨m', hlt, gs_proposes_insert hm' hne'⟩
  · obtain ⟨m2, hlt2, hp2⟩ := hI m1 w1 hr
    by_cases heq : (m2, w1) = (m, w)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact ⟨m', hlt.trans hlt2, gs_proposes_insert hm' hne'⟩
    · exact ⟨m2, hlt2, gs_proposes_insert hp2 heq⟩

/-- At a rejection set where no woman has two proposers, the proposals form a stable matching. -/
theorem gs_stable_of_fixed {n : ℕ} (p : Profile n) (R : Finset (Fin n × Fin n)) (hI : GSInv p R)
    (hfix : ∀ m w m', GSProposes p R m w → GSProposes p R m' w →
      ¬ p.womanRank w m' < p.womanRank w m) :
    ∃ μ : Matching n, IsStable p μ := by
  have hone : ∀ m m' w, GSProposes p R m w → GSProposes p R m' w → m = m' := by
    intro m m' w h h'
    by_contra hne
    rcases lt_or_gt_of_ne (fun e => hne ((p.womanRank w).injective e)) with hl | hl
    · exact hfix m' w m h' h hl
    · exact hfix m w m' h h' hl
  have hall : ∀ m, ∃ w, GSProposes p R m w := by
    intro m
    by_contra hno
    push Not at hno
    have hrej : ∀ w, (m, w) ∈ R := by
      intro w
      by_contra hw
      obtain ⟨w', hw'⟩ := gs_exists_proposes p R hw
      exact hno w' hw'
    have hprop : ∀ w, ∃ m', GSProposes p R m' w := by
      intro w
      obtain ⟨m', _, hm'⟩ := hI m w (hrej w)
      exact ⟨m', hm'⟩
    choose f hf using hprop
    have finj : Function.Injective f := by
      intro w1 w2 he
      have h2 := hf w2
      rw [← he] at h2
      exact gs_proposes_unique (hf w1) h2
    obtain ⟨w, hw⟩ := Finite.surjective_of_injective finj m
    have := hf w
    rw [hw] at this
    exact (this.1 (hrej w)).elim
  choose g hg using hall
  have ginj : Function.Injective g := by
    intro m1 m2 he
    have h2 := hg m2
    rw [← he] at h2
    exact hone m1 m2 (g m1) (hg m1) h2
  let μ : Matching n := Equiv.ofBijective g ginj.bijective_of_finite
  refine ⟨μ, ?_⟩
  rintro m w ⟨_, hman, hwoman⟩
  have hμm : μ m = g m := rfl
  have hR : (m, w) ∈ R := by
    by_contra hw
    have := (hg m).2 w hw
    rw [hμm] at hman
    exact absurd hman (not_lt.mpr this)
  obtain ⟨m', hlt, hm'⟩ := hI m w hR
  have hgm' : g m' = w := gs_proposes_unique (hg m') hm'
  have hsymm : μ.symm w = m' := by
    rw [Equiv.symm_apply_eq]
    exact hgm'.symm
  rw [hsymm] at hwoman
  exact lt_asymm hlt hwoman

theorem gs_exists_stable {n : ℕ} (p : Profile n) : ∃ μ : Matching n, IsStable p μ := by
  classical
  have key : ∀ k (R : Finset (Fin n × Fin n)), (Finset.univ \ R).card = k → GSInv p R →
      ∃ μ : Matching n, IsStable p μ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro R hk hI
      by_cases hnew : ∃ m w m', GSProposes p R m w ∧ GSProposes p R m' w ∧
          p.womanRank w m' < p.womanRank w m
      · obtain ⟨m, w, m', hm, hm', hlt⟩ := hnew
        have hmem : (m, w) ∈ Finset.univ \ R := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hm.1⟩
        refine ih _ ?_ (insert (m, w) R) rfl (gs_inv_insert hI hm hm' hlt)
        rw [Finset.sdiff_insert, ← hk]
        exact Finset.card_erase_lt_of_mem hmem
      · push Not at hnew
        exact gs_stable_of_fixed p R hI fun m w m' h h' => not_lt.mpr (hnew m w m' h h')
  exact key _ ∅ rfl (fun m w h => absurd h (Finset.notMem_empty _))

theorem gs_pos {n : ℕ} (p : Profile n) : 0 < numStableMatchings p := by
  classical
  obtain ⟨μ, hμ⟩ := gs_exists_stable p
  unfold numStableMatchings
  exact Fintype.card_pos_iff.mpr ⟨⟨μ, hμ⟩⟩

end OMA.Helpers

theorem OMA.solution : OMA.R_LennonPittel_lennon_pittel_conjecture_R2.H1 :=
  fun _ p => OMA.Helpers.gs_pos p
