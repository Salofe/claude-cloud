import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R1

/-!
# Step H1 of reduction LennonPittel.lennon_pittel_conjecture.R1

Every complete strict preference profile has at least one stable matching (Gale and Shapley, 1962).

Proof: deferred acceptance phrased as an extremal argument. A state assigns to each man the
number of rejections he has received; the invariant says that every woman who rejected a man
currently holds a proposal she prefers. Among invariant states take one with the maximal total
number of rejections. If two men propose to the same woman, rejecting the worse one gives a
larger invariant state (a pigeonhole argument shows he still has a woman left to propose to),
so in a maximal state the proposals form a perfect matching, and the invariant makes it stable.
-/

namespace OMA.Helpers

open StableMarriage

/-- The woman that man `m` currently proposes to, given the number `r m` of rejections. -/
def gsTarget {n : ℕ} (p : Profile n) (r : Fin n → Fin n) (m : Fin n) : Fin n :=
  (p.manRank m).symm (r m)

/-- Deferred-acceptance invariant: every woman who rejected `m` holds a better proposal. -/
def GSInv {n : ℕ} (p : Profile n) (r : Fin n → Fin n) : Prop :=
  ∀ m w, p.manRank m w < r m →
    ∃ m', gsTarget p r m' = w ∧ p.womanRank w m' < p.womanRank w m

lemma manRank_gsTarget {n : ℕ} (p : Profile n) (r : Fin n → Fin n) (m : Fin n) :
    p.manRank m (gsTarget p r m) = r m := by
  simp [gsTarget]

lemma gsInv_zero {n : ℕ} (p : Profile n) : GSInv p (fun m => ⟨0, m.pos⟩) := by
  intro m w hw
  exact absurd hw (by rw [Fin.lt_def]; exact Nat.not_lt_zero _)

/-- If the targets are injective, the induced matching is stable. -/
lemma stable_of_injective {n : ℕ} (p : Profile n) (r : Fin n → Fin n) (hI : GSInv p r)
    (hinj : Function.Injective (gsTarget p r)) :
    IsStable p (Equiv.ofBijective _ hinj.bijective_of_finite) := by
  rintro m w ⟨-, hm, hw⟩
  simp only [Equiv.ofBijective_apply] at hm
  rw [manRank_gsTarget] at hm
  obtain ⟨m', hm', hlt⟩ := hI m w hm
  have hsymm : (Equiv.ofBijective _ hinj.bijective_of_finite).symm w = m' := by
    rw [Equiv.symm_apply_eq]
    simp [hm']
  rw [hsymm] at hw
  exact lt_asymm hw hlt

/-- From a non-injective state satisfying the invariant, one man can be rejected once more. -/
lemma step {n : ℕ} (p : Profile n) (r : Fin n → Fin n) (hI : GSInv p r)
    (hinj : ¬ Function.Injective (gsTarget p r)) :
    ∃ r' : Fin n → Fin n, GSInv p r' ∧ ∑ m, (r m : ℕ) < ∑ m, (r' m : ℕ) := by
  classical
  have hex : ∃ a b, a ≠ b ∧ gsTarget p r a = gsTarget p r b ∧
      p.womanRank (gsTarget p r a) b < p.womanRank (gsTarget p r a) a := by
    simp only [Function.Injective, not_forall] at hinj
    obtain ⟨x, y, hxy, hne⟩ := hinj
    rcases lt_trichotomy (p.womanRank (gsTarget p r x) x) (p.womanRank (gsTarget p r x) y)
      with h | h | h
    · exact ⟨y, x, Ne.symm hne, hxy.symm, by rw [← hxy]; exact h⟩
    · exact absurd ((p.womanRank _).injective h) hne
    · exact ⟨x, y, hne, hxy, h⟩
  obtain ⟨a, b, hab, hsame, hpref⟩ := hex
  have hlt : (r a : ℕ) + 1 < n := by
    by_contra hcon
    push Not at hcon
    have hsurj : Function.Surjective (gsTarget p r) := by
      intro w'
      by_cases h : p.manRank a w' < r a
      · obtain ⟨m', hm', -⟩ := hI a w' h
        exact ⟨m', hm'⟩
      · refine ⟨a, ?_⟩
        push Not at h
        have heq : p.manRank a w' = r a := by
          apply le_antisymm _ h
          rw [Fin.le_iff_val_le_val]
          have := (p.manRank a w').isLt
          omega
        rw [gsTarget, ← heq, Equiv.symm_apply_apply]
    exact hab (Finite.injective_iff_surjective.mpr hsurj hsame)
  refine ⟨Function.update r a ⟨r a + 1, hlt⟩, ?_, ?_⟩
  · intro m w' hm
    by_cases hma : m = a
    · subst hma
      rw [Function.update_self, Fin.lt_def] at hm
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h | h
      · obtain ⟨m', hm', hlt'⟩ := hI m w' (Fin.lt_def.mpr h)
        have hm'a : m' ≠ m := by
          rintro rfl
          rw [← hm', manRank_gsTarget] at h
          exact lt_irrefl _ h
        refine ⟨m', ?_, hlt'⟩
        rw [gsTarget, Function.update_of_ne hm'a]
        exact hm'
      · have hw' : w' = gsTarget p r m := by
          rw [gsTarget, Equiv.eq_symm_apply]
          exact Fin.ext h
        subst hw'
        refine ⟨b, ?_, hpref⟩
        rw [gsTarget, Function.update_of_ne (Ne.symm hab)]
        exact hsame.symm
    · rw [Function.update_of_ne hma] at hm
      obtain ⟨m', hm', hlt'⟩ := hI m w' hm
      by_cases hm'a : m' = a
      · subst hm'a
        subst hm'
        refine ⟨b, ?_, lt_trans hpref hlt'⟩
        rw [gsTarget, Function.update_of_ne (Ne.symm hab)]
        exact hsame.symm
      · refine ⟨m', ?_, hlt'⟩
        rw [gsTarget, Function.update_of_ne hm'a]
        exact hm'
  · apply Finset.sum_lt_sum
    · intro i _
      by_cases h : i = a
      · subst h
        simp
      · rw [Function.update_of_ne h]
    · exact ⟨a, Finset.mem_univ _, by simp⟩

/-- Every complete strict preference profile admits a stable matching (Gale–Shapley). -/
theorem exists_stable {n : ℕ} (p : Profile n) : ∃ μ : Matching n, IsStable p μ := by
  classical
  have hne : Nonempty {r : Fin n → Fin n // GSInv p r} := ⟨⟨_, gsInv_zero p⟩⟩
  obtain ⟨⟨r, hr⟩, hmax⟩ :=
    Finite.exists_max (fun s : {r : Fin n → Fin n // GSInv p r} => ∑ m, (s.1 m : ℕ))
  by_cases hinj : Function.Injective (gsTarget p r)
  · exact ⟨_, stable_of_injective p r hr hinj⟩
  · obtain ⟨r', hr', hlt⟩ := step p r hr hinj
    exact absurd (hmax ⟨r', hr'⟩) (not_le.mpr hlt)

end OMA.Helpers

theorem OMA.solution : OMA.R_LennonPittel_lennon_pittel_conjecture_R1.H1 := by
  intro n p
  obtain ⟨μ, hμ⟩ := OMA.Helpers.exists_stable p
  classical
  unfold StableMarriage.numStableMatchings
  exact Fintype.card_pos_iff.mpr ⟨⟨μ, hμ⟩⟩
