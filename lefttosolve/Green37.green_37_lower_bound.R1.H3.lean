import OMAReductions.R_Green37_green_37_lower_bound_R1

/-!
# Step H3 of the reduction Green37.green_37_lower_bound.R1

Two base cases for the minimum size `m N k` of an AP-cover.

* `k = 1`: for `N ≥ 1` a cover must contain a progression of length one with difference one,
  so it is nonempty; and covers exist (the singleton `{0}`), so `m N 1 ≥ 1`.
* `k = 2`: a cover `A` contains, for each `d ∈ [1, N]`, two elements `a_d` and `a_d + d`.
  The ordered pairs `(a_d, a_d + d)` and `(a_d + d, a_d)` are `2N` distinct off-diagonal pairs of
  `A`, so `2N ≤ |A| (|A| - 1)`. Covers exist (the interval `[0, N]`), so the infimum is attained.

Only upstream definitions are used.
-/

namespace OMA.Helpers

open Green37

/-- The two-element progression `{a, a + d}` with `d ≠ 0`. -/
theorem green37_ap_two (a d : ℕ) (hd : d ≠ 0) :
    ({a, a + d} : Set ℕ).IsAPOfLengthWith ((2 : ℕ) : ℕ∞) a d := by
  have hne : a ≠ a + d := by omega
  refine ⟨?_, ?_⟩
  · change ({a, a + d} : Set ℕ).encard = _
    rw [Set.encard_pair hne]
    rfl
  · ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, smul_eq_mul]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, by simp⟩
    · rintro ⟨n, hn, rfl⟩
      have hn2 : n < 2 := by exact_mod_cast hn
      interval_cases n <;> simp

/-- The singleton progression `{a}`. -/
theorem green37_ap_one (a d : ℕ) :
    ({a} : Set ℕ).IsAPOfLengthWith ((1 : ℕ) : ℕ∞) a d := by
  refine ⟨?_, ?_⟩
  · change ({a} : Set ℕ).encard = _
    rw [Set.encard_singleton]
    rfl
  · ext x
    simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq, smul_eq_mul]
    constructor
    · rintro rfl
      exact ⟨0, by norm_num, by simp⟩
    · rintro ⟨n, hn, rfl⟩
      have hn1 : n < 1 := by exact_mod_cast hn
      interval_cases n
      simp

/-- The first term of a progression lies in it. -/
theorem green37_first_mem {s : Set ℕ} {l : ℕ} {a d : ℕ} (hl : 0 < l)
    (h : s.IsAPOfLengthWith (l : ℕ∞) a d) : a ∈ s := by
  rw [h.2]
  exact ⟨0, by exact_mod_cast hl, by simp⟩

/-- The second term of a progression of length at least two lies in it. -/
theorem green37_second_mem {s : Set ℕ} {l : ℕ} {a d : ℕ} (hl : 1 < l)
    (h : s.IsAPOfLengthWith (l : ℕ∞) a d) : a + d ∈ s := by
  rw [h.2]
  exact ⟨1, by exact_mod_cast hl, by simp⟩

theorem green37_nonempty_one (N : ℕ) :
    { m | ∃ A : Finset ℕ, A.card = m ∧ IsAPCover (A : Set ℕ) N 1 }.Nonempty := by
  refine ⟨1, {0}, by simp, ?_⟩
  intro d _
  exact ⟨0, {0}, by simp, green37_ap_one 0 d⟩

theorem green37_nonempty_two (N : ℕ) :
    { m | ∃ A : Finset ℕ, A.card = m ∧ IsAPCover (A : Set ℕ) N 2 }.Nonempty := by
  refine ⟨_, Finset.range (N + 1), rfl, ?_⟩
  intro d hd
  refine ⟨0, {0, 0 + d}, ?_, green37_ap_two 0 d (by omega)⟩
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  simp only [Finset.coe_range, Set.mem_Iio]
  omega

theorem green37_two_bound (N : ℕ) (A : Finset ℕ) (hA : IsAPCover (A : Set ℕ) N 2) :
    2 * N ≤ A.card * (A.card - 1) := by
  classical
  have hex : ∀ d : ℕ, ∃ a : ℕ, ¬(1 ≤ d ∧ d ≤ N) ∨ (a ∈ A ∧ a + d ∈ A) := by
    intro d
    by_cases h : 1 ≤ d ∧ d ≤ N
    · obtain ⟨a, s, hs, hap⟩ := hA d h
      exact ⟨a, Or.inr ⟨hs (green37_first_mem (by norm_num) hap),
        hs (green37_second_mem (by norm_num) hap)⟩⟩
    · exact ⟨0, Or.inl h⟩
  choose f hf using hex
  let g : ℕ × Bool → ℕ × ℕ := fun q =>
    if q.2 then (f q.1, f q.1 + q.1) else (f q.1 + q.1, f q.1)
  have hmaps : Set.MapsTo g ((Finset.Icc 1 N ×ˢ (Finset.univ : Finset Bool) : Finset _) : Set _)
      (A.offDiag : Set (ℕ × ℕ)) := by
    rintro ⟨d, b⟩ hq
    simp only [Finset.coe_product, Finset.coe_Icc, Finset.coe_univ, Set.mem_prod,
      Set.mem_Icc, Set.mem_univ, and_true] at hq
    obtain ⟨h1, h2⟩ := (hf d).resolve_left (fun h => h hq)
    cases b
    · simp only [g, Finset.coe_offDiag, Set.mem_offDiag, Finset.mem_coe]
      exact ⟨h2, h1, by simp; omega⟩
    · simp only [g, Finset.coe_offDiag, Set.mem_offDiag, Finset.mem_coe]
      exact ⟨h1, h2, by simp; omega⟩
  have hinj : Set.InjOn g ((Finset.Icc 1 N ×ˢ (Finset.univ : Finset Bool) : Finset _) : Set _) := by
    rintro ⟨d, b⟩ hq ⟨d', b'⟩ hq' he
    simp only [Finset.coe_product, Finset.coe_Icc, Finset.coe_univ, Set.mem_prod,
      Set.mem_Icc, Set.mem_univ, and_true] at hq hq'
    cases b <;> cases b' <;> simp only [g, Bool.false_eq_true, ite_false, ite_true,
      Prod.mk.injEq] at he
    · have : d = d' := by omega
      subst this; rfl
    · omega
    · omega
    · have : d = d' := by omega
      subst this; rfl
  have hc := Finset.card_le_card_of_injOn g hmaps hinj
  rw [Finset.card_product, Nat.card_Icc, Finset.card_univ, Fintype.card_bool,
    Finset.offDiag_card] at hc
  rw [Nat.mul_sub_one]
  have : N + 1 - 1 = N := by omega
  rw [this] at hc
  linarith

end OMA.Helpers

open Green37 in
theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H3 := by
  refine ⟨fun N hN => ?_, fun N => ?_⟩
  · apply le_csInf (OMA.Helpers.green37_nonempty_one N)
    rintro m ⟨A, rfl, hA⟩
    obtain ⟨a, s, hs, hap⟩ := hA 1 ⟨le_refl 1, hN⟩
    have ha : a ∈ (A : Set ℕ) := hs (OMA.Helpers.green37_first_mem (by norm_num) hap)
    exact Finset.card_pos.mpr ⟨a, ha⟩
  · obtain ⟨A, hAc, hA⟩ := Nat.sInf_mem (OMA.Helpers.green37_nonempty_two N)
    show 2 * N ≤ Green37.m N 2 * (Green37.m N 2 - 1)
    unfold Green37.m
    rw [← hAc]
    exact OMA.Helpers.green37_two_bound N A hA
