import OMAStatements.S_oeis_a384350
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a384350

/-- A finite set of positive numbers that contains `s` and sums to `s` is `{s}`. -/
theorem a384350_eq_singleton {s : ℕ} {A : Finset ℕ} (hs : s ∈ A) (hpos : ∀ x ∈ A, 0 < x)
    (hsum : A.sum id = s) : A = {s} := by
  have h := Finset.add_sum_erase A id hs
  rw [hsum] at h
  have h0 : (A.erase s).sum id = 0 := by
    change s + (A.erase s).sum id = s at h
    omega
  rw [Finset.sum_eq_zero_iff] at h0
  ext x
  constructor
  · intro hx
    rw [Finset.mem_singleton]
    by_contra hne
    have h1 := h0 x (Finset.mem_erase.2 ⟨hne, hx⟩)
    have h2 := hpos x hx
    simp only [id] at h1
    omega
  · intro hx
    rw [Finset.mem_singleton] at hx
    rw [hx]
    exact hs

/-- The family of singletons is always a family of strict partitions. -/
theorem a384350_trivial_family (S : Finset ℕ) (hS : ∀ s ∈ S, 0 < s) :
    IsFamily S (fun x => {x}) := by
  refine ⟨fun s hs => ⟨?_, by simp⟩, fun s _ t _ hst => ?_⟩
  · intro x hx
    rw [Finset.mem_singleton] at hx
    rw [hx]
    exact hS s hs
  · rw [Finset.disjoint_singleton_right, Finset.mem_singleton]
    exact fun h => hst h.symm

/-- Without an element that is a sum of non-elements, every family is the singleton family. -/
theorem a384350_family_eq (S : Finset ℕ) (hno : ¬ HasNonElementSum S)
    (h : ℕ → Finset ℕ) (hf : IsFamily S h) : ∀ s, s ∈ S → h s = {s} := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro hs
  by_contra hne
  obtain ⟨hpos, hsum⟩ := hf.1 s hs
  by_cases hall : ∀ t ∈ h s, t ∉ S
  · exact hno ⟨s, hs, h s, fun t ht => ⟨hpos t ht, hall t ht⟩, hsum⟩
  · push Not at hall
    obtain ⟨t, hts, htS⟩ := hall
    by_cases hts' : t = s
    · rw [hts'] at hts
      exact hne (a384350_eq_singleton hts hpos hsum)
    · have hle : t ≤ s := by
        have h3 := Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le i) hts
        rw [hsum] at h3
        exact h3
      have hlt : t < s := lt_of_le_of_ne hle hts'
      have ht1 := ih t hlt htS
      have h4 := hf.2 s hs t htS (Ne.symm hts')
      rw [ht1, Finset.disjoint_singleton_right] at h4
      exact h4 hts

theorem a384350_iff (S : Finset ℕ) (hS : ∀ s ∈ S, 0 < s) :
    HasNonElementSum S ↔ MoreThanOneWay S := by
  constructor
  · rintro ⟨s, hs, T, hT, hsum⟩
    refine ⟨fun x => {x}, fun x => if x = s then T else {x}, a384350_trivial_family S hS,
      ⟨fun x hx => ?_, fun x hx y hy hxy => ?_⟩, s, hs, ?_⟩
    · dsimp only
      by_cases hxs : x = s
      · rw [if_pos hxs, hxs]
        exact ⟨fun t ht => (hT t ht).1, hsum⟩
      · rw [if_neg hxs]
        refine ⟨fun z hz => ?_, by simp⟩
        rw [Finset.mem_singleton] at hz
        rw [hz]
        exact hS x hx
    · dsimp only
      by_cases hxs : x = s
      · have hys : y ≠ s := fun e => hxy (hxs.trans e.symm)
        rw [if_pos hxs, if_neg hys, Finset.disjoint_singleton_right]
        intro hyT
        exact (hT y hyT).2 hy
      · by_cases hys : y = s
        · rw [if_neg hxs, if_pos hys, Finset.disjoint_singleton_left]
          intro hxT
          exact (hT x hxT).2 hx
        · rw [if_neg hxs, if_neg hys, Finset.disjoint_singleton_right, Finset.mem_singleton]
          exact fun e => hxy e.symm
    · dsimp only
      rw [if_pos rfl]
      intro heq
      have hsT : s ∈ T := by
        rw [← heq]
        exact Finset.mem_singleton_self s
      exact (hT s hsT).2 hs
  · rintro ⟨f, g, hf, hg, s, hs, hfg⟩
    by_contra hno
    exact hfg ((a384350_family_eq S hno f hf s hs).trans (a384350_family_eq S hno g hg s hs).symm)

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a384350.main := by
  intro n
  unfold OMA.S_oeis_a384350.a
  classical
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro S hS
  rw [Finset.mem_powerset] at hS
  exact OMA.Helpers.a384350_iff S (fun s hs => (Finset.mem_Icc.1 (hS hs)).1)
