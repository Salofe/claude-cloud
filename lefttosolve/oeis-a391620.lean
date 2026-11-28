import OMAStatements.S_oeis_a391620
import Mathlib

/-!
Proof of the A391620 characterization: a partition is the first sums of a composition with all
parts at least 2 exactly when all its parts are at least 4. Such a composition is built from the
last part backwards, starting with a final part 2.
-/

namespace OMA.Helpers
open OMA.S_oeis_a391620

/-- Builds a composition from a nonincreasing list, working from the last part with final part 2. -/
def a391620Build : List ℕ → List ℕ
  | [] => [2]
  | y :: rest => (y - (a391620Build rest).headD 0) :: a391620Build rest

theorem a391620Build_cons_form (l : List ℕ) : ∃ h t, a391620Build l = h :: t := by
  cases l with
  | nil => exact ⟨2, [], rfl⟩
  | cons y rest => exact ⟨_, _, rfl⟩

theorem a391620_firstSums_cons2 (a b : ℕ) (t : List ℕ) :
    firstSums (a :: b :: t) = (a + b) :: firstSums (b :: t) := rfl

theorem a391620Build_spec : ∀ l : List ℕ, l.Pairwise (· ≥ ·) → (∀ x ∈ l, 4 ≤ x) →
    (∀ x ∈ a391620Build l, 2 ≤ x) ∧
    (∀ y t, l = y :: t → (a391620Build l).headD 0 + 2 ≤ y) ∧
    firstSums (a391620Build l) = l := by
  intro l
  induction l with
  | nil =>
    intro _ _
    refine ⟨?_, ?_, rfl⟩
    · intro x hx
      simp [a391620Build] at hx
      omega
    · intro y t h
      simp at h
  | cons y rest ih =>
    intro hp h4
    rw [List.pairwise_cons] at hp
    obtain ⟨ih1, ih2, ih3⟩ := ih hp.2 (fun x hx => h4 x (List.mem_cons_of_mem _ hx))
    obtain ⟨h, t, hht⟩ := a391620Build_cons_form rest
    have hy : 4 ≤ y := h4 y List.mem_cons_self
    have hh2 : 2 ≤ h := ih1 h (by rw [hht]; exact List.mem_cons_self)
    have hhy : h + 2 ≤ y := by
      cases rest with
      | nil =>
        simp [a391620Build] at hht
        omega
      | cons z t' =>
        have := ih2 z t' rfl
        rw [hht] at this
        have hz : y ≥ z := hp.1 z List.mem_cons_self
        simp at this
        omega
    have hb : a391620Build (y :: rest) = (y - h) :: h :: t := by
      show (y - (a391620Build rest).headD 0) :: a391620Build rest = _
      rw [hht]
      rfl
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [hb] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · exact ih1 x (by rw [hht]; exact hx)
    · intro y' t' he
      rw [List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      rw [hb]
      simp
      omega
    · rw [hb, a391620_firstSums_cons2, ← hht, ih3]
      congr 1
      omega

theorem a391620_firstSums_ge : ∀ c : List ℕ, (∀ x ∈ c, 1 < x) → ∀ s ∈ firstSums c, 4 ≤ s := by
  intro c
  induction c with
  | nil => intro _ s hs; simp [firstSums] at hs
  | cons a t ih =>
    intro hc s hs
    cases t with
    | nil => simp [firstSums] at hs
    | cons b t' =>
      rw [a391620_firstSums_cons2] at hs
      rcases List.mem_cons.1 hs with rfl | hs
      · have ha := hc a List.mem_cons_self
        have hb := hc b (List.mem_cons_of_mem _ List.mem_cons_self)
        omega
      · exact ih (fun x hx => hc x (List.mem_cons_of_mem _ hx)) s hs

end OMA.Helpers

open OMA.S_oeis_a391620 OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a391620.main := by
  intro n _ y
  constructor
  · intro hnot
    by_contra hall
    simp only [not_exists, not_and, not_lt] at hall
    apply hnot
    have hp : (partsDesc y).Pairwise (· ≥ ·) := Multiset.pairwise_sort _ _
    have h4 : ∀ x ∈ partsDesc y, 4 ≤ x := fun x hx => hall x ((Multiset.mem_sort _).1 hx)
    obtain ⟨s1, -, s3⟩ := a391620Build_spec (partsDesc y) hp h4
    obtain ⟨h, t, hht⟩ := a391620Build_cons_form (partsDesc y)
    refine ⟨a391620Build (partsDesc y), by rw [hht]; exact List.cons_ne_nil _ _, ?_, s3⟩
    intro x hx
    have := s1 x hx
    omega
  · rintro ⟨x, hx, hx4⟩ ⟨c, -, hc1, hfs⟩
    have hmem : x ∈ firstSums c := by
      rw [hfs]
      exact (Multiset.mem_sort _).2 hx
    have := a391620_firstSums_ge c hc1 x hmem
    omega
