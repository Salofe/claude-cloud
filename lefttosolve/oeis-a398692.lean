import OMAStatements.S_oeis_a398692
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a398692

theorem walk_reaches {old : List ℕ} (hold : ∀ x ∈ old, ReachesOne x) :
    ∀ {n : ℕ} {block : List ℕ}, Walk old n block → ReachesOne n ∧ ∀ x ∈ block, ReachesOne x := by
  intro n block hw
  induction hw with
  | hit h => exact ⟨hold _ h, by simp⟩
  | fresh _ _ ih =>
    refine ⟨ReachesOne.back ih.1, ?_⟩
    intro x hx
    rw [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ih.2 x hx
    · exact ReachesOne.back ih.1

theorem stage_reaches {xs : List ℕ} (h : Stage xs) : ∀ x ∈ xs, ReachesOne x := by
  induction h with
  | initial => intro x hx; rw [List.mem_singleton] at hx; subst hx; exact ReachesOne.one
  | extend _ _ _ _ hw ih =>
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact ih x hx
    · exact (walk_reaches ih hw).2 x hx

theorem one_mem_stage {xs : List ℕ} (h : Stage xs) : 1 ∈ xs := by
  induction h with
  | initial => simp
  | extend _ _ _ _ _ ih => exact List.mem_append_left _ ih

theorem walk_exists {old : List ℕ} (h1 : 1 ∈ old) :
    ∀ {n : ℕ}, ReachesOne n → ∃ block, Walk old n block := by
  intro n hr
  induction hr with
  | one => exact ⟨[], Walk.hit h1⟩
  | @back m _ ih =>
    obtain ⟨tail, ht⟩ := ih
    by_cases hm : m ∈ old
    · exact ⟨[], Walk.hit hm⟩
    · exact ⟨tail ++ [m], Walk.fresh hm ht⟩

theorem walk_mem {old : List ℕ} {n : ℕ} {block : List ℕ} (hw : Walk old n block)
    (hn : n ∉ old) : n ∈ block := by
  cases hw with
  | hit h => exact absurd h hn
  | fresh _ _ => simp

theorem stage_upto (hC : Collatz) :
    ∀ N : ℕ, ∃ xs, Stage xs ∧ ∀ k, 0 < k → k ≤ N → k ∈ xs := by
  intro N
  induction N with
  | zero => exact ⟨[1], Stage.initial, fun k hk hkN => by omega⟩
  | succ N ih =>
    obtain ⟨xs, hxs, hall⟩ := ih
    by_cases hmem : N + 1 ∈ xs
    · refine ⟨xs, hxs, fun k hk hkN => ?_⟩
      rcases Nat.lt_or_ge k (N + 1) with h | h
      · exact hall k hk (by omega)
      · have : k = N + 1 := by omega
        subst this; exact hmem
    · obtain ⟨block, hw⟩ := walk_exists (one_mem_stage hxs) (hC (N + 1) (by omega))
      refine ⟨xs ++ block, Stage.extend hxs (by omega) hmem
        (fun k hk hkN => hall k hk (by omega)) hw, fun k hk hkN => ?_⟩
      rcases Nat.lt_or_ge k (N + 1) with h | h
      · exact List.mem_append_left _ (hall k hk (by omega))
      · have : k = N + 1 := by omega
        subst this
        exact List.mem_append_right _ (walk_mem hw hmem)

end OMA.Helpers

open OMA.S_oeis_a398692 OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a398692.main := by
  constructor
  · rintro ⟨_, hall⟩ n hn
    obtain ⟨xs, hxs, hmem⟩ := hall n hn
    exact stage_reaches hxs n hmem
  · intro hC
    have hall : ∀ n : ℕ, 0 < n → n ∈ printed := by
      intro n hn
      obtain ⟨xs, hxs, h⟩ := stage_upto hC n
      exact ⟨xs, hxs, h n hn le_rfl⟩
    refine ⟨?_, hall⟩
    apply Set.infinite_of_not_bddAbove
    rintro ⟨b, hb⟩
    have := hb (hall (b + 1) (by omega))
    omega
