import OMAStatements.S_oeis_a261702
import Mathlib

/-!
A nonempty finite set of positive integers `s` always has an eligible element (`1` if
`1 ∉ s`, otherwise twice the maximum), so every term is eligible: positive and new, which
gives injectivity. If `k` is eligible from some stage on and never chosen, all later terms
lie in `[1, k]` and are distinct, which is impossible; induction on `ReachesOne k` then
shows that every positive `k` appears.
-/

namespace OMA.Helpers

open OMA.S_oeis_a261702

theorem exists_eligible (s : Finset ℕ) (hs : ∀ x ∈ s, 0 < x) : ∃ k, eligible s k := by
  by_cases h1 : 1 ∈ s
  · have hne : s.Nonempty := ⟨1, h1⟩
    have hM : s.max' hne ∈ s := s.max'_mem hne
    have hMpos : 0 < s.max' hne := hs _ hM
    refine ⟨2 * s.max' hne, by omega, ?_, Or.inr ?_⟩
    · intro h
      have : 2 * s.max' hne ≤ s.max' hne := s.le_max' (2 * s.max' hne) h
      omega
    · have : step (2 * s.max' hne) = s.max' hne := by
        unfold step
        rw [if_pos (by omega)]
        omega
      rw [this]
      exact hM
  · exact ⟨1, one_pos, h1, Or.inl rfl⟩

theorem pick_spec (s : Finset ℕ) (hs : ∀ x ∈ s, 0 < x) : eligible s (pick s) := by
  classical
  have h := exists_eligible s hs
  unfold pick
  rw [dif_pos h]
  exact Nat.find_spec h

theorem pick_le (s : Finset ℕ) {k : ℕ} (hk : eligible s k) : pick s ≤ k := by
  classical
  have h : ∃ k, eligible s k := ⟨k, hk⟩
  unfold pick
  rw [dif_pos h]
  exact Nat.find_min' h hk

theorem seen_pos : ∀ n, ∀ x ∈ seen n, 0 < x
  | 0 => by simp [seen]
  | n + 1 => by
    intro x hx
    simp only [seen, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact (pick_spec _ (seen_pos n)).1
    · exact seen_pos n x hx

theorem term_elig (n : ℕ) : eligible (seen n) (term n) := pick_spec _ (seen_pos n)

theorem term_mem (n : ℕ) : term n ∈ seen (n + 1) := Finset.mem_insert_self _ _

theorem seen_mono {n m : ℕ} (h : n ≤ m) : seen n ⊆ seen m := by
  induction m, h using Nat.le_induction with
  | base => exact le_refl _
  | succ m _ ih => exact ih.trans (Finset.subset_insert _ _)

theorem mem_seen : ∀ {m x : ℕ}, x ∈ seen m → ∃ j < m, term j = x
  | 0, x, hx => by simp [seen] at hx
  | m + 1, x, hx => by
    simp only [seen, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact ⟨m, Nat.lt_succ_self m, rfl⟩
    · obtain ⟨j, hj, e⟩ := mem_seen hx
      exact ⟨j, by omega, e⟩

theorem term_ne {n m : ℕ} (h : n < m) : term n ≠ term m := by
  intro e
  have h1 : term n ∈ seen m := seen_mono h (term_mem n)
  rw [e] at h1
  exact (term_elig m).2.1 h1

theorem term_inj : Function.Injective term := by
  intro a b e
  rcases lt_trichotomy a b with h | h | h
  · exact absurd e (term_ne h)
  · exact h
  · exact absurd e.symm (term_ne h)

theorem appears (k N : ℕ) (hk : 0 < k)
    (H : ∀ m, N ≤ m → k ∉ seen m → eligible (seen m) k) : ∃ n, term n = k := by
  by_contra hne
  push Not at hne
  have hnot : ∀ m, k ∉ seen m := by
    intro m hm
    obtain ⟨j, -, hj⟩ := mem_seen hm
    exact hne j hj
  have hmaps : Set.MapsTo term (Finset.Ico N (N + k + 1) : Set ℕ) (Finset.Icc 1 k : Set ℕ) := by
    intro m hm
    simp only [Finset.coe_Ico, Set.mem_Ico] at hm
    simp only [Finset.coe_Icc, Set.mem_Icc]
    exact ⟨(term_elig m).1, pick_le _ (H m hm.1 (hnot m))⟩
  have := Finset.card_le_card_of_injOn term hmaps term_inj.injOn
  simp only [Nat.card_Ico, Nat.card_Icc] at this
  omega

theorem step_pos {k : ℕ} (hk : 0 < k) : 0 < step k := by
  unfold step
  split_ifs <;> omega

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a261702.main := by
  intro hC
  refine ⟨term_inj, fun n => (term_elig n).1, ?_⟩
  intro k hk
  have hR := hC k hk
  revert hk
  induction hR with
  | one => exact fun _ => appears 1 0 one_pos (fun m _ h => ⟨one_pos, h, Or.inl rfl⟩)
  | @back k _ ih =>
    intro hk
    obtain ⟨n, hn⟩ := ih (step_pos hk)
    exact appears k (n + 1) hk
      (fun m hm h => ⟨hk, h, Or.inr (seen_mono hm (hn ▸ term_mem n))⟩)
