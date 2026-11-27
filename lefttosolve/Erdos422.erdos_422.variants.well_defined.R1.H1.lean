import OMAReductions.R_Erdos422_erdos_422_variants_well_defined_R1

/-!
# Step H1 of the reduction Erdos422.erdos_422.variants.well_defined.R1

We build the guarded Hofstadter recurrence as a list: `hqList k` holds the values at the
indices `0, 1, ..., k + 2`, and each step appends the next value computed from the list so
far. The function `hq n` reads index `n` of `hqList n`. Since every list is a prefix of the
later ones, `hq` satisfies the guarded recurrence for every `n > 2`. Positivity of the first
512 terms is a finite check on `hqList 510`, done by the kernel.
-/

namespace OMA.Helpers

/-- The next value of the guarded recurrence, read off from the list of earlier values. -/
def hqNext (l : List ℕ) : ℕ :=
  if 0 < l.getD (l.length - 1) 0 ∧ l.getD (l.length - 1) 0 < l.length ∧
      0 < l.getD (l.length - 2) 0 ∧ l.getD (l.length - 2) 0 < l.length then
    l.getD (l.length - l.getD (l.length - 1) 0) 0 +
      l.getD (l.length - l.getD (l.length - 2) 0) 0
  else 0

/-- The values at the indices `0, ..., k + 2`. -/
def hqList : ℕ → List ℕ
  | 0 => [0, 1, 1]
  | k + 1 => hqList k ++ [hqNext (hqList k)]

/-- The guarded Hofstadter sequence. -/
def hq (n : ℕ) : ℕ := (hqList n).getD n 0

theorem hqList_length (k : ℕ) : (hqList k).length = k + 3 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [hqList, ih]

theorem hqList_prefix (k : ℕ) : ∀ k', k ≤ k' → ∀ i, i < k + 3 →
    (hqList k').getD i 0 = (hqList k).getD i 0 := by
  intro k' hk'
  induction k', hk' using Nat.le_induction with
  | base => intro i _; rfl
  | succ k' hkk' ih =>
    intro i hi
    rw [hqList, List.getD_append _ _ _ _ (by rw [hqList_length]; omega)]
    exact ih i hi

theorem hqList_getD (k i : ℕ) (hi : i < k + 3) : (hqList k).getD i 0 = hq i := by
  unfold hq
  rcases le_total k i with h | h
  · exact (hqList_prefix k i h i hi).symm
  · exact hqList_prefix i k h i (by omega)

theorem hq_succ3 (m : ℕ) : hq (m + 3) = hqNext (hqList m) := by
  rw [← hqList_getD (m + 1) (m + 3) (by omega), hqList,
    List.getD_append_right _ _ _ _ (by rw [hqList_length])]
  rw [hqList_length]
  simp

theorem hq_rec (n : ℕ) (hn : 2 < n) : hq n =
    if 0 < hq (n - 1) ∧ hq (n - 1) < n ∧ 0 < hq (n - 2) ∧ hq (n - 2) < n then
      hq (n - hq (n - 1)) + hq (n - hq (n - 2)) else 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [hq_succ3]
  unfold hqNext
  rw [hqList_length, hqList_getD m (m + 3 - 1) (by omega),
    hqList_getD m (m + 3 - 2) (by omega)]
  by_cases h : 0 < hq (m + 3 - 1) ∧ hq (m + 3 - 1) < m + 3 ∧
      0 < hq (m + 3 - 2) ∧ hq (m + 3 - 2) < m + 3
  · rw [if_pos h, if_pos h, hqList_getD m _ (by omega), hqList_getD m _ (by omega)]
  · rw [if_neg h, if_neg h]

theorem hqList_pos_check : ∀ i, i < 513 → 0 < i → 0 < (hqList 510).getD i 0 := by
  decide +kernel

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos422_erdos_422_variants_well_defined_R1.H1 := by
  refine ⟨hq, rfl, rfl, hq_rec, ?_⟩
  intro n hn hle
  rw [← hqList_getD 510 n (by omega)]
  exact hqList_pos_check n (by omega) hn
