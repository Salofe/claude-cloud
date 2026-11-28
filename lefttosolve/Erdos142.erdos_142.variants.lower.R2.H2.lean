import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2

/-!
# Step H2 of the reduction Erdos142.erdos_142.variants.lower.R2

Block j occupies (4 4^j, 5 4^j]. Consecutive blocks are separated by a gap larger than the
length of a block, so an arithmetic progression of length at least three whose first two terms
lie in different blocks has its third term in a gap. Hence the first two terms share a block,
the common difference is less than 4^j, and by induction every term stays in that block. The
progression then translates to one inside B j, which is excluded.
-/

namespace OMA.Helpers

theorem pow4_cases (j j' : ℕ) : j = j' ∨ 4 * 4 ^ j ≤ 4 ^ j' ∨ 4 * 4 ^ j' ≤ 4 ^ j := by
  rcases lt_trichotomy j j' with h | h | h
  · right; left
    calc 4 * 4 ^ j = 4 ^ (j + 1) := by ring
      _ ≤ 4 ^ j' := Nat.pow_le_pow_right (by norm_num) h
  · left; exact h
  · right; right
    calc 4 * 4 ^ j' = 4 ^ (j' + 1) := by ring
      _ ≤ 4 ^ j := Nat.pow_le_pow_right (by norm_num) h

theorem block_bounds {B : ℕ → Finset ℕ} (hB : ∀ j, B j ⊆ Finset.Icc 1 (4 ^ j))
    {j b : ℕ} (hb : b ∈ B j) : 1 ≤ b ∧ b ≤ 4 ^ j := by
  have := Finset.mem_Icc.mp (hB j hb)
  exact this

theorem block_unique {x j j' : ℕ} (h1 : 4 * 4 ^ j < x) (h2 : x ≤ 5 * 4 ^ j)
    (h3 : 4 * 4 ^ j' < x) (h4 : x ≤ 5 * 4 ^ j') : j = j' := by
  rcases pow4_cases j j' with h | h | h
  · exact h
  · omega
  · omega

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2.H2 := by
  unfold OMA.R_Erdos142_erdos_142_variants_lower_R2.H2
  intro k hk B hB hfree ⟨a, d, hd, h⟩
  obtain ⟨j0, b0, hb0, e0⟩ := h 0 (by omega)
  obtain ⟨j1, b1, hb1, e1⟩ := h 1 (by omega)
  obtain ⟨j2, b2, hb2, e2⟩ := h 2 (by omega)
  have B0 := block_bounds hB hb0
  have B1 := block_bounds hB hb1
  have B2 := block_bounds hB hb2
  simp only [zero_mul, add_zero, one_mul] at e0 e1
  -- the first two terms share a block
  have j10 : j1 = j0 := by
    rcases pow4_cases j0 j1 with h01 | h01 | h01
    · exact h01.symm
    · exfalso
      rcases pow4_cases j1 j2 with h12 | h12 | h12
      · subst h12; omega
      · omega
      · omega
    · exfalso; omega
  subst j10
  have hdP : d < 4 ^ j1 := by omega
  -- every term lies in the block of the first one
  have all : ∀ i, i < k → 4 * 4 ^ j1 < a + i * d ∧ a + i * d ≤ 5 * 4 ^ j1 := by
    intro i
    induction i with
    | zero => intro _; simp only [zero_mul, add_zero]; omega
    | succ i ih =>
      intro hi
      obtain ⟨l1, l2⟩ := ih (by omega)
      obtain ⟨j', b', hb', e'⟩ := h (i + 1) hi
      have B' := block_bounds hB hb'
      rw [add_mul, one_mul] at e' ⊢
      rcases pow4_cases j1 j' with h' | h' | h'
      · subst h'; omega
      · omega
      · omega
  apply hfree j1
  refine ⟨a - 4 * 4 ^ j1, d, hd, fun i hi => ?_⟩
  obtain ⟨j', b', hb', e'⟩ := h i hi
  have B' := block_bounds hB hb'
  obtain ⟨l1, l2⟩ := all i hi
  have hj : j' = j1 := block_unique (x := a + i * d) (by omega) (by omega) l1 l2
  subst hj
  have : a - 4 * 4 ^ j' + i * d = b' := by omega
  rw [this]; exact hb'
