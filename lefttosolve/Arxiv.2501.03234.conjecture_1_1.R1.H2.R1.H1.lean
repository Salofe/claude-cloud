import OMAReductions.R_Arxiv_2501_03234_conjecture_1_1_R1_H2_R1

/-!
# Step H1 of the reduction Arxiv.2501.03234.conjecture_1_1.R1.H2.R1

Square-block estimate for the odd harmonic sum S(n) = sum over k < n of 1/(2k+1):
for L at most n at most L^2 we have S(n) at most 2 S(L).

Cut [L, L^2) into the blocks [(j+1) L, (j+2) L) for j < L - 1. Each block has L terms,
each at most 1/(2 (j+1) L + 1), so the block costs at most L/(2 (j+1) L + 1), which is
at most 1/(2j+1). By induction S((j+1) L) is at most S(L) + S(j); with j = L - 1 and
monotonicity this gives S(n) at most S(L^2) at most S(L) + S(L-1) at most 2 S(L).
-/

open Finset

namespace OMA.Helpers

/-- Monotonicity of the odd harmonic partial sums. -/
theorem oddHarm_mono {a b : ℕ} (h : a ≤ b) :
    ∑ k ∈ range a, (1 : ℚ)/(2*k+1) ≤ ∑ k ∈ range b, (1 : ℚ)/(2*k+1) :=
  Finset.sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr h)
    (fun _ _ _ => by positivity)

/-- The block of `L` consecutive terms starting at `(j+1) L` costs at most `1/(2j+1)`. -/
theorem oddHarm_block (L j : ℕ) :
    ∑ i ∈ range L, (1 : ℚ)/(2*(((j+1)*L + i : ℕ) : ℚ)+1) ≤ 1/(2*(j : ℚ)+1) := by
  have hle : ∀ i ∈ range L, (1 : ℚ)/(2*(((j+1)*L + i : ℕ) : ℚ)+1) ≤
      1/(2*(((j+1)*L : ℕ) : ℚ)+1) := by
    intro i _
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    nlinarith [(Nat.cast_nonneg i : (0 : ℚ) ≤ i)]
  refine (Finset.sum_le_sum hle).trans ?_
  rw [Finset.sum_const, card_range, nsmul_eq_mul]
  push_cast
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [(Nat.cast_nonneg L : (0 : ℚ) ≤ L), (Nat.cast_nonneg j : (0 : ℚ) ≤ j)]

/-- Square-block estimate: `S((j+1) L) ≤ S(L) + S(j)`. -/
theorem oddHarm_blocks (L : ℕ) : ∀ j : ℕ,
    ∑ k ∈ range ((j+1)*L), (1 : ℚ)/(2*k+1) ≤
      ∑ k ∈ range L, (1 : ℚ)/(2*k+1) + ∑ k ∈ range j, (1 : ℚ)/(2*k+1) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have e : (j+1+1)*L = (j+1)*L + L := by ring
    rw [e, Finset.sum_range_add, Finset.sum_range_succ]
    have hb := oddHarm_block L j
    push_cast at hb ⊢
    linarith

end OMA.Helpers

theorem OMA.solution : OMA.R_Arxiv_2501_03234_conjecture_1_1_R1_H2_R1.H1 := by
  intro n L _ hn
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    have : n = 0 := by simpa using hn
    subst this
    simp
  · obtain ⟨j, rfl⟩ : ∃ j, L = j + 1 := ⟨L - 1, by omega⟩
    have h1 := OMA.Helpers.oddHarm_mono hn
    have h2 := OMA.Helpers.oddHarm_blocks (j+1) j
    have h3 := OMA.Helpers.oddHarm_mono (Nat.le_succ j)
    have e : (j+1)^2 = (j+1)*(j+1) := by ring
    rw [e] at h1
    linarith
