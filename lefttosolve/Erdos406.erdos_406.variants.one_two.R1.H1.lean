import OMAReductions.R_Erdos406_erdos_406_variants_one_two_R1

/-!
# Erdős 406 (digits 1 and 2), reduction R1, step H1

No power `2 ^ k` with `15 < k ≤ 1000` has all its base-3 digits in `{1, 2}`.

For every such `k`, one of the 26 lowest base-3 digits of `2 ^ k` is `0` (a finite computation
checked in the kernel by `decide +kernel`; the worst case is `k = 143`, whose first zero digit
is at position 25). A zero digit at a position `j` with `0 < 2 ^ k / 3 ^ j` means that `0` is a
member of `Nat.digits 3 (2 ^ k)`, and `0` is not a member of `[1, 2]`.
-/

namespace OMA.Helpers

/-- If `n` has a base-3 digit at position `j` (that is, `0 < n / 3 ^ j`) and that digit
is `0`, then `0` occurs in `Nat.digits 3 n`. -/
theorem zero_mem_digits_three :
    ∀ (j n : ℕ), 0 < n / 3 ^ j → (n / 3 ^ j) % 3 = 0 → 0 ∈ Nat.digits 3 n := by
  intro j
  induction j with
  | zero =>
    intro n hpos hmod
    rw [pow_zero, Nat.div_one] at hpos hmod
    rw [Nat.digits_def' (by norm_num) hpos, hmod]
    exact List.mem_cons_self
  | succ j ih =>
    intro n hpos hmod
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h
        simp at hpos
      · exact h
    rw [Nat.digits_def' (by norm_num) hn]
    apply List.mem_cons_of_mem
    apply ih (n / 3)
    · rwa [Nat.div_div_eq_div_mul, ← pow_succ']
    · rwa [Nat.div_div_eq_div_mul, ← pow_succ']

/-- The finite computation: for `15 < k ≤ 1000`, one of the 26 lowest base-3 digits of
`2 ^ k` is `0`. -/
theorem finite_zero_digit :
    ∀ k < 1001, 15 < k → ∃ j < 26, 0 < 2 ^ k / 3 ^ j ∧ (2 ^ k / 3 ^ j) % 3 = 0 := by
  decide +kernel

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos406_erdos_406_variants_one_two_R1.H1 := by
  intro k h1 h2 hsub
  obtain ⟨j, -, hpos, hmod⟩ := OMA.Helpers.finite_zero_digit k (by omega) h1
  have h0 := hsub (OMA.Helpers.zero_mem_digits_three j (2 ^ k) hpos hmod)
  simp at h0
