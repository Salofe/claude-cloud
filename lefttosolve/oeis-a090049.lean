import OMAStatements.S_oeis_a090049
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a090049

theorem not_block_full (m : ℕ) (hm : m ≠ 0) :
    ¬ zeroBlock (Nat.digits 2 m) (Nat.digits 2 m).length := by
  rintro ⟨before, after, h⟩
  have hl := congrArg List.length h
  simp only [List.length_append, List.length_replicate] at hl
  have hb : before = [] := List.eq_nil_of_length_eq_zero (by omega)
  have ha : after = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hb ha
  simp only [List.nil_append, List.append_nil] at h
  have hall : ∀ x ∈ Nat.digits 2 m, x = 0 := by
    intro x hx
    rw [h] at hx
    exact List.eq_of_mem_replicate hx
  exact Nat.getLast_digit_ne_zero 2 hm (hall _ (List.getLast_mem _))

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a090049.main := by
  classical
  refine ⟨?_, ?_⟩
  · intro n e hn hdvd
    obtain ⟨c, rfl⟩ := hdvd
    have hc : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; simp at hn
      · exact h
    unfold OMA.S_oeis_a090049.a
    rw [if_neg hn]
    have hpow : (2 ^ e * c) ^ 3 = 2 ^ (3 * e) * c ^ 3 := by ring
    have hd : Nat.digits 2 ((2 ^ e * c) ^ 3) = List.replicate (3 * e) 0 ++ Nat.digits 2 (c ^ 3) := by
      rw [hpow]
      exact Nat.digits_base_pow_mul (by norm_num) (by positivity)
    apply Nat.le_findGreatest
    · rw [hd, List.length_append, List.length_replicate]
      omega
    · exact ⟨[], Nat.digits 2 (c ^ 3), by rw [hd, List.nil_append]⟩
  · intro n k hn
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : n = 0 := by simpa using hn
      subst this
      simp [OMA.S_oeis_a090049.a]
    · simp only [hk, iff_true]
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp [OMA.S_oeis_a090049.a]
        omega
      · have hne : n ≠ 0 := by omega
        unfold OMA.S_oeis_a090049.a
        rw [if_neg hne]
        have hn3 : n ^ 3 ≠ 0 := by positivity
        have hlen : (Nat.digits 2 (n ^ 3)).length ≤ 3 * k := by
          rw [Nat.digits_length_le_iff (by norm_num)]
          calc n ^ 3 < (2 ^ k) ^ 3 := Nat.pow_lt_pow_left hn (by norm_num)
            _ = 2 ^ (3 * k) := by ring
        refine lt_of_lt_of_le (lt_of_le_of_ne (Nat.findGreatest_le _) ?_) hlen
        intro heq
        have hL : (Nat.digits 2 (n ^ 3)).length ≠ 0 := by
          simp [Nat.digits_ne_nil_iff_ne_zero.mpr hn3]
        exact not_block_full _ hn3 (Nat.findGreatest_of_ne_zero heq hL)
