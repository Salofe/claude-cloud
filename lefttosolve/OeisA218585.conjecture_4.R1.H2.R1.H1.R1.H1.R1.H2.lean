import OMAReductions.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1
import Mathlib

/-! The higher prime-power part of the von Mangoldt series is dominated by the
summable non-prime part of Lambda(n)/n, so its L-series converges uniformly and
is continuous on the closed half-plane Re s >= 1 (Weierstrass M-test). -/

namespace OMA.Helpers
open ArithmeticFunction

theorem oeis218585_summ_np :
    Summable fun n : ℕ => (if n.Prime then 0 else Λ n) / (n : ℝ) := by
  have hres := ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div
    (q := 1) (1 : ZMod 1)
  convert hres using 3 with n
  simp [ArithmeticFunction.vonMangoldt.residueClass, Subsingleton.elim (n : ZMod 1) (1 : ZMod 1)]

end OMA.Helpers

open ArithmeticFunction in
theorem OMA.solution : OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1.H2 := by
  intro b hb hΛ
  have hcont : ∀ n : ℕ, ContinuousOn (fun s : ℂ => LSeries.term b s n) {s : ℂ | 1 ≤ s.re} := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [LSeries.term_zero]
      exact continuousOn_const
    · have heq : (fun s : ℂ => LSeries.term b s n) = fun s => b n / (n : ℂ) ^ s := by
        funext s
        simp [LSeries.term, hn]
      rw [heq]
      refine ContinuousOn.div (g := fun s : ℂ => (n : ℂ) ^ s) continuousOn_const ?_ ?_
      · exact (continuousOn_id.const_cpow (Or.inl (by exact_mod_cast hn)))
      · intro s _
        exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn))
  have hbound : ∀ (n : ℕ) (s : ℂ), s ∈ {s : ℂ | 1 ≤ s.re} →
      ‖LSeries.term b s n‖ ≤ (if n.Prime then 0 else Λ n) / (n : ℝ) := by
    intro n s hs
    have hs' : (1 : ℝ) ≤ s.re := hs
    rw [LSeries.norm_term_eq]
    by_cases h0 : n = 0
    · subst h0; simp
    rw [if_neg h0]
    by_cases hp : n.Prime
    · rw [hb n hp, if_pos hp]; simp
    · rw [if_neg hp]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
      have hnrpow : (n : ℝ) ≤ (n : ℝ) ^ s.re := by
        calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (n : ℝ) ^ s.re := Real.rpow_le_rpow_of_exponent_le hn1 hs'
      calc ‖b n‖ / (n : ℝ) ^ s.re ≤ ‖b n‖ / (n : ℝ) :=
            div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hnrpow
        _ ≤ Λ n / (n : ℝ) := div_le_div_of_nonneg_right (hΛ n) (by positivity)
  exact continuousOn_tsum hcont OMA.Helpers.oeis218585_summ_np (fun n s hs => hbound n s hs)
