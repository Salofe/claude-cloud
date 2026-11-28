import OMAReductions.R_InscribedSquare_exists_inscribed_rectangle_R1
import Mathlib

/-! Unordered chords of the circle: the point `(s, t)` of the square is sent to the pair of
angles `π (s + t)` and `π (s - t)`, so `s` is the midpoint angle over `π` and `t` the half
opening over `π`. Coincidences of the two angle pairs reduce to small integer equations. -/

namespace OMA.Helpers

open Real

/-- Two angle pairs that agree modulo full turns. -/
lemma same_pair {s t s' t' : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs' : 0 ≤ s') (hs1' : s' ≤ 1) (ht' : 0 ≤ t') (ht1' : t' ≤ 1) {m n : ℤ}
    (h1 : s + t = s' + t' + 2 * m) (h2 : s - t = s' - t' + 2 * n) :
    (s = s' ∧ t = t') ∨ (s = 0 ∧ s' = 1 ∧ t' = 1 - t) ∨ (s = 1 ∧ s' = 0 ∧ t = 1 - t') := by
  have hm1 : m ≤ 1 := by exact_mod_cast (show (m : ℝ) ≤ 1 by linarith)
  have hm2 : -1 ≤ m := by exact_mod_cast (show (-1 : ℝ) ≤ m by linarith)
  have hn1 : n ≤ 1 := by exact_mod_cast (show (n : ℝ) ≤ 1 by linarith)
  have hn2 : -1 ≤ n := by exact_mod_cast (show (-1 : ℝ) ≤ n by linarith)
  interval_cases m <;> interval_cases n <;> push_cast at h1 h2 <;>
    first
    | (left; constructor <;> linarith)
    | (right; left; refine ⟨?_, ?_, ?_⟩ <;> linarith)
    | (right; right; refine ⟨?_, ?_, ?_⟩ <;> linarith)

/-- Two angle pairs that agree after a swap, modulo full turns. -/
lemma swapped_pair {s t s' t' : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs' : 0 ≤ s') (hs1' : s' ≤ 1) (ht' : 0 ≤ t') (ht1' : t' ≤ 1) {m n : ℤ}
    (h1 : s + t = s' - t' + 2 * m) (h2 : s - t = s' + t' + 2 * n) :
    (s = s' ∧ t = t') ∨ (s = 0 ∧ s' = 1 ∧ t' = 1 - t) ∨ (s = 1 ∧ s' = 0 ∧ t = 1 - t') := by
  have hm1 : m < 2 := by exact_mod_cast (show (m : ℝ) < 2 by linarith)
  have hm2 : -1 < m := by exact_mod_cast (show (-1 : ℝ) < m by linarith)
  have hn1 : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
  have hn2 : -2 < n := by exact_mod_cast (show (-2 : ℝ) < n by linarith)
  interval_cases m <;> interval_cases n <;> push_cast at h1 h2 <;>
    first
    | (left; constructor <;> linarith)
    | (right; left; refine ⟨?_, ?_, ?_⟩ <;> linarith)
    | (right; right; refine ⟨?_, ?_, ?_⟩ <;> linarith)

/-- Clearing the factor `π` from an angle identity. -/
lemma clear_pi {a b : ℝ} {m : ℤ} (h : π * a = π * b + m * (2 * π)) : a = b + 2 * m := by
  have hp := Real.pi_pos
  have h' : π * (a - (b + 2 * m)) = 0 := by linarith
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact absurd h0 hp.ne'
  · linarith

end OMA.Helpers

open Real OMA.Helpers in
theorem OMA.solution : OMA.R_InscribedSquare_exists_inscribed_rectangle_R1.H1 := by
  unfold OMA.R_InscribedSquare_exists_inscribed_rectangle_R1.H1
  intro seam
  have seam_of (p q : unitInterval × unitInterval)
      (h : ((p.1 : ℝ) = q.1 ∧ (p.2 : ℝ) = q.2) ∨
        ((p.1 : ℝ) = 0 ∧ (q.1 : ℝ) = 1 ∧ (q.2 : ℝ) = 1 - p.2) ∨
        ((p.1 : ℝ) = 1 ∧ (q.1 : ℝ) = 0 ∧ (p.2 : ℝ) = 1 - q.2)) : seam p q := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl (Prod.ext (Subtype.ext h1) (Subtype.ext h2))
    · refine Or.inr (Or.inl ⟨Subtype.ext h1, Subtype.ext h2, Subtype.ext ?_⟩)
      rw [unitInterval.coe_symm_eq]; exact h3
    · refine Or.inr (Or.inr ⟨Subtype.ext h1, Subtype.ext h2, Subtype.ext ?_⟩)
      rw [unitInterval.coe_symm_eq]; exact h3
  refine ⟨fun p => Circle.exp (π * ((p.1 : ℝ) + p.2)),
    fun p => Circle.exp (π * ((p.1 : ℝ) - p.2)), ?_, ?_, ?_, ?_, ?_⟩
  · exact Circle.exp.continuous.comp (by fun_prop)
  · exact Circle.exp.continuous.comp (by fun_prop)
  · intro t
    constructor
    · rw [Circle.exp_eq_exp]
      refine ⟨0, ?_⟩
      simp only [unitInterval.coe_symm_eq, Set.Icc.coe_zero, Set.Icc.coe_one]
      push_cast
      ring
    · rw [Circle.exp_eq_exp]
      refine ⟨-1, ?_⟩
      simp only [unitInterval.coe_symm_eq, Set.Icc.coe_zero, Set.Icc.coe_one]
      push_cast
      ring
  · intro p
    rw [Circle.exp_eq_exp]
    have ht0 := p.2.2.1
    have ht1 := p.2.2.2
    constructor
    · rintro ⟨m, hm⟩
      have hm' := clear_pi hm
      have h1 : m ≤ 1 := by exact_mod_cast (show (m : ℝ) ≤ 1 by linarith)
      have h2 : 0 ≤ m := by exact_mod_cast (show (0 : ℝ) ≤ m by linarith)
      interval_cases m
      · left; apply Subtype.ext; push_cast at hm' ⊢; linarith
      · right; apply Subtype.ext; push_cast at hm' ⊢; linarith
    · rintro (h | h)
      · refine ⟨0, ?_⟩
        rw [h]; push_cast; ring
      · refine ⟨1, ?_⟩
        rw [h]; push_cast; ring
  · intro p q h
    apply seam_of
    have a1 := p.1.2.1
    have a2 := p.1.2.2
    have b1 := p.2.2.1
    have b2 := p.2.2.2
    have c1 := q.1.2.1
    have c2 := q.1.2.2
    have d1 := q.2.2.1
    have d2 := q.2.2.2
    rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · rw [Circle.exp_eq_exp] at hu hv
      obtain ⟨m, hm⟩ := hu
      obtain ⟨n, hn⟩ := hv
      exact same_pair a1 a2 b1 b2 c1 c2 d1 d2 (clear_pi hm) (clear_pi hn)
    · rw [Circle.exp_eq_exp] at hu hv
      obtain ⟨m, hm⟩ := hu
      obtain ⟨n, hn⟩ := hv
      exact swapped_pair a1 a2 b1 b2 c1 c2 d1 d2 (clear_pi hm) (clear_pi hn)
