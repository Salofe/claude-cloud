import OMAStatements.S_oeis_a188572
import Mathlib

/-!
Every prime `p` divides `a n` for infinitely many `n`.

* `p = 2`: `(1 + √2 + √3)^2 = 2 * (3 + √2 + √3 + √6)`, so every coordinate of
  `(1 + √2 + √3)^(n+2)` is even; in particular `a (n + 2)` is even.
* `p` odd: the norm of `1 + √2 + √3` is `-8`, a unit mod `p`, so multiplication by
  `1 + √2 + √3` is injective on `(ZMod p)^4`. An injective self-map of a finite set is a
  permutation, so the orbit of `(1, 0, 0, 0)` is purely periodic, with some period `T > 0`;
  hence `a (k * T) = 0` in `ZMod p` for every `k`.
-/

namespace OMA.Helpers

open OMA.S_oeis_a188572

/-- Multiplication by `1 + √2 + √3` in `(ZMod p)^4`. -/
def stepZ (p : ℕ) (v : ZMod p × ZMod p × ZMod p × ZMod p) :
    ZMod p × ZMod p × ZMod p × ZMod p :=
  (v.1 + 2 * v.2.1 + 3 * v.2.2.1, v.1 + v.2.1 + 3 * v.2.2.2, v.1 + v.2.2.1 + 2 * v.2.2.2,
    v.2.1 + v.2.2.1 + v.2.2.2)

/-- Reduction mod `p` of the four coordinates. -/
def castV (p : ℕ) (v : ℤ × ℤ × ℤ × ℤ) : ZMod p × ZMod p × ZMod p × ZMod p :=
  ((v.1 : ZMod p), (v.2.1 : ZMod p), (v.2.2.1 : ZMod p), (v.2.2.2 : ZMod p))

theorem castV_step (p : ℕ) (v : ℤ × ℤ × ℤ × ℤ) :
    castV p (quadStep v) = stepZ p (castV p v) := by
  obtain ⟨c1, c2, c3, c6⟩ := v
  simp [quadStep, castV, stepZ]

theorem castV_pow (p : ℕ) (n : ℕ) :
    castV p (quadPow n) = (stepZ p)^[n] (castV p (1, 0, 0, 0)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih]
    exact castV_step p (quadPow n)

theorem eight_ne_zero (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) : (8 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((8 : ℤ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
  have h8 : p ∣ 2 ^ 3 := by exact_mod_cast h'
  have hd := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h8)
  have := hp.two_le
  omega

theorem stepZ_injective (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
    Function.Injective (stepZ p) := by
  rintro ⟨x1, x2, x3, x4⟩ ⟨y1, y2, y3, y4⟩ h
  simp only [stepZ, Prod.mk.injEq] at h
  obtain ⟨e1, e2, e3, e4⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have h8 := eight_ne_zero p hp h2
  have k1 : 8 * x1 = 8 * y1 := by linear_combination 4 * e1 + 4 * e2 - 12 * e4
  have k2 : 8 * x2 = 8 * y2 := by linear_combination 2 * e1 + 4 * e2 - 6 * e3
  have k3 : 8 * x3 = 8 * y3 := by linear_combination (-4) * e2 + 4 * e3 + 4 * e4
  have k4 : 8 * x4 = 8 * y4 := by linear_combination (-2) * e1 + 2 * e3 + 4 * e4
  rw [mul_left_cancel₀ h8 k1, mul_left_cancel₀ h8 k2, mul_left_cancel₀ h8 k3,
    mul_left_cancel₀ h8 k4]

theorem two_dvd (n : ℕ) : (2 : ℤ) ∣ a (n + 2) := by
  show (2 : ℤ) ∣ (quadStep (quadStep (quadPow n))).2.2.1
  generalize quadPow n = v
  obtain ⟨c1, c2, c3, c6⟩ := v
  simp only [quadStep]
  exact ⟨c1 + c2 + 2 * c3 + c6 + (c2 + c3 + c6), by ring⟩

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a188572.main := by
  intro p hp N
  by_cases h2 : p = 2
  · subst h2
    refine ⟨N + 2, by omega, ?_⟩
    exact_mod_cast OMA.Helpers.two_dvd N
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨T, hT, hper⟩ := Function.mem_periodicPts.mp
      ((OMA.Helpers.stepZ_injective p hp h2).mem_periodicPts (OMA.Helpers.castV p (1, 0, 0, 0)))
    refine ⟨T * N, Nat.le_mul_of_pos_left N hT, ?_⟩
    have hc := OMA.Helpers.castV_pow p (T * N)
    rw [(hper.mul_const N).eq] at hc
    have h3 := congrArg (fun v => v.2.2.1) hc
    simp only [OMA.Helpers.castV, Int.cast_zero] at h3
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h3
