import OMAStatements.S_oeis_a377112
import Mathlib

namespace OMA.Helpers
open OMA.S_oeis_a377112

/-- Reduction of a coefficient vector modulo `p`. -/
def red377 (p : ℕ) (v : ℤ × ℤ × ℤ × ℤ) : ZMod p × ZMod p × ZMod p × ZMod p :=
  ((v.1 : ZMod p), (v.2.1 : ZMod p), (v.2.2.1 : ZMod p), (v.2.2.2 : ZMod p))

/-- The step map over `ZMod p`. -/
def stepZ377 (p : ℕ) (v : ZMod p × ZMod p × ZMod p × ZMod p) : ZMod p × ZMod p × ZMod p × ZMod p :=
  (2 * v.1 + 2 * v.2.1 + 3 * v.2.2.1,
   v.1 + 2 * v.2.1 + 3 * v.2.2.2,
   v.1 + 2 * v.2.2.1 + 2 * v.2.2.2,
   v.2.1 + v.2.2.1 + 2 * v.2.2.2)

/-- The adjugate of the step matrix over `ZMod p`. -/
def adjZ377 (p : ℕ) (v : ZMod p × ZMod p × ZMod p × ZMod p) : ZMod p × ZMod p × ZMod p × ZMod p :=
  (-2 * v.1 - 10 * v.2.1 - 9 * v.2.2.1 + 24 * v.2.2.2,
   -5 * v.1 - 2 * v.2.1 + 12 * v.2.2.1 - 9 * v.2.2.2,
   -3 * v.1 + 8 * v.2.1 - 2 * v.2.2.1 - 10 * v.2.2.2,
   4 * v.1 - 3 * v.2.1 - 5 * v.2.2.1 - 2 * v.2.2.2)

theorem red377_step (p : ℕ) (v : ℤ × ℤ × ℤ × ℤ) : red377 p (step v) = stepZ377 p (red377 p v) := by
  obtain ⟨a, b, c, d⟩ := v
  simp only [red377, step, stepZ377]
  push_cast
  rfl

theorem red377_coeffs_succ (p n : ℕ) :
    red377 p (coeffs (n + 1)) = stepZ377 p (red377 p (coeffs n)) := by
  rw [coeffs, red377_step]

theorem adjZ377_stepZ (p : ℕ) (v : ZMod p × ZMod p × ZMod p × ZMod p) :
    adjZ377 p (stepZ377 p v) = ((-23) * v.1, (-23) * v.2.1, (-23) * v.2.2.1, (-23) * v.2.2.2) := by
  obtain ⟨a, b, c, d⟩ := v
  simp only [adjZ377, stepZ377, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem stepZ377_inj (p : ℕ) (hp : p.Prime) (h23 : p ≠ 23) :
    Function.Injective (stepZ377 p) := by
  have := Fact.mk hp
  have hu : (-23 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((23 : ℕ) : ZMod p) = 0 := by
      have : (23 : ZMod p) = 0 := by
        have := congrArg Neg.neg h
        simpa using this
      exact_mod_cast this
    rw [ZMod.natCast_eq_zero_iff] at h'
    rcases (Nat.prime_def.mp (by norm_num : Nat.Prime 23)).2 p h' with h1 | h1
    · exact hp.one_lt.ne' h1
    · exact h23 h1
  intro v w hvw
  have e := congrArg (adjZ377 p) hvw
  rw [adjZ377_stepZ, adjZ377_stepZ] at e
  obtain ⟨a, b, c, d⟩ := v
  obtain ⟨a', b', c', d'⟩ := w
  simp only [Prod.mk.injEq] at e ⊢
  obtain ⟨e1, e2, e3, e4⟩ := e
  exact ⟨mul_left_cancel₀ hu e1, mul_left_cancel₀ hu e2, mul_left_cancel₀ hu e3,
    mul_left_cancel₀ hu e4⟩

theorem red377_shift (p i j : ℕ) (h : red377 p (coeffs i) = red377 p (coeffs j)) :
    ∀ m, red377 p (coeffs (i + m)) = red377 p (coeffs (j + m))
  | 0 => h
  | m + 1 => by
    rw [← add_assoc, ← add_assoc, red377_coeffs_succ, red377_coeffs_succ, red377_shift p i j h m]

theorem red377_descend (p : ℕ) (hp : p.Prime) (h23 : p ≠ 23) (d : ℕ) :
    ∀ i, red377 p (coeffs i) = red377 p (coeffs (i + d)) → red377 p (coeffs 0) = red377 p (coeffs d)
  | 0, h => by simpa using h
  | i + 1, h => by
    apply red377_descend p hp h23 d i
    rw [show i + 1 + d = (i + d) + 1 by omega, red377_coeffs_succ, red377_coeffs_succ] at h
    exact stepZ377_inj p hp h23 h

theorem red377_period (p : ℕ) (hp : p.Prime) :
    ∃ N d : ℕ, 0 < d ∧ (p : ℤ) ∣ a N ∧ red377 p (coeffs N) = red377 p (coeffs (N + d)) := by
  by_cases h23 : p = 23
  · subst h23
    refine ⟨1, 22, by norm_num, by decide, ?_⟩
    decide +kernel
  · have : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite (fun n => red377 p (coeffs n))
    rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
    · refine ⟨0, j - i, by omega, dvd_zero _, ?_⟩
      rw [zero_add]
      exact red377_descend p hp h23 (j - i) i (by rw [show i + (j - i) = j by omega]; exact e)
    · refine ⟨0, i - j, by omega, dvd_zero _, ?_⟩
      rw [zero_add]
      exact red377_descend p hp h23 (i - j) j (by rw [show j + (i - j) = i by omega]; exact e.symm)

theorem nth_periodic (P : ℕ → Prop) [DecidablePred P] (hinf : {n | P n}.Infinite) (N d : ℕ)
    (hd : 0 < d) (hN : P N) (hper : ∀ n, N ≤ n → (P n ↔ P (n + d))) :
    ∃ N0 Q : ℕ, 0 < Q ∧ ∀ i, N0 ≤ i →
      Nat.nth P (i + Q + 1) - Nat.nth P (i + Q) = Nat.nth P (i + 1) - Nat.nth P i := by
  set Q := Nat.count P (N + d) - Nat.count P N with hQ
  have hmono : Nat.count P (N + 1) ≤ Nat.count P (N + d) := Nat.count_monotone P (by omega)
  have hsucc : Nat.count P (N + 1) = Nat.count P N + 1 := by
    rw [Nat.count_succ, if_pos hN]
  have hcount : ∀ k, Nat.count P (N + k + d) = Nat.count P (N + k) + Q := by
    intro k
    induction k with
    | zero => simp only [add_zero]; omega
    | succ k ih =>
      rw [show N + (k + 1) + d = (N + k + d) + 1 by omega, show N + (k + 1) = (N + k) + 1 by omega,
        Nat.count_succ, Nat.count_succ, ih]
      have := hper (N + k) (by omega)
      by_cases h : P (N + k)
      · rw [if_pos h, if_pos (this.mp h)]; omega
      · rw [if_neg h, if_neg (fun h' => h (this.mpr h'))]; omega
  have key : ∀ i, Nat.count P N ≤ i → Nat.nth P (i + Q) = Nat.nth P i + d := by
    intro i hi
    have hge : N ≤ Nat.nth P i := (Nat.count_le_iff_le_nth hinf).mp hi
    have hm := Nat.nth_mem_of_infinite hinf i
    have hm' : P (Nat.nth P i + d) := (hper _ hge).mp hm
    have hc : Nat.count P (Nat.nth P i + d) = i + Q := by
      obtain ⟨k, hk⟩ : ∃ k, Nat.nth P i = N + k := ⟨Nat.nth P i - N, by omega⟩
      rw [hk, hcount k, ← hk, Nat.count_nth_of_infinite hinf]
    rw [← hc, Nat.nth_count hm']
  refine ⟨Nat.count P N, Q, by omega, fun i hi => ?_⟩
  rw [key i hi, show i + Q + 1 = (i + 1) + Q by omega, key (i + 1) (by omega)]
  omega

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a377112.main := by
  intro p hp
  classical
  obtain ⟨N, d, hd, hN, he⟩ := red377_period p hp
  have hper : ∀ m, red377 p (OMA.S_oeis_a377112.coeffs (N + m)) =
      red377 p (OMA.S_oeis_a377112.coeffs (N + d + m)) := red377_shift p N (N + d) he
  have hmem : ∀ n, ((p : ℤ) ∣ OMA.S_oeis_a377112.a n ↔
      (red377 p (OMA.S_oeis_a377112.coeffs n)).2.2.2 = 0) := by
    intro n
    simp only [red377, OMA.S_oeis_a377112.a]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hk : ∀ k, red377 p (OMA.S_oeis_a377112.coeffs (N + k * d)) =
      red377 p (OMA.S_oeis_a377112.coeffs N) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [show N + (k + 1) * d = N + d + k * d by ring, ← hper, ih]
  have hinf : {n : ℕ | (p : ℤ) ∣ OMA.S_oeis_a377112.a n}.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro b
    refine ⟨N + (b + 1) * d, ?_, ?_⟩
    · show (p : ℤ) ∣ OMA.S_oeis_a377112.a (N + (b + 1) * d)
      rw [hmem, hk, ← hmem]
      exact hN
    · nlinarith
  refine ⟨hinf, ?_⟩
  exact nth_periodic _ hinf N d hd hN (fun n hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = N + m := ⟨n - N, by omega⟩
    rw [hmem, hmem, show N + m + d = N + d + m by omega, ← hper])
