import OMAStatements.S_oeis_a270490
import Mathlib

/-!
Proof of Mathar's recurrence for A270490,
a(n) = Sum_{i=0..(n+1)/2} C(2i+1,i) C(2n-2i,n) / (2i+1),
by creative telescoping (a Gosper certificate found by computer algebra and checked here).

Write `f(N, k)` for the summand, set to zero for `2k > N` (the extra term of the sum vanishes).
Its ratios `f(N, k+1) / f(N, k) = sg(N, k)` and `f(N-1, k) / f(N, k) = rh(N, k)` are rational
(`f_succ`, `f_pred`). With the certificate `Rc`, the rational identity `key` (valid for
`n ≥ 8`, `0 ≤ k ≤ n/2`) gives
  `p0 f(n,k) + p1 f(n-1,k) + p2 f(n-2,k) + p3 f(n-3,k) + p4 f(n-4,k) = G(k+1) - G(k)`
with `G(k) = Rc(n,k) f(n,k)`; summing over `k ≤ n/2` telescopes to `0`. The cases
`n = 4, ..., 7` are direct computations.
-/

namespace OMA.Helpers

open OMA.S_oeis_a270490 Finset

/-- The summand `C(2K+1,K) C(2N-2K,N) / (2K+1)`, set to zero for `2K > N`. -/
def f (N K : ℕ) : ℚ :=
  if 2 * K ≤ N then ((2 * K + 1).choose K : ℚ) * ((2 * N - 2 * K).choose N : ℚ) / (2 * (K : ℚ) + 1)
  else 0

/-- The ratio `f(N, K+1) / f(N, K)`. -/
def sg (x y : ℚ) : ℚ :=
  2 * (2 * y + 1) * (x - 2 * y) * (x - 2 * y - 1) / ((y + 2) * (2 * x - 2 * y) * (2 * x - 2 * y - 1))

/-- The ratio `f(N-1, K) / f(N, K)`. -/
def rh (x y : ℚ) : ℚ := x * (x - 2 * y) / ((2 * x - 2 * y) * (2 * x - 2 * y - 1))

theorem term (K j : ℕ) :
    f (2 * K + j) K = ((2 * K).factorial : ℚ) / ((K.factorial : ℚ) * ((K + 1).factorial : ℚ)) *
      ((2 * K + 2 * j).factorial : ℚ) / (((2 * K + j).factorial : ℚ) * (j.factorial : ℚ)) := by
  unfold f
  rw [if_pos (by omega), show 2 * (2 * K + j) - 2 * K = 2 * K + 2 * j by omega,
    Nat.cast_choose ℚ (show K ≤ 2 * K + 1 by omega),
    Nat.cast_choose ℚ (show 2 * K + j ≤ 2 * K + 2 * j by omega),
    show 2 * K + 1 - K = K + 1 by omega, show 2 * K + 2 * j - (2 * K + j) = j by omega,
    Nat.factorial_succ (2 * K)]
  push_cast
  have h1 : (2 * (K : ℚ) + 1) ≠ 0 := by positivity
  field_simp

theorem f_succ (N K : ℕ) : f N (K + 1) = f N K * sg N K := by
  by_cases h : 2 * (K + 1) ≤ N
  · obtain ⟨j, rfl⟩ : ∃ j, N = 2 * K + 2 + j := ⟨N - (2 * K + 2), by omega⟩
    have h1 : f (2 * K + 2 + j) (K + 1) = ((2 * K + 2).factorial : ℚ) /
        (((K + 1).factorial : ℚ) * ((K + 2).factorial : ℚ)) *
        ((2 * K + 2 * j + 2).factorial : ℚ) / (((2 * K + 2 + j).factorial : ℚ) * (j.factorial : ℚ)) := by
      have := term (K + 1) j
      rw [show 2 * (K + 1) + j = 2 * K + 2 + j by ring, show 2 * (K + 1) = 2 * K + 2 by ring,
        show 2 * K + 2 + 2 * j = 2 * K + 2 * j + 2 by ring] at this
      exact this
    have h2 : f (2 * K + 2 + j) K = ((2 * K).factorial : ℚ) /
        ((K.factorial : ℚ) * ((K + 1).factorial : ℚ)) *
        ((2 * K + 2 * j + 4).factorial : ℚ) /
          (((2 * K + 2 + j).factorial : ℚ) * ((j + 2).factorial : ℚ)) := by
      have := term K (j + 2)
      rw [show 2 * K + (j + 2) = 2 * K + 2 + j by ring,
        show 2 * K + 2 * (j + 2) = 2 * K + 2 * j + 4 by ring] at this
      exact this
    rw [h1, h2, Nat.factorial_succ (2 * K + 1), Nat.factorial_succ (2 * K),
      Nat.factorial_succ (2 * K + 2 * j + 3), Nat.factorial_succ (2 * K + 2 * j + 2),
      show K + 2 = K + 1 + 1 by ring, Nat.factorial_succ (K + 1), Nat.factorial_succ K,
      Nat.factorial_succ (j + 1), Nat.factorial_succ j]
    unfold sg
    push_cast
    rw [show (2 * (2 * (K : ℚ) + 2 + j) - 2 * K - 1) = 2 * K + 2 * j + 3 by ring,
      show (2 * (2 * (K : ℚ) + 2 + j) - 2 * K) = 2 * K + 2 * j + 4 by ring,
      show (2 * (K : ℚ) + 2 + j - 2 * K - 1) = j + 1 by ring,
      show (2 * (K : ℚ) + 2 + j - 2 * K) = j + 2 by ring]
    have hK : (0 : ℚ) ≤ K := Nat.cast_nonneg K
    have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    have n1 : ((K : ℚ) + 2) ≠ 0 := by intro h; linarith
    have n2 : ((K : ℚ) + 1) ≠ 0 := by intro h; linarith
    have n3 : ((j : ℚ) + 1) ≠ 0 := by intro h; linarith
    have n4 : ((j : ℚ) + 1 + 1) ≠ 0 := by intro h; linarith
    have n5 : (2 * (K : ℚ) + 2 * j + 3 + 1) ≠ 0 := by intro h; linarith
    have n6 : (2 * (K : ℚ) + 2 * j + 2 + 1) ≠ 0 := by intro h; linarith
    have n7 : (2 * (K : ℚ) + 2 * j + 4) ≠ 0 := by intro h; linarith
    have n8 : (2 * (K : ℚ) + 2 * j + 3) ≠ 0 := by intro h; linarith
    have n9 : ((j : ℚ) + 2) ≠ 0 := by intro h; linarith
    field_simp
    ring
  · have h0 : f N (K + 1) = 0 := by unfold f; rw [if_neg h]
    rw [h0]
    by_cases h' : 2 * K ≤ N
    · unfold sg
      rcases (show N = 2 * K ∨ N = 2 * K + 1 by omega) with rfl | rfl
      · push_cast
        rw [show 2 * (K : ℚ) - 2 * K = 0 by ring]
        simp
      · push_cast
        rw [show 2 * (K : ℚ) + 1 - 2 * K - 1 = 0 by ring]
        simp
    · unfold f
      rw [if_neg h']
      simp

theorem f_pred (M K : ℕ) : f M K = f (M + 1) K * rh ((M : ℚ) + 1) K := by
  by_cases h : 2 * K ≤ M
  · obtain ⟨j, rfl⟩ : ∃ j, M = 2 * K + j := ⟨M - 2 * K, by omega⟩
    have h2 : f (2 * K + j + 1) K = ((2 * K).factorial : ℚ) /
        ((K.factorial : ℚ) * ((K + 1).factorial : ℚ)) *
        ((2 * K + 2 * j + 2).factorial : ℚ) /
          (((2 * K + j + 1).factorial : ℚ) * ((j + 1).factorial : ℚ)) := by
      have := term K (j + 1)
      rw [show 2 * K + (j + 1) = 2 * K + j + 1 by ring,
        show 2 * K + 2 * (j + 1) = 2 * K + 2 * j + 2 by ring] at this
      exact this
    rw [term K j, h2, Nat.factorial_succ (2 * K + 2 * j + 1), Nat.factorial_succ (2 * K + 2 * j),
      Nat.factorial_succ (2 * K + j), Nat.factorial_succ j]
    unfold rh
    push_cast
    rw [show (2 * (2 * (K : ℚ) + j + 1) - 2 * K - 1) = 2 * K + 2 * j + 1 by ring,
      show (2 * (2 * (K : ℚ) + j + 1) - 2 * K) = 2 * K + 2 * j + 2 by ring,
      show (2 * (K : ℚ) + j + 1 - 2 * K) = j + 1 by ring]
    have hK : (0 : ℚ) ≤ K := Nat.cast_nonneg K
    have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    have n3 : ((j : ℚ) + 1) ≠ 0 := by intro h; linarith
    have n4 : (2 * (K : ℚ) + j + 1) ≠ 0 := by intro h; linarith
    have n5 : (2 * (K : ℚ) + 2 * j + 1 + 1) ≠ 0 := by intro h; linarith
    have n6 : (2 * (K : ℚ) + 2 * j + 1) ≠ 0 := by intro h; linarith
    have n7 : (2 * (K : ℚ) + 2 * j + 2) ≠ 0 := by intro h; linarith
    field_simp
    ring
  · have h0 : f M K = 0 := by unfold f; rw [if_neg h]
    rw [h0]
    by_cases h' : 2 * K ≤ M + 1
    · have hM : M + 1 = 2 * K := by omega
      unfold rh
      have : ((M : ℚ) + 1) = 2 * (K : ℚ) := by exact_mod_cast hM
      rw [this, show 2 * (K : ℚ) - 2 * K = 0 by ring]
      simp
    · unfold f
      rw [if_neg h']
      simp


/-- The numerator polynomial of the certificate. -/
def Q (x y : ℚ) : ℚ :=
  (8*y^4*x^2 - 32*y^4 - 16*y^3*x^3 - 12*y^3*x^2 + 176*y^3*x - 208*y^3 + 100*y^2*x^3 - 442*y^2*x^2 + 688*y^2*x - 376*y^2 + 4*y*x^4 - 120*y*x^3 + 467*y*x^2 - 628*y*x + 292*y - 22*x^4 + 213*x^3 - 678*x^2 + 856*x - 360)

/-- The certificate. -/
def Rc (x y : ℚ) : ℚ :=
  y * x * (y + 1) * Q x y / ((y - x) * (y - x + 1) * (y - x + 2) * (2 * y - 2 * x + 1) *
    (2 * y - 2 * x + 3) * (2 * y - 2 * x + 5))

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem key (x y : ℚ) (hx : 8 ≤ x) (hy0 : 0 ≤ y) (hy : 2 * y ≤ x) :
    (3 * x ^ 3 - 12 * x) + (-32 * x ^ 3 + 60 * x ^ 2 + 44 * x - 48) * rh x y + (96 * x ^ 3 - 368 * x ^ 2 + 320 * x) * (rh x y * rh (x - 1) y) +
      (64 * x ^ 2 - 208 * x + 168) * (rh x y * rh (x - 1) y * rh (x - 2) y) +
      (-256 * x ^ 3 + 1792 * x ^ 2 - 4032 * x + 2880) * (rh x y * rh (x - 1) y * rh (x - 2) y * rh (x - 3) y) =
      Rc x (y + 1) * sg x y - Rc x y := by
  have h0 : (y + 2 : ℚ) ≠ 0 := by intro h; linarith
  have h1 : (2 * x - 2 * y : ℚ) ≠ 0 := by intro h; linarith
  have h2 : (x * 2 - y * 2 : ℚ) ≠ 0 := by intro h; linarith
  have h3 : (2 * x - 2 * y - 1 : ℚ) ≠ 0 := by intro h; linarith
  have h4 : (x * 2 - y * 2 - 1 : ℚ) ≠ 0 := by intro h; linarith
  have h5 : (2 * x - 2 * y - 2 : ℚ) ≠ 0 := by intro h; linarith
  have h6 : (x * 2 - y * 2 - 2 : ℚ) ≠ 0 := by intro h; linarith
  have h7 : (2 * x - 2 * y - 3 : ℚ) ≠ 0 := by intro h; linarith
  have h8 : (x * 2 - y * 2 - 3 : ℚ) ≠ 0 := by intro h; linarith
  have h9 : (2 * x - 2 * y - 4 : ℚ) ≠ 0 := by intro h; linarith
  have h10 : (x * 2 - y * 2 - 4 : ℚ) ≠ 0 := by intro h; linarith
  have h11 : (2 * x - 2 * y - 5 : ℚ) ≠ 0 := by intro h; linarith
  have h12 : (x * 2 - y * 2 - 5 : ℚ) ≠ 0 := by intro h; linarith
  have h13 : (2 * x - 2 * y - 6 : ℚ) ≠ 0 := by intro h; linarith
  have h14 : (x * 2 - y * 2 - 6 : ℚ) ≠ 0 := by intro h; linarith
  have h15 : (2 * x - 2 * y - 7 : ℚ) ≠ 0 := by intro h; linarith
  have h16 : (x * 2 - y * 2 - 7 : ℚ) ≠ 0 := by intro h; linarith
  have h17 : (y - x : ℚ) ≠ 0 := by intro h; linarith
  have h18 : (y - x + 1 : ℚ) ≠ 0 := by intro h; linarith
  have h19 : (y - x + 2 : ℚ) ≠ 0 := by intro h; linarith
  have h20 : (y + 1 - x : ℚ) ≠ 0 := by intro h; linarith
  have h21 : (y + 2 - x : ℚ) ≠ 0 := by intro h; linarith
  have h22 : (y + 3 - x : ℚ) ≠ 0 := by intro h; linarith
  have h23 : (2 * y - 2 * x + 1 : ℚ) ≠ 0 := by intro h; linarith
  have h24 : (y * 2 - x * 2 + 1 : ℚ) ≠ 0 := by intro h; linarith
  have h25 : (2 * y - 2 * x + 3 : ℚ) ≠ 0 := by intro h; linarith
  have h26 : (y * 2 - x * 2 + 3 : ℚ) ≠ 0 := by intro h; linarith
  have h27 : (2 * y - 2 * x + 5 : ℚ) ≠ 0 := by intro h; linarith
  have h28 : (y * 2 - x * 2 + 5 : ℚ) ≠ 0 := by intro h; linarith
  have h29 : (2 * y - 2 * x + 7 : ℚ) ≠ 0 := by intro h; linarith
  have h30 : (y * 2 - x * 2 + 7 : ℚ) ≠ 0 := by intro h; linarith
  have g0 : (x - y : ℚ) ≠ 0 := by intro h; linarith
  have g1 : (2 * (x - y) - 1 : ℚ) ≠ 0 := by intro h; linarith
  have g2 : (x - y - 1 : ℚ) ≠ 0 := by intro h; linarith
  have g3 : (2 * (x - y) - 3 : ℚ) ≠ 0 := by intro h; linarith
  have g4 : (2 * (x - y) - 4 : ℚ) ≠ 0 := by intro h; linarith
  have g5 : (2 * (x - y) - 5 : ℚ) ≠ 0 := by intro h; linarith
  have g6 : (2 * (x - y) - 6 : ℚ) ≠ 0 := by intro h; linarith
  have g7 : (2 * (x - y) - 7 : ℚ) ≠ 0 := by intro h; linarith
  have g8 : (2 * (y - x) + 1 : ℚ) ≠ 0 := by intro h; linarith
  have g9 : (2 * (y - x) + 3 : ℚ) ≠ 0 := by intro h; linarith
  have g10 : (2 * (y - x) + 5 : ℚ) ≠ 0 := by intro h; linarith
  have g11 : (2 * (y - x) + 7 : ℚ) ≠ 0 := by intro h; linarith
  have g12 : (x - y - 2 : ℚ) ≠ 0 := by intro h; linarith
  have g13 : (x - y - 3 : ℚ) ≠ 0 := by intro h; linarith
  have e1 : rh (x - 1) y = (x - 1) * (x - 1 - 2 * y) / ((2 * x - 2 * y - 2) * (2 * x - 2 * y - 3)) := by
    unfold rh; ring_nf
  have e2 : rh (x - 2) y = (x - 2) * (x - 2 - 2 * y) / ((2 * x - 2 * y - 4) * (2 * x - 2 * y - 5)) := by
    unfold rh; ring_nf
  have e3 : rh (x - 3) y = (x - 3) * (x - 3 - 2 * y) / ((2 * x - 2 * y - 6) * (2 * x - 2 * y - 7)) := by
    unfold rh; ring_nf
  have eR : Rc x (y + 1) = (y + 1) * x * (y + 2) * Q x (y + 1) / ((y + 1 - x) * (y + 2 - x) *
      (y + 3 - x) * (2 * y - 2 * x + 3) * (2 * y - 2 * x + 5) * (2 * y - 2 * x + 7)) := by
    unfold Rc; ring_nf
  rw [e1, e2, e3, eR]
  unfold rh sg Rc Q
  field_simp
  ring

theorem f_out (N K : ℕ) (h : N < 2 * K) : f N K = 0 := by
  unfold f
  rw [if_neg (by omega)]

theorem sum_ext (N L : ℕ) (h : N / 2 + 1 ≤ L) :
    ∑ k ∈ range L, f N k = ∑ k ∈ range (N / 2 + 1), f N k := by
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr h) ?_
  intro k _ hk
  rw [Finset.mem_range] at hk
  exact f_out N k (by omega)

theorem A_eq (N : ℕ) : a N = ∑ k ∈ range (N / 2 + 1), f N k := by
  unfold a
  rw [← sum_ext N ((N + 1) / 2 + 1) (by omega)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  unfold f
  by_cases h : 2 * k ≤ N
  · rw [if_pos h]
  · rw [if_neg h, Nat.choose_eq_zero_of_lt (show 2 * N - 2 * k < N by omega)]
    simp

theorem tele (m : ℕ) :
    (3 * ((m : ℚ) + 8) ^ 3 - 12 * ((m : ℚ) + 8)) * ∑ k ∈ range ((m + 8) / 2 + 1), f (m + 8) k +
      (-32 * ((m : ℚ) + 8) ^ 3 + 60 * ((m : ℚ) + 8) ^ 2 + 44 * ((m : ℚ) + 8) - 48) * ∑ k ∈ range ((m + 7) / 2 + 1), f (m + 7) k +
      (96 * ((m : ℚ) + 8) ^ 3 - 368 * ((m : ℚ) + 8) ^ 2 + 320 * ((m : ℚ) + 8)) * ∑ k ∈ range ((m + 6) / 2 + 1), f (m + 6) k +
      (64 * ((m : ℚ) + 8) ^ 2 - 208 * ((m : ℚ) + 8) + 168) * ∑ k ∈ range ((m + 5) / 2 + 1), f (m + 5) k +
      (-256 * ((m : ℚ) + 8) ^ 3 + 1792 * ((m : ℚ) + 8) ^ 2 - 4032 * ((m : ℚ) + 8) + 2880) * ∑ k ∈ range ((m + 4) / 2 + 1), f (m + 4) k = 0 := by
  set x : ℚ := (m : ℚ) + 8 with hx
  rw [← sum_ext (m + 7) ((m + 8) / 2 + 1) (by omega), ← sum_ext (m + 6) ((m + 8) / 2 + 1) (by omega),
    ← sum_ext (m + 5) ((m + 8) / 2 + 1) (by omega), ← sum_ext (m + 4) ((m + 8) / 2 + 1) (by omega),
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  have hstep : ∀ k ∈ range ((m + 8) / 2 + 1),
      (3 * x ^ 3 - 12 * x) * f (m + 8) k + (-32 * x ^ 3 + 60 * x ^ 2 + 44 * x - 48) * f (m + 7) k + (96 * x ^ 3 - 368 * x ^ 2 + 320 * x) * f (m + 6) k + (64 * x ^ 2 - 208 * x + 168) * f (m + 5) k +
        (-256 * x ^ 3 + 1792 * x ^ 2 - 4032 * x + 2880) * f (m + 4) k =
      Rc x ((k + 1 : ℕ) : ℚ) * f (m + 8) (k + 1) - Rc x (k : ℚ) * f (m + 8) k := by
    intro k hk
    rw [Finset.mem_range] at hk
    have e3 : f (m + 7) k = f (m + 8) k * rh x k := by
      rw [f_pred (m + 7) k]
      congr 2
      rw [hx]
      push_cast
      ring
    have e2 : f (m + 6) k = f (m + 7) k * rh (x - 1) k := by
      rw [f_pred (m + 6) k]
      congr 2
      rw [hx]
      push_cast
      ring
    have e1 : f (m + 5) k = f (m + 6) k * rh (x - 2) k := by
      rw [f_pred (m + 5) k]
      congr 2
      rw [hx]
      push_cast
      ring
    have e0 : f (m + 4) k = f (m + 5) k * rh (x - 3) k := by
      rw [f_pred (m + 4) k]
      congr 2
      rw [hx]
      push_cast
      ring
    have es : f (m + 8) (k + 1) = f (m + 8) k * sg x k := by
      rw [f_succ, hx]
      push_cast
      ring_nf
    have hx8 : (8 : ℚ) ≤ x := by rw [hx]; linarith [(Nat.cast_nonneg m : (0 : ℚ) ≤ m)]
    have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    have hk2 : 2 * (k : ℚ) ≤ x := by
      rw [hx]
      have : 2 * k ≤ m + 8 := by omega
      exact_mod_cast (show ((2 * k : ℕ) : ℚ) ≤ ((m + 8 : ℕ) : ℚ) by exact_mod_cast this)
    have hkey := key x k hx8 hk0 hk2
    rw [e0, e1, e2, e3, es]
    push_cast
    linear_combination (f (m + 8) k) * hkey
  rw [Finset.sum_congr rfl hstep, Finset.sum_range_sub (fun k => Rc x (k : ℚ) * f (m + 8) k)]
  simp only [f_out (m + 8) ((m + 8) / 2 + 1) (by omega), mul_zero, Nat.cast_zero]
  simp [Rc]

theorem a_small : a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 7 ∧ a 3 = 24 ∧ a 4 = 87 ∧ a 5 = 320 ∧ a 6 = 1195 ∧
    a 7 = 4504 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [a, Finset.sum_range_succ, Finset.sum_range_zero] <;>
  norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]

theorem rec (n : ℕ) (hn : 4 ≤ n) :
    (3 * (n : ℚ) ^ 3 - 12 * (n : ℚ)) * a n
      + (-32 * (n : ℚ) ^ 3 + 60 * (n : ℚ) ^ 2 + 44 * (n : ℚ) - 48) * a (n - 1)
      + (96 * (n : ℚ) ^ 3 - 368 * (n : ℚ) ^ 2 + 320 * (n : ℚ)) * a (n - 2)
      + (64 * (n : ℚ) ^ 2 - 208 * (n : ℚ) + 168) * a (n - 3)
      + (-256 * (n : ℚ) ^ 3 + 1792 * (n : ℚ) ^ 2 - 4032 * (n : ℚ) + 2880) * a (n - 4) = 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := a_small
  rcases (show n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ 8 ≤ n by omega) with rfl | rfl | rfl | rfl | h8
  · norm_num [h0, h1, h2, h3, h4]
  · norm_num [h1, h2, h3, h4, h5]
  · norm_num [h2, h3, h4, h5, h6]
  · norm_num [h3, h4, h5, h6, h7]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    rw [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
      show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega,
      A_eq, A_eq, A_eq, A_eq, A_eq]
    have h := tele m
    push_cast
    linear_combination h

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a270490.main := OMA.Helpers.rec
