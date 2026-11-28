import OMAStatements.S_oeis_a278618
import Mathlib

/-!
Proof of Mathar's recurrence for A278618, a(n) = Sum_{j=0..n/2} C(n-j-1,n-2j) C(2n+1,j),
by creative telescoping (a Gosper certificate found by computer algebra and checked here).

For `n ≥ 1` the term `j = 0` vanishes and the term `j = K+1` equals
`f(n, K) = C(n-K-2, K) C(2n+1, K+1)` (zero for `2K+2 > n`), so `a(n) = Sum_{K < n/2} f(n, K)`
(`A_eq`). The ratios `f(N, K+1) / f(N, K) = sg(N, K)` and `f(N-1, K) / f(N, K) = rh(N, K)` are
rational (`f_succ`, `f_pred`). With the certificate `Rc`, the rational identity `key` (valid for
`n ≥ 9`, `0 ≤ K`, `2K+2 ≤ n`) gives
  `p0 f(n,K) + p1 f(n-1,K) + p2 f(n-2,K) + p3 f(n-3,K) = G(K+1) - G(K)`
with `G(K) = Rc(n,K) f(n,K)`; summing over `K < n/2` telescopes to `0`. The cases
`n = 3, ..., 8` are direct computations.
-/

namespace OMA.Helpers

open OMA.S_oeis_a278618 Finset

/-- The shifted summand `C(N-K-2,K) C(2N+1,K+1)` (the term `j = K+1`), zero for `2K+2 > N`. -/
def f (N K : ℕ) : ℚ :=
  if 2 * K + 2 ≤ N then ((N - K - 2).choose K : ℚ) * ((2 * N + 1).choose (K + 1) : ℚ) else 0

/-- The ratio `f(N, K+1) / f(N, K)`. -/
def sg (x y : ℚ) : ℚ :=
  (x - 2 * y - 2) * (x - 2 * y - 3) * (2 * x - y) / ((y + 1) * (x - y - 2) * (y + 2))

/-- The ratio `f(N-1, K) / f(N, K)`. -/
def rh (x y : ℚ) : ℚ :=
  (x - 2 * y - 2) * (2 * x - y) * (2 * x - y - 1) / ((x - y - 2) * (2 * x + 1) * (2 * x))

theorem term (K j : ℕ) :
    f (2 * K + 2 + j) K = ((K + j).factorial : ℚ) / ((K.factorial : ℚ) * (j.factorial : ℚ)) *
      ((4 * K + 2 * j + 5).factorial : ℚ) /
        (((K + 1).factorial : ℚ) * ((3 * K + 2 * j + 4).factorial : ℚ)) := by
  unfold f
  rw [if_pos (by omega), show 2 * K + 2 + j - K - 2 = K + j by omega,
    show 2 * (2 * K + 2 + j) + 1 = 4 * K + 2 * j + 5 by ring,
    Nat.cast_choose ℚ (show K ≤ K + j by omega),
    Nat.cast_choose ℚ (show K + 1 ≤ 4 * K + 2 * j + 5 by omega),
    show K + j - K = j by omega, show 4 * K + 2 * j + 5 - (K + 1) = 3 * K + 2 * j + 4 by omega]
  field_simp

theorem f_succ (N K : ℕ) : f N (K + 1) = f N K * sg N K := by
  by_cases h : 2 * (K + 1) + 2 ≤ N
  · obtain ⟨j, rfl⟩ : ∃ j, N = 2 * K + 4 + j := ⟨N - (2 * K + 4), by omega⟩
    have h1 : f (2 * K + 4 + j) (K + 1) = ((K + 1 + j).factorial : ℚ) /
        (((K + 1).factorial : ℚ) * (j.factorial : ℚ)) *
        ((4 * K + 2 * j + 9).factorial : ℚ) /
          (((K + 2).factorial : ℚ) * ((3 * K + 2 * j + 7).factorial : ℚ)) := by
      have := term (K + 1) j
      rw [show 2 * (K + 1) + 2 + j = 2 * K + 4 + j by ring,
        show 4 * (K + 1) + 2 * j + 5 = 4 * K + 2 * j + 9 by ring,
        show 3 * (K + 1) + 2 * j + 4 = 3 * K + 2 * j + 7 by ring] at this
      exact this
    have h2 : f (2 * K + 4 + j) K = ((K + 1 + j + 1).factorial : ℚ) /
        ((K.factorial : ℚ) * ((j + 1 + 1).factorial : ℚ)) *
        ((4 * K + 2 * j + 9).factorial : ℚ) /
          (((K + 1).factorial : ℚ) * ((3 * K + 2 * j + 7 + 1).factorial : ℚ)) := by
      have := term K (j + 2)
      rw [show 2 * K + 2 + (j + 2) = 2 * K + 4 + j by ring,
        show 4 * K + 2 * (j + 2) + 5 = 4 * K + 2 * j + 9 by ring,
        show 3 * K + 2 * (j + 2) + 4 = 3 * K + 2 * j + 7 + 1 by ring,
        show K + (j + 2) = K + 1 + j + 1 by ring, show j + 2 = j + 1 + 1 by ring] at this
      exact this
    rw [h1, h2, Nat.factorial_succ (K + 1 + j), Nat.factorial_succ (3 * K + 2 * j + 7),
      Nat.factorial_succ (j + 1), Nat.factorial_succ j, show K + 2 = K + 1 + 1 by ring,
      Nat.factorial_succ (K + 1), Nat.factorial_succ K]
    unfold sg
    push_cast
    rw [show (2 * (K : ℚ) + 4 + j - 2 * K - 2) = j + 2 by ring,
      show (2 * (K : ℚ) + 4 + j - 2 * K - 3) = j + 1 by ring,
      show (2 * (2 * (K : ℚ) + 4 + j) - K) = 3 * K + 2 * j + 8 by ring,
      show (2 * (K : ℚ) + 4 + j - K - 2) = K + j + 2 by ring]
    have hK : (0 : ℚ) ≤ K := Nat.cast_nonneg K
    have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    have n1 : ((K : ℚ) + 2) ≠ 0 := by intro h; linarith
    have n2 : ((K : ℚ) + 1) ≠ 0 := by intro h; linarith
    have n3 : ((j : ℚ) + 1) ≠ 0 := by intro h; linarith
    have n4 : ((j : ℚ) + 1 + 1) ≠ 0 := by intro h; linarith
    have n5 : ((K : ℚ) + j + 2) ≠ 0 := by intro h; linarith
    have n6 : ((K : ℚ) + 1 + j + 1) ≠ 0 := by intro h; linarith
    have n7 : ((K : ℚ) + 1 + 1) ≠ 0 := by intro h; linarith
    have n8 : (3 * (K : ℚ) + 2 * j + 7 + 1) ≠ 0 := by intro h; linarith
    field_simp
    ring
  · have h0 : f N (K + 1) = 0 := by unfold f; rw [if_neg h]
    rw [h0]
    by_cases h' : 2 * K + 2 ≤ N
    · unfold sg
      rcases (show N = 2 * K + 2 ∨ N = 2 * K + 3 by omega) with rfl | rfl
      · push_cast
        rw [show 2 * (K : ℚ) + 2 - 2 * K - 2 = 0 by ring]
        simp
      · push_cast
        rw [show 2 * (K : ℚ) + 3 - 2 * K - 3 = 0 by ring]
        simp
    · unfold f
      rw [if_neg h']
      simp

theorem f_pred (M K : ℕ) : f M K = f (M + 1) K * rh ((M : ℚ) + 1) K := by
  by_cases h : 2 * K + 2 ≤ M
  · obtain ⟨j, rfl⟩ : ∃ j, M = 2 * K + 2 + j := ⟨M - (2 * K + 2), by omega⟩
    have h2 : f (2 * K + 2 + j + 1) K = ((K + j + 1).factorial : ℚ) /
        ((K.factorial : ℚ) * ((j + 1).factorial : ℚ)) *
        ((4 * K + 2 * j + 5 + 1 + 1).factorial : ℚ) /
          (((K + 1).factorial : ℚ) * ((3 * K + 2 * j + 4 + 1 + 1).factorial : ℚ)) := by
      have := term K (j + 1)
      rw [show 2 * K + 2 + (j + 1) = 2 * K + 2 + j + 1 by ring,
        show 4 * K + 2 * (j + 1) + 5 = 4 * K + 2 * j + 5 + 1 + 1 by ring,
        show 3 * K + 2 * (j + 1) + 4 = 3 * K + 2 * j + 4 + 1 + 1 by ring,
        show K + (j + 1) = K + j + 1 by ring] at this
      exact this
    rw [term K j, h2, Nat.factorial_succ (4 * K + 2 * j + 5 + 1), Nat.factorial_succ (4 * K + 2 * j + 5),
      Nat.factorial_succ (3 * K + 2 * j + 4 + 1), Nat.factorial_succ (3 * K + 2 * j + 4),
      Nat.factorial_succ (K + j), Nat.factorial_succ j]
    unfold rh
    push_cast
    rw [show (2 * (K : ℚ) + 2 + j + 1 - 2 * K - 2) = j + 1 by ring,
      show (2 * (2 * (K : ℚ) + 2 + j + 1) - K - 1) = 3 * K + 2 * j + 5 by ring,
      show (2 * (2 * (K : ℚ) + 2 + j + 1) - K) = 3 * K + 2 * j + 6 by ring,
      show (2 * (K : ℚ) + 2 + j + 1 - K - 2) = K + j + 1 by ring,
      show (2 * (2 * (K : ℚ) + 2 + j + 1) + 1) = 4 * K + 2 * j + 7 by ring,
      show (2 * (2 * (K : ℚ) + 2 + j + 1)) = 4 * K + 2 * j + 6 by ring]
    have hK : (0 : ℚ) ≤ K := Nat.cast_nonneg K
    have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    have n3 : ((j : ℚ) + 1) ≠ 0 := by intro h; linarith
    have n4 : ((K : ℚ) + j + 1) ≠ 0 := by intro h; linarith
    have n5 : (4 * (K : ℚ) + 2 * j + 7) ≠ 0 := by intro h; linarith
    have n6 : (4 * (K : ℚ) + 2 * j + 6) ≠ 0 := by intro h; linarith
    have n6' : (2 * (K : ℚ) + j + 3) ≠ 0 := by intro h; linarith
    have n7 : (4 * (K : ℚ) + 2 * j + 5 + 1 + 1) ≠ 0 := by intro h; linarith
    have n8 : (4 * (K : ℚ) + 2 * j + 5 + 1) ≠ 0 := by intro h; linarith
    have n9 : (3 * (K : ℚ) + 2 * j + 4 + 1 + 1) ≠ 0 := by intro h; linarith
    have n10 : (3 * (K : ℚ) + 2 * j + 4 + 1) ≠ 0 := by intro h; linarith
    field_simp
    ring
  · have h0 : f M K = 0 := by unfold f; rw [if_neg h]
    rw [h0]
    by_cases h' : 2 * K + 2 ≤ M + 1
    · have hM : M + 1 = 2 * K + 2 := by omega
      unfold rh
      have : ((M : ℚ) + 1) = 2 * (K : ℚ) + 2 := by exact_mod_cast hM
      rw [this, show 2 * (K : ℚ) + 2 - 2 * K - 2 = 0 by ring]
      simp
    · unfold f
      rw [if_neg h']
      simp


/-- The numerator polynomial of the certificate. -/
def Q (x y : ℚ) : ℚ :=
  120*y^6*x - 72*y^6 - 1180*y^5*x^2 + 1888*y^5*x - 708*y^5 + 4750*y^4*x^3 - 12650*y^4*x^2 + 10396*y^4*x - 2700*y^4 - 9925*y^3*x^4 + 37630*y^3*x^3 - 49183*y^3*x^2 + 26434*y^3*x - 4980*y^3 + 11125*y^2*x^5 - 55740*y^2*x^4 + 102569*y^2*x^3 - 86242*y^2*x^2 + 32752*y^2*x - 4428*y^2 - 6105*y*x^6 + 38958*y*x^5 - 95704*y*x^4 + 114136*y*x^3 - 67919*y*x^2 + 18242*y*x - 1512*y + 1170*x^7 - 9462*x^6 + 31010*x^5 - 51346*x^4 + 44500*x^3 - 18944*x^2 + 3120*x

/-- The certificate. -/
def Rc (x y : ℚ) : ℚ :=
  y * (y + 1) * Q x y / (2 * x * (x - 1) * (2 * x + 1) * (y - x + 2) * (y - x + 3))

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem key (x y : ℚ) (hx : 9 ≤ x) (hy0 : 0 ≤ y) (hy : 2 * y + 2 ≤ x) :
    (20 * x ^ 4 - 22 * x ^ 3 - 26 * x ^ 2 + 16 * x) + (-115 * x ^ 4 + 344 * x ^ 3 - 299 * x ^ 2 + 82 * x) * rh x y + (-40 * x ^ 4 - 196 * x ^ 3 + 700 * x ^ 2 - 536 * x + 120) * (rh x y * rh (x - 1) y) +
      (720 * x ^ 4 - 3312 * x ^ 3 + 5148 * x ^ 2 - 3132 * x + 648) * (rh x y * rh (x - 1) y * rh (x - 2) y) =
      Rc x (y + 1) * sg x y - Rc x y := by
  have h0 : (y + 1 : ℚ) ≠ 0 := by intro h; linarith
  have h1 : (x - y - 2 : ℚ) ≠ 0 := by intro h; linarith
  have h2 : (y + 2 : ℚ) ≠ 0 := by intro h; linarith
  have h3 : (2 * x + 1 : ℚ) ≠ 0 := by intro h; linarith
  have h4 : (2 * x : ℚ) ≠ 0 := by intro h; linarith
  have h5 : (x - y - 3 : ℚ) ≠ 0 := by intro h; linarith
  have h6 : (2 * x - 1 : ℚ) ≠ 0 := by intro h; linarith
  have h7 : (2 * x - 2 : ℚ) ≠ 0 := by intro h; linarith
  have h8 : (x - y - 4 : ℚ) ≠ 0 := by intro h; linarith
  have h9 : (2 * x - 3 : ℚ) ≠ 0 := by intro h; linarith
  have h10 : (2 * x - 4 : ℚ) ≠ 0 := by intro h; linarith
  have h11 : (x : ℚ) ≠ 0 := by intro h; linarith
  have h12 : (x - 1 : ℚ) ≠ 0 := by intro h; linarith
  have h13 : (x - 2 : ℚ) ≠ 0 := by intro h; linarith
  have h14 : (y - x + 2 : ℚ) ≠ 0 := by intro h; linarith
  have h15 : (y - x + 3 : ℚ) ≠ 0 := by intro h; linarith
  have h16 : (y - x + 4 : ℚ) ≠ 0 := by intro h; linarith
  have v0 : (x * 2 - 1 : ℚ) ≠ 0 := by intro h; linarith
  have v1 : (x * 2 + 1 : ℚ) ≠ 0 := by intro h; linarith
  have v2 : (x * 2 - 3 : ℚ) ≠ 0 := by intro h; linarith
  have v3 : (x * 2 - 4 : ℚ) ≠ 0 := by intro h; linarith
  have v4 : (x * 2 - 2 : ℚ) ≠ 0 := by intro h; linarith
  have v5 : (x * 2 : ℚ) ≠ 0 := by intro h; linarith
  have v6 : (y - x + 2 : ℚ) ≠ 0 := by intro h; linarith
  have v7 : (y - x + 3 : ℚ) ≠ 0 := by intro h; linarith
  have v8 : (y - x + 4 : ℚ) ≠ 0 := by intro h; linarith
  have v9 : (x - 2 - y : ℚ) ≠ 0 := by intro h; linarith
  have v10 : (x - 4 - y : ℚ) ≠ 0 := by intro h; linarith
  have v11 : (x - 3 - y : ℚ) ≠ 0 := by intro h; linarith
  have e1 : rh (x - 1) y = (x - 2 * y - 3) * (2 * x - y - 2) * (2 * x - y - 3) /
      ((x - y - 3) * (2 * x - 1) * (2 * x - 2)) := by
    unfold rh; ring_nf
  have e2 : rh (x - 2) y = (x - 2 * y - 4) * (2 * x - y - 4) * (2 * x - y - 5) /
      ((x - y - 4) * (2 * x - 3) * (2 * x - 4)) := by
    unfold rh; ring_nf
  have eR : Rc x (y + 1) = (y + 1) * (y + 2) * Q x (y + 1) /
      (2 * x * (x - 1) * (2 * x + 1) * (y - x + 3) * (y - x + 4)) := by
    unfold Rc; ring_nf
  rw [e1, e2, eR]
  unfold rh sg Rc Q
  field_simp
  ring

theorem f_out (N K : ℕ) (h : N < 2 * K + 2) : f N K = 0 := by
  unfold f
  rw [if_neg (by omega)]

theorem sum_ext (N L : ℕ) (h : N / 2 ≤ L) :
    ∑ k ∈ range L, f N k = ∑ k ∈ range (N / 2), f N k := by
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr h) ?_
  intro k _ hk
  rw [Finset.mem_range] at hk
  exact f_out N k (by omega)

theorem A_eq (N : ℕ) (hN : 1 ≤ N) : ((a N : ℤ) : ℚ) = ∑ k ∈ range (N / 2), f N k := by
  unfold a
  push_cast
  rw [Finset.sum_range_succ', show N - 0 - 1 = N - 1 by omega, show N - 2 * 0 = N by omega,
    Nat.choose_eq_zero_of_lt (show N - 1 < N by omega)]
  simp only [Nat.cast_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  unfold f
  rw [if_pos (by omega), show N - (k + 1) - 1 = N - k - 2 by omega,
    show N - 2 * (k + 1) = N - k - 2 - k by omega, Nat.choose_symm (show k ≤ N - k - 2 by omega)]

theorem tele (m : ℕ) :
    (20 * ((m : ℚ) + 9) ^ 4 - 22 * ((m : ℚ) + 9) ^ 3 - 26 * ((m : ℚ) + 9) ^ 2 + 16 * ((m : ℚ) + 9)) * ∑ k ∈ range ((m + 9) / 2), f (m + 9) k +
      (-115 * ((m : ℚ) + 9) ^ 4 + 344 * ((m : ℚ) + 9) ^ 3 - 299 * ((m : ℚ) + 9) ^ 2 + 82 * ((m : ℚ) + 9)) * ∑ k ∈ range ((m + 8) / 2), f (m + 8) k +
      (-40 * ((m : ℚ) + 9) ^ 4 - 196 * ((m : ℚ) + 9) ^ 3 + 700 * ((m : ℚ) + 9) ^ 2 - 536 * ((m : ℚ) + 9) + 120) * ∑ k ∈ range ((m + 7) / 2), f (m + 7) k +
      (720 * ((m : ℚ) + 9) ^ 4 - 3312 * ((m : ℚ) + 9) ^ 3 + 5148 * ((m : ℚ) + 9) ^ 2 - 3132 * ((m : ℚ) + 9) + 648) * ∑ k ∈ range ((m + 6) / 2), f (m + 6) k = 0 := by
  set x : ℚ := (m : ℚ) + 9 with hx
  rw [← sum_ext (m + 8) ((m + 9) / 2) (by omega), ← sum_ext (m + 7) ((m + 9) / 2) (by omega),
    ← sum_ext (m + 6) ((m + 9) / 2) (by omega),
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hstep : ∀ k ∈ range ((m + 9) / 2),
      (20 * x ^ 4 - 22 * x ^ 3 - 26 * x ^ 2 + 16 * x) * f (m + 9) k + (-115 * x ^ 4 + 344 * x ^ 3 - 299 * x ^ 2 + 82 * x) * f (m + 8) k + (-40 * x ^ 4 - 196 * x ^ 3 + 700 * x ^ 2 - 536 * x + 120) * f (m + 7) k + (720 * x ^ 4 - 3312 * x ^ 3 + 5148 * x ^ 2 - 3132 * x + 648) * f (m + 6) k =
      Rc x ((k + 1 : ℕ) : ℚ) * f (m + 9) (k + 1) - Rc x (k : ℚ) * f (m + 9) k := by
    intro k hk
    rw [Finset.mem_range] at hk
    have e2 : f (m + 8) k = f (m + 9) k * rh x k := by
      rw [f_pred (m + 8) k]
      congr 2
      rw [hx]
      push_cast
      ring
    have e1 : f (m + 7) k = f (m + 8) k * rh (x - 1) k := by
      rw [f_pred (m + 7) k]
      congr 2
      rw [hx]
      push_cast
      ring
    have e0 : f (m + 6) k = f (m + 7) k * rh (x - 2) k := by
      rw [f_pred (m + 6) k]
      congr 2
      rw [hx]
      push_cast
      ring
    have es : f (m + 9) (k + 1) = f (m + 9) k * sg x k := by
      rw [f_succ, hx]
      push_cast
      ring_nf
    have hx9 : (9 : ℚ) ≤ x := by rw [hx]; linarith [(Nat.cast_nonneg m : (0 : ℚ) ≤ m)]
    have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    have hk2 : 2 * (k : ℚ) + 2 ≤ x := by
      rw [hx]
      have : 2 * k + 2 ≤ m + 9 := by omega
      exact_mod_cast (show ((2 * k + 2 : ℕ) : ℚ) ≤ ((m + 9 : ℕ) : ℚ) by exact_mod_cast this)
    have hkey := key x k hx9 hk0 hk2
    rw [e0, e1, e2, es]
    push_cast
    linear_combination (f (m + 9) k) * hkey
  rw [Finset.sum_congr rfl hstep, Finset.sum_range_sub (fun k => Rc x (k : ℚ) * f (m + 9) k)]
  simp only [f_out (m + 9) ((m + 9) / 2) (by omega), mul_zero, Nat.cast_zero]
  simp [Rc]

theorem a_small : a 0 = 1 ∧ a 1 = 0 ∧ a 2 = 5 ∧ a 3 = 7 ∧ a 4 = 45 ∧ a 5 = 121 ∧ a 6 = 533 ∧
    a 7 = 1800 ∧ a 8 = 7157 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [a, Finset.sum_range_succ, Finset.sum_range_zero] <;>
  norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]

set_option maxRecDepth 100000 in
theorem rec (n : ℕ) (hn : 3 ≤ n) :
    (20 * (n : ℤ) ^ 4 - 22 * (n : ℤ) ^ 3 - 26 * (n : ℤ) ^ 2 + 16 * (n : ℤ)) * a n
      + (-115 * (n : ℤ) ^ 4 + 344 * (n : ℤ) ^ 3 - 299 * (n : ℤ) ^ 2 + 82 * (n : ℤ)) * a (n - 1)
      + (-40 * (n : ℤ) ^ 4 - 196 * (n : ℤ) ^ 3 + 700 * (n : ℤ) ^ 2 - 536 * (n : ℤ) + 120) * a (n - 2)
      + (720 * (n : ℤ) ^ 4 - 3312 * (n : ℤ) ^ 3 + 5148 * (n : ℤ) ^ 2 - 3132 * (n : ℤ) + 648) * a (n - 3) = 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := a_small
  rcases (show n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ 9 ≤ n by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | h9
  · norm_num [h0, h1, h2, h3]
  · norm_num [h1, h2, h3, h4]
  · norm_num [h2, h3, h4, h5]
  · norm_num [h3, h4, h5, h6]
  · norm_num [h4, h5, h6, h7]
  · norm_num [h5, h6, h7, h8]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    rw [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega,
      show m + 9 - 3 = m + 6 by omega]
    have h := tele m
    have hq : (((20 * ((m + 9 : ℕ) : ℤ) ^ 4 - 22 * ((m + 9 : ℕ) : ℤ) ^ 3 - 26 * ((m + 9 : ℕ) : ℤ) ^ 2 + 16 * ((m + 9 : ℕ) : ℤ)) * a (m + 9) + (-115 * ((m + 9 : ℕ) : ℤ) ^ 4 + 344 * ((m + 9 : ℕ) : ℤ) ^ 3 - 299 * ((m + 9 : ℕ) : ℤ) ^ 2 + 82 * ((m + 9 : ℕ) : ℤ)) * a (m + 8) + (-40 * ((m + 9 : ℕ) : ℤ) ^ 4 - 196 * ((m + 9 : ℕ) : ℤ) ^ 3 + 700 * ((m + 9 : ℕ) : ℤ) ^ 2 - 536 * ((m + 9 : ℕ) : ℤ) + 120) * a (m + 7) + (720 * ((m + 9 : ℕ) : ℤ) ^ 4 - 3312 * ((m + 9 : ℕ) : ℤ) ^ 3 + 5148 * ((m + 9 : ℕ) : ℤ) ^ 2 - 3132 * ((m + 9 : ℕ) : ℤ) + 648) * a (m + 6) : ℤ) : ℚ)
        = 0 := by
      push_cast
      rw [A_eq (m + 9) (by omega), A_eq (m + 8) (by omega), A_eq (m + 7) (by omega),
        A_eq (m + 6) (by omega)]
      linear_combination h
    exact_mod_cast hq

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a278618.main := OMA.Helpers.rec
