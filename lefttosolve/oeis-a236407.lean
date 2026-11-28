import OMAStatements.S_oeis_a236407
import Mathlib

/-!
Proof of Mathar's recurrence for A236407, a(n) = 2 Sum_{k=0..n-1} C(n-1,k) C(n+k,k) + n,
by creative telescoping (a Gosper certificate found by computer algebra and checked here).

Write `f(N, k) = C(N-1,k) C(N+k,k)` for `k < N` and `0` otherwise, so that
`a(N) = 2 Sum_k f(N, k) + N`. The ratios `f(N, k+1) / f(N, k) = sg(N, k)` and
`f(N-1, k) / f(N, k) = rh(N, k)` are rational (`f_succ`, `f_pred`). With the certificate `Rc`,
the rational identity `key` gives, for `n ≥ 5`,
  `p0 f(n,k) + p1 f(n-1,k) + p2 f(n-2,k) + p3 f(n-3,k) + p4 f(n-4,k) = G(k+1) - G(k)`
with `G(k) = Rc(n,k) f(n,k)`; summing over `k < n` telescopes to `0` (`f(n,n) = 0`,
`Rc(n,0) = 0`). The operator also kills the term `n` (its coefficients sum to a polynomial
identity), so the recurrence holds for `a`. The case `n = 4` is a direct computation.
-/

namespace OMA.Helpers

open OMA.S_oeis_a236407 Finset

/-- The summand `C(N-1,K) C(N+K,K)`, set to zero for `K ≥ N`. -/
def f (N K : ℕ) : ℚ := if K < N then ((N - 1).choose K : ℚ) * ((N + K).choose K : ℚ) else 0

/-- The ratio `f(N, K+1) / f(N, K)`. -/
def sg (x y : ℚ) : ℚ := (x + y + 1) * (x - 1 - y) / ((y + 1) ^ 2)

/-- The ratio `f(N-1, K) / f(N, K)`. -/
def rh (x y : ℚ) : ℚ := x * (x - 1 - y) / ((x - 1) * (x + y))

theorem term (K j : ℕ) :
    f (K + j + 1) K = ((2 * K + j + 1).factorial : ℚ) /
      (((K : ℚ) + j + 1) * (K.factorial : ℚ) ^ 2 * (j.factorial : ℚ)) := by
  unfold f
  rw [if_pos (by omega), show K + j + 1 - 1 = K + j by omega,
    show K + j + 1 + K = 2 * K + j + 1 by ring,
    Nat.cast_choose ℚ (show K ≤ K + j by omega),
    Nat.cast_choose ℚ (show K ≤ 2 * K + j + 1 by omega),
    show K + j - K = j by omega, show 2 * K + j + 1 - K = K + j + 1 by omega,
    Nat.factorial_succ (K + j)]
  push_cast
  field_simp

theorem f_succ (N K : ℕ) : f N (K + 1) = f N K * sg N K := by
  by_cases h : K + 1 < N
  · obtain ⟨j, rfl⟩ : ∃ j, N = K + j + 2 := ⟨N - (K + 2), by omega⟩
    have h1 : f (K + j + 2) (K + 1) = ((2 * K + j + 3).factorial : ℚ) /
        (((K : ℚ) + j + 2) * ((K + 1).factorial : ℚ) ^ 2 * (j.factorial : ℚ)) := by
      have := term (K + 1) j
      rw [show K + 1 + j + 1 = K + j + 2 by ring, show 2 * (K + 1) + j + 1 = 2 * K + j + 3 by ring]
        at this
      rw [this]
      push_cast
      ring_nf
    have h2 : f (K + j + 2) K = ((2 * K + j + 2).factorial : ℚ) /
        (((K : ℚ) + j + 2) * (K.factorial : ℚ) ^ 2 * ((j + 1).factorial : ℚ)) := by
      have := term K (j + 1)
      rw [show K + (j + 1) + 1 = K + j + 2 by ring, show 2 * K + (j + 1) + 1 = 2 * K + j + 2 by ring]
        at this
      rw [this]
      push_cast
      ring_nf
    rw [h1, h2, Nat.factorial_succ (2 * K + j + 2), Nat.factorial_succ K, Nat.factorial_succ j]
    unfold sg
    push_cast
    have hK : (0 : ℚ) ≤ K := Nat.cast_nonneg K
    have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    have n1 : ((K : ℚ) + j + 2) ≠ 0 := by intro h; linarith
    have n2 : ((K : ℚ) + 1) ≠ 0 := by intro h; linarith
    have n3 : ((j : ℚ) + 1) ≠ 0 := by intro h; linarith
    field_simp
    ring
  · have h0 : f N (K + 1) = 0 := by unfold f; rw [if_neg h]
    rw [h0]
    by_cases h' : K < N
    · obtain rfl : N = K + 1 := by omega
      simp [sg]
    · unfold f
      rw [if_neg h']
      simp

theorem f_pred (M K : ℕ) : f (M + 1) K = f (M + 2) K * rh ((M : ℚ) + 2) K := by
  by_cases h : K < M + 1
  · obtain ⟨j, rfl⟩ : ∃ j, M = K + j := ⟨M - K, by omega⟩
    have h2 : f (K + j + 2) K = ((2 * K + j + 2).factorial : ℚ) /
        (((K : ℚ) + j + 2) * (K.factorial : ℚ) ^ 2 * ((j + 1).factorial : ℚ)) := by
      have := term K (j + 1)
      rw [show K + (j + 1) + 1 = K + j + 2 by ring, show 2 * K + (j + 1) + 1 = 2 * K + j + 2 by ring]
        at this
      rw [this]
      push_cast
      ring_nf
    rw [term K j, h2, Nat.factorial_succ (2 * K + j + 1), Nat.factorial_succ j]
    unfold rh
    push_cast
    have hK : (0 : ℚ) ≤ K := Nat.cast_nonneg K
    have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    have n1 : ((K : ℚ) + j + 2) ≠ 0 := by intro h; linarith
    have n1' : ((K : ℚ) + j + 1) ≠ 0 := by intro h; linarith
    have n2 : (2 * (K : ℚ) + j + 2) ≠ 0 := by intro h; linarith
    have n3 : ((j : ℚ) + 1) ≠ 0 := by intro h; linarith
    have n4 : ((K : ℚ) + j + 2 - 1) ≠ 0 := by intro h; linarith
    have n5 : ((K : ℚ) + j + 2 + K) ≠ 0 := by intro h; linarith
    field_simp
    ring
  · have h0 : f (M + 1) K = 0 := by unfold f; rw [if_neg h]
    rw [h0]
    by_cases h' : K < M + 2
    · obtain rfl : K = M + 1 := by omega
      simp only [rh]
      push_cast
      rw [show (M : ℚ) + 2 - 1 - (M + 1) = 0 by ring]
      simp
    · unfold f
      rw [if_neg h']
      simp


/-- The numerator polynomial of the certificate. -/
def Q (x y : ℚ) : ℚ :=
  4*y^2*x^4 - 32*y^2*x^3 + 88*y^2*x^2 - 96*y^2*x + 34*y^2 - 8*y*x^4 + 64*y*x^3 - 174*y*x^2 +
    184*y*x - 60*y + 3*x^4 - 24*x^3 + 63*x^2 - 60*x + 14

/-- The certificate. -/
def Rc (x y : ℚ) : ℚ :=
  -4 * y ^ 2 * x * Q x y / ((y + x) * (x - 3) * (x - 2) * (x - 1) * (y + x - 3) * (y + x - 2) *
    (y + x - 1))

set_option maxRecDepth 20000 in
theorem key (x y : ℚ) (hx : 5 ≤ x) (hy0 : 0 ≤ y) :
    (x ^ 2 - 3 * x) + (-8 * x ^ 2 + 28 * x - 12) * rh x y +
      (14 * x ^ 2 - 56 * x + 40) * (rh x y * rh (x - 1) y) +
      (-8 * x ^ 2 + 36 * x - 28) * (rh x y * rh (x - 1) y * rh (x - 2) y) +
      (x ^ 2 - 5 * x + 4) * (rh x y * rh (x - 1) y * rh (x - 2) y * rh (x - 3) y) =
      Rc x (y + 1) * sg x y - Rc x y := by
  have q1 : (x - 1 : ℚ) ≠ 0 := by intro h; linarith
  have q2 : (x - 2 : ℚ) ≠ 0 := by intro h; linarith
  have q3 : (x - 3 : ℚ) ≠ 0 := by intro h; linarith
  have q4 : (x - 1 - 1 : ℚ) ≠ 0 := by intro h; linarith
  have q5 : (x - 2 - 1 : ℚ) ≠ 0 := by intro h; linarith
  have q6 : (x - 3 - 1 : ℚ) ≠ 0 := by intro h; linarith
  have r0 : (x + y : ℚ) ≠ 0 := by intro h; linarith
  have r1 : (x - 1 + y : ℚ) ≠ 0 := by intro h; linarith
  have r2 : (x - 2 + y : ℚ) ≠ 0 := by intro h; linarith
  have r3 : (x - 3 + y : ℚ) ≠ 0 := by intro h; linarith
  have s0 : (y + x : ℚ) ≠ 0 := by intro h; linarith
  have s1 : (y + x - 1 : ℚ) ≠ 0 := by intro h; linarith
  have s2 : (y + x - 2 : ℚ) ≠ 0 := by intro h; linarith
  have s3 : (y + x - 3 : ℚ) ≠ 0 := by intro h; linarith
  have t0 : (y + 1 + x : ℚ) ≠ 0 := by intro h; linarith
  have t1 : (y + 1 + x - 1 : ℚ) ≠ 0 := by intro h; linarith
  have t2 : (y + 1 + x - 2 : ℚ) ≠ 0 := by intro h; linarith
  have t3 : (y + 1 + x - 3 : ℚ) ≠ 0 := by intro h; linarith
  have u0 : (y + 1 : ℚ) ≠ 0 := by intro h; linarith
  unfold rh sg Rc Q
  field_simp
  ring

theorem f_out (N K : ℕ) (h : N ≤ K) : f N K = 0 := by
  unfold f
  rw [if_neg (by omega)]

theorem sum_ext (N L : ℕ) (h : N ≤ L) : ∑ k ∈ range L, f N k = ∑ k ∈ range N, f N k := by
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr h) ?_
  intro k _ hk
  rw [Finset.mem_range] at hk
  exact f_out N k (by omega)

theorem A_eq (N : ℕ) : ((a N : ℤ) : ℚ) = 2 * ∑ k ∈ range N, f N k + N := by
  unfold a
  push_cast
  congr 2
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [f, if_pos hk]

theorem tele (m : ℕ) :
    (((m : ℚ) + 5) ^ 2 - 3 * ((m : ℚ) + 5)) * ∑ k ∈ range (m + 5), f (m + 5) k +
      (-8 * ((m : ℚ) + 5) ^ 2 + 28 * ((m : ℚ) + 5) - 12) * ∑ k ∈ range (m + 4), f (m + 4) k +
      (14 * ((m : ℚ) + 5) ^ 2 - 56 * ((m : ℚ) + 5) + 40) * ∑ k ∈ range (m + 3), f (m + 3) k +
      (-8 * ((m : ℚ) + 5) ^ 2 + 36 * ((m : ℚ) + 5) - 28) * ∑ k ∈ range (m + 2), f (m + 2) k +
      (((m : ℚ) + 5) ^ 2 - 5 * ((m : ℚ) + 5) + 4) * ∑ k ∈ range (m + 1), f (m + 1) k = 0 := by
  set x : ℚ := (m : ℚ) + 5 with hx
  rw [← sum_ext (m + 4) (m + 5) (by omega), ← sum_ext (m + 3) (m + 5) (by omega),
    ← sum_ext (m + 2) (m + 5) (by omega), ← sum_ext (m + 1) (m + 5) (by omega),
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  have hstep : ∀ k ∈ range (m + 5),
      (x ^ 2 - 3 * x) * f (m + 5) k + (-8 * x ^ 2 + 28 * x - 12) * f (m + 4) k +
        (14 * x ^ 2 - 56 * x + 40) * f (m + 3) k + (-8 * x ^ 2 + 36 * x - 28) * f (m + 2) k +
        (x ^ 2 - 5 * x + 4) * f (m + 1) k =
      Rc x ((k + 1 : ℕ) : ℚ) * f (m + 5) (k + 1) - Rc x (k : ℚ) * f (m + 5) k := by
    intro k _
    have e4 : f (m + 4) k = f (m + 5) k * rh x k := by
      rw [show m + 4 = (m + 3) + 1 by ring, f_pred (m + 3) k]
      congr 2
      rw [hx]
      push_cast
      ring
    have e3 : f (m + 3) k = f (m + 4) k * rh (x - 1) k := by
      rw [show m + 3 = (m + 2) + 1 by ring, f_pred (m + 2) k]
      congr 2
      rw [hx]
      push_cast
      ring
    have e2 : f (m + 2) k = f (m + 3) k * rh (x - 2) k := by
      rw [show m + 2 = (m + 1) + 1 by ring, f_pred (m + 1) k]
      congr 2
      rw [hx]
      push_cast
      ring
    have e1 : f (m + 1) k = f (m + 2) k * rh (x - 3) k := by
      rw [f_pred m k]
      congr 2
      rw [hx]
      ring
    have es : f (m + 5) (k + 1) = f (m + 5) k * sg x k := by
      rw [f_succ, hx]
      push_cast
      ring_nf
    have hx5 : (5 : ℚ) ≤ x := by rw [hx]; linarith [(Nat.cast_nonneg m : (0 : ℚ) ≤ m)]
    have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    have hkey := key x k hx5 hk0
    rw [e1, e2, e3, e4, es]
    push_cast
    linear_combination (f (m + 5) k) * hkey
  rw [Finset.sum_congr rfl hstep, Finset.sum_range_sub (fun k => Rc x (k : ℚ) * f (m + 5) k)]
  simp only [f_out (m + 5) (m + 5) le_rfl, mul_zero, Nat.cast_zero]
  simp [Rc]

theorem a_small : a 0 = 0 ∧ a 1 = 3 ∧ a 2 = 10 ∧ a 3 = 41 ∧ a 4 = 196 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [a, Finset.sum_range_succ, Nat.choose_succ_succ]

theorem rec (n : ℕ) (hn : 4 ≤ n) :
    ((n : ℤ) ^ 2 - 3 * (n : ℤ)) * a n + (-8 * (n : ℤ) ^ 2 + 28 * (n : ℤ) - 12) * a (n - 1)
      + (14 * (n : ℤ) ^ 2 - 56 * (n : ℤ) + 40) * a (n - 2)
      + (-8 * (n : ℤ) ^ 2 + 36 * (n : ℤ) - 28) * a (n - 3)
      + ((n : ℤ) ^ 2 - 5 * (n : ℤ) + 4) * a (n - 4) = 0 := by
  rcases Nat.eq_or_lt_of_le hn with rfl | h5
  · obtain ⟨h0, h1, h2, h3, h4⟩ := a_small
    norm_num [h0, h1, h2, h3, h4]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
    have h := tele m
    have hq : ((((m + 5 : ℕ) : ℤ) ^ 2 - 3 * ((m + 5 : ℕ) : ℤ)) * a (m + 5)
        + (-8 * ((m + 5 : ℕ) : ℤ) ^ 2 + 28 * ((m + 5 : ℕ) : ℤ) - 12) * a (m + 4)
        + (14 * ((m + 5 : ℕ) : ℤ) ^ 2 - 56 * ((m + 5 : ℕ) : ℤ) + 40) * a (m + 3)
        + (-8 * ((m + 5 : ℕ) : ℤ) ^ 2 + 36 * ((m + 5 : ℕ) : ℤ) - 28) * a (m + 2)
        + (((m + 5 : ℕ) : ℤ) ^ 2 - 5 * ((m + 5 : ℕ) : ℤ) + 4) * a (m + 1) : ℤ) = (0 : ℚ) := by
      push_cast
      rw [A_eq, A_eq, A_eq, A_eq, A_eq]
      push_cast
      linear_combination 2 * h
    exact_mod_cast hq

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a236407.main := OMA.Helpers.rec
