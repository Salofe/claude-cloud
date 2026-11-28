import OMAStatements.S_oeis_a270530
import Mathlib

/-!
Proof of Mathar's recurrence for A270530, a(n) = Sum_{k=0..n} C(2k,k)/(k+1) C(2n+2,n-k),
by creative telescoping (a Gosper certificate found by computer algebra and checked here).

Write `f(N, k)` for the summand (zero for `k > N`). Its ratios `f(N, k+1) / f(N, k) = sg(N, k)`
and `f(N-1, k) / f(N, k) = rh(N, k)` are rational (`f_succ`, `f_pred`). With the certificate
`Rc`, the rational identity `key` gives, for `n ≥ 4`,
  `p0 f(n,k) + p1 f(n-1,k) + p2 f(n-2,k) + p3 f(n-3,k) + p4 f(n-4,k) = G(k+1) - G(k)`
with `G(k) = Rc(n,k) f(n,k)`; summing over `k ≤ n` telescopes to `0` (`f(n,n+1) = 0`,
`Rc(n,0) = 0`).
-/

namespace OMA.Helpers

open OMA.S_oeis_a270530 Finset

/-- The summand `C(2K,K)/(K+1) C(2N+2,N-K)`, set to zero for `K > N`. -/
def f (N K : ℕ) : ℚ :=
  if K ≤ N then ((2 * K).choose K : ℚ) / ((K : ℚ) + 1) * ((2 * N + 2).choose (N - K) : ℚ) else 0

/-- The ratio `f(N, K+1) / f(N, K)`. -/
def sg (x y : ℚ) : ℚ := 2 * (2 * y + 1) * (x - y) / ((y + 2) * (x + y + 3))

/-- The ratio `f(N-1, K) / f(N, K)`. -/
def rh (x y : ℚ) : ℚ := (x - y) * (x + y + 2) / ((2 * x + 2) * (2 * x + 1))

theorem term (K j : ℕ) :
    f (K + j) K = ((2 * K).factorial : ℚ) / ((K.factorial : ℚ) ^ 2 * ((K : ℚ) + 1)) *
      ((2 * K + 2 * j + 2).factorial : ℚ) / ((j.factorial : ℚ) * ((2 * K + j + 2).factorial : ℚ)) := by
  unfold f
  rw [if_pos (by omega), show K + j - K = j by omega,
    show 2 * (K + j) + 2 = 2 * K + 2 * j + 2 by ring,
    Nat.cast_choose ℚ (show K ≤ 2 * K by omega),
    Nat.cast_choose ℚ (show j ≤ 2 * K + 2 * j + 2 by omega),
    show 2 * K - K = K by omega, show 2 * K + 2 * j + 2 - j = 2 * K + j + 2 by omega]
  field_simp

theorem f_succ (N K : ℕ) : f N (K + 1) = f N K * sg N K := by
  by_cases h : K + 1 ≤ N
  · obtain ⟨j, rfl⟩ : ∃ j, N = K + 1 + j := ⟨N - (K + 1), by omega⟩
    have h2 : f (K + 1 + j) K = ((2 * K).factorial : ℚ) / ((K.factorial : ℚ) ^ 2 * ((K : ℚ) + 1)) *
        ((2 * K + 2 * j + 4).factorial : ℚ) /
          (((j + 1).factorial : ℚ) * ((2 * K + j + 3).factorial : ℚ)) := by
      have := term K (j + 1)
      rw [show K + (j + 1) = K + 1 + j by ring, show 2 * K + 2 * (j + 1) + 2 = 2 * K + 2 * j + 4 by ring,
        show 2 * K + (j + 1) + 2 = 2 * K + j + 3 by ring] at this
      exact this
    have h1 : f (K + 1 + j) (K + 1) = ((2 * K + 2).factorial : ℚ) /
        (((K + 1).factorial : ℚ) ^ 2 * ((K : ℚ) + 2)) *
        ((2 * K + 2 * j + 4).factorial : ℚ) /
          ((j.factorial : ℚ) * ((2 * K + j + 4).factorial : ℚ)) := by
      have := term (K + 1) j
      rw [show 2 * (K + 1) = 2 * K + 2 by ring, show 2 * K + 2 + 2 * j + 2 = 2 * K + 2 * j + 4 by ring,
        show 2 * K + 2 + j + 2 = 2 * K + j + 4 by ring] at this
      rw [this]
      push_cast
      ring_nf
    rw [h1, h2, Nat.factorial_succ (2 * K + 1), Nat.factorial_succ (2 * K),
      Nat.factorial_succ (2 * K + j + 3), Nat.factorial_succ K, Nat.factorial_succ j]
    unfold sg
    push_cast
    have hK : (0 : ℚ) ≤ K := Nat.cast_nonneg K
    have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    have n1 : ((K : ℚ) + 2) ≠ 0 := by intro h; linarith
    have n2 : ((K : ℚ) + 1) ≠ 0 := by intro h; linarith
    have n3 : ((j : ℚ) + 1) ≠ 0 := by intro h; linarith
    have n4 : (2 * (K : ℚ) + j + 3 + 1) ≠ 0 := by intro h; linarith
    have n5 : ((K : ℚ) + 1 + j + K + 3) ≠ 0 := by intro h; linarith
    field_simp
    ring
  · have h0 : f N (K + 1) = 0 := by unfold f; rw [if_neg h]
    rw [h0]
    by_cases h' : K ≤ N
    · obtain rfl : N = K := by omega
      simp [sg]
    · unfold f
      rw [if_neg h']
      simp

theorem f_pred (M K : ℕ) : f M K = f (M + 1) K * rh ((M : ℚ) + 1) K := by
  by_cases h : K ≤ M
  · obtain ⟨j, rfl⟩ : ∃ j, M = K + j := ⟨M - K, by omega⟩
    have h2 : f (K + j + 1) K = ((2 * K).factorial : ℚ) / ((K.factorial : ℚ) ^ 2 * ((K : ℚ) + 1)) *
        ((2 * K + 2 * j + 4).factorial : ℚ) /
          (((j + 1).factorial : ℚ) * ((2 * K + j + 3).factorial : ℚ)) := by
      have := term K (j + 1)
      rw [show K + (j + 1) = K + j + 1 by ring, show 2 * K + 2 * (j + 1) + 2 = 2 * K + 2 * j + 4 by ring,
        show 2 * K + (j + 1) + 2 = 2 * K + j + 3 by ring] at this
      exact this
    rw [term K j, h2, Nat.factorial_succ (2 * K + 2 * j + 3), Nat.factorial_succ (2 * K + 2 * j + 2),
      Nat.factorial_succ (2 * K + j + 2), Nat.factorial_succ j]
    unfold rh
    push_cast
    have hK : (0 : ℚ) ≤ K := Nat.cast_nonneg K
    have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    have n1 : ((K : ℚ) + 1) ≠ 0 := by intro h; linarith
    have n3 : ((j : ℚ) + 1) ≠ 0 := by intro h; linarith
    have n4 : (2 * ((K : ℚ) + j + 1) + 2) ≠ 0 := by intro h; linarith
    have n5 : (2 * ((K : ℚ) + j + 1) + 1) ≠ 0 := by intro h; linarith
    have n6 : (2 * (K : ℚ) + 2 * j + 3 + 1) ≠ 0 := by intro h; linarith
    have n7 : (2 * (K : ℚ) + 2 * j + 2 + 1) ≠ 0 := by intro h; linarith
    have n8 : (2 * (K : ℚ) + j + 2 + 1) ≠ 0 := by intro h; linarith
    field_simp
    ring
  · have h0 : f M K = 0 := by unfold f; rw [if_neg h]
    rw [h0]
    by_cases h' : K ≤ M + 1
    · obtain rfl : K = M + 1 := by omega
      simp only [rh]
      push_cast
      rw [show (M : ℚ) + 1 - (M + 1) = 0 by ring]
      simp
    · unfold f
      rw [if_neg h']
      simp


/-- The numerator polynomial of the certificate. -/
def Q (x y : ℚ) : ℚ :=
  (25*y^5 + 15*y^4*x + 55*y^4 - 5*y^3*x^2 - 25*y^3*x + 45*y^3 - 3*y^2*x^3 - 15*y^2*x^2 - 81*y^2*x + 29*y^2 + y*x^3 - 16*y*x^2 - 39*y*x + 14*y - 4*x^3 + 6*x^2 - 2*x)

/-- The certificate. -/
def Rc (x y : ℚ) : ℚ :=
  -y * (y + 1) * (y + x + 2) * Q x y / (4 * x * (x - 1) * (x + 1) * (2 * x - 1) * (2 * x + 1))

set_option maxRecDepth 20000 in
theorem key (x y : ℚ) (hx : 4 ≤ x) (hy0 : 0 ≤ y) :
    (4 * x ^ 3 + 10 * x ^ 2 + 6 * x) + (-77 * x ^ 3 - 27 * x ^ 2 + 4 * x) * rh x y + (549 * x ^ 3 - 987 * x ^ 2 + 686 * x - 168) * (rh x y * rh (x - 1) y) +
      (-1720 * x ^ 3 + 6740 * x ^ 2 - 9040 * x + 4200) * (rh x y * rh (x - 1) y * rh (x - 2) y) +
      (2000 * x ^ 3 - 12000 * x ^ 2 + 23500 * x - 15000) * (rh x y * rh (x - 1) y * rh (x - 2) y * rh (x - 3) y) =
      Rc x (y + 1) * sg x y - Rc x y := by
  have q1 : (x : ℚ) ≠ 0 := by intro h; linarith
  have q2 : (x - 1 : ℚ) ≠ 0 := by intro h; linarith
  have q3 : (x + 1 : ℚ) ≠ 0 := by intro h; linarith
  have q4 : (2 * x - 1 : ℚ) ≠ 0 := by intro h; linarith
  have q5 : (2 * x + 1 : ℚ) ≠ 0 := by intro h; linarith
  have q6 : (2 * x + 2 : ℚ) ≠ 0 := by intro h; linarith
  have r1 : (2 * (x - 1) + 2 : ℚ) ≠ 0 := by intro h; linarith
  have r2 : (2 * (x - 1) + 1 : ℚ) ≠ 0 := by intro h; linarith
  have r3 : (2 * (x - 2) + 2 : ℚ) ≠ 0 := by intro h; linarith
  have r4 : (2 * (x - 2) + 1 : ℚ) ≠ 0 := by intro h; linarith
  have r5 : (2 * (x - 3) + 2 : ℚ) ≠ 0 := by intro h; linarith
  have r6 : (2 * (x - 3) + 1 : ℚ) ≠ 0 := by intro h; linarith
  have s1 : (y + 2 : ℚ) ≠ 0 := by intro h; linarith
  have s2 : (x + y + 3 : ℚ) ≠ 0 := by intro h; linarith
  have e1 : rh (x - 1) y = (x - 1 - y) * (x + y + 1) / ((2 * x) * (2 * x - 1)) := by
    unfold rh; ring_nf
  have e2 : rh (x - 2) y = (x - 2 - y) * (x + y) / ((2 * x - 2) * (2 * x - 3)) := by
    unfold rh; ring_nf
  have e3 : rh (x - 3) y = (x - 3 - y) * (x + y - 1) / ((2 * x - 4) * (2 * x - 5)) := by
    unfold rh; ring_nf
  have t1 : (2 * x : ℚ) ≠ 0 := by intro h; linarith
  have t2 : (2 * x - 2 : ℚ) ≠ 0 := by intro h; linarith
  have t3 : (2 * x - 3 : ℚ) ≠ 0 := by intro h; linarith
  have t4 : (2 * x - 4 : ℚ) ≠ 0 := by intro h; linarith
  have t5 : (2 * x - 5 : ℚ) ≠ 0 := by intro h; linarith
  have w0 : (x * 2 - 1 : ℚ) ≠ 0 := by intro h; linarith
  have w1 : (x * 2 + 1 : ℚ) ≠ 0 := by intro h; linarith
  have w2 : (x * 2 + 2 : ℚ) ≠ 0 := by intro h; linarith
  have w3 : (x * 2 : ℚ) ≠ 0 := by intro h; linarith
  have w4 : (x * 2 - 2 : ℚ) ≠ 0 := by intro h; linarith
  have w5 : (x * 2 - 3 : ℚ) ≠ 0 := by intro h; linarith
  have w6 : (x * 2 - 4 : ℚ) ≠ 0 := by intro h; linarith
  have w7 : (x * 2 - 5 : ℚ) ≠ 0 := by intro h; linarith
  have w8 : (x * 4 : ℚ) ≠ 0 := by intro h; linarith
  have w9 : (x - 2 : ℚ) ≠ 0 := by intro h; linarith
  have w10 : (x - 3 : ℚ) ≠ 0 := by intro h; linarith
  have w11 : (y + x + 3 : ℚ) ≠ 0 := by intro h; linarith
  have w12 : (x + 2 * y + 4 : ℚ) ≠ 0 := by intro h; linarith
  rw [e1, e2, e3]
  unfold rh sg Rc Q
  field_simp
  ring

theorem f_out (N K : ℕ) (h : N < K) : f N K = 0 := by
  unfold f
  rw [if_neg (by omega)]

theorem sum_ext (N L : ℕ) (h : N + 1 ≤ L) :
    ∑ k ∈ range L, f N k = ∑ k ∈ range (N + 1), f N k := by
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr h) ?_
  intro k _ hk
  rw [Finset.mem_range] at hk
  exact f_out N k (by omega)

theorem A_eq (N : ℕ) : a N = ∑ k ∈ range (N + 1), f N k := by
  unfold a
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [f, if_pos (by omega)]

theorem tele (m : ℕ) :
    (4 * ((m : ℚ) + 4) ^ 3 + 10 * ((m : ℚ) + 4) ^ 2 + 6 * ((m : ℚ) + 4)) * ∑ k ∈ range (m + 4 + 1), f (m + 4) k +
      (-77 * ((m : ℚ) + 4) ^ 3 - 27 * ((m : ℚ) + 4) ^ 2 + 4 * ((m : ℚ) + 4)) * ∑ k ∈ range (m + 3 + 1), f (m + 3) k +
      (549 * ((m : ℚ) + 4) ^ 3 - 987 * ((m : ℚ) + 4) ^ 2 + 686 * ((m : ℚ) + 4) - 168) * ∑ k ∈ range (m + 2 + 1), f (m + 2) k +
      (-1720 * ((m : ℚ) + 4) ^ 3 + 6740 * ((m : ℚ) + 4) ^ 2 - 9040 * ((m : ℚ) + 4) + 4200) * ∑ k ∈ range (m + 1 + 1), f (m + 1) k +
      (2000 * ((m : ℚ) + 4) ^ 3 - 12000 * ((m : ℚ) + 4) ^ 2 + 23500 * ((m : ℚ) + 4) - 15000) * ∑ k ∈ range (m + 1), f m k = 0 := by
  set x : ℚ := (m : ℚ) + 4 with hx
  rw [← sum_ext (m + 3) (m + 4 + 1) (by omega), ← sum_ext (m + 2) (m + 4 + 1) (by omega),
    ← sum_ext (m + 1) (m + 4 + 1) (by omega), ← sum_ext m (m + 4 + 1) (by omega),
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  have hstep : ∀ k ∈ range (m + 4 + 1),
      (4 * x ^ 3 + 10 * x ^ 2 + 6 * x) * f (m + 4) k + (-77 * x ^ 3 - 27 * x ^ 2 + 4 * x) * f (m + 3) k + (549 * x ^ 3 - 987 * x ^ 2 + 686 * x - 168) * f (m + 2) k + (-1720 * x ^ 3 + 6740 * x ^ 2 - 9040 * x + 4200) * f (m + 1) k + (2000 * x ^ 3 - 12000 * x ^ 2 + 23500 * x - 15000) * f m k =
      Rc x ((k + 1 : ℕ) : ℚ) * f (m + 4) (k + 1) - Rc x (k : ℚ) * f (m + 4) k := by
    intro k _
    have e3 : f (m + 3) k = f (m + 4) k * rh x k := by
      rw [f_pred (m + 3) k]
      congr 2
      rw [hx]
      push_cast
      ring
    have e2 : f (m + 2) k = f (m + 3) k * rh (x - 1) k := by
      rw [f_pred (m + 2) k]
      congr 2
      rw [hx]
      push_cast
      ring
    have e1 : f (m + 1) k = f (m + 2) k * rh (x - 2) k := by
      rw [f_pred (m + 1) k]
      congr 2
      rw [hx]
      push_cast
      ring
    have e0 : f m k = f (m + 1) k * rh (x - 3) k := by
      rw [f_pred m k]
      congr 2
      rw [hx]
      ring
    have es : f (m + 4) (k + 1) = f (m + 4) k * sg x k := by
      rw [f_succ, hx]
      push_cast
      ring_nf
    have hx4 : (4 : ℚ) ≤ x := by rw [hx]; linarith [(Nat.cast_nonneg m : (0 : ℚ) ≤ m)]
    have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    have hkey := key x k hx4 hk0
    rw [e0, e1, e2, e3, es]
    push_cast
    linear_combination (f (m + 4) k) * hkey
  rw [Finset.sum_congr rfl hstep, Finset.sum_range_sub (fun k => Rc x (k : ℚ) * f (m + 4) k)]
  simp only [f_out (m + 4) (m + 4 + 1) (by omega), mul_zero, Nat.cast_zero]
  simp [Rc]

theorem rec (n : ℕ) (hn : 4 ≤ n) :
    (4 * (n : ℚ) ^ 3 + 10 * (n : ℚ) ^ 2 + 6 * (n : ℚ)) * a n
      + (-77 * (n : ℚ) ^ 3 - 27 * (n : ℚ) ^ 2 + 4 * (n : ℚ)) * a (n - 1)
      + (549 * (n : ℚ) ^ 3 - 987 * (n : ℚ) ^ 2 + 686 * (n : ℚ) - 168) * a (n - 2)
      + (-1720 * (n : ℚ) ^ 3 + 6740 * (n : ℚ) ^ 2 - 9040 * (n : ℚ) + 4200) * a (n - 3)
      + (2000 * (n : ℚ) ^ 3 - 12000 * (n : ℚ) ^ 2 + 23500 * (n : ℚ) - 15000) * a (n - 4) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega,
    A_eq, A_eq, A_eq, A_eq, A_eq]
  have h := tele m
  push_cast
  linear_combination h

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a270530.main := OMA.Helpers.rec
