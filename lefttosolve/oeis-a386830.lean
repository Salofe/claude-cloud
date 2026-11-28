import OMAStatements.S_oeis_a386830

/-!
Proof of Mathar's recurrence for A386830, a(n) = Sum_{k=0..n} 3^k 2^(n-k) C(3n+1,k) C(3n-k,n-k),
by creative telescoping (a Zeilberger certificate, found by computer algebra and checked here).

For `k ≤ N` the summand is the hypergeometric term
  `F(N, k) = 3^k 2^(N-k) (3N+1)! / (k! (N-k)! (2N)! (3N+1-k))`
(`term_eq`); set `F(N, k) = 0` for `k > N` (`f`). Its ratios are rational functions:
`F(N, k+1) = F(N, k) sg(N, k)` and `F(N-1, k) = F(N, k) rh(N, k)` (`f_succ`, `f_pred`), for
every `k`, both sides vanishing at the boundary. With `x = n ≥ 3` and the certificate
`Rc(x, k) = -2k Np(x, k) / ((k-3x)(3x-1)(3x+1)(k-3x+1)(k-3x+2)(k-3x+3)(k-3x+4))`, where `Np` is an
explicit polynomial of degree 8, the identity of rational functions
  `p0 + p1 rh(x,k) + p2 rh(x,k) rh(x-1,k) = Rc(x,k+1) sg(x,k) - Rc(x,k)`
(`key`, all denominators being nonzero for `0 ≤ k ≤ x`) gives, with `G k = Rc(n,k) F(n,k)`,
  `p0 F(n,k) + p1 F(n-1,k) + p2 F(n-2,k) = G (k+1) - G k`   for `0 ≤ k ≤ n`.
Summing over `k = 0..n` telescopes to `G (n+1) - G 0 = 0` (`F(n, n+1) = 0` and `Rc(n, 0) = 0`),
which is the recurrence for `n ≥ 3`; the case `n = 2` is a direct computation.
-/

namespace OMA.Helpers

open OMA.S_oeis_a386830 Finset

/-- The ratio `F(n, k+1) / F(n, k)`. -/
noncomputable def sg (x y : ℚ) : ℚ := 3 * (x - y) * (3 * x + 1 - y) / (2 * (y + 1) * (3 * x - y))

/-- The ratio `F(n-1, k) / F(n, k)`. -/
noncomputable def rh (x y : ℚ) : ℚ :=
  (2 * x) * (2 * x - 1) * (x - y) * (3 * x + 1 - y) /
    (2 * (3 * x + 1) * (3 * x) * (3 * x - 1) * (3 * x - 2 - y))

/-- The numerator of the certificate. -/
def Np (x y : ℚ) : ℚ :=
  -8748*x^8 + 5832*x^7*y + 58320*x^7 + 4860*x^6*y^2 - 54432*x^6*y - 140211*x^6 - 6480*x^5*y^3 + 1944*x^5*y^2 + 144504*x^5*y + 153657*x^5 + 2700*x^4*y^4 + 14688*x^4*y^3 - 39879*x^4*y^2 - 159597*x^4*y - 74439*x^4 - 504*x^3*y^5 - 6624*x^3*y^4 - 5256*x^3*y^3 + 54450*x^3*y^2 + 77346*x^3*y + 7371*x^3 + 36*x^2*y^6 + 1152*x^2*y^5 + 4287*x^2*y^4 - 4938*x^2*y^3 - 27144*x^2*y^2 - 11193*x^2*y + 4818*x^2 - 72*x*y^6 - 656*x*y^5 - 699*x*y^4 + 3406*x*y^3 + 4581*x*y^2 - 2072*x*y - 1008*x + 27*y^6 + 103*y^5 - 65*y^4 - 535*y^3 + 38*y^2 + 432*y

/-- The certificate. -/
noncomputable def Rc (x y : ℚ) : ℚ :=
  -2 * y * Np x y / ((y - 3 * x) * (3 * x - 1) * (3 * x + 1) * (y - 3 * x + 1) * (y - 3 * x + 2) *
    (y - 3 * x + 3) * (y - 3 * x + 4))

set_option maxRecDepth 20000 in
theorem key (x y : ℚ) (hx : 3 ≤ x) (hy0 : 0 ≤ y) (hy : y ≤ x) :
    (16 * x ^ 2 - 24 * x) + (-648 * x ^ 2 + 1242 * x - 480) * rh x y +
      (3645 * x ^ 2 - 7290 * x + 3240) * (rh x y * rh (x - 1) y) =
      Rc x (y + 1) * sg x y - Rc x y := by
  have p0 : (y + 1 : ℚ) ≠ 0 := by intro h; linarith
  have p1 : (3 * x - y : ℚ) ≠ 0 := by intro h; linarith
  have p2 : (x * 3 - y : ℚ) ≠ 0 := by intro h; linarith
  have p3 : (3 * x + 1 : ℚ) ≠ 0 := by intro h; linarith
  have p4 : (x * 3 + 1 : ℚ) ≠ 0 := by intro h; linarith
  have p5 : (3 * x : ℚ) ≠ 0 := by intro h; linarith
  have p6 : (x * 3 : ℚ) ≠ 0 := by intro h; linarith
  have p7 : (3 * x - 1 : ℚ) ≠ 0 := by intro h; linarith
  have p8 : (x * 3 - 1 : ℚ) ≠ 0 := by intro h; linarith
  have p9 : (3 * x - 2 - y : ℚ) ≠ 0 := by intro h; linarith
  have p10 : (x * 3 - 2 - y : ℚ) ≠ 0 := by intro h; linarith
  have p11 : (3 * (x - 1) + 1 : ℚ) ≠ 0 := by intro h; linarith
  have p12 : (3 * (x - 1) : ℚ) ≠ 0 := by intro h; linarith
  have p13 : (3 * (x - 1) - 1 : ℚ) ≠ 0 := by intro h; linarith
  have p14 : (3 * (x - 1) - 2 - y : ℚ) ≠ 0 := by intro h; linarith
  have p15 : (x : ℚ) ≠ 0 := by intro h; linarith
  have p16 : (x - 1 : ℚ) ≠ 0 := by intro h; linarith
  have p18 : (y - 3 * x : ℚ) ≠ 0 := by intro h; linarith
  have p19 : (y - x * 3 : ℚ) ≠ 0 := by intro h; linarith
  have p20 : (y - 3 * x + 1 : ℚ) ≠ 0 := by intro h; linarith
  have p21 : (y - x * 3 + 1 : ℚ) ≠ 0 := by intro h; linarith
  have p22 : (y - 3 * x + 2 : ℚ) ≠ 0 := by intro h; linarith
  have p23 : (y - x * 3 + 2 : ℚ) ≠ 0 := by intro h; linarith
  have p24 : (y - 3 * x + 3 : ℚ) ≠ 0 := by intro h; linarith
  have p25 : (y - x * 3 + 3 : ℚ) ≠ 0 := by intro h; linarith
  have p26 : (y - 3 * x + 4 : ℚ) ≠ 0 := by intro h; linarith
  have p27 : (y - x * 3 + 4 : ℚ) ≠ 0 := by intro h; linarith
  have p28 : (y + 1 - 3 * x : ℚ) ≠ 0 := by intro h; linarith
  have p29 : (y + 1 - x * 3 : ℚ) ≠ 0 := by intro h; linarith
  have p30 : (y + 1 - 3 * x + 1 : ℚ) ≠ 0 := by intro h; linarith
  have p31 : (y + 1 - x * 3 + 1 : ℚ) ≠ 0 := by intro h; linarith
  have p32 : (y + 1 - 3 * x + 2 : ℚ) ≠ 0 := by intro h; linarith
  have p33 : (y + 1 - x * 3 + 2 : ℚ) ≠ 0 := by intro h; linarith
  have p34 : (y + 1 - 3 * x + 3 : ℚ) ≠ 0 := by intro h; linarith
  have p35 : (y + 1 - x * 3 + 3 : ℚ) ≠ 0 := by intro h; linarith
  have p36 : (y + 1 - 3 * x + 4 : ℚ) ≠ 0 := by intro h; linarith
  have p37 : (y + 1 - x * 3 + 4 : ℚ) ≠ 0 := by intro h; linarith
  unfold rh sg Rc Np
  field_simp
  ring

/-- The summand in factorial form. -/
noncomputable def ff (N K : ℕ) : ℚ :=
  (3 : ℚ) ^ K * 2 ^ (N - K) * ((3 * N + 1).factorial : ℚ) /
    ((K.factorial : ℚ) * ((N - K).factorial : ℚ) * ((2 * N).factorial : ℚ) *
      ((3 * N + 1 - K : ℕ) : ℚ))

/-- The summand, extended by zero. -/
noncomputable def f (N K : ℕ) : ℚ := if K ≤ N then ff N K else 0

theorem term_eq (N K : ℕ) (h : K ≤ N) :
    (3 : ℚ) ^ K * (2 : ℚ) ^ (N - K) * ((3 * N + 1).choose K : ℚ) *
      ((3 * N - K).choose (N - K) : ℚ) = ff N K := by
  obtain ⟨j, rfl⟩ : ∃ j, N = K + j := ⟨N - K, by omega⟩
  unfold ff
  rw [show K + j - K = j by omega, show 3 * (K + j) - K = 2 * K + 3 * j by omega,
    show 3 * (K + j) + 1 - K = 2 * K + 3 * j + 1 by omega,
    Nat.cast_choose ℚ (show K ≤ 3 * (K + j) + 1 by omega),
    Nat.cast_choose ℚ (show j ≤ 2 * K + 3 * j by omega),
    show 3 * (K + j) + 1 - K = 2 * K + 3 * j + 1 by omega,
    show 2 * K + 3 * j - j = 2 * (K + j) by omega, Nat.factorial_succ (2 * K + 3 * j)]
  push_cast
  field_simp

theorem f_succ (N K : ℕ) : f N (K + 1) = f N K * sg N K := by
  unfold f
  by_cases h : K + 1 ≤ N
  · rw [if_pos h, if_pos (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, N = K + 1 + j := ⟨N - (K + 1), by omega⟩
    unfold ff sg
    rw [show K + 1 + j - (K + 1) = j by omega, show K + 1 + j - K = j + 1 by omega,
      show 3 * (K + 1 + j) + 1 - (K + 1) = 2 * K + 3 * j + 3 by omega,
      show 3 * (K + 1 + j) + 1 - K = 2 * K + 3 * j + 4 by omega,
      Nat.factorial_succ K, Nat.factorial_succ j]
    push_cast
    have hK : (0 : ℚ) ≤ K := Nat.cast_nonneg K
    have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    have n1 : (3 * ((K : ℚ) + 1 + j) - K) ≠ 0 := by intro h; linarith
    have n2 : (2 * (K : ℚ) + 3 * j + 3) ≠ 0 := by intro h; linarith
    have n3 : (2 * (K : ℚ) + 3 * j + 4) ≠ 0 := by intro h; linarith
    have n4 : ((K : ℚ) + 1) ≠ 0 := by intro h; linarith
    have n5 : ((j : ℚ) + 1) ≠ 0 := by intro h; linarith
    field_simp
    ring
  · rw [if_neg h]
    by_cases h' : K ≤ N
    · obtain rfl : K = N := by omega
      simp [sg]
    · rw [if_neg h']
      simp

theorem f_pred (M K : ℕ) : f M K = f (M + 1) K * rh ((M : ℚ) + 1) K := by
  unfold f
  by_cases h : K ≤ M
  · rw [if_pos h, if_pos (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, M = K + j := ⟨M - K, by omega⟩
    unfold ff rh
    rw [show K + j - K = j by omega, show K + j + 1 - K = j + 1 by omega,
      show 3 * (K + j) + 1 - K = 2 * K + 3 * j + 1 by omega,
      show 3 * (K + j + 1) + 1 - K = 2 * K + 3 * j + 4 by omega,
      show 3 * (K + j + 1) + 1 = 3 * (K + j) + 1 + 1 + 1 + 1 by ring,
      show 2 * (K + j + 1) = 2 * (K + j) + 1 + 1 by ring,
      Nat.factorial_succ (3 * (K + j) + 1 + 1 + 1), Nat.factorial_succ (3 * (K + j) + 1 + 1),
      Nat.factorial_succ (3 * (K + j) + 1), Nat.factorial_succ (2 * (K + j) + 1),
      Nat.factorial_succ (2 * (K + j)), Nat.factorial_succ j]
    push_cast
    have hK : (0 : ℚ) ≤ K := Nat.cast_nonneg K
    have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    have n1 : (3 * ((K : ℚ) + j + 1) - 1) ≠ 0 := by intro h; linarith
    have n2 : (3 * ((K : ℚ) + j + 1) - 2 - K) ≠ 0 := by intro h; linarith
    have n3 : (3 * ((K : ℚ) + j + 1) + 1) ≠ 0 := by intro h; linarith
    have n4 : (3 * ((K : ℚ) + j + 1)) ≠ 0 := by intro h; linarith
    have n5 : (2 * (K : ℚ) + 3 * j + 1) ≠ 0 := by intro h; linarith
    have n6 : (2 * (K : ℚ) + 3 * j + 4) ≠ 0 := by intro h; linarith
    have n7 : ((j : ℚ) + 1) ≠ 0 := by intro h; linarith
    field_simp
    ring
  · rw [if_neg h]
    by_cases h' : K ≤ M + 1
    · obtain rfl : K = M + 1 := by omega
      simp [rh]
    · rw [if_neg h']
      simp

theorem A_eq (N : ℕ) : ((a N : ℤ) : ℚ) = ∑ k ∈ range (N + 1), f N k := by
  unfold a
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ N := by
    rw [Finset.mem_range] at hk
    omega
  rw [f, if_pos hk', ← term_eq N k hk']

theorem f_out (N K : ℕ) (h : N < K) : f N K = 0 := by
  unfold f
  rw [if_neg (by omega)]

theorem tele (m : ℕ) :
    (16 * ((m : ℚ) + 3) ^ 2 - 24 * ((m : ℚ) + 3)) * ∑ k ∈ range (m + 3 + 1), f (m + 3) k +
      (-648 * ((m : ℚ) + 3) ^ 2 + 1242 * ((m : ℚ) + 3) - 480) *
        ∑ k ∈ range (m + 2 + 1), f (m + 2) k +
      (3645 * ((m : ℚ) + 3) ^ 2 - 7290 * ((m : ℚ) + 3) + 3240) *
        ∑ k ∈ range (m + 1 + 1), f (m + 1) k = 0 := by
  set x : ℚ := (m : ℚ) + 3 with hx
  have e2 : ∑ k ∈ range (m + 2 + 1), f (m + 2) k = ∑ k ∈ range (m + 4), f (m + 2) k := by
    rw [show m + 4 = m + 2 + 1 + 1 by omega, Finset.sum_range_succ _ (m + 2 + 1),
      f_out (m + 2) (m + 2 + 1) (by omega), add_zero]
  have e1 : ∑ k ∈ range (m + 1 + 1), f (m + 1) k = ∑ k ∈ range (m + 4), f (m + 1) k := by
    rw [show m + 4 = m + 1 + 1 + 1 + 1 by omega, Finset.sum_range_succ _ (m + 1 + 1 + 1),
      Finset.sum_range_succ _ (m + 1 + 1), f_out (m + 1) (m + 1 + 1) (by omega),
      f_out (m + 1) (m + 1 + 1 + 1) (by omega), add_zero, add_zero]
  rw [e2, e1, show m + 3 + 1 = m + 4 by omega, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hstep : ∀ k ∈ range (m + 4),
      (16 * x ^ 2 - 24 * x) * f (m + 3) k + (-648 * x ^ 2 + 1242 * x - 480) * f (m + 2) k +
        (3645 * x ^ 2 - 7290 * x + 3240) * f (m + 1) k =
      Rc x ((k + 1 : ℕ) : ℚ) * f (m + 3) (k + 1) - Rc x (k : ℚ) * f (m + 3) k := by
    intro k hk
    rw [Finset.mem_range] at hk
    have h2 : f (m + 2) k = f (m + 3) k * rh x k := by
      rw [f_pred (m + 2) k]
      congr 2
      rw [hx]
      push_cast
      ring
    have h1' : f (m + 1) k = f (m + 2) k * rh (x - 1) k := by
      rw [f_pred (m + 1) k]
      congr 2
      rw [hx]
      push_cast
      ring
    have h1 : f (m + 1) k = f (m + 3) k * (rh x k * rh (x - 1) k) := by
      rw [h1', h2]
      ring
    have h3 : f (m + 3) (k + 1) = f (m + 3) k * sg x k := by
      rw [f_succ, hx]
      push_cast
      ring_nf
    have hk3 : (3 : ℚ) ≤ x := by rw [hx]; linarith [(Nat.cast_nonneg m : (0 : ℚ) ≤ m)]
    have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    have hkx : (k : ℚ) ≤ x := by
      rw [hx]
      have : (k : ℚ) ≤ (m : ℚ) + 3 := by exact_mod_cast (show k ≤ m + 3 by omega)
      exact this
    have hkey := key x k hk3 hk0 hkx
    rw [h2, h1, h3]
    push_cast
    linear_combination (f (m + 3) k) * hkey
  rw [Finset.sum_congr rfl hstep, Finset.sum_range_sub (fun k => Rc x (k : ℚ) * f (m + 3) k)]
  simp only [f_out (m + 3) (m + 4) (by omega), mul_zero, Nat.cast_zero]
  simp [Rc]

theorem a_small : a 0 = 1 ∧ a 1 = 18 ∧ a 2 = 459 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [a, Finset.sum_range_succ, Nat.choose_succ_succ]

theorem rec_two :
    (16 * ((2 : ℕ) : ℤ) ^ 2 - 24 * ((2 : ℕ) : ℤ)) * a 2
      + (-648 * ((2 : ℕ) : ℤ) ^ 2 + 1242 * ((2 : ℕ) : ℤ) - 480) * a 1
      + (3645 * ((2 : ℕ) : ℤ) ^ 2 - 7290 * ((2 : ℕ) : ℤ) + 3240) * a 0 = 0 := by
  obtain ⟨h0, h1, h2⟩ := a_small
  rw [h0, h1, h2]
  norm_num

theorem rec_ge (m : ℕ) :
    (16 * ((m + 3 : ℕ) : ℤ) ^ 2 - 24 * ((m + 3 : ℕ) : ℤ)) * a (m + 3)
      + (-648 * ((m + 3 : ℕ) : ℤ) ^ 2 + 1242 * ((m + 3 : ℕ) : ℤ) - 480) * a (m + 2)
      + (3645 * ((m + 3 : ℕ) : ℤ) ^ 2 - 7290 * ((m + 3 : ℕ) : ℤ) + 3240) * a (m + 1) = 0 := by
  have h := tele m
  rw [← A_eq, ← A_eq, ← A_eq] at h
  have hq : (((16 * ((m + 3 : ℕ) : ℤ) ^ 2 - 24 * ((m + 3 : ℕ) : ℤ)) * a (m + 3)
    + (-648 * ((m + 3 : ℕ) : ℤ) ^ 2 + 1242 * ((m + 3 : ℕ) : ℤ) - 480) * a (m + 2)
    + (3645 * ((m + 3 : ℕ) : ℤ) ^ 2 - 7290 * ((m + 3 : ℕ) : ℤ) + 3240) * a (m + 1) : ℤ) : ℚ)
      = 0 := by
    push_cast
    linear_combination h
  exact (Int.cast_eq_zero (α := ℚ)).mp hq

theorem rec (n : ℕ) (hn : 2 ≤ n) :
    (16 * (n : ℤ) ^ 2 - 24 * (n : ℤ)) * a n
      + (-648 * (n : ℤ) ^ 2 + 1242 * (n : ℤ) - 480) * a (n - 1)
      + (3645 * (n : ℤ) ^ 2 - 7290 * (n : ℤ) + 3240) * a (n - 2) = 0 := by
  rcases Nat.eq_or_lt_of_le hn with rfl | h3
  · exact rec_two
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
    exact rec_ge m

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a386830.main := OMA.Helpers.rec
