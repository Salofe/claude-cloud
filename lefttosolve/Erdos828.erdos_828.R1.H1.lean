import OMAReductions.R_Erdos828_erdos_828_R1

/-!
# Step H1 of the reduction Erdos828.erdos_828.R1

For `a = 0`, or `a = -m` with `0 < m` and `φ m ∣ m`, there are infinitely many `n` with
`φ n ∣ n + a`. In both cases we show that the set is not bounded above.

* `a = 0`: for every `B`, the number `n = 2 ^ (B + 1)` has `φ n = 2 ^ B`, which divides `n`,
  and `n > B`.
* `a = -m`: for every `B`, take a prime `p ≥ m + B + 1`. Since `p > m`, `p` does not divide `m`,
  so `φ (m * p) = φ m * (p - 1)`. Writing `m = φ m * c`, we get
  `m * p - m = m * (p - 1) = φ m * (p - 1) * c`, so `φ (m * p) ∣ m * p - m`, and `m * p ≥ p > B`.

Only Mathlib and the definition `H1` of the reduction are used; no upstream theorem is used.
-/

namespace OMA.Helpers

/-- A set of natural numbers with an element above every bound is infinite. -/
theorem erdos828_infinite_of_unbounded {S : Set ℕ} (h : ∀ B : ℕ, ∃ n ∈ S, B < n) :
    S.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨n, hn, hBn⟩ := h B
  have hnB : n ≤ B := hB hn
  omega

/-- The case `a = 0`: `φ (2 ^ (B + 1)) = 2 ^ B` divides `2 ^ (B + 1)`. -/
theorem erdos828_totient_two_pow_dvd (B : ℕ) :
    ((Nat.totient (2 ^ (B + 1)) : ℕ) : ℤ) ∣ ((2 ^ (B + 1) : ℕ) : ℤ) + 0 := by
  rw [add_zero, Nat.totient_prime_pow_succ Nat.prime_two B]
  exact ⟨2, by push_cast; ring⟩

/-- The case `a = -m`: if `0 < m`, `φ m ∣ m` and `p` is a prime with `m < p`, then
`φ (m * p) ∣ m * p - m`. -/
theorem erdos828_totient_mul_prime_dvd {m p : ℕ} (hm : 0 < m) (hdvd : Nat.totient m ∣ m)
    (hp : p.Prime) (hmp : m < p) :
    ((Nat.totient (m * p) : ℕ) : ℤ) ∣ ((m * p : ℕ) : ℤ) + -(m : ℤ) := by
  have hcop : Nat.Coprime m p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have hpm : p ≤ m := Nat.le_of_dvd hm h
    omega
  rw [Nat.totient_mul hcop, Nat.totient_prime hp]
  obtain ⟨c, hc⟩ := hdvd
  have hcZ : (m : ℤ) = (Nat.totient m : ℤ) * c := by exact_mod_cast hc
  refine ⟨c, ?_⟩
  push_cast [Nat.cast_sub hp.one_lt.le]
  linear_combination ((p : ℤ) - 1) * hcZ

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos828_erdos_828_R1.H1 := by
  intro a ha
  apply OMA.Helpers.erdos828_infinite_of_unbounded
  intro B
  rcases ha with rfl | ⟨m, hm, hdvd, rfl⟩
  · refine ⟨2 ^ (B + 1), OMA.Helpers.erdos828_totient_two_pow_dvd B, ?_⟩
    have h1 : B < 2 ^ B := Nat.lt_two_pow_self
    have h2 : 2 ^ B ≤ 2 ^ (B + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (m + B + 1)
    refine ⟨m * p, OMA.Helpers.erdos828_totient_mul_prime_dvd hm hdvd hp (by omega), ?_⟩
    have h1 : p ≤ m * p := Nat.le_mul_of_pos_left p hm
    omega
