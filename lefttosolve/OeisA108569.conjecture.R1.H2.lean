import OMAReductions.R_OeisA108569_conjecture_R1

/-!
# Step H2 of the reduction OeisA108569.conjecture.R1

Let `n > 1` be odd with `φ n = φ (n + φ n)`, and let `p` be a prime with `p ^ 3 ∣ n`.
Write `n = p * m` with `m = n / p`, so `p ^ 2 ∣ m`. Since `p ∣ m`, multiplicativity at a
repeated prime gives `φ n = p * φ m`. Since `p ^ 2 ∣ m`, also `p ∣ φ m`, hence
`p ∣ m + φ m`, and therefore `n + φ n = p * (m + φ m)` has
`φ (n + φ n) = p * φ (m + φ m)`. Cancelling `p` gives `φ m = φ (m + φ m)`.
Finally `m` is odd (a factor of the odd `n`), `1 < p ^ 2 ≤ m` and `m < p * m = n`.

Only the upstream definition `OeisA108569.A` is used, together with Mathlib.
-/

namespace OMA.Helpers

/-- The descent step: if `p` is prime, `p ^ 2 ∣ m` and `p * m` satisfies the defining
equation of A108569, then so does `m`. -/
theorem a108569_descent {p m : ℕ} (hp : p.Prime) (hm : p ^ 2 ∣ m)
    (hA : OeisA108569.A (p * m)) : OeisA108569.A m := by
  obtain ⟨hpos, heq⟩ := hA
  have hpm : p ∣ m := (dvd_pow_self p two_ne_zero).trans hm
  -- `p ∣ φ m`, because `m = p * (p * k)` with `p ∣ p * k`.
  have hphi : p ∣ Nat.totient m := by
    obtain ⟨k, rfl⟩ := hm
    have hk : p ^ 2 * k = p * (p * k) := by ring
    rw [hk, Nat.totient_mul_of_prime_of_dvd hp (dvd_mul_right p k)]
    exact dvd_mul_right _ _
  have hsum : p ∣ m + Nat.totient m := dvd_add hpm hphi
  have h1 : Nat.totient (p * m) = p * Nat.totient m :=
    Nat.totient_mul_of_prime_of_dvd hp hpm
  have h2 : p * m + Nat.totient (p * m) = p * (m + Nat.totient m) := by
    rw [h1, mul_add]
  have h3 : Nat.totient (p * (m + Nat.totient m)) = p * Nat.totient (m + Nat.totient m) :=
    Nat.totient_mul_of_prime_of_dvd hp hsum
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hpos
      exact absurd hpos (lt_irrefl 0)
    · exact h0
  · rw [h2, h3, h1] at heq
    exact Nat.eq_of_mul_eq_mul_left hp.pos heq

end OMA.Helpers

theorem OMA.solution : OMA.R_OeisA108569_conjecture_R1.H2 := by
  intro n hn1 hodd hA hp3
  obtain ⟨p, hp, hpn⟩ := hp3
  obtain ⟨k, rfl⟩ := hpn
  have hn : p ^ 3 * k = p * (p ^ 2 * k) := by ring
  rw [hn] at hn1 hodd hA
  rw [hn]
  have hp2 : 2 ≤ p := hp.two_le
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, mul_zero, mul_zero] at hn1
      exact absurd hn1 (Nat.not_lt_zero 1)
    · exact h0
  have hsq : 4 ≤ p ^ 2 := Nat.pow_le_pow_left hp2 2
  have hm1 : 1 < p ^ 2 * k := by
    have : p ^ 2 * 1 ≤ p ^ 2 * k := Nat.mul_le_mul_left _ hk
    omega
  refine ⟨p ^ 2 * k, hm1, ?_, ?_, ?_⟩
  · exact lt_mul_of_one_lt_left (by omega) (by omega)
  · exact (Nat.odd_mul.mp hodd).2
  · exact OMA.Helpers.a108569_descent hp (dvd_mul_right _ _) hA
