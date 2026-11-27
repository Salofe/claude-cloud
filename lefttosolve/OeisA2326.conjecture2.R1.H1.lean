import OMAReductions.R_OeisA2326_conjecture2_R1

/-!
# Step H1 of the reduction OeisA2326.conjecture2.R1

Let p be an odd prime that is not a Wieferich prime, so that p divides 2^(p-1) - 1 exactly
once, and let k be at least one. Write d and D for the orders of 2 modulo p^k and p^(k+1).

* Lifting the exponent (Mathlib `padicValNat.pow_sub_pow`) shows that the exponent of p in
  2^N - 1 is exactly k for N = (p - 1) p^(k-1). Hence d divides N, and since 2^d - 1 divides
  2^N - 1, the power p^(k+1) does not divide 2^d - 1; so the exponent of p in 2^d - 1 is k.
* Lifting the exponent once more gives that p^(k+1) divides 2^(d p) - 1, so D divides d p.
* d divides D, so D = d m with m dividing p. The case m = 1 would make p^(k+1) divide
  2^d - 1, hence m = p and D = p d.

Only Mathlib, the upstream definition behind the step and the helper lemmas below are used.
-/

namespace OMA.Helpers

/-- In `ZMod N`, a power of two is one exactly when `N` divides that power of two minus one. -/
theorem zmod_two_pow_eq_one_iff (N n : ℕ) : (2 : ZMod N) ^ n = 1 ↔ N ∣ 2 ^ n - 1 := by
  have h : ((2 ^ n : ℕ) : ZMod N) = ((1 : ℕ) : ZMod N) ↔ N ∣ 2 ^ n - 1 := by
    rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq.comm, Nat.modEq_iff_dvd' Nat.one_le_two_pow]
  rw [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at h
  exact h

/-- The order of two in `ZMod N` divides `n` exactly when `N` divides `2 ^ n - 1`. -/
theorem orderOf_two_zmod_dvd_iff (N n : ℕ) : orderOf (2 : ZMod N) ∣ n ↔ N ∣ 2 ^ n - 1 := by
  rw [orderOf_dvd_iff_pow_eq_one, zmod_two_pow_eq_one_iff]

/-- Lifting the exponent for `2 ^ (a * m) - 1` at an odd prime `p` dividing `2 ^ a - 1`
(a specialisation of Mathlib's `padicValNat.pow_sub_pow`). -/
theorem padicValNat_two_pow_mul_sub_one {p : ℕ} [Fact p.Prime] (hodd : Odd p) {a m : ℕ}
    (ha : a ≠ 0) (hm : m ≠ 0) (hpa : p ∣ 2 ^ a - 1) :
    padicValNat p (2 ^ (a * m) - 1) = padicValNat p (2 ^ a - 1) + padicValNat p m := by
  have hp : p.Prime := Fact.out
  have h2 : ¬ p ∣ 2 ^ a := by
    intro h
    have hle : p ≤ 2 := Nat.le_of_dvd two_pos (hp.dvd_of_dvd_pow h)
    obtain ⟨t, ht⟩ := hodd
    have := hp.two_le
    omega
  have h := padicValNat.pow_sub_pow (x := 2 ^ a) (y := 1) hodd (Nat.one_lt_two_pow ha) hpa h2 hm
  rwa [one_pow, ← pow_mul] at h

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_OeisA2326_conjecture2_R1.H1 := by
  intro p hp hp2 hW k hk
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by
    obtain ⟨t, ht⟩ := hodd
    have := hp.two_le
    omega
  have hp1 : p - 1 ≠ 0 := by omega
  have hne : ∀ n : ℕ, n ≠ 0 → 2 ^ n - 1 ≠ 0 := fun n hn =>
    Nat.sub_ne_zero_of_lt (Nat.one_lt_two_pow hn)
  -- Fermat's little theorem for the base two
  have hferm : p ∣ 2 ^ (p - 1) - 1 := by
    rw [← zmod_two_pow_eq_one_iff]
    apply ZMod.pow_card_sub_one_eq_one
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd two_pos h'
    omega
  -- p is not a Wieferich prime: the exponent of p in 2^(p-1) - 1 is exactly one
  have hv1 : padicValNat p (2 ^ (p - 1) - 1) = 1 := by
    have h1 : 1 ≤ padicValNat p (2 ^ (p - 1) - 1) :=
      (padicValNat_dvd_iff_le (hne _ hp1)).mp (by rwa [pow_one])
    have h2 : ¬ 2 ≤ padicValNat p (2 ^ (p - 1) - 1) := fun h =>
      hW ((padicValNat_dvd_iff_le (hne _ hp1)).mpr h)
    omega
  -- N = (p - 1) p^(k-1) has exponent exactly k
  have hpk1 : p ^ (k - 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hN0 : (p - 1) * p ^ (k - 1) ≠ 0 := Nat.mul_ne_zero hp1 hpk1
  have hvN : padicValNat p (2 ^ ((p - 1) * p ^ (k - 1)) - 1) = k := by
    rw [padicValNat_two_pow_mul_sub_one hodd hp1 hpk1 hferm, hv1, padicValNat.prime_pow]
    omega
  -- the two orders
  obtain ⟨d, hd⟩ : ∃ d, orderOf (2 : ZMod (p ^ k)) = d := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, orderOf (2 : ZMod (p ^ (k + 1))) = D := ⟨_, rfl⟩
  rw [hd, hD]
  have hdi : ∀ n, d ∣ n ↔ p ^ k ∣ 2 ^ n - 1 := by
    intro n
    rw [← hd]
    exact orderOf_two_zmod_dvd_iff _ _
  have hDi : ∀ n, D ∣ n ↔ p ^ (k + 1) ∣ 2 ^ n - 1 := by
    intro n
    rw [← hD]
    exact orderOf_two_zmod_dvd_iff _ _
  -- d divides N, so d is nonzero
  have hdN : d ∣ (p - 1) * p ^ (k - 1) := by
    rw [hdi, padicValNat_dvd_iff_le (hne _ hN0), hvN]
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hN0 (Nat.eq_zero_of_zero_dvd hdN)
  have hpkd : p ^ k ∣ 2 ^ d - 1 := (hdi d).mp dvd_rfl
  have hpd : p ∣ 2 ^ d - 1 := (dvd_pow_self p (by omega : k ≠ 0)).trans hpkd
  -- p^(k+1) does not divide 2^d - 1, since 2^d - 1 divides 2^N - 1
  have hnot : ¬ p ^ (k + 1) ∣ 2 ^ d - 1 := by
    intro h
    obtain ⟨m, hm⟩ := hdN
    have hdiv : 2 ^ d - 1 ∣ 2 ^ ((p - 1) * p ^ (k - 1)) - 1 := by
      rw [hm, pow_mul]
      simpa using Nat.sub_dvd_pow_sub_pow (2 ^ d) 1 m
    have := (padicValNat_dvd_iff_le (hne _ hN0)).mp (h.trans hdiv)
    omega
  have hvd : padicValNat p (2 ^ d - 1) = k := by
    have h1 := (padicValNat_dvd_iff_le (hne _ hd0)).mp hpkd
    have h2 : ¬ k + 1 ≤ padicValNat p (2 ^ d - 1) := fun h =>
      hnot ((padicValNat_dvd_iff_le (hne _ hd0)).mpr h)
    omega
  -- D divides d p
  have hDdp : D ∣ d * p := by
    rw [hDi, padicValNat_dvd_iff_le (hne _ (Nat.mul_ne_zero hd0 hp.ne_zero)),
      padicValNat_two_pow_mul_sub_one hodd hd0 hp.ne_zero hpd, hvd, padicValNat_self]
  -- d divides D
  have hdD : d ∣ D := by
    rw [hdi]
    exact (pow_dvd_pow p (Nat.le_succ k)).trans ((hDi D).mp dvd_rfl)
  obtain ⟨m, hm⟩ := hdD
  have hmp : m ∣ p := by
    rw [hm] at hDdp
    exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hd0) hDdp
  rcases hp.eq_one_or_self_of_dvd m hmp with h1 | h1
  · exfalso
    apply hnot
    have h := (hDi D).mp dvd_rfl
    rwa [hm, h1, mul_one] at h
  · rw [hm, h1, mul_comm]
