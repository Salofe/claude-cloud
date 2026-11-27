import OMAStatements.S_oeis_a256171
import Mathlib

/-!
Disproof of the conjunction in `OMA.S_oeis_a256171.main`: part (ii) fails for `m = 14`.

The generalized 14-gonal numbers are `6 k ^ 2 - 5 k` (`k ∈ ℤ`). For `L = 13 ^ j = 12 K + 1`
the number `n = 18 K ^ 2 + 3 K - 3 = (L ^ 2 - 25) / 8` is never a sum of three of them, so
infinitely many `n` are not represented. This is the case `ℓ ≡ 1 (mod 12)` of
Haensch and Kane, Almost universal ternary sums of polygonal numbers, Theorem 5.2 / Theorem 1.5;
here it is proved by an elementary argument.

If `n = P x + P y + P z`, put `σ = x + y + z`, `a = x - y`, `b = y - z`,
`N = a ^ 2 + a b + b ^ 2`. Then `(3 K - 1 + σ) (12 K + 1 - 2 (3 K - 1 + σ)) = 4 N`; the second
factor is odd, so `3 K - 1 + σ = 4 t`, and with `w = 12 K + 1 - 8 t` one gets `t w = N`,
`L = 8 t + w` and `t ≡ 2 (mod 3)`, `t > 0`. A prime `q ≡ 2 (mod 3)` dividing `t` and `w` would
divide `L = 13 ^ j`, impossible; and a prime `q ≡ 2 (mod 3)` dividing `a ^ 2 + a b + b ^ 2`
divides `a` and `b`. Descent on `t` then gives `t ≢ 2 (mod 3)`, a contradiction.
-/

namespace OMA.Helpers

/-- A prime `q ≡ 2 (mod 3)` dividing `a ^ 2 + a b + b ^ 2` divides `a` and `b`. -/
theorem a256171_loesch (q : ℕ) (hq : q.Prime) (h3 : q % 3 = 2) (a b : ℤ)
    (h : (q : ℤ) ∣ a ^ 2 + a * b + b ^ 2) : (q : ℤ) ∣ a ∧ (q : ℤ) ∣ b := by
  have := Fact.mk hq
  have hz : ((a ^ 2 + a * b + b ^ 2 : ℤ) : ZMod q) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
  push_cast at hz
  have hcube : (a : ZMod q) ^ 3 = (b : ZMod q) ^ 3 := by
    linear_combination ((a : ZMod q) - (b : ZMod q)) * hz
  have key : ∀ x : ZMod q, (x ^ 3) ^ (2 * (q / 3) + 1) = x := by
    intro x
    rw [← pow_mul, show 3 * (2 * (q / 3) + 1) = q + (q - 1) by omega, pow_add, ZMod.pow_card,
      ← pow_succ', Nat.sub_add_cancel hq.one_lt.le, ZMod.pow_card]
  have hab : (a : ZMod q) = (b : ZMod q) := by
    rw [← key (a : ZMod q), hcube, key]
  have h3ne : (3 : ZMod q) ≠ 0 := by
    intro h0
    have h0' : ((3 : ℕ) : ZMod q) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h0'
    have := (Nat.dvd_prime Nat.prime_three).mp h0'
    omega
  have hb0 : (b : ZMod q) = 0 := by
    rw [hab] at hz
    have h3b : (3 : ZMod q) * (b : ZMod q) ^ 2 = 0 := by linear_combination hz
    rcases mul_eq_zero.mp h3b with h0 | h0
    · exact absurd h0 h3ne
    · exact (pow_eq_zero_iff (by norm_num)).mp h0
  have ha0 : (a : ZMod q) = 0 := hab.trans hb0
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ha0,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb0⟩

/-- Descent: if `t w = a ^ 2 + a b + b ^ 2` with `t > 0` and no prime `q ≡ 2 (mod 3)` divides both
`t` and `w`, then `t ≢ 2 (mod 3)`. -/
theorem a256171_descent : ∀ t : ℕ, ∀ w a b : ℤ, 0 < t → (t : ℤ) * w = a ^ 2 + a * b + b ^ 2 →
    (∀ q : ℕ, q.Prime → q % 3 = 2 → q ∣ t → ¬ (q : ℤ) ∣ w) → t % 3 ≠ 2 := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro w a b ht hN hq
  by_cases h1 : t = 1
  · subst h1; norm_num
  obtain ⟨p, hp, hpt⟩ := Nat.exists_prime_and_dvd h1
  obtain ⟨t', ht'⟩ := hpt
  have hp2 : 2 ≤ p := hp.two_le
  have ht'pos : 0 < t' := by
    rcases Nat.eq_zero_or_pos t' with h | h
    · subst h; omega
    · exact h
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  by_cases hp3 : p % 3 = 2
  · have hpw : ¬ (p : ℤ) ∣ w := hq p hp hp3 ⟨t', ht'⟩
    have hdvd : (p : ℤ) ∣ a ^ 2 + a * b + b ^ 2 := by
      rw [← hN, ht']; push_cast
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) w
    obtain ⟨⟨a1, ha1⟩, ⟨b1, hb1⟩⟩ := a256171_loesch p hp hp3 a b hdvd
    have e1 : (p : ℤ) * ((t' : ℤ) * w) =
        (p : ℤ) * ((p : ℤ) * (a1 ^ 2 + a1 * b1 + b1 ^ 2)) := by
      rw [ht', ha1, hb1] at hN; push_cast at hN; linear_combination hN
    have e2 : (t' : ℤ) * w = (p : ℤ) * (a1 ^ 2 + a1 * b1 + b1 ^ 2) := mul_left_cancel₀ hp0 e1
    have hpt' : (p : ℤ) ∣ (t' : ℤ) := by
      rcases hpz.dvd_or_dvd (show (p : ℤ) ∣ (t' : ℤ) * w from ⟨_, e2⟩) with h | h
      · exact h
      · exact absurd h hpw
    obtain ⟨t'', ht''⟩ := Int.natCast_dvd_natCast.mp hpt'
    have e3 : (t'' : ℤ) * w = a1 ^ 2 + a1 * b1 + b1 ^ 2 := by
      rw [ht''] at e2; push_cast at e2
      exact mul_left_cancel₀ hp0 (by linear_combination e2)
    have htt : t = p * p * t'' := by rw [ht', ht'']; ring
    have ht''pos : 0 < t'' := by
      rcases Nat.eq_zero_or_pos t'' with h | h
      · subst h; omega
      · exact h
    have hlt : t'' < t := by
      rw [htt]
      have : 1 * t'' < p * p * t'' := Nat.mul_lt_mul_of_pos_right (by nlinarith) ht''pos
      omega
    have hrec := ih t'' hlt w a1 b1 ht''pos e3
      (fun q hq' hq3 hqd => hq q hq' hq3 (by rw [htt]; exact Dvd.dvd.mul_left hqd _))
    have hmod : t % 3 = t'' % 3 := by
      rw [htt, Nat.mul_mod, Nat.mul_mod p, hp3]
      simp
    omega
  · have hlt : t' < t := by
      rw [ht']
      have : 1 * t' < p * t' := Nat.mul_lt_mul_of_pos_right (by omega) ht'pos
      omega
    have e : (t' : ℤ) * ((p : ℤ) * w) = a ^ 2 + a * b + b ^ 2 := by
      rw [← hN, ht']; push_cast; ring
    have hrec := ih t' hlt ((p : ℤ) * w) a b ht'pos e (by
      intro q hq' hq3 hqd hqpw
      have hqz : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq'
      rcases hqz.dvd_or_dvd hqpw with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hq' hp).mp (Int.natCast_dvd_natCast.mp h)
        subst this; exact hp3 hq3
      · exact hq q hq' hq3 (by rw [ht']; exact Dvd.dvd.mul_left hqd _) h)
    have hpm : p % 3 = 0 ∨ p % 3 = 1 := by omega
    have htm : t' % 3 = 0 ∨ t' % 3 = 1 := by omega
    rw [ht', Nat.mul_mod]
    rcases hpm with h | h <;> rcases htm with h' | h' <;> rw [h, h'] <;> norm_num

/-- The generalized 14-gonal numbers. -/
theorem a256171_gp14 (k : ℤ) : OMA.S_oeis_a256171.genPolygonal 14 k = 6 * k ^ 2 - 5 * k := by
  unfold OMA.S_oeis_a256171.genPolygonal
  rw [show (((14 : ℕ) : ℤ) - 2) * k ^ 2 - (((14 : ℕ) : ℤ) - 4) * k = 2 * (6 * k ^ 2 - 5 * k) by
    push_cast; ring]
  exact Int.mul_ediv_cancel_left _ (by norm_num)

/-- `18 K ^ 2 + 3 K - 3` is not a sum of three generalized 14-gonal numbers when no prime
`q ≡ 2 (mod 3)` divides `12 K + 1`. -/
theorem a256171_nonrep (K : ℤ) (hK : 0 ≤ K)
    (hprime : ∀ q : ℕ, q.Prime → q % 3 = 2 → ¬ (q : ℤ) ∣ 12 * K + 1) (x y z : ℤ) :
    18 * K ^ 2 + 3 * K - 3 ≠ (6 * x ^ 2 - 5 * x) + (6 * y ^ 2 - 5 * y) + (6 * z ^ 2 - 5 * z) := by
  intro h
  have hc : (3 * K - 1 + (x + y + z)) * (12 * K + 1 - 2 * (3 * K - 1 + (x + y + z))) =
      4 * ((x - y) ^ 2 + (x - y) * (y - z) + (y - z) ^ 2) := by
    have h8 : 8 * ((3 * K - 1 + (x + y + z)) * (12 * K + 1 - 2 * (3 * K - 1 + (x + y + z)))) =
        8 * (4 * ((x - y) ^ 2 + (x - y) * (y - z) + (y - z) ^ 2)) := by
      linear_combination 8 * h
    exact mul_left_cancel₀ (by norm_num) h8
  have hcop : IsCoprime (4 : ℤ) (12 * K + 1 - 2 * (3 * K - 1 + (x + y + z))) :=
    ⟨-((6 * K - (3 * K - 1 + (x + y + z))) ^ 2 + (6 * K - (3 * K - 1 + (x + y + z)))),
      12 * K + 1 - 2 * (3 * K - 1 + (x + y + z)), by ring⟩
  obtain ⟨t, ht⟩ := hcop.dvd_of_dvd_mul_right ⟨_, hc⟩
  rw [ht] at hc
  have hx : x = 4 * t - 3 * K + 1 - y - z := by linarith
  subst hx
  have htw : t * (12 * K + 1 - 8 * t) =
      (4 * t - 3 * K + 1 - y - z - y) ^ 2 + (4 * t - 3 * K + 1 - y - z - y) * (y - z) +
        (y - z) ^ 2 := by
    exact mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num) (by linear_combination hc)
  have h3 : t + 1 = 3 * ((-8 * t ^ 2 + 4 * K * t - 2 * t - 3 * (K + y) ^ 2 + 8 * t * (K + y) +
      2 * (K + y)) - (4 * t - 3 * K + 1 - y - z - y) * (y - z)) := by
    linear_combination (-1 : ℤ) * htw
  have ht3 : t % 3 = 2 := by
    generalize ((-8 * t ^ 2 + 4 * K * t - 2 * t - 3 * (K + y) ^ 2 + 8 * t * (K + y) +
      2 * (K + y)) - (4 * t - 3 * K + 1 - y - z - y) * (y - z)) = M at h3
    omega
  set a := 4 * t - 3 * K + 1 - y - z - y with ha
  set b := y - z with hb
  set w := 12 * K + 1 - 8 * t with hw
  have hN : 0 ≤ a ^ 2 + a * b + b ^ 2 := by nlinarith [sq_nonneg (2 * a + b), sq_nonneg b]
  have htpos : 0 < t := by
    by_contra hneg
    have ht0 : t < 0 := by omega
    have hw0 : w ≤ 0 := by nlinarith
    have : 12 * K + 1 = 8 * t + w := by rw [hw]; ring
    linarith
  have htn : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg htpos.le
  have hd := a256171_descent t.toNat w a b (by omega) (by rw [htn]; exact htw) (by
    intro q hq hq3 hqt hqw
    have hqt' : (q : ℤ) ∣ t := by rw [← htn]; exact Int.natCast_dvd_natCast.mpr hqt
    apply hprime q hq hq3
    have : 12 * K + 1 = 8 * t + w := by rw [hw]; ring
    rw [this]
    exact dvd_add (Dvd.dvd.mul_left hqt' 8) hqw)
  omega

end OMA.Helpers

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a256171.main) := by
  intro h
  have h2 := h.2 14 (by norm_num) (by norm_num)
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp h2
  have hpow : N0 < 13 ^ N0 := Nat.lt_pow_self (by norm_num)
  have hL13 : 13 ^ (N0 + 1) = 13 * 13 ^ N0 := by rw [pow_succ]; ring
  have hLmod : 13 ^ (N0 + 1) % 12 = 1 := by rw [Nat.pow_mod]; norm_num
  obtain ⟨K, hK⟩ : ∃ K, K = 13 ^ (N0 + 1) / 12 := ⟨_, rfl⟩
  have hLK : 13 ^ (N0 + 1) = 12 * K + 1 := by omega
  have hKN : N0 + 1 ≤ K := by omega
  have hKK : K ≤ K * K := Nat.le_mul_self K
  obtain ⟨x, y, z, hxyz⟩ := hN0 (18 * K * K + 3 * K - 3) (by omega)
  rw [OMA.Helpers.a256171_gp14, OMA.Helpers.a256171_gp14, OMA.Helpers.a256171_gp14] at hxyz
  have hsub : 3 ≤ 18 * K * K + 3 * K := by omega
  push_cast [Nat.cast_sub hsub] at hxyz
  refine OMA.Helpers.a256171_nonrep (K : ℤ) (by positivity) ?_ x y z (by linear_combination hxyz)
  intro q hq hq3 hdvd
  have hdvd' : q ∣ 13 ^ (N0 + 1) := by
    rw [hLK]; exact_mod_cast hdvd
  have := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 13)).mp (hq.dvd_of_dvd_pow hdvd')
  omega
