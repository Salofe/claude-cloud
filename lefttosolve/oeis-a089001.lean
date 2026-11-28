import OMAStatements.S_oeis_a089001
import Mathlib

/-!
Proof of the A089001 characterization: for k > 0, 2k^2 + 1 is prime iff k is not of the form
d + t/d with t = n(n+1)/2 triangular and d a divisor of t.

Writing k = d + e with de = t, we have 8de + 1 = (2n+1)^2, so 2k^2 + 1 = (2n+1)^2 + 2(d-e)^2 is a
second representation by x^2 + 2y^2 besides 1 + 2k^2; for a prime this is impossible, since
(ks - m)(ks + m) = (2k^2+1)(k^2 - m^2) with both factors strictly between 0 and 2k^2 + 1.
Conversely, if 2k^2 + 1 = AB with A, B > 1, each factor divides 2k^2 + 1, so (Thue pigeonhole) has
the form u^2 + 2v^2; composing gives a representation s^2 + 2m^2 with s^2 > 1, and
d = (k+m)/2, e = (k-m)/2, n = (s-1)/2 give the required form.
-/

namespace OMA.Helpers

/-- Thue-type lemma: a positive divisor of `2 r ^ 2 + 1` has the form `u ^ 2 + 2 v ^ 2`. -/
theorem rep_of_dvd (A : ℕ) (hA : 1 ≤ A) (r : ℤ) (hr : (A : ℤ) ∣ 2 * r ^ 2 + 1) :
    ∃ u v : ℤ, (A : ℤ) = u ^ 2 + 2 * v ^ 2 := by
  classical
  have : NeZero A := ⟨by omega⟩
  have hq1 : Nat.sqrt A * Nat.sqrt A ≤ A := Nat.sqrt_le A
  have hq2 : A < (Nat.sqrt A + 1) * (Nat.sqrt A + 1) := Nat.lt_succ_sqrt A
  have hcard : Fintype.card (ZMod A) <
      Fintype.card (Fin (Nat.sqrt A + 1) × Fin (Nat.sqrt A + 1)) := by
    rw [ZMod.card, Fintype.card_prod, Fintype.card_fin]
    exact hq2
  obtain ⟨⟨a, b⟩, ⟨a', b'⟩, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun p : Fin (Nat.sqrt A + 1) × Fin (Nat.sqrt A + 1) =>
      ((p.1 : ℕ) : ZMod A) + (r : ZMod A) * ((p.2 : ℕ) : ZMod A)) hcard
  simp only at heq
  have ha := a.isLt
  have ha' := a'.isLt
  have hb := b.isLt
  have hb' := b'.isLt
  obtain ⟨x, hx⟩ : ∃ x : ℤ, x = ((a : ℕ) : ℤ) - ((a' : ℕ) : ℤ) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℤ, y = ((b : ℕ) : ℤ) - ((b' : ℕ) : ℤ) := ⟨_, rfl⟩
  have hdvd : (A : ℤ) ∣ x + r * y := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hx, hy]
    push_cast
    linear_combination heq
  have hdvd2 : (A : ℤ) ∣ 2 * x ^ 2 + y ^ 2 := by
    have e : 2 * x ^ 2 + y ^ 2 =
        (x + r * y) * (2 * x - 2 * r * y) + y ^ 2 * (2 * r ^ 2 + 1) := by ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left hdvd _) (dvd_mul_of_dvd_right hr _)
  set q : ℕ := Nat.sqrt A with hq
  have hxq : x ^ 2 ≤ (q : ℤ) ^ 2 := by
    have h1 : x ≤ q := by omega
    have h2 : -(q : ℤ) ≤ x := by omega
    nlinarith
  have hyq : y ^ 2 ≤ (q : ℤ) ^ 2 := by
    have h1 : y ≤ q := by omega
    have h2 : -(q : ℤ) ≤ y := by omega
    nlinarith
  have hqA : (q : ℤ) ^ 2 ≤ A := by
    have : ((q * q : ℕ) : ℤ) ≤ A := by exact_mod_cast hq1
    push_cast at this
    nlinarith
  have hpos : 0 < 2 * x ^ 2 + y ^ 2 := by
    by_contra hcon
    have hx0 : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy0 : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    apply hne
    rw [Prod.mk.injEq]
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  obtain ⟨c, hc⟩ := hdvd2
  have hA0 : (0 : ℤ) < A := by exact_mod_cast hA
  have hc0 : 0 < c := by
    by_contra h
    push_neg at h
    nlinarith
  have hc3 : c ≤ 3 := by
    by_contra h
    push_neg at h
    nlinarith
  interval_cases c
  · exact ⟨y, x, by linarith⟩
  · rcases Int.even_or_odd y with ⟨w, hw⟩ | ⟨w, hw⟩
    · refine ⟨x, w, ?_⟩
      subst hw
      linarith
    · exfalso
      subst hw
      have : (2 * ((A : ℤ) - x ^ 2 - 2 * w ^ 2 - 2 * w) : ℤ) = 1 := by linarith
      omega
  · have e : (A : ℤ) = (q : ℤ) ^ 2 := by linarith
    exact ⟨q, 0, by rw [e]; ring⟩

/-- Two representations: if `2 k ^ 2 + 1` is a product of two numbers `> 1` of the form
`u ^ 2 + 2 v ^ 2`, it has a representation `s ^ 2 + 2 m ^ 2` with `s ^ 2 > 1`. -/
theorem compose (k u1 v1 u2 v2 : ℤ)
    (hA : 1 < u1 ^ 2 + 2 * v1 ^ 2) (hB : 1 < u2 ^ 2 + 2 * v2 ^ 2)
    (hN : 2 * k ^ 2 + 1 = (u1 ^ 2 + 2 * v1 ^ 2) * (u2 ^ 2 + 2 * v2 ^ 2)) :
    ∃ s m : ℤ, 2 * k ^ 2 + 1 = s ^ 2 + 2 * m ^ 2 ∧ 1 < s ^ 2 := by
  by_cases h1 : 1 < (u1 * u2 - 2 * v1 * v2) ^ 2
  · exact ⟨_, u1 * v2 + u2 * v1, by rw [hN]; ring, h1⟩
  by_cases h2 : 1 < (u1 * u2 + 2 * v1 * v2) ^ 2
  · exact ⟨_, u1 * v2 - u2 * v1, by rw [hN]; ring, h2⟩
  exfalso
  push_neg at h1 h2
  have hs1 : |u1 * u2 - 2 * v1 * v2| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]
    exact h1
  have hs2 : |u1 * u2 + 2 * v1 * v2| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]
    exact h2
  have hv : v1 * v2 = 0 := by
    have h3 : |4 * (v1 * v2)| ≤ 2 := by
      have e : 4 * (v1 * v2) = (u1 * u2 + 2 * v1 * v2) - (u1 * u2 - 2 * v1 * v2) := by ring
      rw [e]
      exact (abs_sub _ _).trans (by linarith)
    rw [abs_le] at h3
    omega
  rcases mul_eq_zero.mp hv with hv1 | hv2
  · subst hv1
    have hu2 : u2 = 0 := by
      by_contra hu2
      have h4 : 1 ≤ u2 ^ 2 := by
        have := sq_pos_of_ne_zero hu2
        omega
      nlinarith
    subst hu2
    have e : 2 * k ^ 2 + 1 = 2 * (u1 ^ 2 * v2 ^ 2) := by rw [hN]; ring
    omega
  · subst hv2
    have hu1 : u1 = 0 := by
      by_contra hu1
      have h4 : 1 ≤ u1 ^ 2 := by
        have := sq_pos_of_ne_zero hu1
        omega
      nlinarith
    subst hu1
    have e : 2 * k ^ 2 + 1 = 2 * (v1 ^ 2 * u2 ^ 2) := by rw [hN]; ring
    omega

end OMA.Helpers

namespace OMA.Helpers

/-- The integer core of the forward direction: a second representation
`s ^ 2 + 2 m ^ 2` of the prime `2 K ^ 2 + 1` with `3 ≤ s` and `|m| < K` is impossible. -/
theorem fwd_int (K s m : ℤ) (hp : Prime (2 * K ^ 2 + 1))
    (hs2 : s ^ 2 = 2 * K ^ 2 + 1 - 2 * m ^ 2) (hK2 : 2 ≤ K) (hmK : m < K) (hmK' : -K < m)
    (hs3 : 3 ≤ s) : False := by
  have key : (K * s - m) * (K * s + m) = (2 * K ^ 2 + 1) * (K ^ 2 - m ^ 2) := by
    linear_combination K ^ 2 * hs2
  have hsK : s ≤ 2 * K - 1 := by
    by_contra h
    push_neg at h
    have h' : 2 * K ≤ s := by linarith
    have h1 : (2 * K) * (2 * K) ≤ s * s := mul_le_mul h' h' (by linarith) (by linarith)
    nlinarith [sq_nonneg m]
  have hKs : K * s ≤ K * (2 * K - 1) := mul_le_mul_of_nonneg_left hsK (by linarith)
  have hKs3 : K * 3 ≤ K * s := mul_le_mul_of_nonneg_left hs3 (by linarith)
  have hlt1 : 0 < K * s - m := by linarith
  have hlt2 : 0 < K * s + m := by linarith
  have hlt3 : K * s - m < 2 * K ^ 2 + 1 := by nlinarith
  have hlt4 : K * s + m < 2 * K ^ 2 + 1 := by nlinarith
  rcases hp.dvd_or_dvd ⟨_, key⟩ with h | h
  · have := Int.le_of_dvd hlt1 h
    linarith
  · have := Int.le_of_dvd hlt2 h
    linarith

/-- A representation `d + t / d` with `t` triangular makes `2 k ^ 2 + 1` composite. -/
theorem fwd (k n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hdvd : d ∣ n * (n + 1) / 2)
    (hkd : k = d + n * (n + 1) / 2 / d) : ¬ (2 * k ^ 2 + 1).Prime := by
  intro hp
  obtain ⟨t, ht⟩ : ∃ t, t = n * (n + 1) / 2 := ⟨_, rfl⟩
  rw [← ht] at hdvd hkd
  obtain ⟨e, he⟩ : ∃ e, e = t / d := ⟨_, rfl⟩
  rw [← he] at hkd
  have hde : d * e = t := by rw [he]; exact Nat.mul_div_cancel' hdvd
  have h2t : t * 2 = n * (n + 1) := by
    rw [ht]; exact Nat.div_mul_cancel (Nat.even_mul_succ_self n).two_dvd
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · exfalso
      rw [h, mul_zero] at hde
      rw [← hde, zero_mul] at h2t
      have : 0 < n * (n + 1) := Nat.mul_pos hn (Nat.succ_pos n)
      omega
    · exact h
  have hpZ : Prime (2 * (k : ℤ) ^ 2 + 1) := by
    have := Nat.prime_iff_prime_int.mp hp
    exact_mod_cast this
  have hkZ : (k : ℤ) = d + e := by rw [hkd]; push_cast; ring
  have hdeZ : (d : ℤ) * e * 8 = 4 * n * (n + 1) := by
    have : ((d * e * 2 : ℕ) : ℤ) = ((n * (n + 1) : ℕ) : ℤ) := by rw [hde, h2t]
    push_cast at this
    linarith
  have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have he1' : (1 : ℤ) ≤ e := by exact_mod_cast he1
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
  refine fwd_int k (2 * n + 1) ((d : ℤ) - e) hpZ ?_ ?_ ?_ ?_ ?_
  · rw [hkZ]
    linear_combination (-1 : ℤ) * hdeZ
  · rw [hkZ]; linarith
  · rw [hkZ]; linarith
  · rw [hkZ]; linarith
  · linarith

/-- If `2 k ^ 2 + 1` is composite, `k` has a representation `d + t / d`. -/
theorem bwd (k : ℕ) (hk : 0 < k) (hp : ¬ (2 * k ^ 2 + 1).Prime) :
    ∃ n d : ℕ, 0 < n ∧ 0 < d ∧ d ∣ n * (n + 1) / 2 ∧
      k = d + (n * (n + 1) / 2) / d := by
  obtain ⟨A, hAdvd, hA2, hAlt⟩ := Nat.exists_dvd_of_not_prime2 (by nlinarith) hp
  obtain ⟨B, hB⟩ := hAdvd
  have hB2 : 2 ≤ B := by
    rcases (show B = 0 ∨ B = 1 ∨ 2 ≤ B by omega) with h | h | h
    · rw [h, mul_zero] at hB; omega
    · rw [h, mul_one] at hB; omega
    · exact h
  have hBZ : 2 * (k : ℤ) ^ 2 + 1 = (A : ℤ) * B := by exact_mod_cast hB
  have hAd : (A : ℤ) ∣ 2 * (k : ℤ) ^ 2 + 1 := ⟨B, hBZ⟩
  have hBd : (B : ℤ) ∣ 2 * (k : ℤ) ^ 2 + 1 := ⟨A, by rw [hBZ, mul_comm]⟩
  obtain ⟨u1, v1, hA⟩ := rep_of_dvd A (by omega) k hAd
  obtain ⟨u2, v2, hBr⟩ := rep_of_dvd B (by omega) k hBd
  have hNZ : 2 * (k : ℤ) ^ 2 + 1 = (u1 ^ 2 + 2 * v1 ^ 2) * (u2 ^ 2 + 2 * v2 ^ 2) := by
    rw [← hA, ← hBr]; exact hBZ
  have hA1 : (1 : ℤ) < u1 ^ 2 + 2 * v1 ^ 2 := by rw [← hA]; exact_mod_cast hA2
  have hB1 : (1 : ℤ) < u2 ^ 2 + 2 * v2 ^ 2 := by rw [← hBr]; exact_mod_cast hB2
  obtain ⟨s0, m, hsm, hs1⟩ := compose k u1 v1 u2 v2 hA1 hB1 hNZ
  -- normalize s to be nonnegative
  obtain ⟨s, hs0, hss⟩ : ∃ s : ℤ, 0 ≤ s ∧ s ^ 2 = s0 ^ 2 := ⟨|s0|, abs_nonneg _, sq_abs s0⟩
  rw [← hss] at hsm hs1
  obtain ⟨K, hK⟩ : ∃ K : ℤ, K = k := ⟨_, rfl⟩
  rw [← hK] at hsm
  have hK1 : (1 : ℤ) ≤ K := by rw [hK]; exact_mod_cast hk
  -- s is odd
  obtain ⟨a, ha⟩ : Odd s := by
    rcases Int.even_or_odd s with ⟨a, ha⟩ | h
    · exfalso
      subst ha
      have : (2 * (K ^ 2 - 2 * a ^ 2 - m ^ 2) : ℤ) = -1 := by linarith
      omega
    · exact h
  subst ha
  -- parity of m and K agree
  have hpar : ∃ c : ℤ, K + m = 2 * c := by
    have h8 : K ^ 2 = 2 * (a * (a + 1)) + m ^ 2 := by linarith
    obtain ⟨w, hw⟩ := Int.even_mul_succ_self a
    rw [hw] at h8
    rcases Int.even_or_odd (K + m) with ⟨c, hc⟩ | ⟨c, hc⟩
    · exact ⟨c, by rw [hc]; ring⟩
    · exfalso
      have hK' : K = 2 * c + 1 - m := by linarith
      rw [hK'] at h8
      have : 2 * (w + w - 2 * c ^ 2 - 2 * c + 2 * c * m + m) = (1 : ℤ) := by
        linear_combination (-1 : ℤ) * h8
      omega
  obtain ⟨c, hc⟩ := hpar
  have hmK : m ^ 2 < K ^ 2 := by linarith
  have habs : |m| < K := abs_lt_of_sq_lt_sq hmK (by linarith)
  rw [abs_lt] at habs
  have hc1 : 1 ≤ c := by omega
  have hc2 : 1 ≤ K - c := by omega
  have ha0 : 0 ≤ a := by omega
  have ha1 : 1 ≤ a := by
    rcases (show a = 0 ∨ 1 ≤ a by omega) with h | h
    · subst h
      norm_num at hs1
    · exact h
  lift c to ℕ using (by linarith)
  obtain ⟨e, he⟩ : ∃ e : ℕ, (e : ℤ) = K - c := ⟨(K - c).toNat, Int.toNat_of_nonneg (by linarith)⟩
  lift a to ℕ using (by linarith)
  have hkce : k = c + e := by
    have : (k : ℤ) = c + e := by rw [he, hK]; ring
    exact_mod_cast this
  have hcube : a * (a + 1) = 2 * (c * e) := by
    have : ((a * (a + 1) : ℕ) : ℤ) = ((2 * (c * e) : ℕ) : ℤ) := by
      push_cast
      rw [he]
      have h4 : 4 * ((a : ℤ) * (a + 1)) = 4 * (2 * (c * (K - c))) := by
        linear_combination (-1 : ℤ) * hsm + (2 * (K - m) - 4 * (c : ℤ)) * hc
      linarith
    exact_mod_cast this
  have hc0 : 0 < c := by exact_mod_cast hc1
  refine ⟨a, c, by exact_mod_cast ha1, hc0, ?_, ?_⟩
  · rw [hcube, Nat.mul_div_cancel_left _ (by norm_num)]
    exact dvd_mul_right _ _
  · rw [hcube, Nat.mul_div_cancel_left _ (by norm_num), Nat.mul_div_cancel_left _ hc0]
    exact hkce

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a089001.main := by
  intro k hk
  constructor
  · rintro hp ⟨n, d, hn, hd, hdvd, hkd⟩
    exact OMA.Helpers.fwd k n d hn hd hdvd hkd hp
  · intro h
    by_contra hp
    exact h (OMA.Helpers.bwd k hk hp)
