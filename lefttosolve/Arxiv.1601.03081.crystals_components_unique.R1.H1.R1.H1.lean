import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1_H1_R1

/-!
# Step H1 of the reduction Arxiv.1601.03081.crystals_components_unique.R1.H1.R1

Multiplier three. Write P = (a+1)(b+1) and s = a+b. For odd a = 2k+1 the factor P is even,
P = 2(k+1)(b+1), and s^2 + (ab+1)^2 + 2Ps = 2s^2 + 2P(k+1)(b+1) because ab+1 = P - s.
Hence the crystal condition 2P | s^2 + (ab+1)^2 gives P | s^2. Applied to the two
factorizations (a, 3c) and (c, 3a) this yields (a+3c)^2 = k(a+1)(3c+1) and
(c+3a)^2 = k'(c+1)(3a+1). The ratio bounds a <= 3c and c <= 3a force k and k' into 1..11.
For k = k' the claim is immediate; for every other pair the two equations have no common
solution modulo one of 3, 5, 7, 9 or 11, which the kernel checks by enumeration over ZMod.

Only the upstream definition IsCrystalWithComponents is used.
-/

open Arxiv.«1601.03081»

namespace OMA.Helpers

/-- For odd a, the crystal divisibility 2(a+1)(b+1) | (a+b)^2 + (ab+1)^2 implies
(a+1)(b+1) | (a+b)^2. -/
theorem crystal_sq_dvd {a b : ℕ} (ha : Odd a)
    (h : 2 * (a + 1) * (b + 1) ∣ (a + b)^2 + (a * b + 1)^2) :
    (a + 1) * (b + 1) ∣ (a + b)^2 := by
  obtain ⟨k, rfl⟩ := ha
  have key : (2 * k + 1 + b)^2 + ((2 * k + 1) * b + 1)^2 +
      2 * (2 * k + 1 + 1) * (b + 1) * (2 * k + 1 + b) =
      2 * (2 * k + 1 + b)^2 + 2 * (2 * k + 1 + 1) * (b + 1) * ((k + 1) * (b + 1)) := by
    ring
  have h1 : 2 * (2 * k + 1 + 1) * (b + 1) ∣
      2 * (2 * k + 1 + b)^2 + 2 * (2 * k + 1 + 1) * (b + 1) * ((k + 1) * (b + 1)) := by
    rw [← key]
    exact dvd_add h (dvd_mul_right _ _)
  have h2 : 2 * (2 * k + 1 + 1) * (b + 1) ∣ 2 * (2 * k + 1 + b)^2 :=
    (Nat.dvd_add_left (dvd_mul_right _ _)).mp h1
  rw [Nat.mul_assoc] at h2
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2

/-- If x <= 3y and y <= 3x then (x + 3y)^2 < 12 (x+1)(3y+1), so the exact quotient is at most 11.
The key inequality is (3y - x)(9x - 3y) >= 0, i.e. 9x^2 + 9y^2 <= 30xy. -/
theorem quot_bound {x y k : ℕ} (hxy : x ≤ y * 3) (hyx : y ≤ x * 3)
    (hk : (x + y * 3)^2 = (x + 1) * (y * 3 + 1) * k) : k ≤ 11 := by
  have hlt : (x + 1) * (y * 3 + 1) * k < (x + 1) * (y * 3 + 1) * 12 := by
    rw [← hk]
    have h2 : 0 ≤ ((y : ℤ) * 3 - x) * (x * 9 - y * 3) := mul_nonneg (by omega) (by omega)
    have h3 : ((x : ℤ) + y * 3)^2 < (x + 1) * (y * 3 + 1) * 12 := by nlinarith
    exact_mod_cast h3
  have := Nat.lt_of_mul_lt_mul_left hlt
  omega

/-- The exact quotient is positive as soon as x > 1. -/
theorem quot_pos {x y k : ℕ} (hx : 1 < x)
    (hk : (x + y * 3)^2 = (x + 1) * (y * 3 + 1) * k) : 0 < k := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h
    have h0 : (x + y * 3)^2 = 0 := by rw [hk, Nat.mul_zero]
    have h1 : x + y * 3 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h0
    omega
  · exact h

/-- Reduce both quotient equations modulo N. -/
theorem modcheck (N : ℕ) {a c k k' : ℕ} (hk : (a + c * 3)^2 = (a + 1) * (c * 3 + 1) * k)
    (hk' : (c + a * 3)^2 = (c + 1) * (a * 3 + 1) * k') :
    ∃ x y : ZMod N, (x + y * 3)^2 = (x + 1) * (y * 3 + 1) * (k : ZMod N) ∧
      (y + x * 3)^2 = (y + 1) * (x * 3 + 1) * (k' : ZMod N) :=
  ⟨a, c, by exact_mod_cast congrArg (fun t : ℕ => (t : ZMod N)) hk,
    by exact_mod_cast congrArg (fun t : ℕ => (t : ZMod N)) hk'⟩

end OMA.Helpers

theorem OMA.solution : OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H1_R1.H1 := by
  intro a c _ hs ht hab hcd
  have hao : Odd a := Nat.Odd.of_mul_left hab.1
  have hco : Odd c := Nat.Odd.of_mul_left (Nat.Odd.of_mul_right hab.1)
  obtain ⟨k, hk⟩ := OMA.Helpers.crystal_sq_dvd hao hab.2.2.2.2
  obtain ⟨k', hk'⟩ := OMA.Helpers.crystal_sq_dvd hco hcd.2.2.2.2
  have p1 : 0 < (a + 1) * (c * 3 + 1) := by positivity
  have p2 : 0 < (c + 1) * (a * 3 + 1) := by positivity
  rw [hk, hk', Nat.mul_div_cancel_left _ p1, Nat.mul_div_cancel_left _ p2]
  have u1 := OMA.Helpers.quot_bound hs ht hk
  have u2 := OMA.Helpers.quot_bound ht hs hk'
  have l1 := OMA.Helpers.quot_pos hab.2.1 hk
  have l2 := OMA.Helpers.quot_pos hcd.2.1 hk'
  interval_cases k <;> interval_cases k' <;> first
    | rfl
    | exact absurd (OMA.Helpers.modcheck 3 hk hk') (by decide)
    | exact absurd (OMA.Helpers.modcheck 5 hk hk') (by decide)
    | exact absurd (OMA.Helpers.modcheck 7 hk hk') (by decide)
    | exact absurd (OMA.Helpers.modcheck 9 hk hk') (by decide)
    | exact absurd (OMA.Helpers.modcheck 11 hk hk') (by decide)
