import OMAReductions.R_OeisA7406_conjecture_R1

/-!
# Step H1 of reduction OeisA7406.conjecture.R1

The prime case of the Wolstenholme numerator: for a prime p > 3, p divides the numerator of
S = sum_{k=1}^{p-1} 1/k^2.

Proof: with D = ((p-1)!)^2 and N = sum_k D/k^2 (exact divisions), S * D = N. In ZMod p,
N = D * sum_k (k^-1)^2 = D * sum_{x in ZMod p} x^2 = 0 because 2 < p - 1, while D is a unit.
From num(S) * D = N * den(S) we get p | num(S), hence gcd p (a (p-1)) = p = A089026(p).
-/

namespace OMA.Helpers

/-- In `ZMod p` (p > 3 prime), the sum of the squares of the inverses of all elements vanishes. -/
theorem a7406_sum_inv_sq_univ (p : ℕ) [Fact p.Prime] (h3 : 3 < p) :
    ∑ x : ZMod p, (x⁻¹) ^ 2 = 0 := by
  rw [show (∑ x : ZMod p, (x⁻¹) ^ 2) = ∑ x : ZMod p, x ^ 2 from
    Fintype.sum_equiv (Equiv.inv (ZMod p)) _ _ (fun x => by simp)]
  apply FiniteField.sum_pow_lt_card_sub_one
  rw [ZMod.card]; omega

/-- The integers 1, ..., p - 1 are nonzero in `ZMod p`. -/
theorem a7406_natCast_ne_zero_of_mem (p : ℕ) (k : ℕ) (hk : k ∈ Finset.Icc 1 (p - 1)) :
    (k : ZMod p) ≠ 0 := by
  rw [Finset.mem_Icc] at hk
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)

/-- The same vanishing, indexed by the natural numbers 1, ..., p - 1. -/
theorem a7406_sum_inv_sq_Icc (p : ℕ) [Fact p.Prime] (h3 : 3 < p) :
    ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2 = 0 := by
  rw [← a7406_sum_inv_sq_univ p h3]
  have e : (Finset.Icc 1 (p - 1)).image (fun k : ℕ => (k : ZMod p)) = Finset.univ.erase 0 := by
    ext x
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact a7406_natCast_ne_zero_of_mem p k hk
    · intro hx
      refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
      rw [Finset.mem_Icc]
      constructor
      · exact Nat.pos_of_ne_zero (by simpa [ZMod.val_eq_zero] using hx)
      · have := ZMod.val_lt x; omega
  rw [← Finset.sum_erase (f := fun x : ZMod p => (x⁻¹) ^ 2) (a := 0) _ (by simp), ← e,
    Finset.sum_image]
  intro a ha b hb hab
  simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
  have := (ZMod.natCast_eq_natCast_iff' a b p).mp hab
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

/-- For a prime p > 3, p divides the numerator of sum_{k=1}^{p-1} 1/k^2. -/
theorem a7406_prime_dvd_num (p : ℕ) (hp : p.Prime) (h3 : 3 < p) :
    (p : ℤ) ∣ (∑ k ∈ Finset.Icc 1 (p - 1), (1 : ℚ) / (k : ℚ) ^ 2).num := by
  have := Fact.mk hp
  set S : ℚ := ∑ k ∈ Finset.Icc 1 (p - 1), (1 : ℚ) / (k : ℚ) ^ 2 with hS
  set D : ℕ := ((p - 1).factorial) ^ 2 with hD
  have hkD : ∀ k ∈ Finset.Icc 1 (p - 1), k ^ 2 ∣ D := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact pow_dvd_pow_of_dvd (Nat.dvd_factorial hk.1 hk.2) 2
  set N : ℕ := ∑ k ∈ Finset.Icc 1 (p - 1), D / k ^ 2 with hN
  -- clearing denominators
  have h1 : S * D = N := by
    rw [hS, hN, Finset.sum_mul, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : (k : ℚ) ≠ 0 := by
      rw [Finset.mem_Icc] at hk
      exact_mod_cast (show k ≠ 0 by omega)
    rw [Nat.cast_div (hkD k hk) (by push_cast; exact pow_ne_zero 2 hk0)]
    push_cast
    ring
  -- the cleared numerator vanishes modulo p
  have h2 : (N : ZMod p) = 0 := by
    rw [hN, Nat.cast_sum]
    have key : ∀ k ∈ Finset.Icc 1 (p - 1),
        (((D / k ^ 2 : ℕ)) : ZMod p) = (D : ZMod p) * ((k : ZMod p)⁻¹) ^ 2 := by
      intro k hk
      have hk0 : (k : ZMod p) ≠ 0 := a7406_natCast_ne_zero_of_mem p k hk
      have hkpos : 0 < k ^ 2 := by
        rw [Finset.mem_Icc] at hk
        exact pow_pos (by omega) 2
      obtain ⟨m, hm⟩ := hkD k hk
      rw [hm, Nat.mul_div_cancel_left m hkpos]
      push_cast
      field_simp
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum, a7406_sum_inv_sq_Icc p h3, mul_zero]
  -- transfer to the reduced numerator
  have h3' : (S.num : ℚ) * D = N * S.den := by
    rw [← Rat.mul_den_eq_num, mul_right_comm, h1]
  have h4 : S.num * (D : ℤ) = (N : ℤ) * S.den := by
    exact_mod_cast h3'
  have h5 : ((S.num : ℤ) : ZMod p) * (D : ZMod p) = 0 := by
    have := congrArg (fun z : ℤ => (z : ZMod p)) h4
    push_cast at this
    rw [this, h2, zero_mul]
  have hD0 : (D : ZMod p) ≠ 0 := by
    rw [hD, Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := hp.dvd_of_dvd_pow hd
    rw [hp.dvd_factorial] at this
    omega
  have h6 : ((S.num : ℤ) : ZMod p) = 0 := by
    rcases mul_eq_zero.mp h5 with h | h
    · exact h
    · exact absurd h hD0
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h6

end OMA.Helpers

theorem OMA.solution : OMA.R_OeisA7406_conjecture_R1.H1 := by
  intro n hn hp
  have hd : n ∣ OeisA7406.a (n - 1) := by
    unfold OeisA7406.a
    exact Int.ofNat_dvd_left.mp (OMA.Helpers.a7406_prime_dvd_num n hp hn)
  rw [Nat.gcd_eq_left hd]
  simp [OeisA89026.a, hp]
