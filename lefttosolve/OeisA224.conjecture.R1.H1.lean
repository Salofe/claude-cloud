import OMAReductions.R_OeisA224_conjecture_R1

/-!
# Step H1 of the reduction OeisA224.conjecture.R1

For an odd prime `p` and `k ≥ 2`, the congruence `(p ^ k) ^ 2 ≡ 1 [MOD a (p ^ k) * (a (p ^ k) - 1)]`
fails, where `a n` (OEIS A000224) is the number of squares modulo `n`.

Only the upstream definition `OeisA224.a` is used, together with Mathlib.

* The squares modulo `p ^ (m + 2)` split into `p ^ 2` times the squares modulo `p ^ m` (from the
  multiples of `p`) and the squares of residues prime to `p`. Squaring is injective on the residues
  prime to `p` in the lower half of `[0, p ^ n)` and every unit square is hit there, so there are
  `φ (p ^ n) / 2` unit squares. Hence `2 a (p ^ (m + 2)) = 2 a (p ^ m) + p ^ (m + 1) (p - 1)`.
* With `a 1 = 1` and `2 a p = p + 1` this gives the closed forms
  `2 (p + 1) a (p ^ (2 j)) = p ^ (2 j + 1) + p + 2` and
  `2 (p + 1) a (p ^ (2 j + 1)) = p ^ (2 j + 2) + 2 p + 1`.
* Even exponent: `p` divides `a - 1`, hence the modulus, but not `(p ^ k) ^ 2 - 1`.
* Odd exponent `k = 2 j + 1`: `b = a - 1` satisfies `2 (p + 1) b = p ^ (2 j + 2) - 1`, so `b` divides
  `p ^ (2 j + 2) - 1`; if it also divided `p ^ (4 j + 2) - 1` it would divide `p ^ (2 j) - 1`,
  which is positive and smaller than `b`.
-/

namespace OMA.Helpers

open Finset

/-- Unfolding `OeisA224.a` at a nonzero argument. -/
theorem a224_eq_card (n : ℕ) (hn : n ≠ 0) :
    OeisA224.a n = ((range n).image (fun k : ℕ => k ^ 2 % n)).card := by
  unfold OeisA224.a
  rw [if_neg hn]

/-- There is one square modulo `1`. -/
theorem a224_one : OeisA224.a 1 = 1 := by
  rw [a224_eq_card 1 one_ne_zero]
  decide

/-- An odd prime is at least `3`. -/
theorem three_le_of_prime_ne_two (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : 3 ≤ p := by
  have := hp.two_le
  rcases hp.eq_two_or_odd with h | h
  · exact absurd h hp2
  · omega

/-- Squaring is injective on the residues prime to `p` in the lower half of `[0, p ^ n)`. -/
theorem sq_mod_injOn (p n : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Set.InjOn (fun x : ℕ => x ^ 2 % p ^ n)
      (((range (p ^ n)).filter (fun x => ¬ p ∣ x)).filter (fun x => 2 * x < p ^ n) : Finset ℕ) := by
  have key : ∀ x y : ℕ, x ≤ y → ¬ p ∣ y → 2 * x < p ^ n → 2 * y < p ^ n →
      x ^ 2 % p ^ n = y ^ 2 % p ^ n → x = y := by
    intro x y hxy hy hx2 hy2 h
    have hdvd : p ^ n ∣ (y + x) * (y - x) := by
      have h1 : p ^ n ∣ y ^ 2 - x ^ 2 := (Nat.modEq_iff_dvd' (Nat.pow_le_pow_left hxy 2)).mp h
      rwa [sq_tsub_sq] at h1
    by_cases hpx : p ∣ y + x
    · exfalso
      have hpy : ¬ p ∣ y - x := by
        intro hpy
        have h5 : p ∣ (y + x) + (y - x) := Nat.dvd_add hpx hpy
        have e : (y + x) + (y - x) = 2 * y := by omega
        rw [e] at h5
        rcases (Nat.Prime.dvd_mul hp).mp h5 with h2 | h2
        · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
        · exact hy h2
      have hcop : Nat.Coprime (p ^ n) (y - x) :=
        Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpy)
      have h3 : p ^ n ∣ y + x := hcop.dvd_of_dvd_mul_right hdvd
      have hy0 : 0 < y := by
        rcases Nat.eq_zero_or_pos y with h0 | h0
        · exact absurd (h0 ▸ dvd_zero p) hy
        · exact h0
      have := Nat.le_of_dvd (by omega) h3
      omega
    · have hcop : Nat.Coprime (p ^ n) (y + x) :=
        Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpx)
      have h3 : p ^ n ∣ y - x := hcop.dvd_of_dvd_mul_left hdvd
      have h4 : y - x = 0 := Nat.eq_zero_of_dvd_of_lt h3 (by omega)
      omega
  intro x hx y hy hxy
  simp only [coe_filter, mem_filter, mem_range, Set.mem_ofPred_eq] at hx hy
  rcases le_total x y with h | h
  · exact key x y h hy.1.2 hx.2 hy.2 hxy
  · exact (key y x h hx.1.2 hy.2 hx.2 hxy.symm).symm

/-- `(N - x) ^ 2` and `x ^ 2` agree modulo `N`. -/
theorem sub_sq_mod (N x : ℕ) (hx : x ≤ N) : (N - x) ^ 2 % N = x ^ 2 % N := by
  rw [← ZMod.natCast_eq_natCast_iff']
  push_cast [Nat.cast_sub hx]
  rw [ZMod.natCast_self]
  ring

/-- For an odd prime `p` and `n ≥ 1`, twice the number of squares modulo `p ^ n` of residues
prime to `p` is `φ (p ^ n) = p ^ (n - 1) * (p - 1)`. -/
theorem two_mul_card_unit_squares (p n : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n) :
    2 * (((range (p ^ n)).filter (fun x => ¬ p ∣ x)).image (fun x => x ^ 2 % p ^ n)).card
      = p ^ (n - 1) * (p - 1) := by
  have hpN : p ∣ p ^ n := dvd_pow_self p (by omega)
  have hNodd : p ^ n % 2 = 1 := by
    have hpo : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hp2
      · exact h
    rw [Nat.pow_mod, hpo, one_pow]
    rfl
  -- the residues prime to `p`
  have hDcard : ((range (p ^ n)).filter (fun x => ¬ p ∣ x)).card = p ^ (n - 1) * (p - 1) := by
    rw [← Nat.totient_prime_pow hp (by omega), Nat.totient_eq_card_coprime]
    congr 1
    ext x
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨hx, hpx⟩
      exact ⟨hx, Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpx)⟩
    · rintro ⟨hx, hc⟩
      refine ⟨hx, fun hpx => ?_⟩
      have h1 : p ∣ Nat.gcd (p ^ n) x := Nat.dvd_gcd hpN hpx
      rw [hc] at h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hpos : ∀ x, ¬ p ∣ x → x ≠ 0 := by
    rintro x hpx rfl
    exact hpx (dvd_zero p)
  have hsub : ∀ x, x ≤ p ^ n → ¬ p ∣ x → ¬ p ∣ p ^ n - x := by
    intro x hx hpx h
    apply hpx
    have h1 := Nat.dvd_sub hpN h
    rwa [Nat.sub_sub_self hx] at h1
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (range (p ^ n)).filter (fun x => ¬ p ∣ x)) (fun x => 2 * x < p ^ n)
  have hRL : (((range (p ^ n)).filter (fun x => ¬ p ∣ x)).filter (fun x => ¬ 2 * x < p ^ n)).card
      = (((range (p ^ n)).filter (fun x => ¬ p ∣ x)).filter (fun x => 2 * x < p ^ n)).card := by
    apply Finset.card_nbij' (fun x => p ^ n - x) (fun x => p ^ n - x)
    · intro x hx
      simp only [coe_filter, mem_filter, mem_range, Set.mem_ofPred_eq] at hx ⊢
      have := hpos x hx.1.2
      refine ⟨⟨by omega, hsub x (by omega) hx.1.2⟩, by omega⟩
    · intro x hx
      simp only [coe_filter, mem_filter, mem_range, Set.mem_ofPred_eq] at hx ⊢
      have := hpos x hx.1.2
      refine ⟨⟨by omega, hsub x (by omega) hx.1.2⟩, by omega⟩
    · intro x hx
      simp only [coe_filter, mem_filter, mem_range, Set.mem_ofPred_eq] at hx
      dsimp only
      omega
    · intro x hx
      simp only [coe_filter, mem_filter, mem_range, Set.mem_ofPred_eq] at hx
      dsimp only
      omega
  have himg : ((range (p ^ n)).filter (fun x => ¬ p ∣ x)).image (fun x => x ^ 2 % p ^ n)
      = (((range (p ^ n)).filter (fun x => ¬ p ∣ x)).filter (fun x => 2 * x < p ^ n)).image
          (fun x => x ^ 2 % p ^ n) := by
    apply le_antisymm
    · intro r hr
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hr
      by_cases h2 : 2 * x < p ^ n
      · exact mem_image.mpr ⟨x, mem_filter.mpr ⟨hx, h2⟩, rfl⟩
      · simp only [mem_filter, mem_range] at hx
        have := hpos x hx.2
        refine mem_image.mpr ⟨p ^ n - x, ?_, sub_sq_mod (p ^ n) x (by omega)⟩
        simp only [mem_filter, mem_range]
        exact ⟨⟨by omega, hsub x (by omega) hx.2⟩, by omega⟩
    · exact image_subset_image (filter_subset _ _)
  rw [himg, card_image_of_injOn (sq_mod_injOn p n hp hp2)]
  omega

/-- Squares modulo `p ^ (m + 2)`: the multiples of `p` contribute `p ^ 2` times the squares
modulo `p ^ m`, and the residues prime to `p` contribute the unit squares. -/
theorem squares_split (p m : ℕ) (hp : p.Prime) :
    (range (p ^ (m + 2))).image (fun x => x ^ 2 % p ^ (m + 2)) =
      ((range (p ^ m)).image (fun x => x ^ 2 % p ^ m)).image (fun r => p ^ 2 * r) ∪
      ((range (p ^ (m + 2))).filter (fun x => ¬ p ∣ x)).image (fun x => x ^ 2 % p ^ (m + 2)) := by
  have hmod : ∀ y : ℕ, (p * y) ^ 2 % p ^ (m + 2) = p ^ 2 * (y ^ 2 % p ^ m) := by
    intro y
    rw [mul_pow, pow_add, mul_comm (p ^ m) (p ^ 2), Nat.mul_mod_mul_left]
  ext r
  simp only [mem_union, mem_image, mem_range, mem_filter]
  constructor
  · rintro ⟨x, hx, rfl⟩
    by_cases hpx : p ∣ x
    · left
      obtain ⟨y, rfl⟩ := hpx
      exact ⟨y ^ 2 % p ^ m, ⟨y % p ^ m, Nat.mod_lt _ (pow_pos hp.pos m),
        (Nat.pow_mod y 2 (p ^ m)).symm⟩, (hmod y).symm⟩
    · right
      exact ⟨x, ⟨hx, hpx⟩, rfl⟩
  · rintro (⟨s, ⟨y, hy, rfl⟩, rfl⟩ | ⟨x, ⟨hx, _⟩, rfl⟩)
    · refine ⟨p * y, ?_, hmod y⟩
      have h1 : p * y < p * p ^ m := Nat.mul_lt_mul_of_pos_left hy hp.pos
      have h2 : p * p ^ m ≤ p ^ (m + 2) := by
        rw [← pow_succ']
        exact Nat.pow_le_pow_right hp.pos (by omega)
      omega
    · exact ⟨x, hx, rfl⟩

/-- The two parts of `squares_split` are disjoint: the first consists of multiples of `p`. -/
theorem squares_disjoint (p m : ℕ) (hp : p.Prime) :
    Disjoint (((range (p ^ m)).image (fun x => x ^ 2 % p ^ m)).image (fun r => p ^ 2 * r))
      (((range (p ^ (m + 2))).filter (fun x => ¬ p ∣ x)).image
        (fun x => x ^ 2 % p ^ (m + 2))) := by
  rw [Finset.disjoint_left]
  intro r hr1 hr2
  obtain ⟨s, _, rfl⟩ := mem_image.mp hr1
  obtain ⟨x, hx, hxr⟩ := mem_image.mp hr2
  rw [mem_filter] at hx
  apply hx.2
  have h1 : p ∣ x ^ 2 % p ^ (m + 2) := by
    rw [hxr]
    exact Dvd.dvd.mul_right (dvd_pow_self p two_ne_zero) s
  have h2 : p ∣ p ^ (m + 2) := dvd_pow_self p (by omega)
  have h3 : p ∣ x ^ 2 := (Nat.dvd_mod_iff h2).mp h1
  exact hp.dvd_of_dvd_pow h3

/-- The recursion `a (p ^ (m + 2)) = a (p ^ m) + p ^ (m + 1) * (p - 1) / 2`. -/
theorem a224_rec (p m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    2 * OeisA224.a (p ^ (m + 2)) = 2 * OeisA224.a (p ^ m) + p ^ (m + 1) * (p - 1) := by
  have hne : ∀ j, p ^ j ≠ 0 := fun j => pow_ne_zero j hp.ne_zero
  rw [a224_eq_card _ (hne _), a224_eq_card _ (hne _), squares_split p m hp,
    card_union_of_disjoint (squares_disjoint p m hp),
    card_image_of_injective _ (mul_right_injective₀ (hne 2)), mul_add,
    two_mul_card_unit_squares p (m + 2) hp hp2 (by omega)]
  rfl

/-- `a p = (p + 1) / 2` for an odd prime `p`. -/
theorem two_mul_a224_prime (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    2 * OeisA224.a p = p + 1 := by
  have hsplit : (range p).image (fun x => x ^ 2 % p) =
      {0} ∪ ((range (p ^ 1)).filter (fun x => ¬ p ∣ x)).image (fun x => x ^ 2 % p ^ 1) := by
    rw [pow_one]
    ext r
    simp only [mem_union, mem_singleton, mem_image, mem_range, mem_filter]
    constructor
    · rintro ⟨x, hx, rfl⟩
      by_cases hpx : p ∣ x
      · left
        have : x = 0 := Nat.eq_zero_of_dvd_of_lt hpx hx
        subst this
        simp
      · right
        exact ⟨x, ⟨hx, hpx⟩, rfl⟩
    · rintro (rfl | ⟨x, ⟨hx, _⟩, rfl⟩)
      · exact ⟨0, hp.pos, by simp⟩
      · exact ⟨x, hx, rfl⟩
  have hdisj : Disjoint ({0} : Finset ℕ)
      (((range (p ^ 1)).filter (fun x => ¬ p ∣ x)).image (fun x => x ^ 2 % p ^ 1)) := by
    rw [Finset.disjoint_singleton_left]
    intro h0
    obtain ⟨x, hx, hx0⟩ := mem_image.mp h0
    rw [mem_filter, pow_one] at hx
    rw [pow_one] at hx0
    apply hx.2
    have : p ∣ x ^ 2 := Nat.dvd_of_mod_eq_zero hx0
    exact hp.dvd_of_dvd_pow this
  have h := two_mul_card_unit_squares p 1 hp hp2 le_rfl
  rw [a224_eq_card p hp.ne_zero, hsplit, card_union_of_disjoint hdisj, card_singleton, mul_add, h]
  have := hp.two_le
  simp only [Nat.sub_self, pow_zero, one_mul]
  omega

/-- Closed form at even exponents: `2 (p + 1) a (p ^ (2 j)) = p ^ (2 j + 1) + p + 2`. -/
theorem a224_even (p j : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    2 * (p + 1) * OeisA224.a (p ^ (2 * j)) = p ^ (2 * j + 1) + p + 2 := by
  induction j with
  | zero =>
    simp only [mul_zero, pow_zero, a224_one, zero_add, pow_one]
    ring
  | succ j ih =>
    have h := a224_rec p (2 * j) hp hp2
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, show 2 * j + 2 + 1 = (2 * j + 1) + 2 by ring]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
    simp only [Nat.add_sub_cancel] at h
    calc 2 * (q + 1 + 1) * OeisA224.a ((q + 1) ^ (2 * j + 2))
        = (q + 2) * (2 * OeisA224.a ((q + 1) ^ (2 * j + 2))) := by ring
      _ = (q + 2) * (2 * OeisA224.a ((q + 1) ^ (2 * j)) + (q + 1) ^ (2 * j + 1) * q) := by
          rw [h]
      _ = 2 * (q + 1 + 1) * OeisA224.a ((q + 1) ^ (2 * j))
            + (q + 2) * q * (q + 1) ^ (2 * j + 1) := by ring
      _ = (q + 1) ^ (2 * j + 1) + (q + 1) + 2 + (q + 2) * q * (q + 1) ^ (2 * j + 1) := by
          rw [ih]
      _ = (q + 1) ^ (2 * j + 1 + 2) + (q + 1) + 2 := by ring

/-- Closed form at odd exponents: `2 (p + 1) a (p ^ (2 j + 1)) = p ^ (2 j + 2) + 2 p + 1`. -/
theorem a224_odd (p j : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    2 * (p + 1) * OeisA224.a (p ^ (2 * j + 1)) = p ^ (2 * j + 2) + 2 * p + 1 := by
  induction j with
  | zero =>
    have h := two_mul_a224_prime p hp hp2
    simp only [mul_zero, zero_add, pow_one]
    calc 2 * (p + 1) * OeisA224.a p = (p + 1) * (2 * OeisA224.a p) := by ring
      _ = (p + 1) * (p + 1) := by rw [h]
      _ = p ^ 2 + 2 * p + 1 := by ring
  | succ j ih =>
    have h := a224_rec p (2 * j + 1) hp hp2
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring,
      show 2 * (j + 1) + 2 = (2 * j + 2) + 2 by ring]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
    simp only [Nat.add_sub_cancel] at h
    calc 2 * (q + 1 + 1) * OeisA224.a ((q + 1) ^ (2 * j + 1 + 2))
        = (q + 2) * (2 * OeisA224.a ((q + 1) ^ (2 * j + 1 + 2))) := by ring
      _ = (q + 2) * (2 * OeisA224.a ((q + 1) ^ (2 * j + 1)) + (q + 1) ^ (2 * j + 1 + 1) * q) := by
          rw [h]
      _ = 2 * (q + 1 + 1) * OeisA224.a ((q + 1) ^ (2 * j + 1))
            + (q + 2) * q * (q + 1) ^ (2 * j + 1 + 1) := by ring
      _ = (q + 1) ^ (2 * j + 2) + 2 * (q + 1) + 1
            + (q + 2) * q * (q + 1) ^ (2 * j + 1 + 1) := by
          rw [ih]
      _ = (q + 1) ^ (2 * j + 2 + 2) + 2 * (q + 1) + 1 := by ring

end OMA.Helpers

/-- Odd prime powers with exponent at least `2` fail the congruence of Ordowski. -/
theorem OMA.solution : OMA.R_OeisA224_conjecture_R1.H1 := by
  intro p k hp hp2 hk hmod
  have hp3 := OMA.Helpers.three_le_of_prime_ne_two p hp hp2
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · -- even exponent `k = 2 j`: `p` divides `a - 1`
    have hA := OMA.Helpers.a224_even p j hp hp2
    obtain ⟨B, hB⟩ : ∃ B, OeisA224.a (p ^ (2 * j)) = B + 1 := by
      refine ⟨OeisA224.a (p ^ (2 * j)) - 1, ?_⟩
      rcases Nat.eq_zero_or_pos (OeisA224.a (p ^ (2 * j))) with h0 | h0
      · rw [h0, mul_zero] at hA
        omega
      · omega
    rw [hB, Nat.add_sub_cancel] at hmod
    rw [hB] at hA
    have e : 2 * (p + 1) * B + p = p ^ (2 * j + 1) := by linarith
    have hdvd : p ∣ B := by
      have h1 : p ∣ 2 * (p + 1) * B + p := e ▸ dvd_pow_self p (by omega)
      have h2 : p ∣ 2 * (p + 1) * B := (Nat.dvd_add_left (dvd_refl p)).mp h1
      have h3 : 2 * (p + 1) * B = p * (2 * B) + 2 * B := by ring
      rw [h3] at h2
      have h4 : p ∣ 2 * B := (Nat.dvd_add_right (dvd_mul_right p _)).mp h2
      rcases (Nat.Prime.dvd_mul hp).mp h4 with h5 | h5
      · have := Nat.le_of_dvd two_pos h5
        omega
      · exact h5
    have hdvd2 : p ∣ (B + 1) * B := Dvd.dvd.mul_left hdvd (B + 1)
    have h' := Nat.ModEq.of_dvd hdvd2 hmod
    have h1 : p ∣ (p ^ (2 * j)) ^ 2 := dvd_pow (dvd_pow_self p (by omega)) two_ne_zero
    unfold Nat.ModEq at h'
    rw [Nat.mod_eq_zero_of_dvd h1, Nat.mod_eq_of_lt hp.one_lt] at h'
    exact absurd h' zero_ne_one
  · -- odd exponent `k = 2 j + 1`: `a - 1 = (p ^ (2 j + 2) - 1) / (2 (p + 1))`
    have hA := OMA.Helpers.a224_odd p j hp hp2
    obtain ⟨B, hB⟩ : ∃ B, OeisA224.a (p ^ (2 * j + 1)) = B + 1 := by
      refine ⟨OeisA224.a (p ^ (2 * j + 1)) - 1, ?_⟩
      rcases Nat.eq_zero_or_pos (OeisA224.a (p ^ (2 * j + 1))) with h0 | h0
      · rw [h0, mul_zero] at hA
        omega
      · omega
    rw [hB, Nat.add_sub_cancel] at hmod
    rw [hB] at hA
    have e : 2 * (p + 1) * B + 1 = p ^ (2 * j + 2) := by linarith
    have hmodB : (p ^ (2 * j + 1)) ^ 2 ≡ 1 [MOD B] := Nat.ModEq.of_mul_left (B + 1) hmod
    have hB1 : p ^ (2 * j + 2) ≡ 1 [MOD B] := by
      rw [← e]
      unfold Nat.ModEq
      rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod]
    have hsq : (p ^ (2 * j + 1)) ^ 2 = p ^ (2 * j) * p ^ (2 * j + 2) := by ring
    rw [hsq] at hmodB
    have h3 : p ^ (2 * j) * p ^ (2 * j + 2) ≡ p ^ (2 * j) * 1 [MOD B] :=
      Nat.ModEq.mul_left _ hB1
    rw [mul_one] at h3
    have h4 : p ^ (2 * j) ≡ 1 [MOD B] := h3.symm.trans hmodB
    have h5 : B ∣ p ^ (2 * j) - 1 :=
      (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.pos)).mp h4.symm
    have h6 : 9 ≤ p ^ (2 * j) := by
      have h7 : p ^ 2 ≤ p ^ (2 * j) := Nat.pow_le_pow_right hp.pos (by omega)
      have h8 : 3 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      omega
    have h7 : B ≤ p ^ (2 * j) - 1 := Nat.le_of_dvd (by omega) h5
    have e2 : p ^ (2 * j + 2) = p ^ (2 * j) * p ^ 2 := by ring
    rw [e2] at e
    generalize p ^ (2 * j) = X at e h6 h7
    have h8 : B + 1 ≤ X := by omega
    have h9 : 2 * (p + 1) * (B + 1) ≤ 2 * (p + 1) * X := Nat.mul_le_mul_left _ h8
    have h10 : X * p * 3 ≤ X * p * p := Nat.mul_le_mul_left _ hp3
    have h11 : X * 3 ≤ X * p := Nat.mul_le_mul_left _ hp3
    nlinarith
