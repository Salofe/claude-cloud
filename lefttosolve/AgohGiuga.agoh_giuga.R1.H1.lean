import OMAReductions.R_AgohGiuga_agoh_giuga_R1

/-!
# Step H1 of the reduction AgohGiuga.agoh_giuga.R1 (Kellner's equivalence)

For every `n ≥ 2`, Agoh's congruence `n ^ 2 ∣ n * num (B'_{n-1}) + den (B'_{n-1})` holds if and
only if Giuga's congruence `n ∣ 1 + ∑_{0 < i < n} i ^ (n - 1)` holds.

Only Mathlib is used: Faulhaber's formula `sum_range_pow`, the von Staudt-Clausen theorem
`Bernoulli.vonStaudt_clausen` and the vanishing of odd Bernoulli numbers. No upstream theorem
of formal-conjectures is used.

Proof outline.

* `n = 2`: both sides hold (`B'_1 = 1/2`).
* `n ≥ 4` even: `B'_{n-1} = 0`, so Agoh's congruence would give `n ^ 2 ∣ 1`. Giuga's fails
  as well: pairing `i` with `n - i` (and `n - 1` odd) gives `2 S = 0` modulo `n`, so
  `n ∣ 1 + S` would force `n ∣ 2`.
* `n` odd: write `S = n B + R` (Faulhaber, `B = B_{n-1}`). For a prime power `p ^ e ∣ n`
  with `e ≥ 1`, von Staudt-Clausen (`p * B_j` is `p`-integral) shows that `R` is divisible by
  `p ^ e` in `ℤ_(p)` (the only term with a single factor `n` has an odd index, hence is `0`
  or `B_1 = -1/2`, and `p` is odd). Both congruences are then equivalent, prime power by prime
  power, to `p ^ e ∣ 1 + n B` in `ℤ_(p)`; for Agoh's side one uses `den B * (1 + n B) =
  n num B + den B`, that `p ^ 2` does not divide `den B`, and that `p ^ e ∣ 1 + n B` forces
  `p ∣ den B` and `e = 1`.

Divisibility in `ℤ_(p)` is handled through the elementary predicate `PD p e x`
(`x * b = p ^ e * a` for integers `a`, `b` with `p` not dividing `b`).
-/

namespace OMA.Helpers

open Finset

-- ### Divisibility by prime powers in the local ring `ℤ_(p)`

/-- `PD p e x`: the rational `x` is divisible by `p ^ e` in the local ring `ℤ_(p)`. -/
def PD (p e : ℕ) (x : ℚ) : Prop := ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ x * b = (p : ℚ) ^ e * a

variable {p : ℕ}

theorem not_dvd_one_int (hp : p.Prime) : ¬ (p : ℤ) ∣ 1 := by
  intro h
  exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp h)

theorem prime_int (hp : p.Prime) : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp

theorem not_dvd_mul_int (hp : p.Prime) {b b' : ℤ} (hb : ¬ (p : ℤ) ∣ b) (hb' : ¬ (p : ℤ) ∣ b') :
    ¬ (p : ℤ) ∣ b * b' := by
  intro h
  rcases (prime_int hp).dvd_or_dvd h with h | h
  · exact hb h
  · exact hb' h

theorem PD_zero (hp : p.Prime) (e : ℕ) : PD p e 0 :=
  ⟨0, 1, not_dvd_one_int hp, by simp⟩

theorem PD_add (hp : p.Prime) {e : ℕ} {x y : ℚ} (hx : PD p e x) (hy : PD p e y) :
    PD p e (x + y) := by
  obtain ⟨a, b, hb, h1⟩ := hx
  obtain ⟨a', b', hb', h2⟩ := hy
  refine ⟨a * b' + a' * b, b * b', not_dvd_mul_int hp hb hb', ?_⟩
  push_cast
  linear_combination (b' : ℚ) * h1 + (b : ℚ) * h2

theorem PD_neg {e : ℕ} {x : ℚ} (hx : PD p e x) : PD p e (-x) := by
  obtain ⟨a, b, hb, h1⟩ := hx
  exact ⟨-a, b, hb, by push_cast; linear_combination -h1⟩

theorem PD_sub (hp : p.Prime) {e : ℕ} {x y : ℚ} (hx : PD p e x) (hy : PD p e y) :
    PD p e (x - y) := by
  rw [sub_eq_add_neg]
  exact PD_add hp hx (PD_neg hy)

theorem PD_mul (hp : p.Prime) {e f : ℕ} {x y : ℚ} (hx : PD p e x) (hy : PD p f y) :
    PD p (e + f) (x * y) := by
  obtain ⟨a, b, hb, h1⟩ := hx
  obtain ⟨a', b', hb', h2⟩ := hy
  refine ⟨a * a', b * b', not_dvd_mul_int hp hb hb', ?_⟩
  push_cast
  rw [pow_add]
  linear_combination (y * b') * h1 + ((p : ℚ) ^ e * a) * h2

theorem PD_mono {e f : ℕ} {x : ℚ} (hx : PD p f x) (hef : e ≤ f) : PD p e x := by
  obtain ⟨a, b, hb, h1⟩ := hx
  refine ⟨(p : ℤ) ^ (f - e) * a, b, hb, ?_⟩
  rw [h1]
  push_cast
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hef]

theorem PD_of_dvd (hp : p.Prime) {e : ℕ} {z : ℤ} (h : (p : ℤ) ^ e ∣ z) : PD p e (z : ℚ) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, 1, not_dvd_one_int hp, by rw [hc]; push_cast; ring⟩

theorem dvd_of_PD (hp : p.Prime) {e : ℕ} {z : ℤ} (h : PD p e (z : ℚ)) : (p : ℤ) ^ e ∣ z := by
  obtain ⟨a, b, hb, h1⟩ := h
  have h2 : z * b = (p : ℤ) ^ e * a := by exact_mod_cast h1
  have hcop : IsCoprime ((p : ℤ) ^ e) b :=
    IsCoprime.pow_left (((prime_int hp).coprime_iff_not_dvd).mpr hb)
  exact hcop.dvd_of_dvd_mul_right ⟨a, h2⟩

theorem PD_natCast (hp : p.Prime) {e m : ℕ} (h : p ^ e ∣ m) : PD p e (m : ℚ) := by
  have h' : (p : ℤ) ^ e ∣ (m : ℤ) := by exact_mod_cast h
  simpa using PD_of_dvd hp h'

theorem dvd_of_PD_nat (hp : p.Prime) {e m : ℕ} (h : PD p e (m : ℚ)) : p ^ e ∣ m := by
  have h' : PD p e ((m : ℤ) : ℚ) := by simpa using h
  exact_mod_cast dvd_of_PD hp h'

theorem PD_nat0 (hp : p.Prime) (m : ℕ) : PD p 0 (m : ℚ) := PD_natCast hp (by simp)

theorem PD_div (hp : p.Prime) {f : ℕ} {x : ℚ} (h : PD p (f + 1) (p * x)) : PD p f x := by
  obtain ⟨a, b, hb, h1⟩ := h
  refine ⟨a, b, hb, ?_⟩
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  apply mul_left_cancel₀ hp0
  rw [pow_succ] at h1
  linear_combination h1

theorem PD_sum (hp : p.Prime) {e : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, PD p e (f i)) : PD p e (∑ i ∈ s, f i) :=
  Finset.sum_induction f (PD p e) (fun _ _ => PD_add hp) (PD_zero hp e) h

-- ### `p`-integrality of `p * B_i` (von Staudt-Clausen)

theorem PD_inv_prime (hp : p.Prime) {q : ℕ} (hq : q.Prime) : PD p 0 ((p : ℚ) * (1 / q)) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  by_cases hpq : q = p
  · subst hpq
    have h1 : (q : ℚ) * (1 / q) = ((1 : ℤ) : ℚ) := by
      rw [one_div, mul_inv_cancel₀ hq0]; simp
    rw [h1]
    exact PD_of_dvd hp (by simp)
  · refine ⟨p, q, ?_, ?_⟩
    · intro h
      have h' : p ∣ q := Int.natCast_dvd_natCast.mp h
      exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h').symm
    · push_cast
      rw [one_div, mul_assoc, inv_mul_cancel₀ hq0]
      simp

/-- For every prime `p` and every `i`, `p * B_i` is `p`-integral. -/
theorem PD_bernoulli (hp : p.Prime) (i : ℕ) : PD p 0 ((p : ℚ) * bernoulli i) := by
  rcases Nat.even_or_odd i with ⟨k, rfl⟩ | hodd
  · obtain ⟨T, hT⟩ := Bernoulli.vonStaudt_clausen k
    have hk : k + k = 2 * k := by ring
    rw [hk]
    have h1 : (p : ℚ) * bernoulli (2 * k) = (((p : ℤ) * T : ℤ) : ℚ) -
        ∑ q ∈ (range (2 * k + 2)).filter (fun q => q.Prime ∧ (q - 1) ∣ 2 * k),
          (p : ℚ) * (1 / q) := by
      rw [← Finset.mul_sum]
      push_cast
      rw [hT]
      ring
    rw [h1]
    apply PD_sub hp
    · exact PD_of_dvd hp (by simp)
    · apply PD_sum hp
      intro q hq
      exact PD_inv_prime hp (Finset.mem_filter.mp hq).2.1
  · rcases Nat.lt_or_ge 1 i with h1 | h1
    · rw [bernoulli_eq_zero_of_odd hodd h1, mul_zero]
      exact PD_zero hp 0
    · have hi : i = 1 := by obtain ⟨j, rfl⟩ := hodd; omega
      subst hi
      rw [bernoulli_one]
      by_cases hp2 : p = 2
      · subst hp2
        have h2 : ((2 : ℕ) : ℚ) * (-1 / 2) = ((-1 : ℤ) : ℚ) := by norm_num
        rw [h2]
        exact PD_of_dvd hp (by simp)
      · refine ⟨-p, 2, ?_, ?_⟩
        · intro h
          have h' : p ∣ 2 := by exact_mod_cast h
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
        · push_cast
          ring

/-- For an odd prime `p` and odd `i`, `B_i` itself is `p`-integral. -/
theorem PD_bernoulli_odd (hp : p.Prime) (hp2 : p ≠ 2) {i : ℕ} (hodd : Odd i) :
    PD p 0 (bernoulli i) := by
  rcases Nat.lt_or_ge 1 i with h1 | h1
  · rw [bernoulli_eq_zero_of_odd hodd h1]
    exact PD_zero hp 0
  · have hi : i = 1 := by obtain ⟨j, rfl⟩ := hodd; omega
    subst hi
    rw [bernoulli_one]
    refine ⟨-1, 2, ?_, ?_⟩
    · intro h
      have h' : p ∣ 2 := by exact_mod_cast h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
    · push_cast
      ring

/-- If `p * B` is `p`-integral then `p ^ 2` does not divide the denominator of `B`. -/
theorem not_sq_dvd_den (hp : p.Prime) {B : ℚ} (hB : PD p 0 ((p : ℚ) * B)) : ¬ p ^ 2 ∣ B.den := by
  rintro ⟨c, hc⟩
  obtain ⟨a, b, hb, h1⟩ := hB
  have hBD : B * B.den = B.num := Rat.mul_den_eq_num B
  have h2 : (p : ℤ) * B.num * b = a * B.den := by
    have h3 : (p : ℚ) * B.num * b = a * B.den := by
      rw [← hBD]
      linear_combination (B.den : ℚ) * h1
    exact_mod_cast h3
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h4 : (p : ℤ) ∣ B.num * b := by
    refine ⟨a * c, mul_left_cancel₀ hp0 ?_⟩
    rw [← mul_assoc, h2, hc]
    push_cast
    ring
  rcases (prime_int hp).dvd_or_dvd h4 with h5 | h5
  · have h6 : p ∣ B.num.natAbs := Int.natCast_dvd.mp h5
    have h7 : p ∣ B.den := ⟨p * c, by rw [hc]; ring⟩
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h6 B.reduced) h7)
  · exact hb h5

-- ### Faulhaber's formula and the remainder term

theorem sum_Ioo_cast (n : ℕ) (hn : 2 ≤ n) :
    ((∑ i ∈ Ioo 0 n, i ^ (n - 1) : ℕ) : ℚ) = ∑ i ∈ range n, (i : ℚ) ^ (n - 1) := by
  push_cast
  rw [range_eq_Ico, ← Finset.Ioo_insert_left (by omega : 0 < n), sum_insert (by simp)]
  have h0 : ((0 : ℕ) : ℚ) ^ (n - 1) = 0 := by
    rw [Nat.cast_zero, zero_pow (by omega)]
  rw [h0, zero_add]

/-- Faulhaber's formula for `∑_{i ≤ m} i ^ m`, with the leading term `(m + 1) B_m` split off. -/
theorem faulhaber_split (m : ℕ) :
    ∑ i ∈ range (m + 1), (i : ℚ) ^ m = ((m + 1 : ℕ) : ℚ) * bernoulli m +
      ∑ i ∈ range m, bernoulli i * ((m + 1).choose i : ℚ) * ((m + 1 : ℕ) : ℚ) ^ (m - i) := by
  rw [sum_range_pow, sum_range_succ, Nat.choose_succ_self_right, show m + 1 - m = 1 by omega]
  have h0 : ((m : ℚ) + 1) ≠ 0 := by positivity
  rw [add_comm]
  congr 1
  · push_cast
    field_simp
  · apply sum_congr rfl
    intro i hi
    have hi' : i < m := mem_range.mp hi
    rw [show m + 1 - i = (m - i) + 1 by omega, pow_succ]
    push_cast
    field_simp

/-- The non-leading part of Faulhaber's sum is divisible, in `ℤ_(p)`, by every prime power
`p ^ e` (with `e ≥ 1`) dividing the odd number `n = m + 1`. -/
theorem PD_rest (hp : p.Prime) {m e : ℕ} (hm : Even m) (he : 1 ≤ e) (hpe : p ^ e ∣ m + 1) :
    PD p e (∑ i ∈ range m, bernoulli i * ((m + 1).choose i : ℚ) * ((m + 1 : ℕ) : ℚ) ^ (m - i)) := by
  apply PD_sum hp
  intro i hi
  have hi' : i < m := mem_range.mp hi
  have hn : PD p e ((m + 1 : ℕ) : ℚ) := PD_natCast hp hpe
  have hC : PD p 0 ((m + 1).choose i : ℚ) := PD_nat0 hp _
  rcases Nat.lt_or_ge (i + 1) m with h2 | h2
  · -- at least two factors `n`, and `p * B_i` is `p`-integral
    obtain ⟨k, hk⟩ : ∃ k, m - i = k + 2 := ⟨m - i - 2, by omega⟩
    have hpB := PD_bernoulli hp i
    have hrest : PD p 0 (((m + 1 : ℕ) : ℚ) ^ k) := by
      have := PD_nat0 hp ((m + 1) ^ k)
      simpa using this
    have h3 := PD_mul hp (PD_mul hp (PD_mul hp (PD_mul hp hpB hC) hn) hn) hrest
    have h4 : (p : ℚ) * bernoulli i * ((m + 1).choose i : ℚ) * ((m + 1 : ℕ) : ℚ) *
        ((m + 1 : ℕ) : ℚ) * ((m + 1 : ℕ) : ℚ) ^ k =
        (p : ℚ) * (bernoulli i * ((m + 1).choose i : ℚ) * ((m + 1 : ℕ) : ℚ) ^ (m - i)) := by
      rw [hk, pow_add]
      ring
    rw [h4, show 0 + 0 + e + e + 0 = (2 * e - 1) + 1 by omega] at h3
    exact PD_mono (PD_div hp h3) (by omega)
  · -- the index `i = m - 1` is odd and `p` is odd
    have hodd : Odd i := by
      obtain ⟨k, hk⟩ := hm
      exact ⟨k - 1, by omega⟩
    have hp2 : p ≠ 2 := by
      rintro rfl
      have h5 : 2 ∣ m + 1 := dvd_trans (dvd_pow_self 2 (by omega)) hpe
      obtain ⟨k, hk⟩ := hm
      omega
    have h3 := PD_mul hp (PD_mul hp (PD_bernoulli_odd hp hp2 hodd) hC) hn
    rw [show m - i = 1 by omega, pow_one]
    simpa using h3

-- ### The comparison, prime power by prime power

/-- For `p ^ e ∣ n` with `e ≥ 1`, Agoh's condition at `p ^ e` (that is, `p ^ (2 e)` divides
`n num B + den B`) is equivalent to Giuga's condition `p ^ e ∣ Z`, where `Z = 1 + n B + R`
and `R` is divisible by `p ^ e` in `ℤ_(p)`. -/
theorem key_pp (hp : p.Prime) {n e Z : ℕ} {B R : ℚ} (he : 1 ≤ e) (hpe : p ^ e ∣ n)
    (hZ : (Z : ℚ) = 1 + n * B + R) (hR : PD p e R) (hB : PD p 0 ((p : ℚ) * B)) :
    (p : ℤ) ^ (2 * e) ∣ (n : ℤ) * B.num + B.den ↔ p ^ e ∣ Z := by
  have hBD : B * B.den = B.num := Rat.mul_den_eq_num B
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hY : (((n : ℤ) * B.num + B.den : ℤ) : ℚ) = (B.den : ℚ) * (1 + n * B) := by
    push_cast
    rw [← hBD]
    ring
  have hZX : p ^ e ∣ Z ↔ PD p e (1 + n * B) := by
    constructor
    · intro h
      have h1 : (1 + n * B) = (Z : ℚ) - R := by rw [hZ]; ring
      rw [h1]
      exact PD_sub hp (PD_natCast hp h) hR
    · intro h
      apply dvd_of_PD_nat hp
      rw [hZ]
      exact PD_add hp h hR
  have hDsq := not_sq_dvd_den hp hB
  rw [hZX]
  constructor
  · intro hdvd
    have hPY : PD p (2 * e) ((B.den : ℚ) * (1 + n * B)) := by
      rw [← hY]
      exact PD_of_dvd hp hdvd
    obtain ⟨a, b, hb, h1⟩ := hPY
    by_cases hpD : p ∣ B.den
    · obtain ⟨D', hD'⟩ := hpD
      have hpD' : ¬ (p : ℤ) ∣ (D' : ℤ) := by
        intro h
        apply hDsq
        rw [hD', pow_two]
        exact Nat.mul_dvd_mul_left p (Int.natCast_dvd_natCast.mp h)
      refine PD_mono (f := 2 * e - 1) ⟨a, D' * b, not_dvd_mul_int hp hpD' hb, ?_⟩ (by omega)
      apply mul_left_cancel₀ hp0
      rw [hD'] at h1
      have hpow : (p : ℚ) ^ (2 * e) = p * p ^ (2 * e - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [hpow] at h1
      push_cast at h1 ⊢
      linear_combination h1
    · have hpD : ¬ (p : ℤ) ∣ (B.den : ℤ) := fun h => hpD (Int.natCast_dvd_natCast.mp h)
      refine PD_mono (f := 2 * e) ⟨a, B.den * b, not_dvd_mul_int hp hpD hb, ?_⟩ (by omega)
      push_cast
      linear_combination h1
  · intro hX
    have hX1 : PD p 1 (1 + n * B) := PD_mono hX he
    have key : ¬ PD p 1 (n * B) := by
      intro h
      have h1 : PD p 1 ((1 + n * B) - n * B) := PD_sub hp hX1 h
      have h2 : (1 + n * B) - n * B = ((1 : ℤ) : ℚ) := by push_cast; ring
      rw [h2] at h1
      have h3 := dvd_of_PD hp h1
      rw [pow_one] at h3
      exact not_dvd_one_int hp h3
    have hpn : p ∣ n := dvd_trans (dvd_pow_self p (by omega)) hpe
    have hpD : p ∣ B.den := by
      by_contra hpD
      apply key
      have hn : PD p 1 (n : ℚ) := PD_natCast hp (by rw [pow_one]; exact hpn)
      have hB0 : PD p 0 B :=
        ⟨B.num, B.den, fun h => hpD (Int.natCast_dvd_natCast.mp h), by push_cast; rw [hBD]; simp⟩
      simpa using PD_mul hp hn hB0
    have hn2 : ¬ p ^ 2 ∣ n := by
      intro h
      apply key
      apply PD_div hp
      have h2 : PD p 2 (n : ℚ) := PD_natCast hp h
      have h3 := PD_mul hp h2 hB
      have h4 : (n : ℚ) * ((p : ℚ) * B) = (p : ℚ) * (n * B) := by ring
      rw [h4] at h3
      simpa using h3
    have he1 : e = 1 := by
      by_contra h
      exact hn2 (dvd_trans (pow_dvd_pow p (by omega)) hpe)
    subst he1
    obtain ⟨D', hD'⟩ := hpD
    apply dvd_of_PD hp
    rw [hY]
    have hp1 : PD p 1 (p : ℚ) := PD_natCast hp (by simp)
    have h3 := PD_mul hp (PD_mul hp hp1 (PD_nat0 hp D')) hX1
    rw [hD']
    push_cast
    simpa using h3

/-- `n ^ 2 ∣ Y` can be tested on the prime powers dividing `n`. -/
theorem sq_dvd_iff (n : ℕ) (hn : n ≠ 0) (Y : ℤ) :
    (n : ℤ) ^ 2 ∣ Y ↔ ∀ p e : ℕ, p.Prime → p ^ e ∣ n → (p : ℤ) ^ (2 * e) ∣ Y := by
  constructor
  · intro h p e _ hpe
    have h1 : (p ^ e) ^ 2 ∣ n ^ 2 := pow_dvd_pow_of_dvd hpe 2
    have h2 : (p : ℤ) ^ (2 * e) = (((p ^ e) ^ 2 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [h2]
    exact dvd_trans (by exact_mod_cast h1) h
  · intro h
    have h1 : n ^ 2 ∣ Y.natAbs := by
      rw [Nat.dvd_iff_prime_pow_dvd_dvd]
      intro p k hp hpk
      have hk : k ≤ 2 * n.factorization p := by
        have h3 := (hp.pow_dvd_iff_le_factorization (pow_ne_zero 2 hn)).mp hpk
        simpa [Nat.factorization_pow] using h3
      have h4 := h p (n.factorization p) hp (Nat.ordProj_dvd n p)
      have h5 : p ^ (2 * n.factorization p) ∣ Y.natAbs := by
        apply Int.natCast_dvd.mp
        exact_mod_cast h4
      exact dvd_trans (pow_dvd_pow p hk) h5
    have h6 : ((n ^ 2 : ℕ) : ℤ) ∣ Y := Int.natCast_dvd.mpr h1
    exact_mod_cast h6

/-- Assembly over all prime powers dividing `n`. -/
theorem odd_assembly {n Z : ℕ} {B R : ℚ} (hn : n ≠ 0)
    (hZ : (Z : ℚ) = 1 + n * B + R)
    (hR : ∀ p e : ℕ, p.Prime → 1 ≤ e → p ^ e ∣ n → PD p e R)
    (hB : ∀ p : ℕ, p.Prime → PD p 0 ((p : ℚ) * B)) :
    (∃ k : ℤ, (n : ℤ) * B.num + B.den = k * (n : ℤ) ^ 2) ↔ n ∣ Z := by
  have h1 : (∃ k : ℤ, (n : ℤ) * B.num + B.den = k * (n : ℤ) ^ 2) ↔
      (n : ℤ) ^ 2 ∣ (n : ℤ) * B.num + B.den := by
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [hk]; ring⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [hk]; ring⟩
  rw [h1, sq_dvd_iff n hn, Nat.dvd_iff_prime_pow_dvd_dvd Z n]
  constructor
  · intro h p e hp hpe
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp
    · exact (key_pp hp he hpe hZ (hR p e hp he hpe) (hB p hp)).mp (h p e hp hpe)
  · intro h p e hp hpe
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp
    · exact (key_pp hp he hpe hZ (hR p e hp he hpe) (hB p hp)).mpr (h p e hp hpe)

/-- The odd case `n = m + 1`, with `m` even and `m ≥ 2`. -/
theorem odd_case (m : ℕ) (hm : Even m) (hm2 : 2 ≤ m) :
    (∃ k : ℤ, ((m + 1 : ℕ) : ℤ) * (bernoulli' m).num + (bernoulli' m).den =
      k * ((m + 1 : ℕ) : ℤ) ^ 2) ↔ (m + 1) ∣ 1 + ∑ i ∈ Ioo 0 (m + 1), i ^ m := by
  rw [← bernoulli_eq_bernoulli'_of_ne_one (by omega)]
  apply odd_assembly (B := bernoulli m)
    (R := ∑ i ∈ range m, bernoulli i * ((m + 1).choose i : ℚ) * ((m + 1 : ℕ) : ℚ) ^ (m - i))
    (by omega)
  · have h1 := sum_Ioo_cast (m + 1) (by omega)
    rw [Nat.add_sub_cancel] at h1
    push_cast [h1]
    rw [faulhaber_split m]
    push_cast
    ring
  · intro p e hp he hpe
    exact PD_rest hp hm he hpe
  · intro p hp
    exact PD_bernoulli hp m

-- ### The even case and `n = 2`

/-- For even `n ≥ 3`, Giuga's congruence fails: pairing `i` with `n - i` shows `n ∣ 2 S`. -/
theorem even_not_dvd (n : ℕ) (hn : 3 ≤ n) (hev : Even n) :
    ¬ n ∣ 1 + ∑ i ∈ Ioo 0 n, i ^ (n - 1) := by
  intro h
  have hodd : Odd (n - 1) := by
    obtain ⟨k, hk⟩ := hev
    exact ⟨k - 1, by omega⟩
  have h1 : ((1 + ∑ i ∈ Ioo 0 n, i ^ (n - 1) : ℕ) : ZMod n) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr h
  push_cast at h1
  set S := ∑ i ∈ Ioo 0 n, ((i : ZMod n)) ^ (n - 1) with hS
  have h2 : S = ∑ i ∈ Ioo 0 n, (((n - i : ℕ) : ZMod n)) ^ (n - 1) := by
    apply Finset.sum_nbij' (fun i => n - i) (fun i => n - i)
    · intro i hi
      simp only [mem_Ioo] at hi ⊢
      omega
    · intro i hi
      simp only [mem_Ioo] at hi ⊢
      omega
    · intro i hi
      simp only [mem_Ioo] at hi
      omega
    · intro i hi
      simp only [mem_Ioo] at hi
      omega
    · intro i hi
      simp only [mem_Ioo] at hi
      rw [Nat.sub_sub_self hi.2.le]
  have h3 : ∀ i ∈ Ioo 0 n, (((n - i : ℕ) : ZMod n)) ^ (n - 1) = -((i : ZMod n) ^ (n - 1)) := by
    intro i hi
    rw [Nat.cast_sub (mem_Ioo.mp hi).2.le, ZMod.natCast_self, zero_sub, hodd.neg_pow]
  have hrefl : S = -S := by
    calc S = ∑ i ∈ Ioo 0 n, (((n - i : ℕ) : ZMod n)) ^ (n - 1) := h2
      _ = ∑ i ∈ Ioo 0 n, -((i : ZMod n) ^ (n - 1)) := sum_congr rfl h3
      _ = -S := by rw [sum_neg_distrib]
  have h4 : ((2 : ℕ) : ZMod n) = 0 := by
    push_cast
    linear_combination (2 : ZMod n) * h1 - hrefl
  have h5 : n ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).mp h4
  have := Nat.le_of_dvd (by norm_num) h5
  omega

/-- For even `n ≥ 3`, Agoh's congruence fails since `B'_{n-1} = 0`. -/
theorem even_not_agoh (n : ℕ) (hn : 3 ≤ n) (hev : Even n) :
    ¬ ∃ k : ℤ, (n : ℤ) * (bernoulli' (n - 1)).num + (bernoulli' (n - 1)).den = k * (n : ℤ) ^ 2 := by
  rintro ⟨k, hk⟩
  have hodd : Odd (n - 1) := by
    obtain ⟨j, hj⟩ := hev
    exact ⟨j - 1, by omega⟩
  rw [bernoulli'_eq_zero_of_odd hodd (by omega)] at hk
  simp only [Rat.num_zero, mul_zero, Rat.den_zero, Nat.cast_one, zero_add] at hk
  have h1 : ((n ^ 2 : ℕ) : ℤ) ∣ 1 := ⟨k, by rw [hk]; push_cast; ring⟩
  have h2 : n ^ 2 ∣ 1 := by exact_mod_cast h1
  have h3 := Nat.le_of_dvd (by norm_num) h2
  nlinarith

/-- For `n = 2` both congruences hold. -/
theorem case_two : ((∃ k : ℤ, ((2 : ℕ) : ℤ) * (bernoulli' (2 - 1)).num + (bernoulli' (2 - 1)).den =
    k * ((2 : ℕ) : ℤ) ^ 2) ↔ 2 ∣ 1 + ∑ i ∈ Ioo 0 2, i ^ (2 - 1)) := by
  refine iff_of_true ⟨1, ?_⟩ (by decide)
  have h1 : bernoulli' (2 - 1) = 1 / 2 := by norm_num
  rw [h1]
  have hnum : (1 / 2 : ℚ).num = 1 := by norm_num
  have hden : (1 / 2 : ℚ).den = 2 := by norm_num
  rw [hnum, hden]
  norm_num

end OMA.Helpers

theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_R1.H1 := by
  intro n hn
  simp only []
  rcases Nat.even_or_odd n with hev | hodd
  · rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
    · exact OMA.Helpers.case_two
    · exact iff_of_false (OMA.Helpers.even_not_agoh n hn3 hev)
        (OMA.Helpers.even_not_dvd n hn3 hev)
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : Even m := by
      obtain ⟨k, hk⟩ := hodd
      exact ⟨k, by omega⟩
    rw [Nat.add_sub_cancel]
    exact OMA.Helpers.odd_case m hm (by obtain ⟨k, hk⟩ := hodd; omega)
