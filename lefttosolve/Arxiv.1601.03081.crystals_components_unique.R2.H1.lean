import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R2

namespace OMA.Helpers

open Arxiv.«1601.03081»

theorem cr_sumsq {n a b : ℕ} (h : IsCrystalWithComponents n a b) :
    (a + 1) * (b + 1) ∣ (a + b) ^ 2 := by
  obtain ⟨hn, _, _, rfl, hd⟩ := h
  have hao : Odd a := Nat.Odd.of_mul_left hn
  obtain ⟨x, rfl⟩ := hao
  set D := (2 * x + 1 + 1) * (b + 1) with hD
  have hsum : D = (2 * x + 1 + b) + ((2 * x + 1) * b + 1) := by rw [hD]; ring
  have h1 : 2 * D ∣ (2 * x + 1 + b) ^ 2 + ((2 * x + 1) * b + 1) ^ 2 + 2 * (2 * x + 1 + b) * D :=
    Nat.dvd_add (by simpa [Nat.mul_assoc] using hd) ⟨2 * x + 1 + b, by ring⟩
  have h2 : (2 * x + 1 + b) ^ 2 + ((2 * x + 1) * b + 1) ^ 2 + 2 * (2 * x + 1 + b) * D
      = 2 * (2 * x + 1 + b) ^ 2 + D ^ 2 := by
    rw [hsum]; ring
  rw [h2] at h1
  have h3 : 2 * D ∣ D ^ 2 := ⟨(x + 1) * (b + 1), by rw [hD]; ring⟩
  have h4 : 2 * D ∣ 2 * (2 * x + 1 + b) ^ 2 := (Nat.dvd_add_left h3).mp h1
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h4

theorem cr_prodsq {a b : ℕ} (h : (a + 1) * (b + 1) ∣ (a + b) ^ 2) :
    (a + 1) * (b + 1) ∣ (a * b + 1) ^ 2 := by
  have e : (a * b + 1) ^ 2 + 2 * (a + b) * ((a + 1) * (b + 1))
      = (a + b) ^ 2 + ((a + 1) * (b + 1)) * ((a + 1) * (b + 1)) := by ring
  have h1 : (a + 1) * (b + 1) ∣ (a * b + 1) ^ 2 + 2 * (a + b) * ((a + 1) * (b + 1)) := by
    rw [e]; exact Nat.dvd_add h (dvd_mul_right _ _)
  exact (Nat.dvd_add_left (dvd_mul_left _ _)).mp h1

/-- a divisor of `2^x * p^y` has the form `2^i * p^j`. -/
theorem cr_div_shape {p u x y : ℕ} (hp : p.Prime) (h : u ∣ 2 ^ x * p ^ y) :
    ∃ i j, u = 2 ^ i * p ^ j := by
  obtain ⟨k1, k2, h1, h2, rfl⟩ := Nat.dvd_mul.mp h
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp h2
  exact ⟨i, j, rfl⟩

theorem cr_split {T0 P0 : ℕ} (h : (T0 + 1) * (P0 + 1) ∣ (T0 + P0 + 1) ^ 2) :
    P0 + 1 ∣ T0 ^ 2 ∧ T0 + 1 ∣ P0 ^ 2 := by
  constructor
  · have h1 : P0 + 1 ∣ T0 ^ 2 + (P0 + 1) * (2 * T0 + P0 + 1) := by
      have e : T0 ^ 2 + (P0 + 1) * (2 * T0 + P0 + 1) = (T0 + P0 + 1) ^ 2 := by ring
      rw [e]; exact (dvd_mul_left _ _).trans h
    exact (Nat.dvd_add_left (dvd_mul_right _ _)).mp h1
  · have h1 : T0 + 1 ∣ P0 ^ 2 + (T0 + 1) * (2 * P0 + T0 + 1) := by
      have e : P0 ^ 2 + (T0 + 1) * (2 * P0 + T0 + 1) = (T0 + P0 + 1) ^ 2 := by ring
      rw [e]; exact (dvd_mul_right _ _).trans h
    exact (Nat.dvd_add_left (dvd_mul_right _ _)).mp h1

/-- The shape of a crystal pair where `x + 1` is a power of two. -/
theorem cr_pow_two_side {p x y i i' j : ℕ} (hpo : Odd p)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hyo : Odd y)
    (hX : x + 1 = 2 ^ i) (hY : y + 1 = 2 ^ i' * p ^ j)
    (hd : (x + 1) * (y + 1) ∣ (x + y) ^ 2) :
    ∃ k, 1 ≤ k ∧ x + 1 = 2 * 2 ^ k ∧ y + 1 = 2 * p ^ j ∧ 3 ≤ p ^ j ∧
      p ^ j ∣ (2 ^ k - 1) ^ 2 ∧ 2 ^ k ∣ (p ^ j - 1) ^ 2 := by
  have hPo : Odd (p ^ j) := hpo.pow
  have hi : 2 ≤ i := by
    by_contra hi
    interval_cases i <;> omega
  -- i' = 1
  have hi' : i' = 1 := by
    rcases Nat.lt_trichotomy i' 1 with h | h | h
    · have : i' = 0 := by omega
      subst this
      obtain ⟨r, hr⟩ := hyo
      obtain ⟨s, hs⟩ := hPo
      omega
    · exact h
    · exfalso
      have h4x : 4 ∣ x + 1 := by
        rw [hX]
        have : (2:ℕ) ^ 2 ∣ 2 ^ i := Nat.pow_dvd_pow 2 hi
        simpa using this
      have h4y : 4 ∣ y + 1 := by
        rw [hY]
        have : (2:ℕ) ^ 2 ∣ 2 ^ i' := Nat.pow_dvd_pow 2 (by omega)
        exact Dvd.dvd.mul_right (by simpa using this) _
      have h16 : 16 ∣ (x + 1) * (y + 1) := by
        have := Nat.mul_dvd_mul h4x h4y
        simpa using this
      obtain ⟨t, ht⟩ : ∃ t, x + y = 4 * t + 2 := ⟨(x + y) / 4, by omega⟩
      have h' : 16 ∣ (x + y) ^ 2 := h16.trans hd
      rw [ht, show (4 * t + 2) ^ 2 = 4 + 16 * (t ^ 2 + t) by ring] at h'
      have : 16 ∣ 4 := (Nat.dvd_add_left (dvd_mul_right 16 _)).mp h'
      omega
  subst hi'
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  refine ⟨k, by omega, by rw [hX]; ring, by rw [hY]; ring, ?_, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := hPo
    omega
  · obtain ⟨T0, hT0⟩ : ∃ T0, 2 ^ k = T0 + 1 := ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
    obtain ⟨P0, hP0⟩ : ∃ P0, p ^ j = P0 + 1 := ⟨p ^ j - 1, by have := hPo.pos; omega⟩
    have hd' : 4 * ((T0 + 1) * (P0 + 1)) ∣ 4 * (T0 + P0 + 1) ^ 2 := by
      have e1 : (x + 1) * (y + 1) = 4 * ((T0 + 1) * (P0 + 1)) := by
        rw [hX, hY, pow_succ, hT0, pow_one, hP0]; ring
      have e2 : (x + y) ^ 2 = 4 * (T0 + P0 + 1) ^ 2 := by
        have : x + y = 2 * (T0 + P0 + 1) := by
          rw [pow_succ, hT0] at hX; rw [pow_one, hP0] at hY; omega
        rw [this]; ring
      rw [← e1, ← e2]; exact hd
    have := (cr_split (Nat.dvd_of_mul_dvd_mul_left (by norm_num) hd')).1
    rw [hT0, hP0]; simpa using this
  · obtain ⟨T0, hT0⟩ : ∃ T0, 2 ^ k = T0 + 1 := ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
    obtain ⟨P0, hP0⟩ : ∃ P0, p ^ j = P0 + 1 := ⟨p ^ j - 1, by have := hPo.pos; omega⟩
    have hd' : 4 * ((T0 + 1) * (P0 + 1)) ∣ 4 * (T0 + P0 + 1) ^ 2 := by
      have e1 : (x + 1) * (y + 1) = 4 * ((T0 + 1) * (P0 + 1)) := by
        rw [hX, hY, pow_succ, hT0, pow_one, hP0]; ring
      have e2 : (x + y) ^ 2 = 4 * (T0 + P0 + 1) ^ 2 := by
        have : x + y = 2 * (T0 + P0 + 1) := by
          rw [pow_succ, hT0] at hX; rw [pow_one, hP0] at hY; omega
        rw [this]; ring
      rw [← e1, ← e2]; exact hd
    have := (cr_split (Nat.dvd_of_mul_dvd_mul_left (by norm_num) hd')).2
    rw [hT0, hP0]; simpa using this

/-- Two different shapes cannot give the same product. -/
theorem cr_compare {p k k' j j' a b c d : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hk : 1 ≤ k) (hkk : k < k')
    (hP : p ^ j ∣ (2 ^ k - 1) ^ 2) (hP' : 3 ≤ p ^ j') (hT' : 2 ^ k' ∣ (p ^ j' - 1) ^ 2)
    (ha : a + 1 = 2 * 2 ^ k) (hb : b + 1 = 2 * p ^ j)
    (hc : c + 1 = 2 * 2 ^ k') (hd : d + 1 = 2 * p ^ j')
    (he : a * b = c * d) : False := by
  have hTT : 2 ^ k < 2 ^ k' := Nat.pow_lt_pow_right (by norm_num) hkk
  have hT2 : 2 ≤ 2 ^ k := by
    have : (2:ℕ) ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    simpa using this
  have hPPodd : Odd (p ^ j') := hpo.pow
  have hPP : p ^ j' < p ^ j := by
    by_contra hcon
    push_neg at hcon
    have h1 : a < c := by omega
    have h2 : b ≤ d := by omega
    have h3 : 0 < d := by omega
    have : a * b < c * d :=
      lt_of_le_of_lt (Nat.mul_le_mul_left a h2) (Nat.mul_lt_mul_of_pos_right h1 h3)
    omega
  have hjj : j' < j := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hPP
  obtain ⟨e, hePe⟩ : p ^ j' ∣ p ^ j := pow_dvd_pow p hjj.le
  -- the larger odd part divides twice the difference of the powers of two
  have hdivZ : ((p ^ j' : ℕ) : ℤ) ∣ 2 * (((2 ^ k' : ℕ) : ℤ) - ((2 ^ k : ℕ) : ℤ)) := by
    refine ⟨4 * ((2 ^ k' : ℕ) : ℤ) - 2 - 4 * ((2 ^ k : ℕ) : ℤ) * e + 2 * e, ?_⟩
    have ha1 : (a : ℤ) = 2 * ((2 ^ k : ℕ) : ℤ) - 1 := by
      have := congrArg (Nat.cast (R := ℤ)) ha; push_cast at this ⊢; linarith
    have hb1 : (b : ℤ) = 2 * ((p ^ j' : ℕ) : ℤ) * e - 1 := by
      have := congrArg (Nat.cast (R := ℤ)) hb; rw [hePe] at this; push_cast at this ⊢; linarith
    have hc1 : (c : ℤ) = 2 * ((2 ^ k' : ℕ) : ℤ) - 1 := by
      have := congrArg (Nat.cast (R := ℤ)) hc; push_cast at this ⊢; linarith
    have hd1 : (d : ℤ) = 2 * ((p ^ j' : ℕ) : ℤ) - 1 := by
      have := congrArg (Nat.cast (R := ℤ)) hd; push_cast at this ⊢; linarith
    have he1 : (a : ℤ) * b = c * d := by exact_mod_cast he
    rw [ha1, hb1, hc1, hd1] at he1
    linear_combination he1
  have hdiv : p ^ j' ∣ 2 * (2 ^ k' - 2 ^ k) := by
    have : ((p ^ j' : ℕ) : ℤ) ∣ ((2 * (2 ^ k' - 2 ^ k) : ℕ) : ℤ) := by
      rw [Nat.cast_mul, Nat.cast_sub hTT.le]; push_cast at hdivZ ⊢; exact hdivZ
    exact Int.natCast_dvd_natCast.mp this
  set R := 2 ^ (k' - k) with hR
  have hTR : 2 ^ k' = 2 ^ k * R := by rw [hR, ← pow_add]; congr 1; omega
  have hR2 : 2 ≤ R := by
    have : (2:ℕ) ^ 1 ≤ 2 ^ (k' - k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa [hR] using this
  have hdiv2 : p ^ j' ∣ 2 ^ (k + 1) * (R - 1) := by
    have e2 : 2 * (2 ^ k' - 2 ^ k) = 2 ^ (k + 1) * (R - 1) := by
      have e3 : 2 ^ k * R - 2 ^ k = 2 ^ k * (R - 1) := (Nat.mul_sub_one _ _).symm
      rw [hTR, e3, pow_succ]; ring
    rw [← e2]; exact hdiv
  have hcop : Nat.Coprime (p ^ j') (2 ^ (k + 1)) :=
    (Nat.coprime_two_right.mpr hPPodd).pow_right (k + 1)
  have hdivR : p ^ j' ∣ R - 1 := hcop.dvd_of_dvd_mul_left hdiv2
  have hPR : p ^ j' ≤ R - 1 := Nat.le_of_dvd (by omega) hdivR
  have hT'le : 2 ^ k' ≤ (p ^ j' - 1) ^ 2 := Nat.le_of_dvd (pow_pos (by omega) 2) hT'
  have hsq : (p ^ j' - 1) ^ 2 < R ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have hTltR : 2 ^ k < R := by
    have h1 : 2 ^ k * R < R * R := by
      rw [← hTR]
      calc 2 ^ k' ≤ (p ^ j' - 1) ^ 2 := hT'le
        _ < R ^ 2 := hsq
        _ = R * R := sq R
    exact Nat.lt_of_mul_lt_mul_right h1
  have h2TR : 2 * 2 ^ k ≤ R := by
    have hkk2 : k < k' - k := (Nat.pow_lt_pow_iff_right (by norm_num)).mp (hR ▸ hTltR)
    have : (2:ℕ) ^ (k + 1) ≤ 2 ^ (k' - k) := Nat.pow_le_pow_right (by norm_num) hkk2
    rw [pow_succ] at this; rw [hR]; linarith
  have hT'big : 2 * (2 ^ k) ^ 2 ≤ 2 ^ k' := by
    rw [hTR]
    calc 2 * (2 ^ k) ^ 2 = 2 ^ k * (2 * 2 ^ k) := by ring
      _ ≤ 2 ^ k * R := Nat.mul_le_mul_left _ h2TR
  have hPle : p ^ j ≤ (2 ^ k - 1) ^ 2 := Nat.le_of_dvd (by
    have : 1 ≤ 2 ^ k - 1 := by omega
    positivity) hP
  have hTsq : (2 ^ k - 1) ^ 2 < (2 ^ k) ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have hxT : 2 ^ k ≤ p ^ j' - 1 := by
    by_contra hcon
    push_neg at hcon
    have : (p ^ j' - 1) ^ 2 < (2 ^ k) ^ 2 := Nat.pow_lt_pow_left hcon (by norm_num)
    have h1 : 1 ≤ (2 ^ k) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    linarith
  have hbig1 : a * b < (2 * 2 ^ k) * (2 * (2 ^ k) ^ 2) :=
    Nat.mul_lt_mul'' (by omega) (by omega)
  have h1 : 1 ≤ (2 ^ k) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have hbig2 : (2 * (2 ^ k) ^ 2) * (2 * 2 ^ k) ≤ c * d :=
    Nat.mul_le_mul (by linarith) (by omega)
  have : (2 * 2 ^ k) * (2 * (2 ^ k) ^ 2) = (2 * (2 ^ k) ^ 2) * (2 * 2 ^ k) := by ring
  rw [he, this] at hbig1
  exact absurd hbig1 (not_lt.mpr hbig2)

/-- The shape of a crystal whose successor has at most one odd prime factor. -/
theorem cr_shape {n a b p A B : ℕ} (hp : p.Prime) (hpo : Odd p)
    (h : IsCrystalWithComponents n a b) (hm : n + 1 = 2 ^ A * p ^ B) :
    ∃ k j x y, 1 ≤ k ∧ 3 ≤ p ^ j ∧ p ^ j ∣ (2 ^ k - 1) ^ 2 ∧ 2 ^ k ∣ (p ^ j - 1) ^ 2 ∧
      x + 1 = 2 * 2 ^ k ∧ y + 1 = 2 * p ^ j ∧ x * y = n ∧
      ({a, b} : Finset ℕ) = {x, y} := by
  have hQ := cr_sumsq h
  have hF := cr_prodsq hQ
  obtain ⟨hn, ha1, hb1, hnab, -⟩ := h
  have hao : Odd a := Nat.Odd.of_mul_left (hnab ▸ hn)
  have hbo : Odd b := Nat.Odd.of_mul_right (hnab ▸ hn)
  have ha3 : 3 ≤ a := by obtain ⟨r, hr⟩ := hao; omega
  have hb3 : 3 ≤ b := by obtain ⟨r, hr⟩ := hbo; omega
  have hsq : (a * b + 1) ^ 2 = 2 ^ (2 * A) * p ^ (2 * B) := by
    rw [← hnab, hm, mul_pow, ← pow_mul, ← pow_mul, mul_comm A, mul_comm B]
  rw [hsq] at hF
  obtain ⟨i, j1, hi⟩ := cr_div_shape hp ((dvd_mul_right _ _).trans hF)
  obtain ⟨i', j2, hi'⟩ := cr_div_shape hp ((dvd_mul_left _ _).trans hF)
  have hnot : j1 = 0 ∨ j2 = 0 := by
    by_contra hcon
    push_neg at hcon
    have hpa : p ∣ a + 1 := by
      rw [hi]; exact Dvd.dvd.mul_left (dvd_pow_self p hcon.1) _
    have hpb : p ∣ b + 1 := by
      rw [hi']; exact Dvd.dvd.mul_left (dvd_pow_self p hcon.2) _
    have hps : p ∣ a + b := hp.dvd_of_dvd_pow ((dvd_mul_of_dvd_left hpa _).trans hQ)
    have hp2 : p ∣ (a + b) + 2 := by
      have : (a + b) + 2 = (a + 1) + (b + 1) := by ring
      rw [this]; exact Nat.dvd_add hpa hpb
    have : p ∣ 2 := (Nat.dvd_add_right hps).mp hp2
    have := Nat.le_of_dvd (by norm_num) this
    have := hp.two_le
    obtain ⟨r, hr⟩ := hpo
    omega
  rcases hnot with h0 | h0
  · subst h0
    simp only [pow_zero, mul_one] at hi
    obtain ⟨k, hk, hX, hY, h3, hPd, hTd⟩ := cr_pow_two_side hpo ha3 hb3 hbo hi hi' hQ
    exact ⟨k, j2, a, b, hk, h3, hPd, hTd, hX, hY, hnab.symm, rfl⟩
  · subst h0
    simp only [pow_zero, mul_one] at hi'
    have hQ' : (b + 1) * (a + 1) ∣ (b + a) ^ 2 := by
      rw [Nat.mul_comm (b + 1), Nat.add_comm b a]; exact hQ
    obtain ⟨k, hk, hX, hY, h3, hPd, hTd⟩ := cr_pow_two_side hpo hb3 ha3 hao hi' hi hQ'
    exact ⟨k, j1, b, a, hk, h3, hPd, hTd, hX, hY, by rw [hnab, mul_comm], Finset.pair_comm a b⟩

end OMA.Helpers

theorem OMA.solution : OMA.R_Arxiv_1601_03081_crystals_components_unique_R2.H1 := by
  intro n a b c d hab hcd hex
  obtain ⟨p, A, B, hp, hpo, hm⟩ := hex
  obtain ⟨k, j, x, y, hk, h3, hPd, hTd, hx, hy, hxy, hs⟩ := OMA.Helpers.cr_shape hp hpo hab hm
  obtain ⟨k', j', x', y', hk', h3', hPd', hTd', hx', hy', hxy', hs'⟩ :=
    OMA.Helpers.cr_shape hp hpo hcd hm
  rw [hs, hs']
  rcases Nat.lt_trichotomy k k' with hlt | heq | hgt
  · exact (OMA.Helpers.cr_compare hp hpo hk hlt hPd h3' hTd' hx hy hx' hy' (hxy.trans hxy'.symm)).elim
  · subst heq
    have hxx : x = x' := by omega
    subst hxx
    have hyy : y = y' := Nat.eq_of_mul_eq_mul_left (by omega) (hxy.trans hxy'.symm)
    rw [hyy]
  · exact (OMA.Helpers.cr_compare hp hpo hk' hgt hPd' h3 hTd hx' hy' hx hy (hxy'.trans hxy.symm)).elim
