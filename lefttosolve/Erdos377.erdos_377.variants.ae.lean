import FormalConjectures.ErdosProblems.«377»

/-!
# Erdős 377, the almost-everywhere variant (Erdős–Graham–Ruzsa–Straus)

Own formalisation.  Write `f n = ∑_{p ≤ n, p ∤ C(2n, n)} 1 / p`.

* Kummer (`not_dvd_centralBinom_iff`): `p ∤ C(2n, n)` iff `2 * (n % p ^ i) < p ^ i` for all `i ≥ 1`.
* `card_sep` (separated moduli): if the moduli in `M` are pairwise separated by a factor `U`
  and all are `≤ L / U`, then the number of `n` in an interval of length `ℓ ≤ L` with
  `2 * (n % m) < m` for all `m ∈ M` is `ℓ / 2 ^ #M` up to `4 ^ #M * L / U`.
* `card_digits_range_le`: at most `2 N (2 / 3) ^ k` integers `n < N` satisfy the first `k`
  digit conditions of `p` (when `p ^ k ≤ N`).
* Mertens: `A_abs` (first theorem, from Legendre and Chebyshev), `sum_inv_short`,
  `sum_inv_cluster`, `sum_inv_class` (short ranges) and `mertens2` (second theorem in
  difference form, by discrete partial summation).
* Good primes at scale `N`: `p ^ k ≤ N / U` and `2 N < p ^ (k + 1)` with `k < K` digits.
  On them `f` is a sum of indicators `Y` with mean `2 ^ (-k)`; `cN_tendsto` gives the main term,
  `second_moment_le` the variance (pairs of primes with all powers `U`-separated are handled by
  `card_sep`, the other pairs have small weight), `bad_sum_le` the remaining primes.
* Chebyshev and Markov inequalities give the density statement.
-/

open Filter Real Finset

open scoped Topology

namespace OMA.Helpers

/-- Kummer criterion for the central binomial coefficient. -/
theorem not_dvd_centralBinom_iff {p n : ℕ} (hp : p.Prime) :
    ¬ p ∣ n.centralBinom ↔ ∀ i, 1 ≤ i → 2 * (n % p ^ i) < p ^ i := by
  have hc : n.centralBinom ≠ 0 := Nat.centralBinom_ne_zero n
  have hfac := Nat.factorization_choose' (p := p) (n := n) (k := n) (b := Nat.log p (n + n) + 1) hp
    (Nat.lt_succ_self _)
  have hcb : n.centralBinom = (n + n).choose n := by
    rw [Nat.centralBinom_eq_two_mul_choose, two_mul]
  rw [hp.dvd_iff_one_le_factorization hc, hcb, hfac]
  constructor
  · intro h i hi
    by_contra hcon
    rw [not_lt] at hcon
    rcases Nat.lt_or_ge i (Nat.log p (n + n) + 1) with hlt | hge
    · apply h
      rw [Nat.succ_le_iff, Finset.card_pos]
      exact ⟨i, by simp only [Finset.mem_filter, Finset.mem_Ico]; exact ⟨⟨hi, hlt⟩, by omega⟩⟩
    · have h1 : n + n < p ^ i := Nat.lt_pow_of_log_lt hp.one_lt (by omega)
      have h2 : n % p ^ i ≤ n := Nat.mod_le _ _
      omega
  · intro h hcon
    rw [Nat.succ_le_iff, Finset.card_pos] at hcon
    obtain ⟨i, hi⟩ := hcon
    simp only [Finset.mem_filter, Finset.mem_Ico] at hi
    have := h i hi.1.1
    omega

/-- number of residues mod `p^k` all of whose `k` digit conditions hold -/
theorem card_digits_le (p : ℕ) (hp : 2 ≤ p) (k : ℕ) :
    #{r ∈ range (p ^ k) | ∀ i ∈ Icc (1 : ℕ) k, 2 * (r % p ^ i) < p ^ i} ≤ ((p + 1) / 2) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp0 : 0 < p := by omega
    calc #{r ∈ range (p ^ (k + 1)) | ∀ i ∈ Icc (1 : ℕ) (k + 1), 2 * (r % p ^ i) < p ^ i}
        ≤ #(range ((p + 1) / 2) ×ˢ {r ∈ range (p ^ k) | ∀ i ∈ Icc (1 : ℕ) k, 2 * (r % p ^ i) < p ^ i}) := by
          apply Finset.card_le_card_of_injOn (fun r => (r % p, r / p))
          · intro r hr
            simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, Finset.mem_Icc] at hr
            simp only [Finset.coe_product, Finset.coe_range, Finset.coe_filter, Finset.mem_range,
              Finset.mem_Icc, Set.mem_prod, Set.mem_Iio, Set.mem_ofPred_eq]
            obtain ⟨hr1, hr2⟩ := hr
            refine ⟨?_, ?_, ?_⟩
            · have := hr2 1 ⟨le_refl _, by omega⟩
              rw [pow_one] at this
              omega
            · rw [Nat.div_lt_iff_lt_mul hp0, ← pow_succ]; exact hr1
            · intro i hi
              have h1 := hr2 (i + 1) ⟨by omega, by omega⟩
              rw [pow_succ', Nat.mod_mul] at h1
              have h2 : 2 * (p * (r / p % p ^ i)) < p * p ^ i := by omega
              have h3 : p * (2 * (r / p % p ^ i)) < p * p ^ i := by
                calc p * (2 * (r / p % p ^ i)) = 2 * (p * (r / p % p ^ i)) := by ring
                  _ < _ := h2
              exact Nat.lt_of_mul_lt_mul_left h3
          · intro r _ s _ hrs
            simp only [Prod.mk.injEq] at hrs
            rw [← Nat.div_add_mod r p, ← Nat.div_add_mod s p, hrs.1, hrs.2]
      _ = ((p + 1) / 2) * #{r ∈ range (p ^ k) | ∀ i ∈ Icc (1 : ℕ) k, 2 * (r % p ^ i) < p ^ i} := by
          rw [Finset.card_product, Finset.card_range]
      _ ≤ ((p + 1) / 2) * ((p + 1) / 2) ^ k := Nat.mul_le_mul_left _ ih
      _ = ((p + 1) / 2) ^ (k + 1) := by ring

theorem card_digits_range_le (p : ℕ) (hp : 2 ≤ p) (k N : ℕ) (hN : p ^ k ≤ N) :
    ((#{n ∈ range N | ∀ i ∈ Icc (1 : ℕ) k, 2 * (n % p ^ i) < p ^ i} : ℕ) : ℝ) ≤ 2 * N * (2 / 3 : ℝ) ^ k := by
  have hp0 : 0 < p := by omega
  have hpk : 0 < p ^ k := pos_of_ne_zero (pow_ne_zero _ (by omega))
  have h1 : #{n ∈ range N | ∀ i ∈ Icc (1 : ℕ) k, 2 * (n % p ^ i) < p ^ i} ≤
      #(range (N / p ^ k + 1) ×ˢ {r ∈ range (p ^ k) | ∀ i ∈ Icc (1 : ℕ) k, 2 * (r % p ^ i) < p ^ i}) := by
    apply Finset.card_le_card_of_injOn (fun n => (n / p ^ k, n % p ^ k))
    · intro n hn
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, Finset.mem_Icc] at hn
      simp only [Finset.coe_product, Finset.coe_range, Finset.coe_filter, Finset.mem_range,
        Finset.mem_Icc, Set.mem_prod, Set.mem_Iio, Set.mem_ofPred_eq]
      obtain ⟨hn1, hn2⟩ := hn
      refine ⟨?_, Nat.mod_lt _ hpk, ?_⟩
      · exact Nat.lt_succ_of_le (Nat.div_le_div_right hn1.le)
      · intro i hi
        rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow p hi.2)]
        exact hn2 i hi
    · intro r _ s _ hrs
      simp only [Prod.mk.injEq] at hrs
      rw [← Nat.div_add_mod r (p ^ k), ← Nat.div_add_mod s (p ^ k), hrs.1, hrs.2]
  rw [Finset.card_product, Finset.card_range] at h1
  have h2 := card_digits_le p hp k
  have h3 : ((#{n ∈ range N | ∀ i ∈ Icc (1 : ℕ) k, 2 * (n % p ^ i) < p ^ i} : ℕ) : ℝ) ≤
      ((N / p ^ k + 1 : ℕ) : ℝ) * (((p + 1) / 2 : ℕ) : ℝ) ^ k := by
    have : #{n ∈ range N | ∀ i ∈ Icc (1 : ℕ) k, 2 * (n % p ^ i) < p ^ i} ≤
        (N / p ^ k + 1) * ((p + 1) / 2) ^ k := h1.trans (Nat.mul_le_mul_left _ h2)
    exact_mod_cast this
  have hpR : (0 : ℝ) < (p : ℝ) ^ k := by positivity
  have h4 : ((N / p ^ k + 1 : ℕ) : ℝ) ≤ 2 * N / (p : ℝ) ^ k := by
    have h5 : ((N / p ^ k : ℕ) : ℝ) ≤ (N : ℝ) / (p : ℝ) ^ k := by
      have := Nat.cast_div_le (α := ℝ) (m := N) (n := p ^ k)
      simpa using this
    have h6 : (1 : ℝ) ≤ (N : ℝ) / (p : ℝ) ^ k := by
      rw [le_div_iff₀ hpR, one_mul]; exact_mod_cast hN
    push_cast
    have : 2 * (N : ℝ) / (p : ℝ) ^ k = (N : ℝ) / (p : ℝ) ^ k + (N : ℝ) / (p : ℝ) ^ k := by ring
    linarith
  have h7 : (((p + 1) / 2 : ℕ) : ℝ) ≤ (2 / 3 : ℝ) * p := by
    have : 3 * ((p + 1) / 2) ≤ 2 * p := by omega
    have h8 : (3 : ℝ) * (((p + 1) / 2 : ℕ) : ℝ) ≤ 2 * (p : ℝ) := by exact_mod_cast this
    linarith
  calc ((#{n ∈ range N | ∀ i ∈ Icc (1 : ℕ) k, 2 * (n % p ^ i) < p ^ i} : ℕ) : ℝ)
      ≤ ((N / p ^ k + 1 : ℕ) : ℝ) * (((p + 1) / 2 : ℕ) : ℝ) ^ k := h3
    _ ≤ (2 * N / (p : ℝ) ^ k) * ((2 / 3 : ℝ) * p) ^ k := by
        gcongr
    _ = 2 * N * (2 / 3 : ℝ) ^ k := by
        rw [mul_pow]; field_simp

/-- fibre decomposition for one modulus -/
theorem card_filter_mod_split (m : ℕ) (hm : 0 < m) (Q : ℕ → Prop) [DecidablePred Q] (a b : ℕ) :
    #{n ∈ Ico a b | 2 * (n % m) < m ∧ Q n} =
      ∑ t ∈ Icc (a / m) (b / m),
        #{n ∈ Ico (max a (t * m)) (min b (t * m + (m + 1) / 2)) | Q n} := by
  have hmaps : (({n ∈ Ico a b | 2 * (n % m) < m ∧ Q n} : Finset ℕ) : Set ℕ).MapsTo
      (fun n => n / m) (Icc (a / m) (b / m) : Finset ℕ) := by
    intro n hn
    have hn' : n ∈ ({n ∈ Ico a b | 2 * (n % m) < m ∧ Q n} : Finset ℕ) := hn
    rw [Finset.mem_filter, Finset.mem_Ico] at hn'
    show n / m ∈ Icc (a / m) (b / m)
    rw [Finset.mem_Icc]
    exact ⟨Nat.div_le_div_right hn'.1.1, Nat.div_le_div_right hn'.1.2.le⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ico]
  have h6 := Nat.div_add_mod n m
  have h7 := Nat.mod_lt n hm
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
    rw [h5, mul_comm] at h6
    generalize t * m = T at *
    refine ⟨⟨?_, ?_⟩, h4⟩
    · rw [max_le_iff]; exact ⟨h1, by omega⟩
    · rw [lt_min_iff]; exact ⟨h2, by omega⟩
  · rintro ⟨⟨h1, h2⟩, h4⟩
    rw [max_le_iff] at h1; rw [lt_min_iff] at h2
    have hdm : n / m = t ∧ n % m = n - t * m := by
      rw [Nat.div_mod_unique hm, mul_comm m t]
      generalize t * m = T at *
      omega
    refine ⟨⟨⟨h1.1, h2.1⟩, ?_, h4⟩, hdm.1⟩
    rw [hdm.2]
    generalize t * m = T at *
    omega

theorem card_full_periods (m : ℕ) (hm : 0 < m) (a q : ℕ) :
    #{n ∈ Ico a (a + q * m) | 2 * (n % m) < m} = q * ((m + 1) / 2) := by
  have hper : Function.Periodic (fun n : ℕ => 2 * (n % m) < m) m := by
    intro x
    simp only [Nat.add_mod_right]
  have hcount : Nat.count (fun n : ℕ => 2 * (n % m) < m) m = (m + 1) / 2 := by
    rw [Nat.count_eq_card_filter_range]
    have : ({x ∈ range m | 2 * (x % m) < m} : Finset ℕ) = range ((m + 1) / 2) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2⟩
        rw [Nat.mod_eq_of_lt h1] at h2
        omega
      · intro h
        have h1 : x < m := by omega
        rw [Nat.mod_eq_of_lt h1]
        omega
    rw [this, Finset.card_range]
  induction q with
  | zero => simp
  | succ q ih =>
    have hsplit : Ico a (a + (q + 1) * m) = Ico a (a + q * m) ∪ Ico (a + q * m) (a + q * m + m) := by
      rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
      congr 1
      ring
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint, ih,
      Nat.filter_Ico_card_eq_of_periodic _ _ _ hper, hcount]
    · ring
    · apply Finset.disjoint_filter_filter
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_Ico] at hx1 hx2
      omega

theorem card_single (m : ℕ) (hm : 0 < m) (a b : ℕ) :
    |((#{n ∈ Ico a b | 2 * (n % m) < m} : ℕ) : ℝ) - ((b - a : ℕ) : ℝ) / 2| ≤
      ((b - a : ℕ) : ℝ) / (2 * m) + m := by
  rcases Nat.lt_or_ge b a with hba | hab
  · have h1 : Ico a b = ∅ := Finset.Ico_eq_empty (by omega)
    have h2 : b - a = 0 := by omega
    rw [h1, h2]
    simp
  obtain ⟨l, rfl⟩ : ∃ l, b = a + l := ⟨b - a, by omega⟩
  rw [Nat.add_sub_cancel_left]
  have hq1 : (l / m) * m ≤ l := Nat.div_mul_le_self l m
  have hq2 : l < (l / m + 1) * m := by
    have := Nat.lt_mul_div_succ l hm
    rwa [mul_comm] at this
  generalize l / m = q at hq1 hq2
  have hh1 : m ≤ 2 * ((m + 1) / 2) := by omega
  have hh2 : 2 * ((m + 1) / 2) ≤ m + 1 := by omega
  have hlow : q * ((m + 1) / 2) ≤ #{n ∈ Ico a (a + l) | 2 * (n % m) < m} := by
    rw [← card_full_periods m hm a q]
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    apply Finset.Ico_subset_Ico_right
    omega
  have hupp : #{n ∈ Ico a (a + l) | 2 * (n % m) < m} ≤ (q + 1) * ((m + 1) / 2) := by
    rw [← card_full_periods m hm a (q + 1)]
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    apply Finset.Ico_subset_Ico_right
    omega
  generalize (m + 1) / 2 = h at hh1 hh2 hlow hupp
  generalize #{n ∈ Ico a (a + l) | 2 * (n % m) < m} = c at hlow hupp
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : (q : ℝ) * m ≤ l := by exact_mod_cast hq1
  have h2 : (l : ℝ) < ((q : ℝ) + 1) * m := by exact_mod_cast hq2
  have h3 : (m : ℝ) ≤ 2 * (h : ℝ) := by exact_mod_cast hh1
  have h4 : 2 * (h : ℝ) ≤ m + 1 := by exact_mod_cast hh2
  have h5 : (q : ℝ) * h ≤ (c : ℝ) := by exact_mod_cast hlow
  have h6 : (c : ℝ) ≤ ((q : ℝ) + 1) * h := by exact_mod_cast hupp
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hqle : (q : ℝ) ≤ (l : ℝ) / (2 * m) * 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- Lemma W: count for a `U`-separated set of moduli. -/
theorem card_sep (U : ℝ) (hU : 2 ≤ U) (M : Finset ℕ) :
    (∀ m ∈ M, U ≤ (m : ℝ)) → (∀ x ∈ M, ∀ y ∈ M, x < y → U * (x : ℝ) ≤ y) →
    ∀ (L : ℝ), (∀ m ∈ M, U * (m : ℝ) ≤ L) → 0 ≤ L → ∀ a b : ℕ, ((b - a : ℕ) : ℝ) ≤ L →
    |((#{n ∈ Ico a b | ∀ m ∈ M, 2 * (n % m) < m} : ℕ) : ℝ) - ((b - a : ℕ) : ℝ) / 2 ^ #M|
      ≤ 4 ^ #M * L / U := by
  induction M using Finset.induction_on_max with
  | empty =>
    intro _ _ L _ hL a b _
    have hU0 : (0 : ℝ) < U := by linarith
    simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, Finset.filter_true,
      Nat.card_Ico, Finset.card_empty, pow_zero, div_one, sub_self, abs_zero, one_mul]
    positivity
  | insert m M hmax ih =>
    intro hge hsep L hL hL0 a b hab
    have hU0 : (0 : ℝ) < U := by linarith
    have hmM : m ∉ M := fun h => lt_irrefl _ (hmax m h)
    have hmU : U ≤ (m : ℝ) := hge m (Finset.mem_insert_self _ _)
    have hmR : (0 : ℝ) < m := by linarith
    have hm : 0 < m := by exact_mod_cast hmR
    have hmL : U * (m : ℝ) ≤ L := hL m (Finset.mem_insert_self _ _)
    have ih' := ih (fun x hx => hge x (Finset.mem_insert_of_mem hx))
      (fun x hx y hy hxy => hsep x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy)
      (m : ℝ) (fun x hx => hsep x (Finset.mem_insert_of_mem hx) m (Finset.mem_insert_self _ _)
        (hmax x hx)) hmR.le
    rw [Finset.card_insert_of_notMem hmM]
    have hfilt : ({n ∈ Ico a b | ∀ x ∈ insert m M, 2 * (n % x) < x} : Finset ℕ) =
        {n ∈ Ico a b | 2 * (n % m) < m ∧ ∀ x ∈ M, 2 * (n % x) < x} := by
      apply Finset.filter_congr
      intro n _
      rw [Finset.forall_mem_insert]
    rw [hfilt, card_filter_mod_split m hm (fun n => ∀ x ∈ M, 2 * (n % x) < x) a b]
    have hc1 := card_filter_mod_split m hm (fun _ => True) a b
    simp only [and_true, Finset.filter_true, Nat.card_Ico] at hc1
    have hsingle := card_single m hm a b
    rw [hc1] at hsingle
    set T := Icc (a / m) (b / m) with hT
    set r := #M with hr
    -- each piece
    have hpiece : ∀ t ∈ T,
        |((#{n ∈ Ico (max a (t * m)) (min b (t * m + (m + 1) / 2)) | ∀ x ∈ M, 2 * (n % x) < x} : ℕ) : ℝ)
          - ((min b (t * m + (m + 1) / 2) - max a (t * m) : ℕ) : ℝ) / 2 ^ r| ≤ 4 ^ r * (m : ℝ) / U := by
      intro t _
      apply ih'
      have : min b (t * m + (m + 1) / 2) - max a (t * m) ≤ m := by
        generalize t * m = T'
        omega
      exact_mod_cast this
    -- number of pieces
    have hcardT : (#T : ℝ) * m ≤ ((b - a : ℕ) : ℝ) + 2 * m := by
      rw [hT, Nat.card_Icc]
      have h1 : (b / m) * m ≤ b := Nat.div_mul_le_self b m
      have h2 : a < (a / m + 1) * m := by
        have := Nat.lt_mul_div_succ a hm
        rwa [mul_comm] at this
      have h3 : (b / m + 1 - a / m) * m ≤ (b - a) + 2 * m := by
        rcases Nat.lt_or_ge (b / m + 1) (a / m) with h | h
        · have : b / m + 1 - a / m = 0 := by omega
          rw [this]; omega
        · have h4 : (b / m + 1 - a / m) * m + (a / m) * m = (b / m + 1) * m := by
            rw [← add_mul]; congr 1; omega
          have h5 : (b / m + 1) * m = (b / m) * m + m := by ring
          have h6 : (a / m + 1) * m = (a / m) * m + m := by ring
          generalize (b / m + 1 - a / m) * m = X at *
          generalize (b / m + 1) * m = Y at *
          generalize (a / m + 1) * m = Z at *
          generalize (b / m) * m = Y' at *
          generalize (a / m) * m = Z' at *
          omega
      exact_mod_cast h3
    have hsum : |(((∑ t ∈ T, #{n ∈ Ico (max a (t * m)) (min b (t * m + (m + 1) / 2)) |
        ∀ x ∈ M, 2 * (n % x) < x} : ℕ) : ℝ))
        - ((∑ t ∈ T, (min b (t * m + (m + 1) / 2) - max a (t * m)) : ℕ) : ℝ) / 2 ^ r|
        ≤ (#T : ℝ) * (4 ^ r * (m : ℝ) / U) := by
      push_cast
      rw [Finset.sum_div, ← Finset.sum_sub_distrib]
      calc |∑ t ∈ T, (((#{n ∈ Ico (max a (t * m)) (min b (t * m + (m + 1) / 2)) |
              ∀ x ∈ M, 2 * (n % x) < x} : ℕ) : ℝ)
              - ((min b (t * m + (m + 1) / 2) - max a (t * m) : ℕ) : ℝ) / 2 ^ r)|
          ≤ ∑ t ∈ T, |(((#{n ∈ Ico (max a (t * m)) (min b (t * m + (m + 1) / 2)) |
              ∀ x ∈ M, 2 * (n % x) < x} : ℕ) : ℝ)
              - ((min b (t * m + (m + 1) / 2) - max a (t * m) : ℕ) : ℝ) / 2 ^ r)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ t ∈ T, (4 ^ r * (m : ℝ) / U) := Finset.sum_le_sum hpiece
        _ = (#T : ℝ) * (4 ^ r * (m : ℝ) / U) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    generalize ((∑ t ∈ T, #{n ∈ Ico (max a (t * m)) (min b (t * m + (m + 1) / 2)) |
        ∀ x ∈ M, 2 * (n % x) < x} : ℕ) : ℝ) = S at hsum ⊢
    generalize ((∑ t ∈ T, (min b (t * m + (m + 1) / 2) - max a (t * m)) : ℕ) : ℝ) = c1
      at hsum hsingle
    generalize ((b - a : ℕ) : ℝ) = l at hsingle hab hcardT ⊢
    generalize (#T : ℝ) = cT at hsum hcardT
    have h4r : (1 : ℝ) ≤ 4 ^ r := one_le_pow₀ (by norm_num)
    have h2r : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
    have h2r0 : (0 : ℝ) < 2 ^ r := by positivity
    have hx : 0 ≤ L / U := by positivity
    have hmx : (m : ℝ) ≤ L / U := by rw [le_div_iff₀ hU0]; linarith
    -- bound of the first error
    have hE1 : cT * (4 ^ r * (m : ℝ) / U) ≤ 2 * 4 ^ r * (L / U) := by
      have : cT * (4 ^ r * (m : ℝ) / U) = 4 ^ r * (cT * m) / U := by ring
      rw [this]
      have h2m : 2 * (m : ℝ) ≤ L := by nlinarith
      have hcm : cT * (m : ℝ) ≤ 2 * L := by linarith
      have : 4 ^ r * (cT * (m : ℝ)) / U ≤ 4 ^ r * (2 * L) / U :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcm (by positivity)) hU0.le
      calc 4 ^ r * (cT * (m : ℝ)) / U ≤ 4 ^ r * (2 * L) / U := this
        _ = 2 * 4 ^ r * (L / U) := by ring
    -- bound of the second error
    have hE2 : l / (2 * m) + m ≤ (3 / 2) * (L / U) := by
      have h1 : l / (2 * (m : ℝ)) ≤ L / (2 * U) := by
        have hl0 : 0 ≤ L := hL0
        calc l / (2 * (m : ℝ)) ≤ L / (2 * (m : ℝ)) := by gcongr
          _ ≤ L / (2 * U) := by gcongr
      have h2 : L / (2 * U) = (1 / 2) * (L / U) := by field_simp
      linarith
    have hl2 : |c1 / 2 ^ r - l / 2 ^ (r + 1)| ≤ l / (2 * m) + m := by
      have : c1 / 2 ^ r - l / 2 ^ (r + 1) = (c1 - l / 2) / 2 ^ r := by
        rw [pow_succ]; field_simp
      rw [this, abs_div, abs_of_pos h2r0]
      calc |c1 - l / 2| / 2 ^ r ≤ |c1 - l / 2| / 1 := by
            gcongr
        _ = |c1 - l / 2| := div_one _
        _ ≤ _ := hsingle
    have hfin : |S - l / 2 ^ (r + 1)| ≤ |S - c1 / 2 ^ r| + |c1 / 2 ^ r - l / 2 ^ (r + 1)| := by
      have : S - l / 2 ^ (r + 1) = (S - c1 / 2 ^ r) + (c1 / 2 ^ r - l / 2 ^ (r + 1)) := by ring
      rw [this]; exact abs_add_le _ _
    have h4 : (4 : ℝ) ^ (r + 1) * L / U = 4 * 4 ^ r * (L / U) := by rw [pow_succ]; ring
    rw [h4]
    nlinarith

/-- sum of `log p / p` over primes `≤ n` -/
noncomputable def A (n : ℕ) : ℝ := ∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, Real.log p / p

theorem log_factorial_eq (n : ℕ) :
    Real.log (n.factorial : ℝ) = ∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime,
      ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hp.1.one_lt.le, (hp.1.dvd_factorial).mp hp.2.1⟩, hp.1⟩
  · intro i _; simp

theorem log_factorial_ge (n : ℕ) : (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Nat.factorial_succ]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity)]
    have h1 : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
      rw [← Real.log_div (by positivity) (by positivity)]
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
      have h2 : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
      linarith
    have h3 : (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ 1 := by
      calc (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ n * (1 / n) := by gcongr
        _ = 1 := by field_simp
    nlinarith [ih]

theorem sum_log_primes_le (n : ℕ) :
    ∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, Real.log p ≤ Real.log 4 * n := by
  have h := Chebyshev.theta_le_log4_mul_x (x := (n : ℝ)) (Nat.cast_nonneg n)
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast] at h
  have : (Finset.Icc 0 n).filter Nat.Prime = (Finset.Icc 1 n).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h2.one_lt.le, h1.2⟩, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨Nat.zero_le _, h1.2⟩, h2⟩
  rw [this] at h
  exact h

theorem A_le (n : ℕ) (hn : 1 ≤ n) : A n ≤ Real.log n + Real.log 4 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (n : ℝ) * A n - ∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, Real.log p
      ≤ Real.log (n.factorial : ℝ) := by
    rw [log_factorial_eq, A, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hp1, hpn⟩, hpp⟩ := hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp1)
    have hv : n / p ≤ n.factorial.factorization p := by
      rw [Nat.factorization_factorial hpp (Nat.lt_succ_self _)]
      have h1 : 1 ∈ Finset.Ico 1 (Nat.log p n + 1) := by
        simp only [Finset.mem_Ico]
        exact ⟨le_refl _, Nat.succ_lt_succ (Nat.log_pos hpp.one_lt hpn)⟩
      calc n / p = n / p ^ 1 := by rw [pow_one]
        _ ≤ _ := Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) h1
    have hv' : (n : ℝ) / p - 1 ≤ ((n.factorial.factorization p : ℕ) : ℝ) := by
      have h2 : n < p * (n / p + 1) := Nat.lt_mul_div_succ n hpp.pos
      have h3 : (n : ℝ) < p * ((n / p : ℕ) + 1) := by exact_mod_cast h2
      have h4 : ((n / p : ℕ) : ℝ) ≤ ((n.factorial.factorization p : ℕ) : ℝ) := by exact_mod_cast hv
      have h5 : (n : ℝ) / p < ((n / p : ℕ) : ℝ) + 1 := by
        rw [div_lt_iff₀ hp0]; linarith
      linarith
    calc (n : ℝ) * (Real.log p / p) - Real.log p = ((n : ℝ) / p - 1) * Real.log p := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hv' hlog
  have h2 : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
    have : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    calc Real.log (n.factorial : ℝ) ≤ Real.log ((n : ℝ) ^ n) :=
          Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) this
      _ = n * Real.log n := Real.log_pow _ _
  have h3 := sum_log_primes_le n
  have h4 : (n : ℝ) * A n ≤ n * (Real.log n + Real.log 4) := by nlinarith
  exact le_of_mul_le_mul_left h4 hnR

theorem G_step (x : ℝ) (hx : 2 ≤ x) :
    Real.log x / (x * (x - 1)) ≤ (Real.log x + 1) / (x - 1) - (Real.log (x + 1) + 1) / x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have h1 : Real.log (x + 1) - Real.log x ≤ 1 / x := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (x + 1) / x by positivity)
    have h2 : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    linarith
  have h3 : (x - 1) * (Real.log (x + 1) - Real.log x) ≤ 1 := by
    calc (x - 1) * (Real.log (x + 1) - Real.log x) ≤ (x - 1) * (1 / x) := by gcongr
      _ ≤ 1 := by rw [mul_one_div, div_le_one hx0]; linarith
  rw [div_sub_div _ _ hx1.ne' hx0.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hx0 hx1, Real.log_nonneg (show (1 : ℝ) ≤ x by linarith)]

theorem sum_tail_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤
      (Real.log 2 + 1) - (Real.log ((n : ℝ) + 1) + 1) / n := by
  induction n, hn using Nat.le_induction with
  | base =>
    have : (Finset.Icc 1 1).filter Nat.Prime = ∅ := by decide
    rw [this]
    simp
    norm_num
  | succ n hn ih =>
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hstep := G_step ((n : ℝ) + 1) (by linarith)
    have hsub : (Finset.Icc 1 (n + 1)).filter Nat.Prime ⊆
        insert (n + 1) ((Finset.Icc 1 n).filter Nat.Prime) := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Icc] at hp
      rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
      rcases Nat.lt_or_ge p (n + 1) with h | h
      · right; exact ⟨⟨hp.1.1, by omega⟩, hp.2⟩
      · left; omega
    have hnot : (n + 1) ∉ (Finset.Icc 1 n).filter Nat.Prime := by
      rw [Finset.mem_filter, Finset.mem_Icc]; omega
    have hnn : ∀ p ∈ insert (n + 1) ((Finset.Icc 1 n).filter Nat.Prime),
        0 ≤ Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
      intro p hp
      have hp1 : 1 ≤ p := by
        rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc] at hp
        omega
      have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp1
      apply div_nonneg (Real.log_nonneg hpR)
      apply mul_nonneg <;> linarith
    calc ∑ p ∈ (Finset.Icc 1 (n + 1)).filter Nat.Prime, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ ∑ p ∈ insert (n + 1) ((Finset.Icc 1 n).filter Nat.Prime),
            Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => hnn p hp)
      _ = Real.log ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1)) +
            ∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) :=
          Finset.sum_insert hnot
      _ ≤ _ := by
          push_cast
          have e1 : (n : ℝ) + 1 - 1 = n := by ring
          have e2 : (n : ℝ) + 1 + 1 = (n : ℝ) + 1 + 1 := rfl
          rw [e1] at hstep ⊢
          linarith

theorem A_ge (n : ℕ) (hn : 1 ≤ n) : Real.log n - (2 + Real.log 2) ≤ A n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : Real.log (n.factorial : ℝ) ≤ (n : ℝ) * A n +
      n * ∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [log_factorial_eq, A, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hp1, hpn⟩, hpp⟩ := hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hp1' : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have hv : n.factorial.factorization p ≤ n / (p - 1) :=
      Nat.factorization_factorial_le_div_pred hpp n
    have hv' : ((n.factorial.factorization p : ℕ) : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) := by
      have h2 : ((n / (p - 1) : ℕ) : ℝ) ≤ (n : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
      have h3 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        rw [Nat.cast_sub hpp.one_lt.le]; simp
      rw [h3] at h2
      have h4 : ((n.factorial.factorization p : ℕ) : ℝ) ≤ ((n / (p - 1) : ℕ) : ℝ) := by
        exact_mod_cast hv
      linarith
    calc ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p
        ≤ (n : ℝ) / ((p : ℝ) - 1) * Real.log p := mul_le_mul_of_nonneg_right hv' hlog
      _ = (n : ℝ) * (Real.log p / p) + n * (Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
          field_simp
          ring
  have h2 := log_factorial_ge n
  have h3 := sum_tail_le n hn
  have h4 : 0 ≤ (Real.log ((n : ℝ) + 1) + 1) / n := by
    apply div_nonneg _ hnR.le
    have := Real.log_nonneg (show (1 : ℝ) ≤ (n : ℝ) + 1 by linarith)
    linarith
  have h5 : (n : ℝ) * (Real.log n - (2 + Real.log 2)) ≤ n * A n := by nlinarith
  exact le_of_mul_le_mul_left h5 hnR

theorem A_abs (n : ℕ) (hn : 1 ≤ n) : |A n - Real.log n| ≤ 3 := by
  have h1 := A_le n hn
  have h2 := A_ge n hn
  have h3 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [abs_le]
  constructor <;> linarith

/-- primes in `[y, V*y)` -/
theorem sum_inv_short (y V : ℕ) (hy : 2 ≤ y) (hV : 1 ≤ V) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ y ≤ q ∧ q < V * y) :
    ∑ q ∈ Q, (1 : ℝ) / q ≤ (Real.log V + 7) / Real.log y := by
  have hy1 : (1 : ℝ) < y := by exact_mod_cast hy
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hVy : y ≤ V * y := Nat.le_mul_of_pos_left y hV
  have h1 : ∀ q ∈ Q, (1 : ℝ) / q ≤ (Real.log q / q) / Real.log y := by
    intro q hq
    obtain ⟨hqp, hyq, _⟩ := hQ q hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
    have hle : Real.log y ≤ Real.log q :=
      Real.log_le_log (by positivity) (by exact_mod_cast hyq)
    rw [div_div, div_le_div_iff₀ hq0 (by positivity)]
    nlinarith
  have h2 : ∑ q ∈ Q, Real.log q / q ≤ A (V * y - 1) - A (y - 1) := by
    have hsub : (Finset.Icc 1 (y - 1)).filter Nat.Prime ⊆
        (Finset.Icc 1 (V * y - 1)).filter Nat.Prime := by
      apply Finset.filter_subset_filter
      apply Finset.Icc_subset_Icc_right
      omega
    rw [A, A, ← Finset.sum_sdiff hsub, add_sub_cancel_right]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      obtain ⟨hqp, hyq, hqV⟩ := hQ q hq
      rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨⟨hqp.one_lt.le, by omega⟩, hqp⟩, fun h => by omega⟩
    · intro q hq _
      rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc] at hq
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hq.1.1.1)) (Nat.cast_nonneg _)
  have h3 := A_abs (V * y - 1) (by omega)
  have h4 := A_abs (y - 1) (by omega)
  rw [abs_le] at h3 h4
  have h5 : Real.log ((V * y - 1 : ℕ) : ℝ) ≤ Real.log V + Real.log y := by
    have hV0 : (0 : ℝ) < V := by exact_mod_cast hV
    rw [← Real.log_mul hV0.ne' (by positivity)]
    apply Real.log_le_log
    · have : 1 ≤ V * y - 1 := by omega
      exact_mod_cast this
    · have : V * y - 1 ≤ V * y := Nat.sub_le _ _
      exact_mod_cast this
  have h6 : Real.log y - Real.log 2 ≤ Real.log ((y - 1 : ℕ) : ℝ) := by
    rw [← Real.log_div (by positivity) (by norm_num)]
    apply Real.log_le_log (by positivity)
    have : y ≤ 2 * (y - 1) := by omega
    have h7 : (y : ℝ) ≤ 2 * ((y - 1 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have h8 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  calc ∑ q ∈ Q, (1 : ℝ) / q ≤ ∑ q ∈ Q, (Real.log q / q) / Real.log y := Finset.sum_le_sum h1
    _ = (∑ q ∈ Q, Real.log q / q) / Real.log y := by rw [Finset.sum_div]
    _ ≤ (Real.log V + 7) / Real.log y := by
        apply div_le_div_of_nonneg_right _ hlogy.le
        linarith

/-- a cluster of primes whose `j`-th powers are within a factor `V` of each other -/
theorem sum_inv_cluster (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (V j : ℕ) (z : ℝ) (hV : 1 ≤ V)
    (hj : 1 ≤ j) (hz : 0 < z) (hzQ : ∀ p ∈ Q, z ≤ Real.log p)
    (h : ∀ p ∈ Q, ∀ q ∈ Q, p ^ j < V * q ^ j) :
    ∑ p ∈ Q, (1 : ℝ) / p ≤ (Real.log V + 7) / z := by
  have hlogV : 0 ≤ Real.log V := Real.log_nonneg (by exact_mod_cast hV)
  rcases Q.eq_empty_or_nonempty with rfl | hne
  · rw [Finset.sum_empty]; positivity
  have hyQ : Q.min' hne ∈ Q := Q.min'_mem hne
  have hy2 : 2 ≤ Q.min' hne := (hQ _ hyQ).two_le
  have hy1 : (1 : ℝ) < (Q.min' hne : ℝ) := by exact_mod_cast hy2
  have hmain := sum_inv_short (Q.min' hne) V hy2 hV Q (fun q hq => ⟨hQ q hq, Q.min'_le q hq, by
    have h1 := h q hq _ hyQ
    have h2 : V * (Q.min' hne) ^ j ≤ (V * Q.min' hne) ^ j := by
      rw [mul_pow]
      exact Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega) V)
    exact lt_of_pow_lt_pow_left₀ j (Nat.zero_le _) (lt_of_lt_of_le h1 h2)⟩)
  calc ∑ p ∈ Q, (1 : ℝ) / p ≤ (Real.log V + 7) / Real.log (Q.min' hne) := hmain
    _ ≤ (Real.log V + 7) / z :=
        div_le_div_of_nonneg_left (by linarith) hz (hzQ _ hyQ)

/-- primes with a prescribed number of digits of `N` -/
theorem sum_inv_class (N k : ℕ) (hk : 1 ≤ k) :
    ∑ p ∈ (Finset.Icc 1 N).filter (fun p => p.Prime ∧ Nat.log p N = k), (1 : ℝ) / p ≤ 12 := by
  rcases ((Finset.Icc 1 N).filter (fun p => p.Prime ∧ Nat.log p N = k)).eq_empty_or_nonempty
    with he | hne
  · rw [he, Finset.sum_empty]; norm_num
  have hyQ := Finset.min'_mem _ hne
  set y := Finset.min' _ hne with hydef
  rw [Finset.mem_filter, Finset.mem_Icc] at hyQ
  obtain ⟨⟨hy1, hyN⟩, hyp, hyk⟩ := hyQ
  have hy2 : 2 ≤ y := hyp.two_le
  have hN0 : N ≠ 0 := by omega
  have hmain := sum_inv_short y y hy2 (by omega)
    ((Finset.Icc 1 N).filter (fun p => p.Prime ∧ Nat.log p N = k)) (fun q hq => by
      have hyq : y ≤ q := Finset.min'_le _ q hq
      rw [Finset.mem_filter, Finset.mem_Icc] at hq
      obtain ⟨⟨hq1, hqN⟩, hqp, hqk⟩ := hq
      refine ⟨hqp, hyq, ?_⟩
      have h1 : q ^ k ≤ N := by rw [← hqk]; exact Nat.pow_log_le_self q hN0
      have h2 : N < y ^ (k + 1) := by rw [← hyk]; exact Nat.lt_pow_succ_log_self hyp.one_lt N
      have h3 : y ^ (k + 1) ≤ (y * y) ^ k := by
        rw [mul_pow, pow_succ]
        exact Nat.mul_le_mul_left _ (Nat.le_self_pow (by omega) y)
      exact lt_of_pow_lt_pow_left₀ k (Nat.zero_le _) (by omega))
  have hy1R : (2 : ℝ) ≤ y := by exact_mod_cast hy2
  have hlog2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hlogy : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy1R
  have hlogy0 : 0 < Real.log y := by linarith
  calc _ ≤ (Real.log y + 7) / Real.log y := hmain
    _ ≤ 12 := by
        rw [div_le_iff₀ hlogy0]
        nlinarith

/-- `A` as a sum of an indicator-weighted function -/
theorem A_succ (n : ℕ) :
    A (n + 1) = A n + (if (n + 1).Prime then Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) else 0) := by
  unfold A
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_Icc_succ_top (by omega)]

theorem loglog_step (v : ℕ) (hv : 2 ≤ v) :
    0 ≤ (Real.log (Real.log ((v + 1 : ℕ) : ℝ)) - Real.log (Real.log (v : ℝ))) -
        (Real.log ((v + 1 : ℕ) : ℝ) - Real.log (v : ℝ)) / Real.log ((v + 1 : ℕ) : ℝ) ∧
    (Real.log (Real.log ((v + 1 : ℕ) : ℝ)) - Real.log (Real.log (v : ℝ))) -
        (Real.log ((v + 1 : ℕ) : ℝ) - Real.log (v : ℝ)) / Real.log ((v + 1 : ℕ) : ℝ) ≤
      Real.log 2 * (1 / Real.log (v : ℝ) - 1 / Real.log ((v + 1 : ℕ) : ℝ)) := by
  have hvR : (2 : ℝ) ≤ v := by exact_mod_cast hv
  have hv0 : (0 : ℝ) < v := by linarith
  have ht : 0 < Real.log (v : ℝ) := Real.log_pos (by linarith)
  have hcast : ((v + 1 : ℕ) : ℝ) = (v : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hst : Real.log (v : ℝ) < Real.log ((v : ℝ) + 1) := Real.log_lt_log hv0 (by linarith)
  have hs : 0 < Real.log ((v : ℝ) + 1) := by linarith
  have hd : Real.log ((v : ℝ) + 1) - Real.log (v : ℝ) ≤ Real.log 2 := by
    rw [← Real.log_div (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ hv0]; linarith
  generalize Real.log ((v : ℝ) + 1) = s at *
  generalize Real.log (v : ℝ) = t at *
  have h1 : Real.log s - Real.log t ≤ s / t - 1 := by
    rw [← Real.log_div hs.ne' ht.ne']
    exact Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log t - Real.log s ≤ t / s - 1 := by
    rw [← Real.log_div ht.ne' hs.ne']
    exact Real.log_le_sub_one_of_pos (by positivity)
  have e1 : (s - t) / s = 1 - t / s := by field_simp
  have e2 : s / t - 1 - (1 - t / s) = (s - t) * (1 / t - 1 / s) := by field_simp
  have h3 : 0 ≤ 1 / t - 1 / s := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le ht hst.le
  constructor
  · rw [e1]; linarith
  · rw [e1]
    calc Real.log s - Real.log t - (1 - t / s) ≤ s / t - 1 - (1 - t / s) := by linarith
      _ = (s - t) * (1 / t - 1 / s) := e2
      _ ≤ Real.log 2 * (1 / t - 1 / s) := mul_le_mul_of_nonneg_right hd h3

/-- Mertens' second theorem in difference form. -/
theorem mertens2 (u v : ℕ) (hu : 2 ≤ u) (huv : u ≤ v) :
    |∑ p ∈ (Finset.Ioc u v).filter Nat.Prime, (1 : ℝ) / p -
      (Real.log (Real.log v) - Real.log (Real.log u))| ≤ 7 / Real.log u := by
  have huR : (2 : ℝ) ≤ u := by exact_mod_cast hu
  have hlogu : 0 < Real.log (u : ℝ) := Real.log_pos (by linarith)
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- joint induction
  have key : ∀ w : ℕ, u ≤ w →
      ∃ e : ℝ, |e| ≤ 3 * (1 / Real.log ((u + 1 : ℕ) : ℝ) - 1 / Real.log ((w + 1 : ℕ) : ℝ)) ∧
      ∃ d : ℝ, 0 ≤ d ∧ d ≤ Real.log 2 * (1 / Real.log (u : ℝ) - 1 / Real.log (w : ℝ)) ∧
      ∑ p ∈ (Finset.Ioc u w).filter Nat.Prime, (1 : ℝ) / p =
        (Real.log (Real.log w) - Real.log (Real.log u)) - d + e
          + (A w - Real.log w) / Real.log ((w + 1 : ℕ) : ℝ)
          - (A u - Real.log u) / Real.log ((u + 1 : ℕ) : ℝ) := by
    intro w hw
    induction w, hw using Nat.le_induction with
    | base => exact ⟨0, by simp, 0, le_refl _, by simp, by simp⟩
    | succ w hw ih =>
      obtain ⟨e, he, d, hd0, hd1, hsum⟩ := ih
      have hw2 : 2 ≤ w := le_trans hu hw
      obtain ⟨hs1, hs2⟩ := loglog_step w hw2
      have hwR : (2 : ℝ) ≤ w := by exact_mod_cast hw2
      have hlw : 0 < Real.log (w : ℝ) := Real.log_pos (by linarith)
      have hlw1 : 0 < Real.log ((w + 1 : ℕ) : ℝ) := Real.log_pos (by push_cast; linarith)
      have hlw2 : 0 < Real.log ((w + 1 + 1 : ℕ) : ℝ) := Real.log_pos (by push_cast; linarith)
      have hmono : Real.log ((w + 1 : ℕ) : ℝ) ≤ Real.log ((w + 1 + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by push_cast; linarith)
      have hRabs := A_abs (w + 1) (by omega)
      have hgdiff : 0 ≤ 1 / Real.log ((w + 1 : ℕ) : ℝ) - 1 / Real.log ((w + 1 + 1 : ℕ) : ℝ) := by
        rw [sub_nonneg]; exact one_div_le_one_div_of_le hlw1 hmono
      refine ⟨e + (A (w + 1) - Real.log ((w + 1 : ℕ) : ℝ)) *
          (1 / Real.log ((w + 1 : ℕ) : ℝ) - 1 / Real.log ((w + 1 + 1 : ℕ) : ℝ)), ?_,
        d + ((Real.log (Real.log ((w + 1 : ℕ) : ℝ)) - Real.log (Real.log (w : ℝ))) -
          (Real.log ((w + 1 : ℕ) : ℝ) - Real.log (w : ℝ)) / Real.log ((w + 1 : ℕ) : ℝ)),
        by linarith, by linarith, ?_⟩
      · calc |e + (A (w + 1) - Real.log ((w + 1 : ℕ) : ℝ)) *
              (1 / Real.log ((w + 1 : ℕ) : ℝ) - 1 / Real.log ((w + 1 + 1 : ℕ) : ℝ))|
            ≤ |e| + |(A (w + 1) - Real.log ((w + 1 : ℕ) : ℝ)) *
              (1 / Real.log ((w + 1 : ℕ) : ℝ) - 1 / Real.log ((w + 1 + 1 : ℕ) : ℝ))| :=
              abs_add_le _ _
          _ ≤ |e| + 3 * (1 / Real.log ((w + 1 : ℕ) : ℝ) - 1 / Real.log ((w + 1 + 1 : ℕ) : ℝ)) := by
              rw [abs_mul, abs_of_nonneg hgdiff]
              have := mul_le_mul_of_nonneg_right hRabs hgdiff
              linarith
          _ ≤ _ := by linarith
      · have hfilt : ∑ p ∈ (Finset.Ioc u (w + 1)).filter Nat.Prime, (1 : ℝ) / p =
            ∑ p ∈ (Finset.Ioc u w).filter Nat.Prime, (1 : ℝ) / p +
              (if (w + 1).Prime then (1 : ℝ) / ((w + 1 : ℕ) : ℝ) else 0) := by
          rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_Ioc_succ_top hw]
        have hA := A_succ w
        have hterm : (if (w + 1).Prime then (1 : ℝ) / ((w + 1 : ℕ) : ℝ) else 0) =
            (A (w + 1) - A w) / Real.log ((w + 1 : ℕ) : ℝ) := by
          rw [hA, add_sub_cancel_left]
          split_ifs with hpr
          · have hw1 : (0 : ℝ) < ((w + 1 : ℕ) : ℝ) := by positivity
            field_simp
          · simp
        rw [hfilt, hsum, hterm]
        field_simp
        ring
  obtain ⟨e, he, d, hd0, hd1, hsum⟩ := key v huv
  have hvR : (2 : ℝ) ≤ v := by exact_mod_cast le_trans hu huv
  have hlogv : 0 < Real.log (v : ℝ) := Real.log_pos (by linarith)
  have hlu1 : 0 < Real.log ((u + 1 : ℕ) : ℝ) := Real.log_pos (by push_cast; linarith)
  have hlv1 : 0 < Real.log ((v + 1 : ℕ) : ℝ) := Real.log_pos (by push_cast; linarith)
  have hRu := A_abs u (by omega)
  have hRv := A_abs v (by omega)
  have hmu : Real.log (u : ℝ) ≤ Real.log ((u + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by push_cast; linarith)
  have hmv : Real.log ((u + 1 : ℕ) : ℝ) ≤ Real.log ((v + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.succ_le_succ huv)
  have hgu : 1 / Real.log ((u + 1 : ℕ) : ℝ) ≤ 1 / Real.log (u : ℝ) :=
    one_div_le_one_div_of_le hlogu hmu
  have hgv : 1 / Real.log ((v + 1 : ℕ) : ℝ) ≤ 1 / Real.log ((u + 1 : ℕ) : ℝ) :=
    one_div_le_one_div_of_le hlu1 hmv
  have hgv0 : 0 < 1 / Real.log ((v + 1 : ℕ) : ℝ) := by positivity
  have hgvv : 0 < 1 / Real.log (v : ℝ) := by positivity
  have hb1 : |(A v - Real.log v) / Real.log ((v + 1 : ℕ) : ℝ)| ≤
      3 * (1 / Real.log ((v + 1 : ℕ) : ℝ)) := by
    rw [abs_div, abs_of_pos hlv1, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right hRv hgv0.le
  have hb2 : |(A u - Real.log u) / Real.log ((u + 1 : ℕ) : ℝ)| ≤
      3 * (1 / Real.log ((u + 1 : ℕ) : ℝ)) := by
    rw [abs_div, abs_of_pos hlu1, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right hRu (by positivity)
  rw [hsum]
  have e7 : (7 : ℝ) / Real.log (u : ℝ) = 7 * (1 / Real.log (u : ℝ)) := by ring
  rw [e7]
  rw [abs_le] at he hb1 hb2 ⊢
  have hgu0 : 0 < 1 / Real.log (u : ℝ) := by positivity
  constructor <;> nlinarith

/-- the moduli `p, p^2, …, p^k` -/
def mods (p k : ℕ) : Finset ℕ := (Finset.Icc 1 k).image (fun j => p ^ j)

/-- good primes at scale `N` -/
def Good (K U N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun p => p.Prime ∧ Nat.log p N < K ∧ U * p ^ Nat.log p N ≤ N ∧
    2 * N < p ^ (Nat.log p N + 1))

/-- digit indicator -/
noncomputable def Y (N p n : ℕ) : ℝ :=
  if ∀ m ∈ mods p (Nat.log p N), 2 * (n % m) < m then 1 else 0

/-- truncated function -/
noncomputable def ft (K U N n : ℕ) : ℝ := ∑ p ∈ Good K U N, Y N p n / p

/-- its expected value -/
noncomputable def cN (K U N : ℕ) : ℝ := ∑ p ∈ Good K U N, (1 / 2 : ℝ) ^ Nat.log p N / p

/-- the bad part -/
noncomputable def bN (K U N n : ℕ) : ℝ :=
  ∑ p ∈ ((Finset.Icc 1 n).filter Nat.Prime) \ Good K U N,
    if p ∣ n.centralBinom then 0 else (1 : ℝ) / p

/-- partial constants -/
noncomputable def gam (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico 1 K, (1 / 2 : ℝ) ^ k * (Real.log ((k : ℝ) + 1) - Real.log k)

/-- error rate -/
noncomputable def rho (K U N : ℕ) : ℝ := K * (Real.log U + 7) / (Real.log N - Real.log U)

theorem rho_tendsto (K U : ℕ) : Tendsto (rho K U) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun N : ℕ => Real.log (N : ℝ) - Real.log U) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-Real.log U) h1
  exact tendsto_const_nhds.div_atTop h2

theorem gam_shift (m : ℕ) :
    gam (m + 2) = ∑ j ∈ range m, Real.log ((j : ℝ) + 2) / 2 ^ (j + 2) +
      (1 / 2 : ℝ) ^ (m + 1) * Real.log ((m : ℝ) + 2) := by
  induction m with
  | zero =>
    simp only [gam, Finset.range_zero, Finset.sum_empty, zero_add]
    norm_num
  | succ m ih =>
    have e : gam (m + 1 + 2) = gam (m + 2) +
        (1 / 2 : ℝ) ^ (m + 2) * (Real.log (((m + 2 : ℕ) : ℝ) + 1) - Real.log ((m + 2 : ℕ) : ℝ)) := by
      unfold gam
      rw [show m + 1 + 2 = (m + 2) + 1 by ring, Finset.sum_Ico_succ_top (by omega)]
    rw [e, ih, Finset.sum_range_succ]
    push_cast
    have e1 : (m : ℝ) + 2 + 1 = (m : ℝ) + 1 + 2 := by ring
    rw [e1]
    have e2 : (1 / 2 : ℝ) ^ (m + 1) = 2 * (1 / 2 : ℝ) ^ (m + 2) := by
      rw [pow_succ (1 / 2 : ℝ) (m + 1)]; ring
    have e3 : Real.log ((m : ℝ) + 2) / 2 ^ (m + 2) = (1 / 2 : ℝ) ^ (m + 2) * Real.log ((m : ℝ) + 2) := by
      rw [one_div, inv_pow]; ring
    rw [e2, e3]
    ring

theorem summable_aux : Summable (fun k : ℕ => (((k + 2 : ℕ) : ℝ)) ^ 1 * (1 / 2 : ℝ) ^ (k + 2)) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 2 : ℝ)) (by norm_num)
  exact (summable_nat_add_iff 2).mpr h

theorem log_le_self_nat (k : ℕ) : Real.log ((k : ℝ) + 2) ≤ (k : ℝ) + 2 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (k : ℝ) + 2 by positivity)
  linarith

theorem gam_tendsto (γ₀ : ℝ) (hγ₀ : γ₀ = ∑' (k : ℕ), Real.log ((k : ℝ) + 2) / 2 ^ (k + 2)) :
    Tendsto gam atTop (𝓝 γ₀) := by
  have hsum : Summable (fun k : ℕ => Real.log ((k : ℝ) + 2) / 2 ^ (k + 2)) := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) summable_aux
    · exact div_nonneg (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k])) (by positivity)
    · have h := log_le_self_nat k
      push_cast
      rw [pow_one, one_div, inv_pow, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right h (by positivity)
  have h1 : Tendsto (fun m : ℕ => ∑ j ∈ range m, Real.log ((j : ℝ) + 2) / 2 ^ (j + 2)) atTop (𝓝 γ₀) := by
    rw [hγ₀]; exact hsum.hasSum.tendsto_sum_nat
  have h2 : Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ (m + 1) * Real.log ((m : ℝ) + 2)) atTop (𝓝 0) := by
    have h3 : Tendsto (fun k : ℕ => 2 * ((((k + 2 : ℕ) : ℝ)) ^ 1 * (1 / 2 : ℝ) ^ (k + 2))) atTop (𝓝 (2 * 0)) :=
      summable_aux.tendsto_atTop_zero.const_mul 2
    rw [mul_zero] at h3
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun m => ?_) (fun m => ?_)
    · exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m]))
    · have h := log_le_self_nat m
      have e2 : (1 / 2 : ℝ) ^ (m + 1) = 2 * (1 / 2 : ℝ) ^ (m + 2) := by
        rw [pow_succ (1 / 2 : ℝ) (m + 1)]; ring
      show (1 / 2 : ℝ) ^ (m + 1) * Real.log ((m : ℝ) + 2) ≤
        2 * ((((m + 2 : ℕ) : ℝ)) ^ 1 * (1 / 2 : ℝ) ^ (m + 2))
      rw [e2, pow_one]
      push_cast
      have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ (m + 2) := by positivity
      nlinarith
  have h3 : Tendsto (fun m : ℕ => gam (m + 2)) atTop (𝓝 γ₀) := by
    have := h1.add h2
    rw [add_zero] at this
    refine this.congr (fun m => ?_)
    rw [gam_shift]
  exact (tendsto_add_atTop_iff_nat 2).mp h3

theorem good_mem {K U N p : ℕ} (hp : p ∈ Good K U N) :
    p.Prime ∧ 1 ≤ p ∧ p ≤ N ∧ Nat.log p N < K ∧ U * p ^ Nat.log p N ≤ N ∧
      2 * N < p ^ (Nat.log p N + 1) := by
  unfold Good at hp
  rw [Finset.mem_filter, Finset.mem_Icc] at hp
  exact ⟨hp.2.1, hp.1.1, hp.1.2, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2⟩

theorem forall_mods (p k : ℕ) (P : ℕ → Prop) :
    (∀ m ∈ mods p k, P m) ↔ ∀ i ∈ Finset.Icc 1 k, P (p ^ i) := by
  unfold mods
  rw [Finset.forall_mem_image]

/-- on good primes, the Kummer criterion only involves the moduli `p^1, …, p^k` -/
theorem good_kummer {K U N p n : ℕ} (hp : p ∈ Good K U N) (hn : n < N) :
    ¬ p ∣ n.centralBinom ↔ ∀ m ∈ mods p (Nat.log p N), 2 * (n % m) < m := by
  obtain ⟨hpp, hp1, hpN, hk, hU, h2⟩ := good_mem hp
  rw [not_dvd_centralBinom_iff hpp, forall_mods]
  constructor
  · intro h i hi
    exact h i (Finset.mem_Icc.mp hi).1
  · intro h i hi
    rcases Nat.lt_or_ge (Nat.log p N) i with hlt | hge
    · have h3 : p ^ (Nat.log p N + 1) ≤ p ^ i := Nat.pow_le_pow_right hpp.pos hlt
      have h4 : n % p ^ i ≤ n := Nat.mod_le _ _
      omega
    · exact h i (Finset.mem_Icc.mpr ⟨hi, hge⟩)

theorem f_decomp (K U N n : ℕ) (hU : 1 ≤ U) (hn : n < N) (hUn : N ≤ U * n) :
    Erdos377.sumInvPrimesNotDvdCentralBinom n = ft K U N n + bN K U N n := by
  have hsub : Good K U N ⊆ (Finset.Icc 1 n).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpp, hp1, hpN, hk, hUp, h2⟩ := good_mem hp
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hp1, ?_⟩, hpp⟩
    have hk1 : 1 ≤ Nat.log p N := Nat.log_pos hpp.one_lt hpN
    have h3 : p ≤ p ^ Nat.log p N := Nat.le_self_pow (by omega) p
    have h4 : U * p ≤ U * n := le_trans (Nat.mul_le_mul_left U h3) (le_trans hUp hUn)
    exact Nat.le_of_mul_le_mul_left h4 (by omega)
  unfold Erdos377.sumInvPrimesNotDvdCentralBinom ft bN
  rw [← Finset.sum_sdiff hsub, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  unfold Y
  by_cases hd : p ∣ n.centralBinom
  · rw [if_pos hd, if_neg (fun h => (good_kummer hp hn).mpr h hd)]
    simp
  · rw [if_neg hd, if_pos ((good_kummer hp hn).mp hd)]

theorem bN_nonneg (K U N n : ℕ) : 0 ≤ bN K U N n := by
  unfold bN
  apply Finset.sum_nonneg
  intro p _
  split_ifs
  · exact le_refl _
  · positivity

theorem log_ratio_tendsto (x a b : ℕ → ℝ) (α β C : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hx : Tendsto x atTop atTop)
    (ha : ∀ᶠ N in atTop, |a N - α * x N| ≤ C) (hb : ∀ᶠ N in atTop, |b N - β * x N| ≤ C) :
    Tendsto (fun N => Real.log (a N) - Real.log (b N)) atTop
      (𝓝 (Real.log α - Real.log β)) := by
  have hC : Tendsto (fun N => C / x N) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hx
  have key : ∀ (c : ℕ → ℝ) (γ : ℝ), 0 < γ → (∀ᶠ N in atTop, |c N - γ * x N| ≤ C) →
      Tendsto (fun N => c N / x N) atTop (𝓝 γ) ∧ ∀ᶠ N in atTop, 0 < c N := by
    intro c γ hγ hc
    constructor
    · have hlo : Tendsto (fun N => γ - C / x N) atTop (𝓝 γ) := by
        simpa using tendsto_const_nhds.sub hC
      have hhi : Tendsto (fun N => γ + C / x N) atTop (𝓝 γ) := by
        simpa using tendsto_const_nhds.add hC
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
      · filter_upwards [hc, hx.eventually_gt_atTop 0] with N h1 h2
        rw [abs_le] at h1
        rw [le_div_iff₀ h2]
        have : (γ - C / x N) * x N = γ * x N - C := by field_simp
        linarith
      · filter_upwards [hc, hx.eventually_gt_atTop 0] with N h1 h2
        rw [abs_le] at h1
        rw [div_le_iff₀ h2]
        have : (γ + C / x N) * x N = γ * x N + C := by field_simp
        linarith
    · filter_upwards [hc, hx.eventually_gt_atTop (C / γ)] with N h1 h2
      rw [abs_le] at h1
      rw [div_lt_iff₀ hγ] at h2
      nlinarith
  obtain ⟨ha1, ha2⟩ := key a α hα ha
  obtain ⟨hb1, hb2⟩ := key b β hβ hb
  have h := (ha1.log hα.ne').sub (hb1.log hβ.ne')
  refine h.congr' ?_
  filter_upwards [ha2, hb2, hx.eventually_gt_atTop 0] with N h1 h2 h3
  rw [Real.log_div h1.ne' h3.ne', Real.log_div h2.ne' h3.ne']
  ring

theorem root_facts (k U : ℕ) (hk : 1 ≤ k) (hU : 1 ≤ U) (N : ℕ) (hN : (2 * U) ^ (k + 1) ≤ N) :
    2 ≤ Nat.nthRoot (k + 1) (2 * N) ∧ Nat.nthRoot (k + 1) (2 * N) ≤ Nat.nthRoot k (N / U) ∧
    |Real.log (Nat.nthRoot (k + 1) (2 * N)) - 1 / ((k : ℝ) + 1) * Real.log N| ≤
      Real.log (2 * U) + Real.log 2 ∧
    |Real.log (Nat.nthRoot k (N / U)) - 1 / (k : ℝ) * Real.log N| ≤
      Real.log (2 * U) + Real.log 2 := by
  have hk0 : k ≠ 0 := by omega
  have hk10 : k + 1 ≠ 0 := by omega
  have h2U : 2 * U ≤ (2 * U) ^ (k + 1) := Nat.le_self_pow hk10 _
  have hNU : 2 * U ≤ N := le_trans h2U hN
  have hN1 : 1 ≤ N := by omega
  set u := Nat.nthRoot (k + 1) (2 * N) with hu
  set v := Nat.nthRoot k (N / U) with hv
  have hu1 : u ^ (k + 1) ≤ 2 * N := Nat.pow_nthRoot_le (Or.inl hk10)
  have hu2 : 2 * N < (u + 1) ^ (k + 1) := Nat.lt_pow_nthRoot_add_one hk10 _
  have hv1 : v ^ k ≤ N / U := Nat.pow_nthRoot_le (Or.inl hk0)
  have hv2 : N / U < (v + 1) ^ k := Nat.lt_pow_nthRoot_add_one hk0 _
  have hu2U : 2 * U ≤ u := by
    rw [hu, Nat.le_nthRoot_iff hk10]; omega
  have huv : u ≤ v := by
    rw [hv, Nat.le_nthRoot_iff hk0, Nat.le_div_iff_mul_le (by omega)]
    have h1 : u ^ k * (2 * U) ≤ u ^ k * u := Nat.mul_le_mul_left _ hu2U
    have h2 : u ^ k * u = u ^ (k + 1) := (pow_succ u k).symm
    have h3 : u ^ k * (2 * U) = 2 * (u ^ k * U) := by ring
    omega
  have hu2' : 2 ≤ u := by omega
  have hv2' : 2 ≤ v := le_trans hu2' huv
  refine ⟨hu2', huv, ?_, ?_⟩
  · -- log u
    have huR : (2 : ℝ) ≤ u := by exact_mod_cast hu2'
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hκ : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hL2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hL2U : 0 ≤ Real.log (2 * (U : ℝ)) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ U := by exact_mod_cast hU
      linarith
    have e1 : Real.log ((2 * N : ℕ) : ℝ) = Real.log 2 + Real.log N := by
      push_cast
      rw [Real.log_mul (by norm_num) (by positivity)]
    have h1 : ((k : ℝ) + 1) * Real.log u ≤ Real.log 2 + Real.log N := by
      rw [← e1]
      have : Real.log (((u ^ (k + 1) : ℕ)) : ℝ) ≤ Real.log ((2 * N : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hu1)
      rw [Nat.cast_pow, Real.log_pow] at this
      push_cast at this ⊢
      linarith
    have h2 : Real.log 2 + Real.log N < ((k : ℝ) + 1) * (Real.log 2 + Real.log u) := by
      have h3 : (u + 1) ^ (k + 1) ≤ (2 * u) ^ (k + 1) := Nat.pow_le_pow_left (by omega) _
      have h4 : (2 * N : ℕ) < (2 * u) ^ (k + 1) := lt_of_lt_of_le hu2 h3
      have h5 : Real.log ((2 * N : ℕ) : ℝ) < Real.log ((((2 * u) ^ (k + 1) : ℕ)) : ℝ) :=
        Real.log_lt_log (by positivity) (by exact_mod_cast h4)
      have e3 : Real.log (((2 * u : ℕ)) : ℝ) = Real.log 2 + Real.log u := by
        push_cast
        rw [Real.log_mul (by norm_num) (by positivity)]
      rw [e1, Nat.cast_pow, Real.log_pow, e3] at h5
      push_cast at h5
      linarith
    have e2 : 1 / ((k : ℝ) + 1) * Real.log N = Real.log N / ((k : ℝ) + 1) := by ring
    rw [e2, abs_le]
    have h3 : Real.log u ≤ (Real.log 2 + Real.log N) / ((k : ℝ) + 1) := by
      rw [le_div_iff₀ hκ]; linarith
    have h4 : (Real.log 2 + Real.log N) / ((k : ℝ) + 1) < Real.log 2 + Real.log u := by
      rw [div_lt_iff₀ hκ]; linarith
    have h5 : (Real.log 2 + Real.log N) / ((k : ℝ) + 1) =
        Real.log 2 / ((k : ℝ) + 1) + Real.log N / ((k : ℝ) + 1) := add_div _ _ _
    have h6 : Real.log 2 / ((k : ℝ) + 1) ≤ Real.log 2 :=
      div_le_self hL2 (by linarith [Nat.cast_nonneg (α := ℝ) k])
    have h7 : 0 ≤ Real.log 2 / ((k : ℝ) + 1) := by positivity
    constructor <;> linarith
  · -- log v
    have hvR : (2 : ℝ) ≤ v := by exact_mod_cast hv2'
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hκ : (0 : ℝ) < (k : ℝ) := by linarith
    have hL2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hUR : (1 : ℝ) ≤ U := by exact_mod_cast hU
    have hL2U : 0 ≤ Real.log (2 * (U : ℝ)) := Real.log_nonneg (by linarith)
    have hq1 : 1 ≤ N / U := by
      rw [Nat.le_div_iff_mul_le (by omega)]; omega
    have hqN : N / U ≤ N := Nat.div_le_self _ _
    have hq2 : N ≤ 2 * U * (N / U) := by
      have h1 : N < U * (N / U + 1) := Nat.lt_mul_div_succ N (by omega)
      have h2 : U * (N / U + 1) ≤ U * (2 * (N / U)) := Nat.mul_le_mul_left _ (by omega)
      have h3 : U * (2 * (N / U)) = 2 * U * (N / U) := by ring
      omega
    have h1 : (k : ℝ) * Real.log v ≤ Real.log N := by
      have : Real.log (((v ^ k : ℕ)) : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast le_trans hv1 hqN)
      rw [Nat.cast_pow, Real.log_pow] at this
      exact this
    have h2 : Real.log N - Real.log (2 * (U : ℝ)) < (k : ℝ) * (Real.log 2 + Real.log v) := by
      have h3 : (v + 1) ^ k ≤ (2 * v) ^ k := Nat.pow_le_pow_left (by omega) _
      have h4 : N / U < (2 * v) ^ k := lt_of_lt_of_le hv2 h3
      have h5 : Real.log ((N / U : ℕ) : ℝ) < Real.log ((((2 * v) ^ k : ℕ)) : ℝ) :=
        Real.log_lt_log (by exact_mod_cast hq1) (by exact_mod_cast h4)
      have e3 : Real.log (((2 * v : ℕ)) : ℝ) = Real.log 2 + Real.log v := by
        push_cast
        rw [Real.log_mul (by norm_num) (by positivity)]
      rw [Nat.cast_pow, Real.log_pow, e3] at h5
      have h6 : Real.log (N : ℝ) ≤ Real.log (2 * (U : ℝ)) + Real.log ((N / U : ℕ) : ℝ) := by
        rw [← Real.log_mul (by positivity) (by exact_mod_cast (by omega : N / U ≠ 0))]
        apply Real.log_le_log (by positivity)
        exact_mod_cast hq2
      linarith
    have e2 : 1 / (k : ℝ) * Real.log N = Real.log N / (k : ℝ) := by ring
    rw [e2, abs_le]
    have h3 : Real.log v ≤ Real.log N / (k : ℝ) := by
      rw [le_div_iff₀ hκ]; linarith
    have h4 : (Real.log N - Real.log (2 * (U : ℝ))) / (k : ℝ) < Real.log 2 + Real.log v := by
      rw [div_lt_iff₀ hκ]; linarith
    have h5 : (Real.log N - Real.log (2 * (U : ℝ))) / (k : ℝ) =
        Real.log N / (k : ℝ) - Real.log (2 * (U : ℝ)) / (k : ℝ) := sub_div _ _ _
    have h6 : Real.log (2 * (U : ℝ)) / (k : ℝ) ≤ Real.log (2 * (U : ℝ)) := div_le_self hL2U hkR
    constructor <;> linarith

theorem Sk_tendsto (k U : ℕ) (hk : 1 ≤ k) (hU : 1 ≤ U) :
    Tendsto (fun N : ℕ => ∑ p ∈ (Finset.Ioc (Nat.nthRoot (k + 1) (2 * N))
        (Nat.nthRoot k (N / U))).filter Nat.Prime, (1 : ℝ) / p)
      atTop (𝓝 (Real.log ((k : ℝ) + 1) - Real.log k)) := by
  have hx : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hN0 : ∀ᶠ N : ℕ in atTop, (2 * U) ^ (k + 1) ≤ N := eventually_ge_atTop _
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hLL : Tendsto (fun N : ℕ => Real.log (Real.log (Nat.nthRoot k (N / U))) -
      Real.log (Real.log (Nat.nthRoot (k + 1) (2 * N)))) atTop
      (𝓝 (Real.log (1 / (k : ℝ)) - Real.log (1 / ((k : ℝ) + 1)))) :=
    log_ratio_tendsto (fun N : ℕ => Real.log (N : ℝ))
      (fun N : ℕ => Real.log (Nat.nthRoot k (N / U)))
      (fun N : ℕ => Real.log (Nat.nthRoot (k + 1) (2 * N))) _ _
      (Real.log (2 * U) + Real.log 2) (by positivity) (by positivity) hx
      (hN0.mono fun N hN => (root_facts k U hk hU N hN).2.2.2)
      (hN0.mono fun N hN => (root_facts k U hk hU N hN).2.2.1)
  have hconst : Real.log (1 / (k : ℝ)) - Real.log (1 / ((k : ℝ) + 1)) =
      Real.log ((k : ℝ) + 1) - Real.log k := by
    rw [one_div, one_div, Real.log_inv, Real.log_inv]; ring
  have hlogu : Tendsto (fun N : ℕ => Real.log (Nat.nthRoot (k + 1) (2 * N))) atTop atTop := by
    have h1 : Tendsto (fun N : ℕ => 1 / ((k : ℝ) + 1) * Real.log (N : ℝ) +
        (-(Real.log (2 * U) + Real.log 2))) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (hx.const_mul_atTop (by positivity))
    refine tendsto_atTop_mono' atTop ?_ h1
    filter_upwards [hN0] with N hN
    have := (root_facts k U hk hU N hN).2.2.1
    rw [abs_le] at this
    linarith
  have herr : Tendsto (fun N : ℕ => 7 / Real.log (Nat.nthRoot (k + 1) (2 * N))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlogu
  have hmain : Tendsto (fun N : ℕ => (∑ p ∈ (Finset.Ioc (Nat.nthRoot (k + 1) (2 * N))
        (Nat.nthRoot k (N / U))).filter Nat.Prime, (1 : ℝ) / p) -
      (Real.log (Real.log (Nat.nthRoot k (N / U))) -
        Real.log (Real.log (Nat.nthRoot (k + 1) (2 * N))))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ herr
    filter_upwards [hN0] with N hN
    obtain ⟨h2, huv, _⟩ := root_facts k U hk hU N hN
    rw [Real.norm_eq_abs]
    exact mertens2 _ _ h2 huv
  have h := hmain.add hLL
  rw [zero_add, hconst] at h
  refine h.congr (fun N => ?_)
  ring

theorem good_fiber (K U N k : ℕ) (hU : 1 ≤ U) (hN : 1 ≤ N) (hk : 1 ≤ k) (hkK : k < K) :
    (Good K U N).filter (fun p => Nat.log p N = k) =
      (Finset.Ioc (Nat.nthRoot (k + 1) (2 * N)) (Nat.nthRoot k (N / U))).filter Nat.Prime := by
  have hk0 : k ≠ 0 := by omega
  have hk10 : k + 1 ≠ 0 := by omega
  ext p
  unfold Good
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  rw [Nat.nthRoot_lt_iff hk10, Nat.le_nthRoot_iff hk0, Nat.le_div_iff_mul_le (by omega)]
  constructor
  · rintro ⟨⟨⟨hp1, hpN⟩, hpp, hlt, hUp, h2⟩, hlog⟩
    rw [hlog] at hUp h2
    exact ⟨⟨h2, by rw [mul_comm]; exact hUp⟩, hpp⟩
  · rintro ⟨⟨h2, hUp⟩, hpp⟩
    have hpk : p ^ k ≤ N := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hUp
    have hlog : Nat.log p N = k := Nat.log_eq_of_pow_le_of_lt_pow hpk (by omega)
    have hpN : p ≤ N := le_trans (Nat.le_self_pow hk0 p) hpk
    refine ⟨⟨⟨hpp.one_lt.le, hpN⟩, hpp, ?_, ?_, ?_⟩, hlog⟩
    · rw [hlog]; exact hkK
    · rw [hlog, mul_comm]; exact hUp
    · rw [hlog]; exact h2

theorem cN_eq (K U N : ℕ) (hU : 1 ≤ U) (hN : 1 ≤ N) :
    cN K U N = ∑ k ∈ Finset.Ico 1 K, (1 / 2 : ℝ) ^ k *
      ∑ p ∈ (Finset.Ioc (Nat.nthRoot (k + 1) (2 * N)) (Nat.nthRoot k (N / U))).filter Nat.Prime,
        (1 : ℝ) / p := by
  unfold cN
  have hmaps : ∀ p ∈ Good K U N, Nat.log p N ∈ Finset.Ico 1 K := by
    intro p hp
    obtain ⟨hpp, hp1, hpN, hk, _, _⟩ := good_mem hp
    rw [Finset.mem_Ico]
    exact ⟨Nat.log_pos hpp.one_lt hpN, hk⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Ico] at hk
  rw [← good_fiber K U N k hU hN hk.1 hk.2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]
  ring

theorem cN_tendsto (K U : ℕ) (hK : 2 ≤ K) (hU : 2 ≤ U) :
    Tendsto (cN K U) atTop (𝓝 (gam K)) := by
  have h1 : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Ico 1 K, (1 / 2 : ℝ) ^ k *
      ∑ p ∈ (Finset.Ioc (Nat.nthRoot (k + 1) (2 * N)) (Nat.nthRoot k (N / U))).filter Nat.Prime,
        (1 : ℝ) / p) atTop (𝓝 (gam K)) := by
    unfold gam
    apply tendsto_finsetSum
    intro k hk
    rw [Finset.mem_Ico] at hk
    exact (Sk_tendsto k U hk.1 (by omega)).const_mul _
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [cN_eq K U N (by omega) hN]

theorem cnt_le (N p : ℕ) (hp : p.Prime) (hpN : p ≤ N) :
    ((#{n ∈ range N | ¬ p ∣ n.centralBinom} : ℕ) : ℝ) ≤
      2 * N * (2 / 3 : ℝ) ^ Nat.log p N := by
  have hN0 : N ≠ 0 := by have := hp.pos; omega
  have h1 : #{n ∈ range N | ¬ p ∣ n.centralBinom} ≤
      #{n ∈ range N | ∀ i ∈ Icc (1 : ℕ) (Nat.log p N), 2 * (n % p ^ i) < p ^ i} := by
    apply Finset.card_le_card
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, fun i hi => (not_dvd_centralBinom_iff hp).mp hn.2 i (Finset.mem_Icc.mp hi).1⟩
  have h2 := card_digits_range_le p hp.two_le (Nat.log p N) N (Nat.pow_log_le_self p hN0)
  have h3 : ((#{n ∈ range N | ¬ p ∣ n.centralBinom} : ℕ) : ℝ) ≤
      ((#{n ∈ range N | ∀ i ∈ Icc (1 : ℕ) (Nat.log p N), 2 * (n % p ^ i) < p ^ i} : ℕ) : ℝ) := by
    exact_mod_cast h1
  exact le_trans h3 h2

theorem cnt_le' (N p : ℕ) : ((#{n ∈ range N | ¬ p ∣ n.centralBinom} : ℕ) : ℝ) ≤ N := by
  have := Finset.card_filter_le (range N) (fun n => ¬ p ∣ n.centralBinom)
  rw [Finset.card_range] at this
  exact_mod_cast this

theorem log_lower (K U N p : ℕ) (hK : 1 ≤ K) (hU : 1 ≤ U) (hp : 1 ≤ p) (hN : U < N)
    (h : N < U * p ^ K) : (Real.log N - Real.log U) / K ≤ Real.log p := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hUR : (0 : ℝ) < U := by exact_mod_cast hU
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h1 : Real.log (N : ℝ) ≤ Real.log ((U * p ^ K : ℕ) : ℝ) :=
    Real.log_le_log hN0 (by exact_mod_cast h.le)
  push_cast at h1
  rw [Real.log_mul hUR.ne' (by positivity), Real.log_pow] at h1
  rw [div_le_iff₀ hKR]
  linarith

theorem bad_sum_le (K U : ℕ) (hK : 2 ≤ K) (hU : 2 ≤ U) (N : ℕ) (hN : U < N) :
    ∑ n ∈ range N, bN K U N n ≤ N * (72 * (2 / 3 : ℝ) ^ K + 2 * K * rho K U N) := by
  have hN0 : N ≠ 0 := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hUR : (2 : ℝ) ≤ U := by exact_mod_cast hU
  have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg (by linarith)
  have hlog2U : Real.log 2 ≤ Real.log U := Real.log_le_log (by norm_num) hUR
  have hlogNU : 0 < Real.log N - Real.log U := by
    rw [sub_pos]; exact Real.log_lt_log (by linarith) (by exact_mod_cast hN)
  have hz0 : 0 < (Real.log N - Real.log U) / K := by positivity
  have hrho : rho K U N = (Real.log U + 7) / ((Real.log N - Real.log U) / K) := by
    unfold rho; field_simp
  have hrho0 : 0 ≤ rho K U N := by rw [hrho]; positivity
  -- Step 1
  have step1 : ∑ n ∈ range N, bN K U N n ≤
      ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime \ Good K U N,
        ((#{n ∈ range N | ¬ p ∣ n.centralBinom} : ℕ) : ℝ) / p := by
    calc ∑ n ∈ range N, bN K U N n
        ≤ ∑ n ∈ range N, ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime \ Good K U N,
            (if p ∣ n.centralBinom then 0 else (1 : ℝ) / p) := by
          apply Finset.sum_le_sum
          intro n hn
          unfold bN
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · apply Finset.sdiff_subset_sdiff _ (le_refl _)
            apply Finset.filter_subset_filter
            apply Finset.Icc_subset_Icc_right
            exact (Finset.mem_range.mp hn).le
          · intro p _ _
            split_ifs
            · exact le_refl _
            · positivity
      _ = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime \ Good K U N, ∑ n ∈ range N,
            (if p ∣ n.centralBinom then 0 else (1 : ℝ) / p) := Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl
          intro p _
          rw [Finset.card_filter, Nat.cast_sum, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro n _
          split_ifs <;> simp
  -- Step 3
  have step3 : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime \ Good K U N,
      ((#{n ∈ range N | ¬ p ∣ n.centralBinom} : ℕ) : ℝ) / p ≤
      ∑ k ∈ Finset.Icc K N, (if Nat.log p N = k then 2 * N * (2 / 3 : ℝ) ^ k / p else 0) +
      ∑ k ∈ Finset.Ico 1 K, (if Nat.log p N = k ∧ N < U * p ^ k then (N : ℝ) / p else 0) +
      ∑ k ∈ Finset.Ico 1 K, (if Nat.log p N = k ∧ p ^ (k + 1) ≤ 2 * N then (N : ℝ) / p else 0) := by
    intro p hp
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hp1, hpN⟩, hpp⟩, hng⟩ := hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hk1 : 1 ≤ Nat.log p N := Nat.log_pos hpp.one_lt hpN
    have nn1 : ∀ k ∈ Finset.Icc K N,
        0 ≤ (if Nat.log p N = k then 2 * N * (2 / 3 : ℝ) ^ k / p else 0) := by
      intro k _; split_ifs <;> positivity
    have nn2 : ∀ k ∈ Finset.Ico 1 K,
        0 ≤ (if Nat.log p N = k ∧ N < U * p ^ k then (N : ℝ) / p else 0) := by
      intro k _; split_ifs <;> positivity
    have nn3 : ∀ k ∈ Finset.Ico 1 K,
        0 ≤ (if Nat.log p N = k ∧ p ^ (k + 1) ≤ 2 * N then (N : ℝ) / p else 0) := by
      intro k _; split_ifs <;> positivity
    have s1 := Finset.sum_nonneg nn1
    have s2 := Finset.sum_nonneg nn2
    have s3 := Finset.sum_nonneg nn3
    rcases Nat.lt_or_ge (Nat.log p N) K with hlt | hge
    · have hbd : N < U * p ^ Nat.log p N ∨ p ^ (Nat.log p N + 1) ≤ 2 * N := by
        by_contra hcon
        rw [not_or, not_lt, not_le] at hcon
        apply hng
        unfold Good
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hp1, hpN⟩, hpp, hlt, hcon.1, hcon.2⟩
      have hc : ((#{n ∈ range N | ¬ p ∣ n.centralBinom} : ℕ) : ℝ) / p ≤ (N : ℝ) / p :=
        div_le_div_of_nonneg_right (cnt_le' N p) hp0.le
      have hmem : Nat.log p N ∈ Finset.Ico 1 K := Finset.mem_Ico.mpr ⟨hk1, hlt⟩
      rcases hbd with hb | hb
      · have h := Finset.single_le_sum nn2 hmem
        rw [if_pos ⟨rfl, hb⟩] at h
        linarith
      · have h := Finset.single_le_sum nn3 hmem
        rw [if_pos ⟨rfl, hb⟩] at h
        linarith
    · have hmem : Nat.log p N ∈ Finset.Icc K N :=
        Finset.mem_Icc.mpr ⟨hge, Nat.log_le_self _ _⟩
      have h := Finset.single_le_sum nn1 hmem
      rw [if_pos rfl] at h
      have hc : ((#{n ∈ range N | ¬ p ∣ n.centralBinom} : ℕ) : ℝ) / p ≤
          2 * N * (2 / 3 : ℝ) ^ Nat.log p N / p :=
        div_le_div_of_nonneg_right (cnt_le N p hpp hpN) hp0.le
      linarith
  -- the three sums
  have sumT1 : ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ∑ k ∈ Finset.Icc K N,
      (if Nat.log p N = k then 2 * N * (2 / 3 : ℝ) ^ k / p else 0) ≤
        N * (72 * (2 / 3 : ℝ) ^ K) := by
    rw [Finset.sum_comm]
    calc ∑ k ∈ Finset.Icc K N, ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          (if Nat.log p N = k then 2 * N * (2 / 3 : ℝ) ^ k / p else 0)
        ≤ ∑ k ∈ Finset.Icc K N, 24 * N * (2 / 3 : ℝ) ^ k := by
          apply Finset.sum_le_sum
          intro k hk
          have hk1 : 1 ≤ k := by have := (Finset.mem_Icc.mp hk).1; omega
          rw [← Finset.sum_filter, Finset.filter_filter]
          have h := sum_inv_class N k hk1
          calc ∑ p ∈ (Finset.Icc 1 N).filter (fun p => p.Prime ∧ Nat.log p N = k),
                2 * N * (2 / 3 : ℝ) ^ k / p
              = 2 * N * (2 / 3 : ℝ) ^ k *
                ∑ p ∈ (Finset.Icc 1 N).filter (fun p => p.Prime ∧ Nat.log p N = k), (1 : ℝ) / p := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro p _
                ring
            _ ≤ 2 * N * (2 / 3 : ℝ) ^ k * 12 := mul_le_mul_of_nonneg_left h (by positivity)
            _ = 24 * N * (2 / 3 : ℝ) ^ k := by ring
      _ = 24 * N * ∑ k ∈ Finset.Ico K (N + 1), (2 / 3 : ℝ) ^ k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr _ (fun _ _ => rfl)
          ext k
          simp only [Finset.mem_Icc, Finset.mem_Ico]
          omega
      _ ≤ 24 * N * ((2 / 3 : ℝ) ^ K / (1 - 2 / 3)) :=
          mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num))
            (by positivity)
      _ = N * (72 * (2 / 3 : ℝ) ^ K) := by ring
  have sumT2 : ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ∑ k ∈ Finset.Ico 1 K,
      (if Nat.log p N = k ∧ N < U * p ^ k then (N : ℝ) / p else 0) ≤ N * (K * rho K U N) := by
    rw [Finset.sum_comm]
    calc ∑ k ∈ Finset.Ico 1 K, ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          (if Nat.log p N = k ∧ N < U * p ^ k then (N : ℝ) / p else 0)
        ≤ ∑ k ∈ Finset.Ico 1 K, (N : ℝ) * rho K U N := by
          apply Finset.sum_le_sum
          intro k hk
          rw [Finset.mem_Ico] at hk
          rw [← Finset.sum_filter]
          have hcl := sum_inv_cluster
            (((Finset.Icc 1 N).filter Nat.Prime).filter (fun p => Nat.log p N = k ∧ N < U * p ^ k))
            (fun p hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2)
            U k ((Real.log N - Real.log U) / K) (by omega) hk.1 hz0
            (fun p hp => by
              rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hp
              obtain ⟨⟨⟨hp1, _⟩, hpp⟩, hlog, hlt⟩ := hp
              apply log_lower K U N p (by omega) (by omega) hp1 hN
              calc N < U * p ^ k := hlt
                _ ≤ U * p ^ K := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp1 hk.2.le))
            (fun p hp q hq => by
              rw [Finset.mem_filter] at hp hq
              calc p ^ k ≤ N := by rw [← hp.2.1]; exact Nat.pow_log_le_self p hN0
                _ < U * q ^ k := hq.2.2)
          calc ∑ p ∈ ((Finset.Icc 1 N).filter Nat.Prime).filter
                (fun p => Nat.log p N = k ∧ N < U * p ^ k), (N : ℝ) / p
              = N * ∑ p ∈ ((Finset.Icc 1 N).filter Nat.Prime).filter
                (fun p => Nat.log p N = k ∧ N < U * p ^ k), (1 : ℝ) / p := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro p _
                ring
            _ ≤ N * rho K U N := by
                rw [hrho]; exact mul_le_mul_of_nonneg_left hcl hNR.le
      _ = ((K - 1 : ℕ) : ℝ) * ((N : ℝ) * rho K U N) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ (K : ℝ) * ((N : ℝ) * rho K U N) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast Nat.sub_le K 1
      _ = N * (K * rho K U N) := by ring
  have sumT3 : ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ∑ k ∈ Finset.Ico 1 K,
      (if Nat.log p N = k ∧ p ^ (k + 1) ≤ 2 * N then (N : ℝ) / p else 0) ≤
        N * (K * rho K U N) := by
    rw [Finset.sum_comm]
    calc ∑ k ∈ Finset.Ico 1 K, ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          (if Nat.log p N = k ∧ p ^ (k + 1) ≤ 2 * N then (N : ℝ) / p else 0)
        ≤ ∑ k ∈ Finset.Ico 1 K, (N : ℝ) * rho K U N := by
          apply Finset.sum_le_sum
          intro k hk
          rw [Finset.mem_Ico] at hk
          rw [← Finset.sum_filter]
          have hcl := sum_inv_cluster
            (((Finset.Icc 1 N).filter Nat.Prime).filter
              (fun p => Nat.log p N = k ∧ p ^ (k + 1) ≤ 2 * N))
            (fun p hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2)
            2 (k + 1) ((Real.log N - Real.log U) / K) (by omega) (by omega) hz0
            (fun p hp => by
              rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hp
              obtain ⟨⟨⟨hp1, _⟩, hpp⟩, hlog, hle⟩ := hp
              apply log_lower K U N p (by omega) (by omega) hp1 hN
              have h1 : N < p ^ (k + 1) := by
                rw [← hlog]; exact Nat.lt_pow_succ_log_self hpp.one_lt N
              have h2 : p ^ (k + 1) ≤ p ^ K := Nat.pow_le_pow_right hp1 hk.2
              have h3 : p ^ K ≤ U * p ^ K := Nat.le_mul_of_pos_left _ (by omega)
              omega)
            (fun p hp q hq => by
              rw [Finset.mem_filter, Finset.mem_filter] at hp hq
              have h1 : N < q ^ (k + 1) := by
                rw [← hq.2.1]; exact Nat.lt_pow_succ_log_self hq.1.2.one_lt N
              have h2 := hp.2.2
              omega)
          calc ∑ p ∈ ((Finset.Icc 1 N).filter Nat.Prime).filter
                (fun p => Nat.log p N = k ∧ p ^ (k + 1) ≤ 2 * N), (N : ℝ) / p
              = N * ∑ p ∈ ((Finset.Icc 1 N).filter Nat.Prime).filter
                (fun p => Nat.log p N = k ∧ p ^ (k + 1) ≤ 2 * N), (1 : ℝ) / p := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro p _
                ring
            _ ≤ N * rho K U N := by
                rw [hrho]
                apply mul_le_mul_of_nonneg_left _ hNR.le
                refine le_trans hcl ?_
                apply div_le_div_of_nonneg_right _ hz0.le
                push_cast
                linarith
      _ = ((K - 1 : ℕ) : ℝ) * ((N : ℝ) * rho K U N) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ (K : ℝ) * ((N : ℝ) * rho K U N) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast Nat.sub_le K 1
      _ = N * (K * rho K U N) := by ring
  -- assemble
  have hnn : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      0 ≤ ∑ k ∈ Finset.Icc K N, (if Nat.log p N = k then 2 * N * (2 / 3 : ℝ) ^ k / p else 0) +
      ∑ k ∈ Finset.Ico 1 K, (if Nat.log p N = k ∧ N < U * p ^ k then (N : ℝ) / p else 0) +
      ∑ k ∈ Finset.Ico 1 K, (if Nat.log p N = k ∧ p ^ (k + 1) ≤ 2 * N then (N : ℝ) / p else 0) := by
    intro p _
    apply add_nonneg (add_nonneg _ _) _
    · apply Finset.sum_nonneg; intro k _; split_ifs <;> positivity
    · apply Finset.sum_nonneg; intro k _; split_ifs <;> positivity
    · apply Finset.sum_nonneg; intro k _; split_ifs <;> positivity
  calc ∑ n ∈ range N, bN K U N n
      ≤ ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime \ Good K U N,
        ((#{n ∈ range N | ¬ p ∣ n.centralBinom} : ℕ) : ℝ) / p := step1
    _ ≤ ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime \ Good K U N,
        (∑ k ∈ Finset.Icc K N, (if Nat.log p N = k then 2 * N * (2 / 3 : ℝ) ^ k / p else 0) +
        ∑ k ∈ Finset.Ico 1 K, (if Nat.log p N = k ∧ N < U * p ^ k then (N : ℝ) / p else 0) +
        ∑ k ∈ Finset.Ico 1 K, (if Nat.log p N = k ∧ p ^ (k + 1) ≤ 2 * N then (N : ℝ) / p else 0)) :=
        Finset.sum_le_sum step3
    _ ≤ ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (∑ k ∈ Finset.Icc K N, (if Nat.log p N = k then 2 * N * (2 / 3 : ℝ) ^ k / p else 0) +
        ∑ k ∈ Finset.Ico 1 K, (if Nat.log p N = k ∧ N < U * p ^ k then (N : ℝ) / p else 0) +
        ∑ k ∈ Finset.Ico 1 K, (if Nat.log p N = k ∧ p ^ (k + 1) ≤ 2 * N then (N : ℝ) / p else 0)) :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun p hp _ => hnn p hp)
    _ ≤ N * (72 * (2 / 3 : ℝ) ^ K + 2 * K * rho K U N) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        linarith

theorem mods_card (p k : ℕ) (hp : 2 ≤ p) : #(mods p k) = k := by
  unfold mods
  rw [Finset.card_image_of_injective _ (Nat.pow_right_injective hp), Nat.card_Icc]
  simp

theorem good_two_U {K U N p : ℕ} (hp : p ∈ Good K U N) : 2 * U < p := by
  obtain ⟨hpp, hp1, hpN, hk, hU, h2⟩ := good_mem hp
  have h3 : 2 * U * p ^ Nat.log p N < p * p ^ Nat.log p N := by
    calc 2 * U * p ^ Nat.log p N = 2 * (U * p ^ Nat.log p N) := by ring
      _ ≤ 2 * N := by omega
      _ < p ^ (Nat.log p N + 1) := h2
      _ = p * p ^ Nat.log p N := pow_succ' _ _
  exact Nat.lt_of_mul_lt_mul_right h3

theorem mods_props {K U N p : ℕ} (hp : p ∈ Good K U N) :
    (∀ m ∈ mods p (Nat.log p N), (U : ℝ) ≤ m) ∧
    (∀ x ∈ mods p (Nat.log p N), ∀ y ∈ mods p (Nat.log p N), x < y → (U : ℝ) * x ≤ y) ∧
    (∀ m ∈ mods p (Nat.log p N), (U : ℝ) * m ≤ N) := by
  obtain ⟨hpp, hp1, hpN, hk, hU, h2⟩ := good_mem hp
  have h2U := good_two_U hp
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    unfold mods at hm
    rw [Finset.mem_image] at hm
    obtain ⟨i, hi, rfl⟩ := hm
    rw [Finset.mem_Icc] at hi
    have : U ≤ p ^ i := le_trans (by omega) (Nat.le_self_pow (by omega) p)
    exact_mod_cast this
  · intro x hx y hy hxy
    unfold mods at hx hy
    rw [Finset.mem_image] at hx hy
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, hj, rfl⟩ := hy
    have hij : i < j := (Nat.pow_lt_pow_iff_right hpp.one_lt).mp hxy
    have : U * p ^ i ≤ p ^ j := by
      calc U * p ^ i ≤ p * p ^ i := Nat.mul_le_mul_right _ (by omega)
        _ = p ^ (i + 1) := (pow_succ' _ _).symm
        _ ≤ p ^ j := Nat.pow_le_pow_right hpp.pos hij
    exact_mod_cast this
  · intro m hm
    unfold mods at hm
    rw [Finset.mem_image] at hm
    obtain ⟨i, hi, rfl⟩ := hm
    rw [Finset.mem_Icc] at hi
    have : U * p ^ i ≤ N :=
      le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hpp.pos hi.2)) hU
    exact_mod_cast this

theorem count_sep (U N : ℕ) (hU : 2 ≤ U) (M : Finset ℕ)
    (h1 : ∀ m ∈ M, (U : ℝ) ≤ m) (h2 : ∀ x ∈ M, ∀ y ∈ M, x < y → (U : ℝ) * x ≤ y)
    (h3 : ∀ m ∈ M, (U : ℝ) * m ≤ N) :
    |∑ n ∈ range N, (if ∀ m ∈ M, 2 * (n % m) < m then (1 : ℝ) else 0) -
      N * (1 / 2 : ℝ) ^ #M| ≤ 4 ^ #M * N / U := by
  have h := card_sep (U : ℝ) (by exact_mod_cast hU) M h1 h2 (N : ℝ) h3 (Nat.cast_nonneg N) 0 N
    (by simp)
  rw [Nat.sub_zero] at h
  rw [Finset.sum_boole, Finset.range_eq_Ico, one_div, inv_pow, ← div_eq_mul_inv]
  exact h

theorem Y_sum (K U N p : ℕ) (hU : 2 ≤ U) (hp : p ∈ Good K U N) :
    |∑ n ∈ range N, Y N p n - N * (1 / 2 : ℝ) ^ Nat.log p N| ≤ 4 ^ K * N / U := by
  obtain ⟨hpp, hp1, hpN, hk, _, _⟩ := good_mem hp
  obtain ⟨h1, h2, h3⟩ := mods_props hp
  have h := count_sep U N hU (mods p (Nat.log p N)) h1 h2 h3
  rw [mods_card p _ hpp.two_le] at h
  unfold Y
  refine le_trans h ?_
  have hUR : (0 : ℝ) < U := by exact_mod_cast (by omega : 0 < U)
  have h4 : (4 : ℝ) ^ Nat.log p N ≤ 4 ^ K := pow_le_pow_right₀ (by norm_num) hk.le
  apply div_le_div_of_nonneg_right _ hUR.le
  exact mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg N)

theorem YY_sum (K U N p q : ℕ) (hU : 2 ≤ U) (hp : p ∈ Good K U N) (hq : q ∈ Good K U N)
    (hnr : ∀ i ∈ Finset.Icc 1 K, ∀ j ∈ Finset.Icc 1 K,
      ¬ (p ^ i ≤ q ^ j ∧ q ^ j < U * p ^ i) ∧ ¬ (q ^ j ≤ p ^ i ∧ p ^ i < U * q ^ j)) :
    |∑ n ∈ range N, Y N p n * Y N q n -
      N * ((1 / 2 : ℝ) ^ Nat.log p N * (1 / 2 : ℝ) ^ Nat.log q N)| ≤ 16 ^ K * N / U := by
  obtain ⟨hpp, hp1, hpN, hkp, hUp, h2p⟩ := good_mem hp
  obtain ⟨hqp, hq1, hqN, hkq, hUq, h2q⟩ := good_mem hq
  obtain ⟨a1, a2, a3⟩ := mods_props hp
  obtain ⟨b1, b2, b3⟩ := mods_props hq
  have cross : ∀ x ∈ mods p (Nat.log p N), ∀ y ∈ mods q (Nat.log q N),
      x ≠ y ∧ (x < y → (U : ℝ) * x ≤ y) ∧ (y < x → (U : ℝ) * y ≤ x) := by
    intro x hx y hy
    unfold mods at hx hy
    rw [Finset.mem_image] at hx hy
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, hj, rfl⟩ := hy
    rw [Finset.mem_Icc] at hi hj
    obtain ⟨n1, n2⟩ := hnr i (Finset.mem_Icc.mpr ⟨hi.1, by omega⟩) j
      (Finset.mem_Icc.mpr ⟨hj.1, by omega⟩)
    have hpi : 0 < p ^ i := pos_of_ne_zero (pow_ne_zero _ (by omega))
    refine ⟨?_, ?_, ?_⟩
    · intro heq
      apply n1
      refine ⟨heq.le, ?_⟩
      rw [← heq]
      calc p ^ i = 1 * p ^ i := (one_mul _).symm
        _ < U * p ^ i := Nat.mul_lt_mul_of_pos_right (by omega) hpi
    · intro hlt
      have : U * p ^ i ≤ q ^ j := by
        by_contra hcon
        exact n1 ⟨hlt.le, not_le.mp hcon⟩
      exact_mod_cast this
    · intro hlt
      have : U * q ^ j ≤ p ^ i := by
        by_contra hcon
        exact n2 ⟨hlt.le, not_le.mp hcon⟩
      exact_mod_cast this
  have hdisj : Disjoint (mods p (Nat.log p N)) (mods q (Nat.log q N)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact (cross x hx x hy).1 rfl
  have h := count_sep U N hU (mods p (Nat.log p N) ∪ mods q (Nat.log q N))
    (fun m hm => by
      rcases Finset.mem_union.mp hm with h | h
      · exact a1 m h
      · exact b1 m h)
    (fun x hx y hy hxy => by
      rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
      · exact a2 x hx y hy hxy
      · exact (cross x hx y hy).2.1 hxy
      · exact (cross y hy x hx).2.2 hxy
      · exact b2 x hx y hy hxy)
    (fun m hm => by
      rcases Finset.mem_union.mp hm with h | h
      · exact a3 m h
      · exact b3 m h)
  rw [Finset.card_union_of_disjoint hdisj, mods_card p _ hpp.two_le, mods_card q _ hqp.two_le,
    pow_add, pow_add] at h
  have hYY : ∑ n ∈ range N, Y N p n * Y N q n = ∑ n ∈ range N,
      (if ∀ m ∈ mods p (Nat.log p N) ∪ mods q (Nat.log q N), 2 * (n % m) < m
        then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro n _
    unfold Y
    by_cases hA : ∀ m ∈ mods p (Nat.log p N), 2 * (n % m) < m
    · by_cases hB : ∀ m ∈ mods q (Nat.log q N), 2 * (n % m) < m
      · rw [if_pos hA, if_pos hB, if_pos (Finset.forall_mem_union.mpr ⟨hA, hB⟩)]
        norm_num
      · rw [if_pos hA, if_neg hB, if_neg (fun h => hB (Finset.forall_mem_union.mp h).2)]
        norm_num
    · rw [if_neg hA, if_neg (fun h => hA (Finset.forall_mem_union.mp h).1)]
      norm_num
  rw [hYY]
  refine le_trans h ?_
  have hUR : (0 : ℝ) < U := by exact_mod_cast (by omega : 0 < U)
  have h4 : (4 : ℝ) ^ Nat.log p N ≤ 4 ^ K := pow_le_pow_right₀ (by norm_num) hkp.le
  have h5 : (4 : ℝ) ^ Nat.log q N ≤ 4 ^ K := pow_le_pow_right₀ (by norm_num) hkq.le
  have h6 : (16 : ℝ) ^ K = 4 ^ K * 4 ^ K := by rw [← mul_pow]; norm_num
  apply div_le_div_of_nonneg_right _ hUR.le
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N)
  rw [h6]
  exact mul_le_mul h4 h5 (by positivity) (by positivity)

theorem T_le (K U N p q : ℕ) (hU : 2 ≤ U) (hp : p ∈ Good K U N) (hq : q ∈ Good K U N) :
    ∑ n ∈ range N, (Y N p n - (1 / 2 : ℝ) ^ Nat.log p N) * (Y N q n - (1 / 2 : ℝ) ^ Nat.log q N) ≤
      N * (3 * 16 ^ K / U + ∑ i ∈ Finset.Icc 1 K, ∑ j ∈ Finset.Icc 1 K,
        ((if p ^ i ≤ q ^ j ∧ q ^ j < U * p ^ i then (1 : ℝ) else 0) +
         (if q ^ j ≤ p ^ i ∧ p ^ i < U * q ^ j then (1 : ℝ) else 0))) := by
  have hUR : (0 : ℝ) < U := by exact_mod_cast (by omega : 0 < U)
  have hμp0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Nat.log p N := by positivity
  have hμp1 : (1 / 2 : ℝ) ^ Nat.log p N ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hμq0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Nat.log q N := by positivity
  have hμq1 : (1 / 2 : ℝ) ^ Nat.log q N ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hYp : ∀ n, 0 ≤ Y N p n ∧ Y N p n ≤ 1 := by
    intro n; unfold Y; split_ifs <;> norm_num
  have hYq : ∀ n, 0 ≤ Y N q n ∧ Y N q n ≤ 1 := by
    intro n; unfold Y; split_ifs <;> norm_num
  have hterm : ∀ i ∈ Finset.Icc 1 K, ∀ j ∈ Finset.Icc 1 K,
      (0 : ℝ) ≤ (if p ^ i ≤ q ^ j ∧ q ^ j < U * p ^ i then (1 : ℝ) else 0) +
         (if q ^ j ≤ p ^ i ∧ p ^ i < U * q ^ j then (1 : ℝ) else 0) := by
    intro i _ j _
    split_ifs <;> norm_num
  have hinner : ∀ i ∈ Finset.Icc 1 K, (0 : ℝ) ≤ ∑ j ∈ Finset.Icc 1 K,
      ((if p ^ i ≤ q ^ j ∧ q ^ j < U * p ^ i then (1 : ℝ) else 0) +
         (if q ^ j ≤ p ^ i ∧ p ^ i < U * q ^ j then (1 : ℝ) else 0)) :=
    fun i hi => Finset.sum_nonneg (hterm i hi)
  have hr0 := Finset.sum_nonneg hinner
  have h16 : (0 : ℝ) ≤ 16 ^ K * N / U := by positivity
  by_cases hres : ∀ i ∈ Finset.Icc 1 K, ∀ j ∈ Finset.Icc 1 K,
      ¬ (p ^ i ≤ q ^ j ∧ q ^ j < U * p ^ i) ∧ ¬ (q ^ j ≤ p ^ i ∧ p ^ i < U * q ^ j)
  · have e1 := YY_sum K U N p q hU hp hq hres
    have e2 := Y_sum K U N p hU hp
    have e3 := Y_sum K U N q hU hq
    have expand : ∑ n ∈ range N,
        (Y N p n - (1 / 2 : ℝ) ^ Nat.log p N) * (Y N q n - (1 / 2 : ℝ) ^ Nat.log q N) =
        (∑ n ∈ range N, Y N p n * Y N q n -
          N * ((1 / 2 : ℝ) ^ Nat.log p N * (1 / 2 : ℝ) ^ Nat.log q N)) -
        (1 / 2 : ℝ) ^ Nat.log q N * (∑ n ∈ range N, Y N p n - N * (1 / 2 : ℝ) ^ Nat.log p N) -
        (1 / 2 : ℝ) ^ Nat.log p N * (∑ n ∈ range N, Y N q n - N * (1 / 2 : ℝ) ^ Nat.log q N) := by
      have : ∀ n ∈ range N,
          (Y N p n - (1 / 2 : ℝ) ^ Nat.log p N) * (Y N q n - (1 / 2 : ℝ) ^ Nat.log q N) =
          Y N p n * Y N q n - (1 / 2 : ℝ) ^ Nat.log q N * Y N p n -
            (1 / 2 : ℝ) ^ Nat.log p N * Y N q n +
            (1 / 2 : ℝ) ^ Nat.log p N * (1 / 2 : ℝ) ^ Nat.log q N := by
        intro n _; ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      ring
    rw [expand]
    have h4 : (4 : ℝ) ^ K * N / U ≤ 16 ^ K * N / U := by
      apply div_le_div_of_nonneg_right _ hUR.le
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N)
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) K
    rw [abs_le] at e1 e2 e3
    have b2 : -(16 ^ K * N / U) ≤
        (1 / 2 : ℝ) ^ Nat.log q N * (∑ n ∈ range N, Y N p n - N * (1 / 2 : ℝ) ^ Nat.log p N) := by
      nlinarith
    have b3 : -(16 ^ K * N / U) ≤
        (1 / 2 : ℝ) ^ Nat.log p N * (∑ n ∈ range N, Y N q n - N * (1 / 2 : ℝ) ^ Nat.log q N) := by
      nlinarith
    have hNr : (0 : ℝ) ≤ N * ∑ i ∈ Finset.Icc 1 K, ∑ j ∈ Finset.Icc 1 K,
        ((if p ^ i ≤ q ^ j ∧ q ^ j < U * p ^ i then (1 : ℝ) else 0) +
         (if q ^ j ≤ p ^ i ∧ p ^ i < U * q ^ j then (1 : ℝ) else 0)) :=
      mul_nonneg (Nat.cast_nonneg N) hr0
    have e5 : (N : ℝ) * (3 * 16 ^ K / U) = 3 * (16 ^ K * N / U) := by ring
    rw [mul_add, e5]
    linarith
  · have hex : ∃ i ∈ Finset.Icc 1 K, ∃ j ∈ Finset.Icc 1 K,
        (p ^ i ≤ q ^ j ∧ q ^ j < U * p ^ i) ∨ (q ^ j ≤ p ^ i ∧ p ^ i < U * q ^ j) := by
      by_contra hcon
      apply hres
      intro i hi j hj
      exact ⟨fun h => hcon ⟨i, hi, j, hj, Or.inl h⟩, fun h => hcon ⟨i, hi, j, hj, Or.inr h⟩⟩
    obtain ⟨i, hi, j, hj, hor⟩ := hex
    have hge1 : (1 : ℝ) ≤ ∑ i ∈ Finset.Icc 1 K, ∑ j ∈ Finset.Icc 1 K,
        ((if p ^ i ≤ q ^ j ∧ q ^ j < U * p ^ i then (1 : ℝ) else 0) +
         (if q ^ j ≤ p ^ i ∧ p ^ i < U * q ^ j then (1 : ℝ) else 0)) := by
      have s1 := Finset.single_le_sum hinner hi
      have s2 := Finset.single_le_sum (hterm i hi) hj
      have s3 : (1 : ℝ) ≤ (if p ^ i ≤ q ^ j ∧ q ^ j < U * p ^ i then (1 : ℝ) else 0) +
         (if q ^ j ≤ p ^ i ∧ p ^ i < U * q ^ j then (1 : ℝ) else 0) := by
        rcases hor with h | h
        · rw [if_pos h]; split_ifs <;> norm_num
        · rw [if_pos h]; split_ifs <;> norm_num
      linarith
    have htriv : ∑ n ∈ range N,
        (Y N p n - (1 / 2 : ℝ) ^ Nat.log p N) * (Y N q n - (1 / 2 : ℝ) ^ Nat.log q N) ≤ N := by
      calc ∑ n ∈ range N,
            (Y N p n - (1 / 2 : ℝ) ^ Nat.log p N) * (Y N q n - (1 / 2 : ℝ) ^ Nat.log q N)
          ≤ ∑ n ∈ range N, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro n _
            obtain ⟨y1, y2⟩ := hYp n
            obtain ⟨y3, y4⟩ := hYq n
            have ha : |Y N p n - (1 / 2 : ℝ) ^ Nat.log p N| ≤ 1 := by
              rw [abs_le]; constructor <;> linarith
            have hb : |Y N q n - (1 / 2 : ℝ) ^ Nat.log q N| ≤ 1 := by
              rw [abs_le]; constructor <;> linarith
            calc (Y N p n - (1 / 2 : ℝ) ^ Nat.log p N) * (Y N q n - (1 / 2 : ℝ) ^ Nat.log q N)
                ≤ |(Y N p n - (1 / 2 : ℝ) ^ Nat.log p N) *
                    (Y N q n - (1 / 2 : ℝ) ^ Nat.log q N)| := le_abs_self _
              _ = |Y N p n - (1 / 2 : ℝ) ^ Nat.log p N| *
                    |Y N q n - (1 / 2 : ℝ) ^ Nat.log q N| := abs_mul _ _
              _ ≤ 1 * 1 := mul_le_mul ha hb (abs_nonneg _) (by norm_num)
              _ = 1 := by norm_num
        _ = N := by simp
    have h3 : (0 : ℝ) ≤ 3 * 16 ^ K / U := by positivity
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith

theorem good_log_mem {K U N p : ℕ} (hp : p ∈ Good K U N) : Nat.log p N ∈ Finset.Ico 1 K := by
  obtain ⟨hpp, hp1, hpN, hk, _, _⟩ := good_mem hp
  rw [Finset.mem_Ico]
  exact ⟨Nat.log_pos hpp.one_lt hpN, hk⟩

theorem good_sum_le (K U N : ℕ) : ∑ p ∈ Good K U N, (1 : ℝ) / p ≤ 12 * K := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun p hp => good_log_mem hp)]
  calc ∑ k ∈ Finset.Ico 1 K, ∑ p ∈ (Good K U N).filter (fun p => Nat.log p N = k), (1 : ℝ) / p
      ≤ ∑ k ∈ Finset.Ico 1 K, (12 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
          (sum_inv_class N k (Finset.mem_Ico.mp hk).1)
        · intro p hp
          rw [Finset.mem_filter] at hp ⊢
          obtain ⟨hpp, hp1, hpN, _, _, _⟩ := good_mem hp.1
          exact ⟨Finset.mem_Icc.mpr ⟨hp1, hpN⟩, hpp, hp.2⟩
        · intro p _ _
          positivity
    _ = ((K - 1 : ℕ) : ℝ) * 12 := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ 12 * K := by
        have : ((K - 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast Nat.sub_le K 1
        linarith

theorem res_inner_le (K U N p : ℕ) (hK : 2 ≤ K) (hU : 2 ≤ U) (hN : U < N) :
    ∑ q ∈ Good K U N, (∑ i ∈ Finset.Icc 1 K, ∑ j ∈ Finset.Icc 1 K,
        ((if p ^ i ≤ q ^ j ∧ q ^ j < U * p ^ i then (1 : ℝ) else 0) +
         (if q ^ j ≤ p ^ i ∧ p ^ i < U * q ^ j then (1 : ℝ) else 0))) * (1 / q) ≤
      2 * (K : ℝ) ^ 2 * rho K U N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hUR : (2 : ℝ) ≤ U := by exact_mod_cast hU
  have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hlogNU : 0 < Real.log N - Real.log U := by
    rw [sub_pos]; exact Real.log_lt_log (by linarith) (by exact_mod_cast hN)
  have hz0 : 0 < (Real.log N - Real.log U) / K := by positivity
  have hrho : rho K U N = (Real.log U + 7) / ((Real.log N - Real.log U) / K) := by
    unfold rho; field_simp
  have hzq : ∀ q ∈ Good K U N, (Real.log N - Real.log U) / K ≤ Real.log q := by
    intro q hq
    obtain ⟨hqp, hq1, hqN, hkq, hUq, h2q⟩ := good_mem hq
    apply log_lower K U N q (by omega) (by omega) hq1 hN
    have h1 : q ^ (Nat.log q N + 1) ≤ q ^ K := Nat.pow_le_pow_right hq1 hkq
    have h2 : q ^ K ≤ U * q ^ K := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have swap : ∑ q ∈ Good K U N, (∑ i ∈ Finset.Icc 1 K, ∑ j ∈ Finset.Icc 1 K,
        ((if p ^ i ≤ q ^ j ∧ q ^ j < U * p ^ i then (1 : ℝ) else 0) +
         (if q ^ j ≤ p ^ i ∧ p ^ i < U * q ^ j then (1 : ℝ) else 0))) * (1 / q) =
      ∑ i ∈ Finset.Icc 1 K, ∑ j ∈ Finset.Icc 1 K,
        (∑ q ∈ (Good K U N).filter (fun q => p ^ i ≤ q ^ j ∧ q ^ j < U * p ^ i), (1 : ℝ) / q +
         ∑ q ∈ (Good K U N).filter (fun q => q ^ j ≤ p ^ i ∧ p ^ i < U * q ^ j), (1 : ℝ) / q) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> ring
  rw [swap]
  calc ∑ i ∈ Finset.Icc 1 K, ∑ j ∈ Finset.Icc 1 K,
        (∑ q ∈ (Good K U N).filter (fun q => p ^ i ≤ q ^ j ∧ q ^ j < U * p ^ i), (1 : ℝ) / q +
         ∑ q ∈ (Good K U N).filter (fun q => q ^ j ≤ p ^ i ∧ p ^ i < U * q ^ j), (1 : ℝ) / q)
      ≤ ∑ i ∈ Finset.Icc 1 K, ∑ j ∈ Finset.Icc 1 K, (rho K U N + rho K U N) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_Icc] at hj
        apply add_le_add
        · rw [hrho]
          exact sum_inv_cluster _ (fun q hq => (good_mem (Finset.mem_filter.mp hq).1).1)
            U j _ (by omega) hj.1 hz0 (fun q hq => hzq q (Finset.mem_filter.mp hq).1)
            (fun q hq q' hq' => by
              rw [Finset.mem_filter] at hq hq'
              calc q ^ j < U * p ^ i := hq.2.2
                _ ≤ U * q' ^ j := Nat.mul_le_mul_left _ hq'.2.1)
        · rw [hrho]
          exact sum_inv_cluster _ (fun q hq => (good_mem (Finset.mem_filter.mp hq).1).1)
            U j _ (by omega) hj.1 hz0 (fun q hq => hzq q (Finset.mem_filter.mp hq).1)
            (fun q hq q' hq' => by
              rw [Finset.mem_filter] at hq hq'
              calc q ^ j ≤ p ^ i := hq.2.1
                _ < U * q' ^ j := hq'.2.2)
    _ = 2 * (K : ℝ) ^ 2 * rho K U N := by
        simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
        ring

theorem second_moment_le (K U : ℕ) (hK : 2 ≤ K) (hU : 2 ≤ U) (N : ℕ) (hN : U < N) :
    ∑ n ∈ range N, (ft K U N n - cN K U N) ^ 2 ≤
      N * (432 * (K : ℝ) ^ 2 * 16 ^ K / U + 24 * (K : ℝ) ^ 3 * rho K U N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hUR : (2 : ℝ) ≤ U := by exact_mod_cast hU
  have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg (by linarith)
  have hlogNU : 0 < Real.log N - Real.log U := by
    rw [sub_pos]; exact Real.log_lt_log (by linarith) (by exact_mod_cast hN)
  have hrho0 : 0 ≤ rho K U N := by unfold rho; positivity
  have hdiff : ∀ n, ft K U N n - cN K U N =
      ∑ p ∈ Good K U N, (Y N p n - (1 / 2 : ℝ) ^ Nat.log p N) * (1 / p) := by
    intro n
    unfold ft cN
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have expand : ∑ n ∈ range N, (ft K U N n - cN K U N) ^ 2 =
      ∑ p ∈ Good K U N, ∑ q ∈ Good K U N,
        (∑ n ∈ range N, (Y N p n - (1 / 2 : ℝ) ^ Nat.log p N) *
          (Y N q n - (1 / 2 : ℝ) ^ Nat.log q N)) * (1 / p * (1 / q)) := by
    simp only [hdiff, sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [expand]
  have hw := good_sum_le K U N
  have hw0 : 0 ≤ ∑ p ∈ Good K U N, (1 : ℝ) / p :=
    Finset.sum_nonneg (fun p _ => by positivity)
  set W := ∑ p ∈ Good K U N, (1 : ℝ) / p with hW
  calc ∑ p ∈ Good K U N, ∑ q ∈ Good K U N,
        (∑ n ∈ range N, (Y N p n - (1 / 2 : ℝ) ^ Nat.log p N) *
          (Y N q n - (1 / 2 : ℝ) ^ Nat.log q N)) * (1 / p * (1 / q))
      ≤ ∑ p ∈ Good K U N, ∑ q ∈ Good K U N,
        ((N : ℝ) * (3 * 16 ^ K / U) * (1 / p * (1 / q)) +
          (N : ℝ) * (1 / p) * ((∑ i ∈ Finset.Icc 1 K, ∑ j ∈ Finset.Icc 1 K,
        ((if p ^ i ≤ q ^ j ∧ q ^ j < U * p ^ i then (1 : ℝ) else 0) +
         (if q ^ j ≤ p ^ i ∧ p ^ i < U * q ^ j then (1 : ℝ) else 0))) * (1 / q))) := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro q hq
        have hT := T_le K U N p q hU hp hq
        have hpq : (0 : ℝ) ≤ 1 / p * (1 / q) := by positivity
        have := mul_le_mul_of_nonneg_right hT hpq
        refine le_trans this (le_of_eq ?_)
        ring
    _ = (N : ℝ) * (3 * 16 ^ K / U) * (W * W) +
        (N : ℝ) * ∑ p ∈ Good K U N, (1 / p) * ∑ q ∈ Good K U N,
          (∑ i ∈ Finset.Icc 1 K, ∑ j ∈ Finset.Icc 1 K,
        ((if p ^ i ≤ q ^ j ∧ q ^ j < U * p ^ i then (1 : ℝ) else 0) +
         (if q ^ j ≤ p ^ i ∧ p ^ i < U * q ^ j then (1 : ℝ) else 0))) * (1 / q) := by
        rw [hW, Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro q _
        ring
    _ ≤ (N : ℝ) * (3 * 16 ^ K / U) * (12 * K * (12 * K)) +
        (N : ℝ) * ∑ p ∈ Good K U N, (1 / p) * (2 * (K : ℝ) ^ 2 * rho K U N) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hw hw hw0 (by positivity)
        · apply mul_le_mul_of_nonneg_left _ hNR.le
          apply Finset.sum_le_sum
          intro p _
          exact mul_le_mul_of_nonneg_left (res_inner_le K U N p hK hU hN) (by positivity)
    _ = (N : ℝ) * (3 * 16 ^ K / U) * (12 * K * (12 * K)) +
        (N : ℝ) * (W * (2 * (K : ℝ) ^ 2 * rho K U N)) := by
        rw [hW, Finset.sum_mul]
    _ ≤ (N : ℝ) * (3 * 16 ^ K / U) * (12 * K * (12 * K)) +
        (N : ℝ) * (12 * K * (2 * (K : ℝ) ^ 2 * rho K U N)) := by
        apply add_le_add (le_refl _)
        apply mul_le_mul_of_nonneg_left _ hNR.le
        exact mul_le_mul_of_nonneg_right hw (by positivity)
    _ = N * (432 * (K : ℝ) ^ 2 * 16 ^ K / U + 24 * (K : ℝ) ^ 3 * rho K U N) := by ring

theorem markov (s : Finset ℕ) (g : ℕ → ℝ) (hg : ∀ n ∈ s, 0 ≤ g n) (c : ℝ) :
    ((#{n ∈ s | c ≤ g n} : ℕ) : ℝ) * c ≤ ∑ n ∈ s, g n := by
  calc ((#{n ∈ s | c ≤ g n} : ℕ) : ℝ) * c = ∑ n ∈ s.filter (fun n => c ≤ g n), c := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ s.filter (fun n => c ≤ g n), g n :=
        Finset.sum_le_sum (fun n hn => (Finset.mem_filter.mp hn).2)
    _ ≤ ∑ n ∈ s, g n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun n hn _ => hg n hn)

theorem density_one_of_exceptional (S : Set ℕ)
    (h : ∀ δ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ((Set.Iio N \ S).ncard : ℝ) ≤ δ * N) :
    S.HasDensity 1 := by
  unfold Set.HasDensity
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (h (δ / 2) (by positivity))
  refine ⟨max N₀ 1, fun b hb => ?_⟩
  have hb0 : N₀ ≤ b := le_trans (le_max_left _ _) hb
  have hb1 : 1 ≤ b := le_trans (le_max_right _ _) hb
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb1
  have h1 := hN₀ b hb0
  have h2 : (Set.Iio b ∩ S).ncard + (Set.Iio b \ S).ncard = b := by
    rw [Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (Set.finite_Iio b)]
    simp
  have h3 : ((Set.Iio b ∩ S).ncard : ℝ) = b - ((Set.Iio b \ S).ncard : ℝ) := by
    have : (((Set.Iio b ∩ S).ncard + (Set.Iio b \ S).ncard : ℕ) : ℝ) = b := by exact_mod_cast h2
    push_cast at this
    linarith
  have h4 : S.partialDensity Set.univ b = 1 - ((Set.Iio b \ S).ncard : ℝ) / b := by
    unfold Set.partialDensity
    rw [Set.inter_univ, Set.univ_inter, Set.inter_comm, h3]
    have : (Set.Iio b : Set ℕ).ncard = b := by simp
    rw [this]
    field_simp
  rw [h4, Real.dist_eq]
  have h5 : (0 : ℝ) ≤ ((Set.Iio b \ S).ncard : ℝ) / b := by positivity
  have h6 : ((Set.Iio b \ S).ncard : ℝ) / b ≤ δ / 2 := by
    rw [div_le_iff₀ hbR]; linarith
  rw [show (1 : ℝ) - ((Set.Iio b \ S).ncard : ℝ) / b - 1 = -(((Set.Iio b \ S).ncard : ℝ) / b) by ring,
    abs_neg, abs_of_nonneg h5]
  linarith

end OMA.Helpers

open OMA.Helpers Topology in
theorem OMA.solution : type_of% @Erdos377.erdos_377.variants.ae := by
  intro γ₀ hγ₀ ε hε
  apply density_one_of_exceptional
  intro δ hδ
  have hγ' : γ₀ = ∑' (k : ℕ), Real.log ((k : ℝ) + 2) / 2 ^ (k + 2) := hγ₀
  -- choose K
  have hK1 : ∀ᶠ K : ℕ in atTop, |gam K - γ₀| < ε / 6 := by
    have := (Metric.tendsto_atTop.mp (gam_tendsto γ₀ hγ')) (ε / 6) (by positivity)
    obtain ⟨K₀, hK₀⟩ := this
    exact eventually_atTop.mpr ⟨K₀, fun K hK => by simpa [Real.dist_eq] using hK₀ K hK⟩
  have hK2 : ∀ᶠ K : ℕ in atTop, 3 / ε * (72 * (2 / 3 : ℝ) ^ K) < δ / 8 := by
    have ht : Tendsto (fun K : ℕ => 3 / ε * (72 * (2 / 3 : ℝ) ^ K)) atTop (𝓝 (3 / ε * (72 * 0))) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul 72).const_mul _
    rw [mul_zero, mul_zero] at ht
    exact ht.eventually (gt_mem_nhds (by positivity))
  obtain ⟨K, hKa, hKb, hK2le⟩ := (hK1.and (hK2.and (eventually_ge_atTop 2))).exists
  -- choose U
  obtain ⟨U, hU⟩ := exists_nat_gt (max (8 / δ) (max 2 (8 * (9 / ε ^ 2 * (432 * (K : ℝ) ^ 2 * 16 ^ K)) / δ)))
  have hU1 : 8 / δ < U := lt_of_le_of_lt (le_max_left _ _) hU
  have hU2 : (2 : ℝ) < U := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hU
  have hU3 : 8 * (9 / ε ^ 2 * (432 * (K : ℝ) ^ 2 * 16 ^ K)) / δ < U :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hU
  have hU2' : 2 ≤ U := by exact_mod_cast hU2.le
  have hUR : (0 : ℝ) < U := by linarith
  -- eventually in N
  have hN1 : ∀ᶠ N : ℕ in atTop, |cN K U N - gam K| < ε / 6 := by
    have := (Metric.tendsto_atTop.mp (cN_tendsto K U hK2le hU2')) (ε / 6) (by positivity)
    obtain ⟨N₀, hN₀⟩ := this
    exact eventually_atTop.mpr ⟨N₀, fun N hN => by simpa [Real.dist_eq] using hN₀ N hN⟩
  have hN2 : ∀ᶠ N : ℕ in atTop, 3 / ε * (2 * K * rho K U N) < δ / 8 := by
    have ht : Tendsto (fun N : ℕ => 3 / ε * (2 * K * rho K U N)) atTop (𝓝 (3 / ε * (2 * K * 0))) :=
      ((rho_tendsto K U).const_mul _).const_mul _
    rw [mul_zero, mul_zero] at ht
    exact ht.eventually (gt_mem_nhds (by positivity))
  have hN3 : ∀ᶠ N : ℕ in atTop, 9 / ε ^ 2 * (24 * (K : ℝ) ^ 3 * rho K U N) < δ / 8 := by
    have ht : Tendsto (fun N : ℕ => 9 / ε ^ 2 * (24 * (K : ℝ) ^ 3 * rho K U N)) atTop
        (𝓝 (9 / ε ^ 2 * (24 * (K : ℝ) ^ 3 * 0))) :=
      ((rho_tendsto K U).const_mul _).const_mul _
    rw [mul_zero, mul_zero] at ht
    exact ht.eventually (gt_mem_nhds (by positivity))
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (8 / δ)
  filter_upwards [hN1, hN2, hN3, eventually_gt_atTop U, eventually_ge_atTop N₁] with N h1 h2 h3 h4 h5
  have hNR : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hN8 : 8 / δ < N := lt_of_lt_of_le hN₁ (by exact_mod_cast h5)
  -- the exceptional set is covered by three finite sets
  set E1 : Finset ℕ := (range N).filter (fun n => n * U < N) with hE1
  set E2 : Finset ℕ := (range N).filter (fun n => ε / 3 ≤ bN K U N n) with hE2
  set E3 : Finset ℕ := (range N).filter (fun n => (ε / 3) ^ 2 ≤ (ft K U N n - cN K U N) ^ 2) with hE3
  have hcover : Set.Iio N \ {n : ℕ | |Erdos377.sumInvPrimesNotDvdCentralBinom n - γ₀| < ε} ⊆
      ((E1 ∪ E2 ∪ E3 : Finset ℕ) : Set ℕ) := by
    intro n hn
    rw [Set.mem_sdiff, Set.mem_Iio, Set.mem_ofPred_eq, not_lt] at hn
    obtain ⟨hnN, hbig⟩ := hn
    rw [Finset.mem_coe, Finset.mem_union, Finset.mem_union]
    by_contra hcon
    rw [not_or, not_or] at hcon
    obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hcon
    rw [hE1, Finset.mem_filter, Finset.mem_range] at hc1
    rw [hE2, Finset.mem_filter, Finset.mem_range] at hc2
    rw [hE3, Finset.mem_filter, Finset.mem_range] at hc3
    have hc1' : N ≤ U * n := by
      have := fun h => hc1 ⟨hnN, h⟩
      rw [mul_comm]; omega
    have hc2' : bN K U N n < ε / 3 := by
      by_contra h; exact hc2 ⟨hnN, not_lt.mp h⟩
    have hc3' : |ft K U N n - cN K U N| < ε / 3 := by
      by_contra h
      rw [not_lt] at h
      apply hc3
      refine ⟨hnN, ?_⟩
      rw [← sq_abs (ft K U N n - cN K U N)]
      exact pow_le_pow_left₀ (by positivity) h 2
    have hdec := f_decomp K U N n (by omega) hnN hc1'
    have hb0 := bN_nonneg K U N n
    rw [hdec] at hbig
    have : |ft K U N n + bN K U N n - γ₀| < ε := by
      have e : ft K U N n + bN K U N n - γ₀ =
          (ft K U N n - cN K U N) + (cN K U N - gam K) + (gam K - γ₀) + bN K U N n := by ring
      rw [e]
      calc |(ft K U N n - cN K U N) + (cN K U N - gam K) + (gam K - γ₀) + bN K U N n|
          ≤ |(ft K U N n - cN K U N) + (cN K U N - gam K) + (gam K - γ₀)| + |bN K U N n| :=
            abs_add_le _ _
        _ ≤ |(ft K U N n - cN K U N) + (cN K U N - gam K)| + |gam K - γ₀| + |bN K U N n| := by
            gcongr; exact abs_add_le _ _
        _ ≤ |ft K U N n - cN K U N| + |cN K U N - gam K| + |gam K - γ₀| + |bN K U N n| := by
            gcongr; exact abs_add_le _ _
        _ < ε := by rw [abs_of_nonneg hb0]; linarith
    linarith
  have hcard : ((Set.Iio N \ {n : ℕ | |Erdos377.sumInvPrimesNotDvdCentralBinom n - γ₀| < ε}).ncard : ℝ)
      ≤ ((#E1 + #E2 + #E3 : ℕ) : ℝ) := by
    have h := Set.ncard_le_ncard hcover (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h
    have h' : #(E1 ∪ E2 ∪ E3) ≤ #E1 + #E2 + #E3 :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    exact_mod_cast h.trans h'
  -- E1
  have hE1c : (#E1 : ℝ) ≤ N / U + 1 := by
    have hsub : E1 ⊆ range (N / U + 1) := by
      intro n hn
      rw [hE1, Finset.mem_filter] at hn
      rw [Finset.mem_range]
      have : n ≤ N / U := by
        rw [Nat.le_div_iff_mul_le (by omega)]; exact hn.2.le
      omega
    have h := Finset.card_le_card hsub
    rw [Finset.card_range] at h
    have h' : (#E1 : ℝ) ≤ ((N / U + 1 : ℕ) : ℝ) := by exact_mod_cast h
    have h'' : ((N / U : ℕ) : ℝ) ≤ (N : ℝ) / U := Nat.cast_div_le
    push_cast at h'
    linarith
  -- E2
  have hE2c : (#E2 : ℝ) * (ε / 3) ≤ N * (72 * (2 / 3 : ℝ) ^ K + 2 * K * rho K U N) :=
    (markov (range N) (fun n => bN K U N n) (fun n _ => bN_nonneg K U N n) (ε / 3)).trans
      (bad_sum_le K U hK2le hU2' N h4)
  -- E3
  have hE3c : (#E3 : ℝ) * (ε / 3) ^ 2 ≤
      N * (432 * (K : ℝ) ^ 2 * 16 ^ K / U + 24 * (K : ℝ) ^ 3 * rho K U N) :=
    (markov (range N) (fun n => (ft K U N n - cN K U N) ^ 2) (fun n _ => sq_nonneg _)
      ((ε / 3) ^ 2)).trans (second_moment_le K U hK2le hU2' N h4)
  refine hcard.trans ?_
  push_cast
  -- numerical wrap-up
  have hU1' : 8 < (U : ℝ) * δ := by rwa [div_lt_iff₀ hδ] at hU1
  have hN8' : 8 < (N : ℝ) * δ := by rwa [div_lt_iff₀ hδ] at hN8
  have a1 : (N : ℝ) / U + 1 ≤ δ / 8 * N + δ / 8 * N := by
    have h6 : (N : ℝ) / U ≤ δ / 8 * N := by
      rw [div_le_iff₀ hUR]
      have h7 : (N : ℝ) * 8 ≤ N * ((U : ℝ) * δ) := mul_le_mul_of_nonneg_left hU1'.le hNR.le
      linarith
    linarith
  have a2 : (#E2 : ℝ) ≤ δ / 8 * N + δ / 8 * N := by
    have e : (#E2 : ℝ) = (#E2 : ℝ) * (ε / 3) * (3 / ε) := by field_simp
    rw [e]
    calc (#E2 : ℝ) * (ε / 3) * (3 / ε)
        ≤ N * (72 * (2 / 3 : ℝ) ^ K + 2 * K * rho K U N) * (3 / ε) := by gcongr
      _ = N * (3 / ε * (72 * (2 / 3 : ℝ) ^ K)) + N * (3 / ε * (2 * K * rho K U N)) := by ring
      _ ≤ N * (δ / 8) + N * (δ / 8) := by gcongr
      _ = _ := by ring
  have a3 : (#E3 : ℝ) ≤ δ / 8 * N + δ / 8 * N := by
    have e : (#E3 : ℝ) = (#E3 : ℝ) * (ε / 3) ^ 2 * (9 / ε ^ 2) := by field_simp; ring
    rw [e]
    have hU3' : 9 / ε ^ 2 * (432 * (K : ℝ) ^ 2 * 16 ^ K / U) ≤ δ / 8 := by
      rw [div_lt_iff₀ hδ] at hU3
      rw [← mul_div_assoc, div_le_iff₀ hUR]
      linarith
    calc (#E3 : ℝ) * (ε / 3) ^ 2 * (9 / ε ^ 2)
        ≤ N * (432 * (K : ℝ) ^ 2 * 16 ^ K / U + 24 * (K : ℝ) ^ 3 * rho K U N) * (9 / ε ^ 2) := by
          gcongr
      _ = N * (9 / ε ^ 2 * (432 * (K : ℝ) ^ 2 * 16 ^ K / U)) +
            N * (9 / ε ^ 2 * (24 * (K : ℝ) ^ 3 * rho K U N)) := by ring
      _ ≤ N * (δ / 8) + N * (δ / 8) := by gcongr
      _ = _ := by ring
  nlinarith
