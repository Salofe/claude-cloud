import FormalConjectures.ErdosProblems.«321»

/-!
# Erdős 321: the Bleicher–Erdős upper bound for `R(N)`

Own formalisation.  Write `T(N) = R(N) * log 2`.

* `core`: for every `y`, `T(N) ≤ log 2 + (√N + 1) log N + y log 4 + ∑_{y < p ≤ N} T(N / p)`
  (smooth elements: all subset sums are multiples of `1 / L` with `L ≤ N ^ √N * 4 ^ y`;
  multiples of a prime `p`: dividing by `p` gives an admissible subset of `[1, N / p]`).
* `lemmaC`: `∑_{z < p ≤ N} ⌊N / p⌋ log p ≤ N log N - N log z + N + z`, since
  `(∏_{z < p ≤ N} p ^ ⌊N / p⌋) * (z !) ^ ⌊N / z⌋ * (N mod z)!` divides `N !`.
* `abel_ineq`, `lemmaE`: summation by parts against an antitone majorant `h` of `T(k) / k`.
* `rec_bound`: the choice `y = ⌈N / (log N - 1)⌉`.
* `case_two` (`r = 2`, trivial majorant) and `step` (`r → r + 1`, majorant
  `min (log 2) (c * log log log k / log k)`), then induction on `r` in `main`.
-/

open Filter Real Finset

namespace OMA.Helpers

open Erdos321

/-- validity predicate -/
def Valid (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ Set.InjOn (fun (S : Finset ℕ) ↦ ∑ n ∈ S, (1 : ℚ) / n) A.powerset

theorem R_set_eq (N : ℕ) :
    { #A | (A) (_ : A ⊆ Finset.Icc 1 N)
      (_ : Set.InjOn (fun (S : Finset ℕ) ↦ ∑ n ∈ S, (1 : ℚ) / n) A.powerset) } =
    {n | ∃ A, Valid N A ∧ #A = n} := by
  ext n
  constructor
  · rintro ⟨A, h1, h2, rfl⟩; exact ⟨A, ⟨h1, h2⟩, rfl⟩
  · rintro ⟨A, ⟨h1, h2⟩, rfl⟩; exact ⟨A, h1, h2, rfl⟩

theorem bdd (N : ℕ) : BddAbove {n | ∃ A, Valid N A ∧ #A = n} := by
  refine ⟨N, ?_⟩
  rintro n ⟨A, ⟨h1, -⟩, rfl⟩
  simpa using Finset.card_le_card h1

theorem card_le_R {N : ℕ} {A : Finset ℕ} (hA : Valid N A) : #A ≤ R N := by
  unfold R
  rw [R_set_eq]
  exact le_csSup (bdd N) ⟨A, hA, rfl⟩

theorem exists_valid (N : ℕ) : ∃ A, Valid N A ∧ #A = R N := by
  have hne : {n | ∃ A, Valid N A ∧ #A = n}.Nonempty :=
    ⟨0, ∅, ⟨by simp, by simp [Set.InjOn]⟩, by simp⟩
  have := Nat.sSup_mem hne (bdd N)
  unfold R
  rw [R_set_eq]
  exact this

theorem R_le (N : ℕ) : R N ≤ N := by
  obtain ⟨A, ⟨h1, -⟩, h⟩ := exists_valid N
  rw [← h]
  simpa using Finset.card_le_card h1

theorem valid_subset {N : ℕ} {A B : Finset ℕ} (hA : Valid N A) (hB : B ⊆ A) : Valid N B :=
  ⟨hB.trans hA.1, hA.2.mono (Finset.coe_subset.mpr (Finset.powerset_mono.mpr hB))⟩

theorem card_filter_dvd_le {N p : ℕ} (hp : 0 < p) {A : Finset ℕ} (hA : Valid N A) :
    #(A.filter (p ∣ ·)) ≤ R (N / p) := by
  have hcard : #((A.filter (p ∣ ·)).image (· / p)) = #(A.filter (p ∣ ·)) := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    have hab' : a / p = b / p := hab
    rw [← Nat.mul_div_cancel' ha', ← Nat.mul_div_cancel' hb', hab']
  rw [← hcard]
  apply card_le_R
  constructor
  · intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨haA, hpa⟩ := Finset.mem_filter.mp ha
    have ha1 := Finset.mem_Icc.mp (hA.1 haA)
    exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hpa) hp,
      Nat.div_le_div_right ha1.2⟩
  · intro S hS S' hS' h
    have hinj : Function.Injective (fun n : ℕ => n * p) := fun a b hab =>
      Nat.eq_of_mul_eq_mul_right hp hab
    have hsub : ∀ T : Finset ℕ, T ⊆ (A.filter (p ∣ ·)).image (· / p) →
        T.image (fun n : ℕ => n * p) ⊆ A := by
      intro T hT a ha
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (hT hn)
      obtain ⟨hbA, hpb⟩ := Finset.mem_filter.mp hb
      have : b / p * p = b := Nat.div_mul_cancel hpb
      simpa [this] using hbA
    have hsum : ∀ T : Finset ℕ, ∑ a ∈ T.image (fun n : ℕ => n * p), (1 : ℚ) / a =
        (1 / (p : ℚ)) * ∑ n ∈ T, (1 : ℚ) / n := by
      intro T
      rw [Finset.sum_image (fun a _ b _ hab => hinj hab), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      push_cast
      ring
    have hS1 := Finset.mem_powerset.mp (Finset.mem_coe.mp hS)
    have hS2 := Finset.mem_powerset.mp (Finset.mem_coe.mp hS')
    have himg : S.image (fun n : ℕ => n * p) = S'.image (fun n : ℕ => n * p) := by
      apply hA.2 (Finset.mem_coe.mpr (Finset.mem_powerset.mpr (hsub S hS1)))
        (Finset.mem_coe.mpr (Finset.mem_powerset.mpr (hsub S' hS2)))
      show ∑ a ∈ S.image (fun n : ℕ => n * p), (1 : ℚ) / a =
        ∑ a ∈ S'.image (fun n : ℕ => n * p), (1 : ℚ) / a
      rw [hsum, hsum]
      have h' : ∑ n ∈ S, (1 : ℚ) / n = ∑ n ∈ S', (1 : ℚ) / n := h
      rw [h']
    exact Finset.image_injective hinj himg

theorem smooth_card_bound {N L : ℕ} {A : Finset ℕ} (hA : Valid N A) (hL : 0 < L)
    (hdvd : ∀ a ∈ A, a ∣ L) : 2 ^ #A ≤ N * L + 1 := by
  have key : ∀ T ∈ A.powerset, ∑ n ∈ T, (1 : ℚ) / n = ((∑ a ∈ T, L / a : ℕ) : ℚ) / L := by
    intro T hT
    rw [Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a ha
    have haA : a ∈ A := Finset.mem_powerset.mp hT ha
    have had : a ∣ L := hdvd a haA
    have ha1 := (Finset.mem_Icc.mp (hA.1 haA)).1
    have ha0 : (a : ℚ) ≠ 0 := by positivity
    have hL0 : (L : ℚ) ≠ 0 := by positivity
    rw [Nat.cast_div had ha0]
    field_simp
  have hinj : Set.InjOn (fun S : Finset ℕ => ∑ a ∈ S, L / a) A.powerset := by
    intro S hS S' hS' h
    apply hA.2 hS hS'
    show ∑ n ∈ S, (1 : ℚ) / n = ∑ n ∈ S', (1 : ℚ) / n
    have h' : ∑ a ∈ S, L / a = ∑ a ∈ S', L / a := h
    rw [key S (Finset.mem_coe.mp hS), key S' (Finset.mem_coe.mp hS'), h']
  have hmaps : ∀ S ∈ A.powerset,
      (fun S : Finset ℕ => ∑ a ∈ S, L / a) S ∈ Finset.range (N * L + 1) := by
    intro S hS
    simp only [Finset.mem_range, Nat.lt_succ_iff]
    calc ∑ a ∈ S, L / a ≤ ∑ a ∈ S, L := Finset.sum_le_sum (fun a _ => Nat.div_le_self _ _)
      _ = #S * L := by simp
      _ ≤ N * L := by
        gcongr
        exact (card_le_card (mem_powerset.mp hS)).trans (by simpa using card_le_card hA.1)
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  simpa [Finset.card_powerset] using this

theorem smooth_dvd {N y a : ℕ} (ha1 : 1 ≤ a) (haN : a ≤ N)
    (hs : ∀ p, p.Prime → p ∣ a → p ≤ y) :
    a ∣ ∏ p ∈ Nat.primesLE y, p ^ p.log N := by
  have h1 : a = ∏ p ∈ a.primeFactors, p ^ a.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self (by omega : a ≠ 0)]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
  calc a = ∏ p ∈ a.primeFactors, p ^ a.factorization p := h1
    _ ∣ ∏ p ∈ a.primeFactors, p ^ p.log N := by
        apply Finset.prod_dvd_prod_of_dvd
        intro p hp
        apply pow_dvd_pow
        exact Nat.le_log_of_pow_le (Nat.prime_of_mem_primeFactors hp).one_lt
          ((Nat.le_of_dvd (by omega) (Nat.ordProj_dvd a p)).trans haN)
    _ ∣ ∏ p ∈ Nat.primesLE y, p ^ p.log N := by
        apply Finset.prod_dvd_prod_of_subset
        intro p hp
        exact Nat.mem_primesLE.mpr ⟨hs p (Nat.prime_of_mem_primeFactors hp)
          (Nat.dvd_of_mem_primeFactors hp), Nat.prime_of_mem_primeFactors hp⟩

theorem L_le (N y : ℕ) (hN : 1 ≤ N) :
    ∏ p ∈ Nat.primesLE y, p ^ p.log N ≤ N ^ (Nat.sqrt N) * 4 ^ y := by
  calc ∏ p ∈ Nat.primesLE y, p ^ p.log N
      ≤ ∏ p ∈ Nat.primesLE y, ((if p ≤ Nat.sqrt N then N else 1) * p) := by
        apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
        intro p hp
        have hpp := Nat.prime_of_mem_primesLE hp
        split_ifs with h
        · exact (Nat.pow_log_le_self p (by omega)).trans (Nat.le_mul_of_pos_right N hpp.pos)
        · have h2 : N < p ^ 2 := Nat.sqrt_lt'.mp (by omega)
          have h3 : p.log N < 2 := Nat.log_lt_of_lt_pow (by omega) h2
          calc p ^ p.log N ≤ p ^ 1 := Nat.pow_le_pow_right hpp.pos (by omega)
            _ = 1 * p := by ring
    _ = (∏ p ∈ Nat.primesLE y, if p ≤ Nat.sqrt N then N else 1) * ∏ p ∈ Nat.primesLE y, p :=
        Finset.prod_mul_distrib
    _ ≤ N ^ Nat.sqrt N * 4 ^ y := by
        apply Nat.mul_le_mul
        · rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
          apply Nat.pow_le_pow_right hN
          calc #((Nat.primesLE y).filter (fun p => p ≤ Nat.sqrt N))
              ≤ #(Finset.Icc 1 (Nat.sqrt N)) := by
                apply card_le_card
                intro p hp
                obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
                exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hp1).one_le, hp2⟩
            _ = Nat.sqrt N := by simp
        · exact primorial_le_four_pow y

theorem core {N : ℕ} (y : ℕ) (hN : 1 ≤ N) :
    (R N : ℝ) * log 2 ≤ log 2 + (Nat.sqrt N + 1) * log N + y * log 4 +
      ∑ p ∈ (Finset.Ioc y N).filter Nat.Prime, (R (N / p) : ℝ) * log 2 := by
  classical
  obtain ⟨A, hA, hcard⟩ := exists_valid N
  set A0 := A.filter (fun a => ∀ p, p.Prime → p ∣ a → p ≤ y) with hA0
  have hsub : A ⊆ A0 ∪ ((Finset.Ioc y N).filter Nat.Prime).biUnion (fun p => A.filter (p ∣ ·)) := by
    intro a ha
    by_cases h : ∀ p, p.Prime → p ∣ a → p ≤ y
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha, h⟩)
    · push Not at h
      obtain ⟨p, hp, hpa, hpy⟩ := h
      refine Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨p, ?_, Finset.mem_filter.mpr ⟨ha, hpa⟩⟩)
      have ha1 := Finset.mem_Icc.mp (hA.1 ha)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hpy, (Nat.le_of_dvd (by omega) hpa).trans ha1.2⟩, hp⟩
  have h1 : #A ≤ #A0 + ∑ p ∈ (Finset.Ioc y N).filter Nat.Prime, R (N / p) := by
    calc #A ≤ _ := Finset.card_le_card hsub
      _ ≤ #A0 + #(((Finset.Ioc y N).filter Nat.Prime).biUnion (fun p => A.filter (p ∣ ·))) :=
          Finset.card_union_le _ _
      _ ≤ #A0 + ∑ p ∈ (Finset.Ioc y N).filter Nat.Prime, #(A.filter (p ∣ ·)) :=
          Nat.add_le_add_left Finset.card_biUnion_le _
      _ ≤ #A0 + ∑ p ∈ (Finset.Ioc y N).filter Nat.Prime, R (N / p) := by
          apply Nat.add_le_add_left
          apply Finset.sum_le_sum
          intro p hp
          exact card_filter_dvd_le (Finset.mem_filter.mp hp).2.pos hA
  have hA0v : Valid N A0 := valid_subset hA (Finset.filter_subset _ _)
  have h2 : 2 ^ #A0 ≤ N * (∏ p ∈ Nat.primesLE y, p ^ p.log N) + 1 := by
    apply smooth_card_bound hA0v
      (Finset.prod_pos (fun p hp => pow_pos (Nat.prime_of_mem_primesLE hp).pos _))
    intro a ha
    obtain ⟨haA, hs⟩ := Finset.mem_filter.mp ha
    have ha1 := Finset.mem_Icc.mp (hA.1 haA)
    exact smooth_dvd ha1.1 ha1.2 hs
  have h3 : 2 ^ #A0 ≤ 2 * (N ^ (Nat.sqrt N + 1) * 4 ^ y) := by
    have hL := L_le N y hN
    have hpos : 1 ≤ N ^ (Nat.sqrt N + 1) * 4 ^ y := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc 2 ^ #A0 ≤ N * (∏ p ∈ Nat.primesLE y, p ^ p.log N) + 1 := h2
      _ ≤ N * (N ^ (Nat.sqrt N) * 4 ^ y) + 1 := by gcongr
      _ = N ^ (Nat.sqrt N + 1) * 4 ^ y + 1 := by ring
      _ ≤ 2 * (N ^ (Nat.sqrt N + 1) * 4 ^ y) := by omega
  have h4 : (#A0 : ℝ) * log 2 ≤ log 2 + (Nat.sqrt N + 1) * log N + y * log 4 := by
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h3' : ((2 : ℝ) ^ #A0) ≤ 2 * ((N : ℝ) ^ (Nat.sqrt N + 1) * 4 ^ y) := by exact_mod_cast h3
    have := Real.log_le_log (by positivity) h3'
    rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at this
    push_cast at this
    linarith
  have h1' : (R N : ℝ) ≤ #A0 + ∑ p ∈ (Finset.Ioc y N).filter Nat.Prime, (R (N / p) : ℝ) := by
    rw [← hcard]
    exact_mod_cast h1
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos (by norm_num)
  calc (R N : ℝ) * log 2
      ≤ (#A0 + ∑ p ∈ (Finset.Ioc y N).filter Nat.Prime, (R (N / p) : ℝ)) * log 2 := by gcongr
    _ = #A0 * log 2 + ∑ p ∈ (Finset.Ioc y N).filter Nat.Prime, (R (N / p) : ℝ) * log 2 := by
        rw [add_mul, Finset.sum_mul]
    _ ≤ _ := by linarith

theorem factorial_block_dvd (z q r : ℕ) :
    (z.factorial) ^ q * r.factorial ∣ (q * z + r).factorial := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h1 : z.factorial * (q * z + r).factorial ∣ (z + (q * z + r)).factorial :=
      Nat.factorial_mul_factorial_dvd_factorial_add z (q * z + r)
    have h2 : (q + 1) * z + r = z + (q * z + r) := by ring
    rw [h2]
    calc z.factorial ^ (q + 1) * r.factorial
        = z.factorial * (z.factorial ^ q * r.factorial) := by ring
      _ ∣ z.factorial * (q * z + r).factorial := Nat.mul_dvd_mul_left _ ih
      _ ∣ _ := h1

theorem prime_pow_div_dvd_factorial {N p : ℕ} (hp : p.Prime) : p ^ (N / p) ∣ N.factorial := by
  rw [hp.pow_dvd_factorial_iff (Nat.lt_succ_self _)]
  rcases Nat.lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  · have h1 : 1 ∈ Finset.Ico 1 (Nat.log p N + 1) := by
      simp only [Finset.mem_Ico]
      exact ⟨le_refl _, Nat.succ_lt_succ (Nat.log_pos hp.one_lt h)⟩
    calc N / p = N / p ^ 1 := by rw [pow_one]
      _ ≤ _ := Finset.single_le_sum (f := fun i => N / p ^ i) (fun _ _ => Nat.zero_le _) h1

theorem prod_primes_pow_dvd_factorial (N : ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, p ^ (N / p) ∣ N.factorial := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
    rw [Finset.prod_insert hat]
    have ha : a.Prime := hs a (Finset.mem_insert_self a t)
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    · apply Nat.Coprime.prod_right
      intro q hq
      have hq' : q.Prime := hs q (Finset.mem_insert_of_mem hq)
      apply Nat.Coprime.pow
      rw [Nat.coprime_primes ha hq']
      rintro rfl
      exact hat hq
    · exact prime_pow_div_dvd_factorial ha
    · exact ih (fun p hp => hs p (Finset.mem_insert_of_mem hp))

theorem log_factorial_ge (n : ℕ) : (n : ℝ) * log n - n ≤ log (n.factorial) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Nat.factorial_succ]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity)]
    have h1 : log ((n : ℝ) + 1) - log n ≤ 1 / n := by
      rw [← Real.log_div (by positivity) (by positivity)]
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
      have h2 : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
      linarith
    have h3 : (n : ℝ) * (log ((n : ℝ) + 1) - log n) ≤ 1 := by
      calc (n : ℝ) * (log ((n : ℝ) + 1) - log n) ≤ n * (1 / n) := by gcongr
        _ = 1 := by field_simp
    nlinarith [ih]

/-- Lemma C -/
theorem lemmaC {N z : ℕ} (hz : 1 ≤ z) :
    ∑ p ∈ (Finset.Ioc z N).filter Nat.Prime, ((N / p : ℕ) : ℝ) * log p ≤
      N * log N - N * log z + N + z := by
  set q := N / z with hq
  set r := N % z with hr
  have hrz : r < z := Nat.mod_lt N hz
  have hN : q * z + r = N := by rw [hq, hr]; exact Nat.div_add_mod' N z
  set P := ∏ p ∈ (Finset.Ioc z N).filter Nat.Prime, p ^ (N / p) with hP
  have hPdvd : P ∣ N.factorial :=
    prod_primes_pow_dvd_factorial N _ (fun p hp => (Finset.mem_filter.mp hp).2)
  have hBdvd : z.factorial ^ q * r.factorial ∣ N.factorial := by
    have := factorial_block_dvd z q r
    rwa [hN] at this
  have hcop : Nat.Coprime P (z.factorial ^ q * r.factorial) := by
    apply Nat.Coprime.prod_left
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    have hpz := (Finset.mem_Ioc.mp hp1).1
    apply Nat.Coprime.pow_left
    apply Nat.Coprime.mul_right
    · apply Nat.Coprime.pow_right
      rw [hp2.coprime_iff_not_dvd, hp2.dvd_factorial]
      omega
    · rw [hp2.coprime_iff_not_dvd, hp2.dvd_factorial]
      omega
  have hdvd : P * (z.factorial ^ q * r.factorial) ∣ N.factorial :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hPdvd hBdvd
  have hle : P * (z.factorial ^ q * r.factorial) ≤ N.factorial :=
    Nat.le_of_dvd (Nat.factorial_pos N) hdvd
  have hPpos : 0 < P := Finset.prod_pos (fun p hp => pow_pos (Finset.mem_filter.mp hp).2.pos _)
  have hle' : ((P : ℝ) * ((z.factorial : ℝ) ^ q * (r.factorial : ℝ))) ≤ (N.factorial : ℝ) := by
    exact_mod_cast hle
  have hlog := Real.log_le_log (by positivity) hle'
  have hzf : (0 : ℝ) < z.factorial := by exact_mod_cast Nat.factorial_pos z
  have hrf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hPr : (0 : ℝ) < P := by exact_mod_cast hPpos
  rw [Real.log_mul hPr.ne' (by positivity), Real.log_mul (by positivity) hrf.ne',
    Real.log_pow] at hlog
  have hlogP : log (P : ℝ) = ∑ p ∈ (Finset.Ioc z N).filter Nat.Prime, ((N / p : ℕ) : ℝ) * log p := by
    rw [hP, Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro p hp
      rw [Nat.cast_pow, Real.log_pow]
    · intro p hp
      have := (Finset.mem_filter.mp hp).2.pos
      positivity
  rw [← hlogP]
  have hNf : log (N.factorial : ℝ) ≤ N * log N := by
    have h1 : (N.factorial : ℝ) ≤ (N : ℝ) ^ N := by exact_mod_cast Nat.factorial_le_pow N
    have := Real.log_le_log (by exact_mod_cast Nat.factorial_pos N) h1
    rwa [Real.log_pow] at this
  have hz1 := log_factorial_ge z
  have hr1 := log_factorial_ge r
  have hzr : (0 : ℝ) < z := by exact_mod_cast hz
  -- r * (log z - log r) ≤ z
  have hrl : (r : ℝ) * log z - r * log r ≤ z - r := by
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · simp [h0]
    · have hr0 : (0 : ℝ) < r := by exact_mod_cast hpos
      have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (z : ℝ) / r by positivity)
      rw [Real.log_div hzr.ne' hr0.ne'] at h1
      have h2 : (r : ℝ) * (log z - log r) ≤ r * ((z : ℝ) / r - 1) := by gcongr
      have h3 : (r : ℝ) * ((z : ℝ) / r - 1) = z - r := by field_simp
      linarith
  have hNr : (N : ℝ) = q * z + r := by exact_mod_cast hN.symm
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have key : (q : ℝ) * log (z.factorial) ≥ q * (z * log z - z) := by gcongr
  have e1 : (q : ℝ) * (z * log z - z) = (N - r) * log z - (N - r) := by rw [hNr]; ring
  linarith

theorem abel_ineq {ι : Type*} (s : Finset ι) (l : ι → ℕ) (w : ι → ℝ) (h : ℕ → ℝ) (B : ℕ → ℝ)
    (M : ℕ) (hh : Antitone h) (hl : ∀ i ∈ s, 1 ≤ l i)
    (hB : ∀ j ≤ M, ∑ i ∈ s.filter (fun i => l i ≤ j), w i ≤ B j) :
    ∀ m ≤ M, ∑ i ∈ s.filter (fun i => l i ≤ m), w i * h (l i) +
        (B m - ∑ i ∈ s.filter (fun i => l i ≤ m), w i) * h m
      ≤ B 0 * h 0 + ∑ j ∈ Finset.range m, (B (j + 1) - B j) * h (j + 1) := by
  classical
  intro m
  induction m with
  | zero =>
    intro _
    have h0 : s.filter (fun i => l i ≤ 0) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i hi
      have := hl i hi
      omega
    rw [h0]
    simp
  | succ m ih =>
    intro hm
    have ih' := ih (by omega)
    have hsplit : ∀ f : ι → ℝ, ∑ i ∈ s.filter (fun i => l i ≤ m + 1), f i =
        ∑ i ∈ s.filter (fun i => l i ≤ m), f i + ∑ i ∈ s.filter (fun i => l i = m + 1), f i := by
      intro f
      rw [← Finset.sum_union]
      · congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨hi, hle⟩
          rcases Nat.lt_or_ge (l i) (m + 1) with h1 | h1
          · exact Or.inl ⟨hi, by omega⟩
          · exact Or.inr ⟨hi, by omega⟩
        · rintro (⟨hi, hle⟩ | ⟨hi, hle⟩)
          · exact ⟨hi, by omega⟩
          · exact ⟨hi, by omega⟩
      · rw [Finset.disjoint_filter]
        intro i _ h1 h2
        omega
    have hE : ∑ i ∈ s.filter (fun i => l i = m + 1), w i * h (l i) =
        (∑ i ∈ s.filter (fun i => l i = m + 1), w i) * h (m + 1) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    rw [hsplit, hsplit, hE, Finset.sum_range_succ]
    have hBm := hB m (by omega)
    have hanti : h (m + 1) ≤ h m := hh (Nat.le_succ m)
    nlinarith [mul_le_mul_of_nonneg_left hanti (sub_nonneg.mpr hBm)]

/-- Lemma E -/
theorem lemmaE {N y : ℕ} (hy : 2 ≤ y) (hm : 4 * (N / y + 1) ≤ N) (h : ℕ → ℝ) (hh : Antitone h)
    (hh0 : ∀ k, 0 ≤ h k) (T : ℕ → ℝ)
    (hT : ∀ k, 1 ≤ k → k ≤ N / y → T k ≤ k * h k) :
    ∑ p ∈ (Finset.Ioc y N).filter Nat.Prime, T (N / p) ≤
      N / log y * (2 * h 0 + ∑ j ∈ Finset.range (N / y),
        h (j + 1) * (log ((j : ℝ) + 2) - log ((j : ℝ) + 1))) := by
  have hN0 : 0 < N := lt_of_lt_of_le (by positivity) hm
  set m := N / y with hmdef
  have hylog : 0 < log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  set s := (Finset.Ioc y N).filter Nat.Prime with hs
  have hmem : ∀ p ∈ s, y < p ∧ p ≤ N ∧ p.Prime := by
    intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
    exact ⟨(Finset.mem_Ioc.mp h1).1, (Finset.mem_Ioc.mp h1).2, h2⟩
  have hl1 : ∀ p ∈ s, 1 ≤ N / p := by
    intro p hp
    obtain ⟨_, h2, h3⟩ := hmem p hp
    exact Nat.div_pos h2 h3.pos
  have hlm : ∀ p ∈ s, N / p ≤ m := by
    intro p hp
    obtain ⟨h1, _, _⟩ := hmem p hp
    exact Nat.div_le_div_left h1.le (by omega)
  set B : ℕ → ℝ := fun j => N / log y * (log ((j : ℝ) + 1) + 2) with hBdef
  have hB : ∀ j ≤ m, ∑ p ∈ s.filter (fun p => N / p ≤ j), ((N / p : ℕ) : ℝ) ≤ B j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · have h0 : s.filter (fun p => N / p ≤ 0) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro p hp
        have := hl1 p hp
        omega
      rw [h0, Finset.sum_empty]
      simp only [hBdef]
      have : (0 : ℝ) ≤ log ((0 : ℕ) + 1 : ℝ) := by simp
      positivity
    · set z := N / (j + 1) with hz
      have hz4 : 4 ≤ z := by
        rw [hz, Nat.le_div_iff_mul_le (by omega)]
        nlinarith
      have hzlt : N < (z + 1) * (j + 1) := by
        have := Nat.lt_succ_self z
        rw [hz] at this ⊢
        exact (Nat.div_lt_iff_lt_mul (by omega)).mp this
      have step1 : ∑ p ∈ s.filter (fun p => N / p ≤ j), ((N / p : ℕ) : ℝ) ≤
          ∑ p ∈ s.filter (fun p => N / p ≤ j), ((N / p : ℕ) : ℝ) * log p / log y := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hp1, _⟩ := Finset.mem_filter.mp hp
        obtain ⟨h1, _, _⟩ := hmem p hp1
        have hyp : log (y : ℝ) ≤ log (p : ℝ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast h1.le)
        rw [le_div_iff₀ hylog]
        gcongr
      have step2 : ∑ p ∈ s.filter (fun p => N / p ≤ j), ((N / p : ℕ) : ℝ) * log p / log y ≤
          (∑ p ∈ (Finset.Ioc z N).filter Nat.Prime, ((N / p : ℕ) : ℝ) * log p) / log y := by
        rw [Finset.sum_div]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
          obtain ⟨h1, h2, h3⟩ := hmem p hp1
          refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, h2⟩, h3⟩
          rw [hz, Nat.div_lt_iff_lt_mul (by omega)]
          have : N / p < j + 1 := by omega
          exact (Nat.div_lt_iff_lt_mul h3.pos).mp this |>.trans_le (by nlinarith)
        · intro p _ _
          have : (0 : ℝ) ≤ log (p : ℝ) := Real.log_natCast_nonneg p
          positivity
      have step3 := lemmaC (N := N) (z := z) (by omega)
      have hzr : (4 : ℝ) ≤ z := by exact_mod_cast hz4
      have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      have hzN2 : (z : ℝ) ≤ N / 2 := by
        have h1 : ((N / (j + 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((j + 1 : ℕ) : ℝ) := Nat.cast_div_le
        have h2 : (N : ℝ) / ((j + 1 : ℕ) : ℝ) ≤ N / 2 := by
          apply div_le_div_of_nonneg_left hNpos.le (by norm_num)
          push_cast; linarith
        rw [hz]; linarith
      have hlogN : log (N : ℝ) ≤ log ((z : ℝ) + 1) + log ((j : ℝ) + 1) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        apply Real.log_le_log hNpos
        exact_mod_cast hzlt.le
      have hlogz : log ((z : ℝ) + 1) - log z ≤ 1 / z := by
        rw [← Real.log_div (by positivity) (by positivity)]
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((z : ℝ) + 1) / z by positivity)
        have h2 : ((z : ℝ) + 1) / z - 1 = 1 / z := by field_simp; ring
        linarith
      have hzinv : (1 : ℝ) / z ≤ 1 / 4 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hzr
      have hfin : (N : ℝ) * log N - N * log z + N + z ≤ N * (log ((j : ℝ) + 1) + 2) := by
        have : (N : ℝ) * (log N - log z) ≤ N * (log ((j : ℝ) + 1) + 1 / 4) := by
          gcongr
          linarith
        nlinarith
      calc ∑ p ∈ s.filter (fun p => N / p ≤ j), ((N / p : ℕ) : ℝ)
          ≤ (∑ p ∈ (Finset.Ioc z N).filter Nat.Prime, ((N / p : ℕ) : ℝ) * log p) / log y :=
            step1.trans step2
        _ ≤ (N * (log ((j : ℝ) + 1) + 2)) / log y := by
            gcongr
            exact step3.trans hfin
        _ = B j := by simp only [hBdef]; ring
  have habel := abel_ineq s (fun p => N / p) (fun p => ((N / p : ℕ) : ℝ)) h B m hh hl1 hB m le_rfl
  have hfilt : s.filter (fun p => N / p ≤ m) = s := Finset.filter_true_of_mem hlm
  rw [hfilt] at habel
  have hnn : 0 ≤ (B m - ∑ p ∈ s, ((N / p : ℕ) : ℝ)) * h m := by
    apply mul_nonneg _ (hh0 m)
    have := hB m le_rfl
    rw [hfilt] at this
    linarith
  have hsum1 : ∑ p ∈ s, T (N / p) ≤ ∑ p ∈ s, ((N / p : ℕ) : ℝ) * h (N / p) := by
    apply Finset.sum_le_sum
    intro p hp
    exact hT (N / p) (hl1 p hp) (hlm p hp)
  have hB0 : B 0 = N / log y * 2 := by simp [hBdef]
  have hBdiff : ∀ j : ℕ, (B (j + 1) - B j) * h (j + 1) =
      N / log y * (h (j + 1) * (log ((j : ℝ) + 2) - log ((j : ℝ) + 1))) := by
    intro j
    simp only [hBdef]
    push_cast
    ring_nf
  calc ∑ p ∈ s, T (N / p) ≤ ∑ p ∈ s, ((N / p : ℕ) : ℝ) * h (N / p) := hsum1
    _ ≤ B 0 * h 0 + ∑ j ∈ Finset.range m, (B (j + 1) - B j) * h (j + 1) := by linarith
    _ = _ := by
        rw [hB0, Finset.sum_congr rfl (fun j _ => hBdiff j), ← Finset.mul_sum]
        ring

theorem exp12 : (150000 : ℝ) ≤ exp 12 := by
  have h := Real.exp_one_gt_d9
  have h2 : exp 1 ^ 12 = exp 12 := by
    exact_mod_cast Real.exp_one_pow 12
  rw [← h2]
  calc (150000 : ℝ) ≤ 2.7 ^ 12 := by norm_num
    _ ≤ exp 1 ^ 12 := by gcongr; linarith

theorem small_terms {a q s x l2 : ℝ} (hq : q * q = a) (hs : s ≤ q) (hx : 150000 ≤ x)
    (hq300 : 300 * x ^ 2 ≤ q) (hl2 : l2 ≤ 0.7) :
    l2 + (s + 1) * x + 2 * l2 ≤ 0.01 * (a / x) := by
  have hxpos : 0 < x := by linarith
  have hq1 : 1 ≤ q := by nlinarith
  have h1 : 3 * q * x ≤ 0.01 * (a / x) := by
    rw [← hq, show 0.01 * (q * q / x) = (0.01 * q * q) / x by ring, le_div_iff₀ hxpos]
    nlinarith [mul_le_mul_of_nonneg_left hq300 (show (0 : ℝ) ≤ q by linarith)]
  have h2 : (s + 1) * x ≤ (q + 1) * x := by gcongr
  nlinarith

theorem y_term {a x l4 : ℝ} (ha : 0 ≤ a) (hx : 150000 ≤ x) (hl4 : 0 ≤ l4) (hl4' : l4 ≤ 1.3863) :
    a / (x - 1) * l4 ≤ 1.39 * (a / x) := by
  have hxpos : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have h1 : a / (x - 1) ≤ 1.0001 * (a / x) := by
    rw [div_le_iff₀ hx1]
    have e : 1.0001 * (a / x) * (x - 1) = a * (1.0001 * (x - 1) / x) := by ring
    rw [e]
    have : 1 ≤ 1.0001 * (x - 1) / x := by
      rw [le_div_iff₀ hxpos]; linarith
    nlinarith
  have h2 : 0 ≤ a / x := by positivity
  calc a / (x - 1) * l4 ≤ (1.0001 * (a / x)) * 1.3863 := by
        apply mul_le_mul h1 hl4' hl4 (by positivity)
    _ ≤ 1.39 * (a / x) := by nlinarith

theorem frac_bound {x L2 : ℝ} (h1 : 0 < L2) (h2 : 2 * L2 ≤ x) :
    1 / (x - L2) ≤ 1 / x * (1 + 2 * L2 / x) := by
  have hxL : 0 < x - L2 := by linarith
  have hxpos : 0 < x := by linarith
  rw [div_le_iff₀ hxL]
  have e : 1 / x * (1 + 2 * L2 / x) * (x - L2) = 1 + L2 * (x - 2 * L2) / x ^ 2 := by
    field_simp
    ring
  rw [e]
  have : 0 ≤ L2 * (x - 2 * L2) / x ^ 2 := by
    apply div_nonneg _ (by positivity)
    nlinarith
  linarith

theorem sqrt_big {a x : ℝ} (hx : 150000 ≤ x) (ha : a = exp x) : 300 * x ^ 2 ≤ √a := by
  have hsqe : √a = exp (x / 4) * exp (x / 4) := by
    rw [ha, ← Real.exp_half, ← Real.exp_add]
    congr 1
    ring
  have hq4 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ x / 4 by linarith)
  rw [hsqe]
  have h1 : x ^ 2 / 32 ≤ exp (x / 4) := by nlinarith
  have h2 : (0 : ℝ) ≤ x ^ 2 / 32 := by positivity
  have hx2 : (307200 : ℝ) ≤ x ^ 2 := by nlinarith
  have hx4 : 307200 * x ^ 2 ≤ x ^ 2 * x ^ 2 := by nlinarith [sq_nonneg x]
  calc 300 * x ^ 2 ≤ (x ^ 2 / 32) * (x ^ 2 / 32) := by linarith
    _ ≤ exp (x / 4) * exp (x / 4) := mul_le_mul h1 h1 h2 (h2.trans h1)

set_option maxHeartbeats 400000 in
theorem rec_bound {N : ℕ} {x L2 : ℝ} (hx : x = log N) (hL2 : L2 = log x) (hx1 : 1 ≤ x)
    (hL : 12 ≤ L2) (h : ℕ → ℝ) (hh : Antitone h) (hh0 : ∀ k, 0 ≤ h k) (hh2 : h 0 ≤ log 2)
    (hT : ∀ k : ℕ, 1 ≤ k → (k : ℝ) + 1 ≤ x → (R k : ℝ) * log 2 ≤ k * h k)
    (S : ℝ)
    (hS : ∀ m : ℕ, (m : ℝ) + 1 ≤ x →
      ∑ j ∈ Finset.range m, h (j + 1) * (log ((j : ℝ) + 2) - log ((j : ℝ) + 1)) ≤ S) :
    (R N : ℝ) * log 2 ≤ N / x * (1.4 + (1 + 2 * L2 / x) * (1.39 + S)) := by
  have hxpos : 0 < x := by linarith
  have hxe : x = exp L2 := by rw [hL2, Real.exp_log hxpos]
  have hx150 : 150000 ≤ x := by
    rw [hxe]
    exact exp12.trans (Real.exp_le_exp.mpr hL)
  have hN1 : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      simp at hx
      linarith
    · exact h0
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNe : (N : ℝ) = exp x := by rw [hx, Real.exp_log hNpos]
  have hquad := Real.quadratic_le_exp_of_nonneg hxpos.le
  have hN4 : 4 * x ≤ N := by rw [hNe]; nlinarith
  have hNx : x + 1 ≤ N := by rw [hNe]; exact Real.add_one_le_exp x
  have hsq : √(N : ℝ) * √(N : ℝ) = N := Real.mul_self_sqrt hNpos.le
  have hsq300 : 300 * x ^ 2 ≤ √(N : ℝ) := sqrt_big hx150 hNe
  have hs : (Nat.sqrt N : ℝ) ≤ √(N : ℝ) := Real.nat_sqrt_le_real_sqrt
  have hquadL := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ L2 by linarith)
  have hL2x : 2 * L2 ≤ x := by rw [hxe]; nlinarith
  -- choice of y
  set y := ⌈(N : ℝ) / (x - 1)⌉₊ with hy
  have hx1' : 0 < x - 1 := by linarith
  have hy_ge : (N : ℝ) / (x - 1) ≤ y := Nat.le_ceil _
  have hy_lt : (y : ℝ) < N / (x - 1) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hy1 : (1 : ℝ) < y := by
    have : 1 < (N : ℝ) / (x - 1) := by rw [lt_div_iff₀ hx1']; linarith
    linarith
  have hy2 : 2 ≤ y := by
    have : 1 < y := by exact_mod_cast hy1
    omega
  have hypos : (0 : ℝ) < y := by linarith
  have hm_le : ((N / y : ℕ) : ℝ) ≤ x - 1 := by
    calc ((N / y : ℕ) : ℝ) ≤ (N : ℝ) / y := Nat.cast_div_le
      _ ≤ x - 1 := by
        rw [div_le_iff₀ hypos]
        rw [div_le_iff₀ hx1'] at hy_ge
        linarith
  have hm4 : 4 * (N / y + 1) ≤ N := by
    have : (4 : ℝ) * (((N / y : ℕ) : ℝ) + 1) ≤ N := by linarith
    exact_mod_cast this
  have hcore := core y hN1
  have hE := lemmaE hy2 hm4 h hh hh0 (fun k => (R k : ℝ) * log 2)
    (fun k hk1 hk2 => hT k hk1 (by
      have : (k : ℝ) ≤ ((N / y : ℕ) : ℝ) := by exact_mod_cast hk2
      linarith))
  have hSm := hS (N / y) (by linarith)
  have hSnn : 0 ≤ ∑ j ∈ Finset.range (N / y),
      h (j + 1) * (log ((j : ℝ) + 2) - log ((j : ℝ) + 1)) := by
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (hh0 _)
    have : log ((j : ℝ) + 1) ≤ log ((j : ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith
  have hlogy : x - L2 ≤ log (y : ℝ) := by
    have h1 : log ((N : ℝ) / (x - 1)) ≤ log (y : ℝ) := Real.log_le_log (by positivity) hy_ge
    rw [Real.log_div hNpos.ne' hx1'.ne'] at h1
    have h2 : log (x - 1) ≤ log x := Real.log_le_log hx1' (by linarith)
    rw [← hx] at h1
    rw [hL2]
    linarith
  have hxL : 0 < x - L2 := by linarith
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos (by norm_num)
  have hlog2u := Real.log_two_lt_d9
  have hlog4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h00 := hh0 0
  -- the sum term
  have hterm : (N : ℝ) / log y * (2 * h 0 + ∑ j ∈ Finset.range (N / y),
        h (j + 1) * (log ((j : ℝ) + 2) - log ((j : ℝ) + 1))) ≤
      N / x * ((1 + 2 * L2 / x) * (1.39 + S)) := by
    have h139 : (0 : ℝ) ≤ 1.39 + S := by linarith
    calc (N : ℝ) / log y * (2 * h 0 + ∑ j ∈ Finset.range (N / y),
        h (j + 1) * (log ((j : ℝ) + 2) - log ((j : ℝ) + 1)))
        ≤ N / (x - L2) * (2 * h 0 + ∑ j ∈ Finset.range (N / y),
        h (j + 1) * (log ((j : ℝ) + 2) - log ((j : ℝ) + 1))) := by
          gcongr
      _ ≤ N / (x - L2) * (1.39 + S) := by
          gcongr
          linarith
      _ = N * (1 / (x - L2)) * (1.39 + S) := by ring
      _ ≤ N * (1 / x * (1 + 2 * L2 / x)) * (1.39 + S) := by
          gcongr
          exact frac_bound (by linarith) hL2x
      _ = _ := by ring
  have hsmall : log 2 + ((Nat.sqrt N : ℝ) + 1) * x + 2 * log 2 ≤ 0.01 * (N / x) :=
    small_terms hsq hs hx150 hsq300 (by linarith)
  have hy4 : (N : ℝ) / (x - 1) * log 4 ≤ 1.39 * (N / x) :=
    y_term hNpos.le hx150 (by rw [hlog4]; linarith) (by rw [hlog4]; linarith)
  have hy4' : (y : ℝ) * log 4 ≤ 1.39 * (N / x) + 2 * log 2 := by
    have h0 : (0 : ℝ) ≤ log 4 := by rw [hlog4]; linarith
    have : (y : ℝ) * log 4 ≤ (N / (x - 1) + 1) * log 4 := by gcongr
    rw [add_mul, one_mul, hlog4] at this
    rw [hlog4] at hy4
    rw [hlog4]
    linarith
  rw [← hx] at hcore
  have e : (N : ℝ) / x * (1.4 + (1 + 2 * L2 / x) * (1.39 + S)) =
      0.01 * (N / x) + 1.39 * (N / x) + N / x * ((1 + 2 * L2 / x) * (1.39 + S)) := by ring
  rw [e]
  linarith

/-- the iterated-log factor of the bound -/
noncomputable def Q (r : ℕ) (u : ℝ) : ℝ := log^[r] u * ∏ i ∈ Finset.Icc 3 r, log^[i] u

theorem Q_one (u : ℝ) : Q 1 u = log u := by
  simp [Q]

theorem Q_two (u : ℝ) : Q 2 u = log (log u) := by
  simp [Q]

theorem Q_succ {r : ℕ} (hr : 2 ≤ r) (u : ℝ) : Q (r + 1) u = log (log (log u)) * Q r (log u) := by
  unfold Q
  rw [Function.iterate_succ_apply]
  have h1 : ∏ i ∈ Finset.Icc 3 (r + 1), log^[i] u =
      log^[3] u * ∏ i ∈ Finset.Icc 3 r, log^[i] (log u) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_eq_prod_Ico_succ_bot (by omega),
      ← Finset.Ico_add_one_right_eq_Icc, ← Finset.prod_Ico_add' (fun i => log^[i] u) 3 (r + 1) 1]
    rfl
  rw [h1]
  have h3 : log^[3] u = log (log (log u)) := rfl
  rw [h3]
  ring

theorem Q_pred {r : ℕ} (hr : 3 ≤ r) (u : ℝ) :
    Q r u = log (log (log u)) * Q (r - 1) (log u) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rw [Q_succ (by omega)]
  simp

theorem iter_log_mono : ∀ (i : ℕ) (a b : ℝ), (∀ j < i, 0 < log^[j] a) → a ≤ b →
    log^[i] a ≤ log^[i] b := by
  intro i
  induction i with
  | zero => intro a b _ hab; simpa using hab
  | succ i ih =>
    intro a b hpos hab
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact Real.log_le_log (hpos i (Nat.lt_succ_self i)) (ih a b (fun j hj => hpos j (by omega)) hab)

theorem Q_mono {s : ℕ} {a b : ℝ} (hpos : ∀ j ≤ s, 0 < log^[j] a) (hab : a ≤ b) :
    Q s a ≤ Q s b := by
  unfold Q
  apply mul_le_mul
  · exact iter_log_mono s a b (fun j hj => hpos j hj.le) hab
  · apply Finset.prod_le_prod
    · intro i hi
      exact (hpos i (Finset.mem_Icc.mp hi).2).le
    · intro i hi
      have hi2 := (Finset.mem_Icc.mp hi).2
      exact iter_log_mono i a b (fun j hj => hpos j (by omega)) hab
  · apply Finset.prod_nonneg
    intro i hi
    exact (hpos i (Finset.mem_Icc.mp hi).2).le
  · exact (hpos s le_rfl).le.trans (iter_log_mono s a b (fun j hj => hpos j hj.le) hab)

theorem Q_ge_one {s : ℕ} {a : ℝ} (hpos : ∀ j ≤ s, 1 ≤ log^[j] a) : 1 ≤ Q s a := by
  unfold Q
  have h1 : 1 ≤ ∏ i ∈ Finset.Icc 3 s, log^[i] a := by
    have := Finset.prod_le_prod (s := Finset.Icc 3 s) (f := fun _ => (1 : ℝ))
      (g := fun i => log^[i] a) (fun _ _ => zero_le_one)
      (fun i hi => hpos i (Finset.mem_Icc.mp hi).2)
    simpa using this
  nlinarith [hpos s le_rfl]

theorem exp_e_ge : (12 : ℝ) ≤ exp (exp 1) := by
  have h := Real.exp_one_gt_d9
  have h1 : exp (2.7 : ℝ) ≤ exp (exp 1) := Real.exp_le_exp.mpr (by linarith)
  have h2 : exp (2.7 : ℝ) = exp 1 * exp 1 * exp 0.7 := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  have h3 : (0.7 : ℝ) + 1 ≤ exp 0.7 := Real.add_one_le_exp _
  have h4 : (12 : ℝ) ≤ exp 1 * exp 1 * exp 0.7 := by
    have : (2.7 : ℝ) * 2.7 ≤ exp 1 * exp 1 := by nlinarith
    nlinarith
  linarith

theorem tele (m : ℕ) :
    ∑ j ∈ Finset.range m, (log ((j : ℝ) + 2) - log ((j : ℝ) + 1)) = log ((m : ℝ) + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring_nf

theorem final_two {x L2 l2 : ℝ} (hL : 12 ≤ L2) (hx : x = exp L2) (hl2 : 0 < l2)
    (hl2' : l2 ≤ 0.6932) : 1.4 + (1 + 2 * L2 / x) * (1.39 + l2 * L2) ≤ L2 := by
  have hxpos : 0 < x := by rw [hx]; exact Real.exp_pos _
  have h12 := exp12
  have hx400 : 400 * L2 ^ 2 ≤ x := by
    have h1 : exp L2 = exp 12 * exp (L2 - 12) := by rw [← Real.exp_add]; congr 1; ring
    have h2 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ L2 - 12 by linarith)
    rw [hx, h1]
    have h3 : (150000 : ℝ) * (1 + (L2 - 12) + (L2 - 12) ^ 2 / 2) ≤ exp 12 * exp (L2 - 12) := by
      apply mul_le_mul h12 h2 (by positivity) (by positivity)
    nlinarith [sq_nonneg (L2 - 12)]
  have h5 : 2 * L2 / x * (1.39 + l2 * L2) ≤ 0.01 := by
    have h6 : 1.39 + l2 * L2 ≤ 2 * L2 := by nlinarith
    have h7 : 2 * L2 / x * (1.39 + l2 * L2) ≤ 2 * L2 / x * (2 * L2) := by
      apply mul_le_mul_of_nonneg_left h6 (by positivity)
    have h8 : 2 * L2 / x * (2 * L2) ≤ 0.01 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hxpos]
      nlinarith
    linarith
  nlinarith

theorem case_two {N : ℕ} (hN : ∀ i ≤ 4, 1 ≤ log^[i] (N : ℝ)) :
    (R N : ℝ) * log 2 ≤ N / log N * Q 2 N := by
  have h1 : 1 ≤ log (N : ℝ) := hN 1 (by norm_num)
  have h2 : 1 ≤ log (log (N : ℝ)) := hN 2 (by norm_num)
  have h3 : 1 ≤ log (log (log (N : ℝ))) := hN 3 (by norm_num)
  have h4 : 1 ≤ log (log (log (log (N : ℝ)))) := hN 4 (by norm_num)
  set x := log (N : ℝ) with hx
  set L2 := log x with hL2
  have hL3 : exp 1 ≤ log L2 := (Real.le_log_iff_exp_le (by linarith)).mp h4
  have hL : 12 ≤ L2 := by
    have : exp (exp 1) ≤ L2 := (Real.le_log_iff_exp_le (by linarith)).mp hL3
    linarith [exp_e_ge]
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos (by norm_num)
  have hlog2u := Real.log_two_lt_d9
  have hxpos : 0 < x := by linarith
  have hxe : x = exp L2 := by rw [hL2, Real.exp_log hxpos]
  have hrec := rec_bound (N := N) hx hL2 h1 hL (fun _ => log 2) antitone_const
    (fun _ => hlog2.le) le_rfl
    (fun k _ _ => by
      have : (R k : ℝ) ≤ k := by exact_mod_cast R_le k
      nlinarith)
    (log 2 * L2)
    (fun m hm => by
      rw [← Finset.mul_sum, tele]
      apply mul_le_mul_of_nonneg_left _ hlog2.le
      rw [hL2]
      exact Real.log_le_log (by positivity) hm)
  rw [Q_two]
  have hfin := final_two hL hxe hlog2 (by linarith)
  have hNx : (0 : ℝ) ≤ (N : ℝ) / x := by positivity
  calc (R N : ℝ) * log 2 ≤ N / x * (1.4 + (1 + 2 * L2 / x) * (1.39 + log 2 * L2)) := hrec
    _ ≤ N / x * L2 := mul_le_mul_of_nonneg_left hfin hNx

theorem psi_anti {a b : ℝ} (ha0 : 0 < a) (hab : a ≤ b) (h1 : exp 1 ≤ log a)
    (h2 : exp 1 ≤ log (log a)) :
    log (log (log b)) / log b ≤ log (log (log a)) / log a := by
  have he : (2 : ℝ) ≤ exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hta : 0 < log a := by linarith
  have htab : log a ≤ log b := Real.log_le_log ha0 hab
  have hsab : log (log a) ≤ log (log b) := Real.log_le_log hta htab
  have A1 : log (log b) / log b ≤ log (log a) / log a :=
    Real.log_div_self_antitoneOn (Set.mem_Ici.mpr h1) (Set.mem_Ici.mpr (h1.trans htab)) htab
  have A2 : log (log (log b)) / log (log b) ≤ log (log (log a)) / log (log a) :=
    Real.log_div_self_antitoneOn (Set.mem_Ici.mpr h2) (Set.mem_Ici.mpr (h2.trans hsab)) hsab
  have hsa : 0 < log (log a) := by linarith
  have hsb : 0 < log (log b) := by linarith
  have htb : 0 < log b := by linarith
  have e1 : log (log (log b)) / log b =
      (log (log (log b)) / log (log b)) * (log (log b) / log b) := by
    field_simp
  have e2 : log (log (log a)) / log a =
      (log (log (log a)) / log (log a)) * (log (log a) / log a) := by
    field_simp
  rw [e1, e2]
  have h3 : 0 ≤ log (log (log a)) := Real.log_nonneg (by linarith)
  exact mul_le_mul A2 A1 (by positivity) (by positivity)

/-- convex primitive of `log` -/
noncomputable def Psi (v : ℝ) : ℝ := v * log v - v

theorem Psi_convex {v w : ℝ} (hv : 0 < v) (hw : 0 < w) : (w - v) * log v ≤ Psi w - Psi v := by
  unfold Psi
  have h1 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < w / v by positivity)
  rw [Real.log_div hw.ne' hv.ne', inv_div] at h1
  have h2 : w * (1 - v / w) ≤ w * (log w - log v) := mul_le_mul_of_nonneg_left h1 hw.le
  have h3 : w * (1 - v / w) = w - v := by field_simp
  nlinarith

noncomputable def G (t : ℝ) : ℝ := Psi (log (log t)) - 1 / (t - 1)

theorem g_ineq {k : ℝ} (hk : 2 ≤ k) (h1 : 1 ≤ log k) (h2 : 1 ≤ log (log k)) :
    log (log (log k)) / log k * (log (k + 1) - log k) ≤ G (k + 1) - G k := by
  have hk0 : 0 < k := by linarith
  set a := log k with ha
  set b := log (k + 1) with hb
  set v := log a with hv
  have hab : a ≤ b := Real.log_le_log hk0 (by linarith)
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hv0 : 0 < v := by linarith
  have hvw : v ≤ log b := Real.log_le_log ha0 hab
  have hw0 : 0 < log b := by linarith
  have hba : b - a ≤ 1 / k := by
    rw [hb, ha, ← Real.log_div (by linarith) hk0.ne']
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (k + 1) / k by positivity)
    have e : (k + 1) / k - 1 = 1 / k := by field_simp; ring
    linarith
  have hba0 : 0 ≤ b - a := by linarith
  have hconv := Psi_convex hv0 hw0
  have hlv0 : 0 ≤ log v := Real.log_nonneg h2
  have hlv : log v ≤ a := by
    have := Real.log_le_sub_one_of_pos hv0
    have := Real.log_le_sub_one_of_pos ha0
    linarith
  have hdiff : (b - a) / b ≤ log b - v := by
    have h3 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < b / a by positivity)
    rw [Real.log_div hb0.ne' ha0.ne', inv_div] at h3
    have e : 1 - a / b = (b - a) / b := by field_simp
    linarith
  -- main chain
  have hP : log v * ((b - a) / b) ≤ Psi (log b) - Psi v := by
    have : log v * ((b - a) / b) ≤ (log b - v) * log v := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hdiff hlv0
    linarith
  have hE : log v / a * (b - a) - log v * ((b - a) / b) ≤ 1 / (k - 1) - 1 / k := by
    have e : log v / a * (b - a) - log v * ((b - a) / b) = log v * (b - a) ^ 2 / (a * b) := by
      field_simp
    rw [e]
    have h4 : log v * (b - a) ^ 2 / (a * b) ≤ (b - a) ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : (b - a) ^ 2 * (a * b) = (b - a) ^ 2 * a * b := by ring
      rw [this]
      have h5 : log v * (b - a) ^ 2 ≤ (b - a) ^ 2 * a := by nlinarith [sq_nonneg (b - a)]
      have h6 : (b - a) ^ 2 * a ≤ (b - a) ^ 2 * a * b := by
        have : 0 ≤ (b - a) ^ 2 * a := by positivity
        nlinarith
      linarith
    have h7 : (b - a) ^ 2 ≤ (1 / k) ^ 2 := by
      apply pow_le_pow_left₀ hba0 hba
    have h8 : (1 / k) ^ 2 ≤ 1 / (k - 1) - 1 / k := by
      have hk1 : 0 < k - 1 := by linarith
      have e2 : 1 / (k - 1) - 1 / k = 1 / (k * (k - 1)) := by field_simp; ring
      rw [e2, one_div_pow, one_div, one_div]
      apply inv_anti₀ (by positivity)
      nlinarith
    linarith
  unfold G
  have e3 : k + 1 - 1 = k := by ring
  rw [e3]
  linarith

theorem sum_le_tele (t D : ℕ → ℝ) (hstep : ∀ j, t j ≤ D (j + 1) - D j) (m : ℕ) :
    ∑ j ∈ Finset.range m, t j ≤ D m - D 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    linarith [hstep m]

theorem exp_cube {t : ℝ} (ht : 1536 ≤ t) : 6 * t ^ 3 ≤ exp t := by
  have h1 : exp t = exp (t / 4) ^ 4 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h2 : t / 4 ≤ exp (t / 4) := by linarith [Real.add_one_le_exp (t / 4)]
  have h3 : (t / 4) ^ 4 ≤ exp (t / 4) ^ 4 := pow_le_pow_left₀ (by linarith) h2 4
  rw [h1]
  have h4 : 6 * t ^ 3 ≤ (t / 4) ^ 4 := by
    have : (t / 4) ^ 4 = t ^ 3 * (t / 256) := by ring
    rw [this]
    have h5 : (0 : ℝ) ≤ t ^ 3 := by positivity
    nlinarith
  linarith

theorem final_step {x L2 L3 L4 c l2 : ℝ} (hc : 1 ≤ c) (hL3 : 150000 ≤ L3) (hL4 : 12 ≤ L4)
    (hL4L3 : L4 ≤ L3) (hL3L2 : L3 ≤ L2) (hx : 6 * L2 ^ 3 ≤ x) (hl2 : 0 < l2) (hl2' : l2 ≤ 0.7) :
    1.4 + (1 + 2 * L2 / x) * (1.39 + (l2 * (L3 + 1) + c * (L3 * L4 - L3 + 2))) ≤ c * L3 * L4 := by
  have hL2 : 0 < L2 := by linarith
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity) hx
  have e0 : c * (L3 * L4 - L3 + 2) = c * L3 * L4 - c * L3 + 2 * c := by ring
  have h1 : l2 * (L3 + 1) ≤ 0.7 * (L3 + 1) := by
    apply mul_le_mul_of_nonneg_right hl2' (by linarith)
  have hLL : L3 * L4 ≤ L2 ^ 2 := by nlinarith
  have hcL : 0 ≤ c * L3 * L4 := by positivity
  have hA : 1.39 + (l2 * (L3 + 1) + c * (L3 * L4 - L3 + 2)) ≤ c * (3 * L2 ^ 2) := by
    have h2 : c * (L3 * L4 - L3 + 2) ≤ c * (L2 ^ 2 + 2) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      linarith
    have h3 : 1.39 + 0.7 * (L3 + 1) ≤ c * (2 * L2 ^ 2 - 2) := by
      have : 1.39 + 0.7 * (L3 + 1) ≤ 2 * L2 ^ 2 - 2 := by nlinarith
      have : (2 * L2 ^ 2 - 2) ≤ c * (2 * L2 ^ 2 - 2) := by
        have h4 : 0 ≤ 2 * L2 ^ 2 - 2 := by nlinarith
        nlinarith
      linarith
    have : c * (3 * L2 ^ 2) = c * (L2 ^ 2 + 2) + c * (2 * L2 ^ 2 - 2) := by ring
    linarith
  have hB : 2 * L2 / x * (1.39 + (l2 * (L3 + 1) + c * (L3 * L4 - L3 + 2))) ≤ c := by
    calc 2 * L2 / x * (1.39 + (l2 * (L3 + 1) + c * (L3 * L4 - L3 + 2)))
        ≤ 2 * L2 / x * (c * (3 * L2 ^ 2)) := mul_le_mul_of_nonneg_left hA (by positivity)
      _ = c * (6 * L2 ^ 3 / x) := by ring
      _ ≤ c * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          rw [div_le_one hxpos]
          exact hx
      _ = c := mul_one c
  have h5 : (c - 1) * 150000 ≤ (c - 1) * L3 := by
    apply mul_le_mul_of_nonneg_left hL3 (by linarith)
  have e1 : (1 + 2 * L2 / x) * (1.39 + (l2 * (L3 + 1) + c * (L3 * L4 - L3 + 2))) =
      (1.39 + (l2 * (L3 + 1) + c * (L3 * L4 - L3 + 2))) +
      2 * L2 / x * (1.39 + (l2 * (L3 + 1) + c * (L3 * L4 - L3 + 2))) := by ring
  rw [e1]
  nlinarith

set_option maxHeartbeats 800000 in
theorem step {N : ℕ} {x L2 L3 L4 c : ℝ} (hx : x = log N) (hL2 : L2 = log x) (hL3 : L3 = log L2)
    (hL4 : L4 = log L3) (hx1 : 1 ≤ x) (h21 : 1 ≤ L2) (h31 : 1 ≤ L3) (hL : 12 ≤ L4) (hc : 1 ≤ c)
    (hk : ∀ k : ℕ, L2 ≤ k → (k : ℝ) ≤ x →
      (R k : ℝ) * log 2 ≤ k * (c * log (log (log k)) / log k)) :
    (R N : ℝ) * log 2 ≤ N / x * (c * L3 * L4) := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos (by norm_num)
  have hlog2u := Real.log_two_lt_d9
  have hxpos : 0 < x := by linarith
  have hL2pos : 0 < L2 := by linarith
  have hL3pos : 0 < L3 := by linarith
  have hxe : x = exp L2 := by rw [hL2, Real.exp_log hxpos]
  have hL2e : L2 = exp L3 := by rw [hL3, Real.exp_log hL2pos]
  have hL3e : L3 = exp L4 := by rw [hL4, Real.exp_log hL3pos]
  have hL3big : 150000 ≤ L3 := by rw [hL3e]; exact exp12.trans (Real.exp_le_exp.mpr hL)
  have hL2big : L3 + 1 ≤ L2 := by rw [hL2e]; exact Real.add_one_le_exp L3
  have hL4L3 : L4 + 1 ≤ L3 := by rw [hL3e]; exact Real.add_one_le_exp L4
  have hL2x : 12 ≤ L2 := by linarith
  have he3 : exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  -- the threshold
  set K := ⌈L2⌉₊ with hK
  have hK1 : L2 ≤ K := Nat.le_ceil _
  have hK2 : (K : ℝ) < L2 + 1 := Nat.ceil_lt_add_one hL2pos.le
  have hKpos : 1 ≤ K := by
    have : (1 : ℝ) ≤ K := by linarith
    exact_mod_cast this
  have hbig : ∀ t : ℝ, L2 ≤ t → L3 ≤ log t ∧ L4 ≤ log (log t) := by
    intro t ht
    have h1 : L3 ≤ log t := by rw [hL3]; exact Real.log_le_log hL2pos ht
    have h2 : L4 ≤ log (log t) := by rw [hL4]; exact Real.log_le_log hL3pos h1
    exact ⟨h1, h2⟩
  set h : ℕ → ℝ := fun k =>
    if k < K then log 2 else min (log 2) (c * log (log (log (k : ℝ))) / log (k : ℝ)) with hh_def
  have hanti : Antitone h := by
    intro a b hab
    simp only [hh_def]
    by_cases hb : b < K
    · have ha : a < K := by omega
      rw [if_pos ha, if_pos hb]
    · by_cases ha : a < K
      · rw [if_pos ha, if_neg hb]
        exact min_le_left _ _
      · rw [if_neg ha, if_neg hb]
        apply min_le_min le_rfl
        have haK : L2 ≤ (a : ℝ) := hK1.trans (by exact_mod_cast (not_lt.mp ha))
        obtain ⟨h1, h2⟩ := hbig a haK
        have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
        have := psi_anti (by linarith) hab' (by linarith) (by linarith)
        rw [mul_div_assoc, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left this (by linarith)
  have hnn : ∀ k, 0 ≤ h k := by
    intro k
    simp only [hh_def]
    split_ifs with hkK
    · exact hlog2.le
    · apply le_min hlog2.le
      have hkK' : L2 ≤ (k : ℝ) := hK1.trans (by exact_mod_cast (not_lt.mp hkK))
      obtain ⟨h1, h2⟩ := hbig k hkK'
      have h3 : 0 ≤ log (log (log (k : ℝ))) := Real.log_nonneg (by linarith)
      have h4 : 0 < log (k : ℝ) := by linarith
      have h5 : 0 ≤ c := by linarith
      positivity
  have h0 : h 0 ≤ log 2 := by
    simp only [hh_def]
    rw [if_pos (by omega)]
  have hT : ∀ k : ℕ, 1 ≤ k → (k : ℝ) + 1 ≤ x → (R k : ℝ) * log 2 ≤ k * h k := by
    intro k hk1 hkx
    have hRk : (R k : ℝ) * log 2 ≤ k * log 2 := by
      have : (R k : ℝ) ≤ k := by exact_mod_cast R_le k
      nlinarith
    simp only [hh_def]
    split_ifs with hkK
    · exact hRk
    · have hkK' : L2 ≤ (k : ℝ) := hK1.trans (by exact_mod_cast (not_lt.mp hkK))
      rw [mul_min_of_nonneg _ _ (Nat.cast_nonneg k)]
      exact le_min hRk (hk k hkK' (by linarith))
  -- the sum bound
  have hS : ∀ m : ℕ, (m : ℝ) + 1 ≤ x →
      ∑ j ∈ Finset.range m, h (j + 1) * (log ((j : ℝ) + 2) - log ((j : ℝ) + 1)) ≤
        log 2 * (L3 + 1) + c * (L3 * L4 - L3 + 2) := by
    intro m hm
    set D : ℕ → ℝ := fun j =>
      if j + 1 ≤ K then log 2 * log ((j : ℝ) + 1)
      else log 2 * log (K : ℝ) + c * (G ((j : ℝ) + 1) - G (K : ℝ)) with hD
    have hstep : ∀ j, h (j + 1) * (log ((j : ℝ) + 2) - log ((j : ℝ) + 1)) ≤ D (j + 1) - D j := by
      intro j
      have e4 : (j : ℝ) + 2 = (j : ℝ) + 1 + 1 := by ring
      by_cases hj : j + 2 ≤ K
      · have e1 : D (j + 1) = log 2 * log ((j : ℝ) + 1 + 1) := by
          simp only [hD]
          rw [if_pos (by omega)]
          push_cast
          rfl
        have e2 : D j = log 2 * log ((j : ℝ) + 1) := by
          simp only [hD]
          rw [if_pos (by omega)]
        have e3 : h (j + 1) = log 2 := by
          simp only [hh_def]
          rw [if_pos (by omega)]
        rw [e1, e2, e3, e4]
        linarith
      · have hjK : K ≤ j + 1 := by omega
        have e1 : D (j + 1) = log 2 * log (K : ℝ) + c * (G ((j : ℝ) + 1 + 1) - G (K : ℝ)) := by
          simp only [hD]
          rw [if_neg (by omega)]
          push_cast
          rfl
        have e2 : D j = log 2 * log (K : ℝ) + c * (G ((j : ℝ) + 1) - G (K : ℝ)) := by
          simp only [hD]
          by_cases hjK' : j + 1 ≤ K
          · have hjeq : j + 1 = K := by omega
            have hc' : ((j : ℝ) + 1) = (K : ℝ) := by exact_mod_cast hjeq
            rw [if_pos hjK', hc']
            ring
          · rw [if_neg hjK']
        have hkK' : L2 ≤ (j : ℝ) + 1 := hK1.trans (by exact_mod_cast hjK)
        obtain ⟨h1, h2⟩ := hbig _ hkK'
        have hg := g_ineq (k := (j : ℝ) + 1) (by linarith) (by linarith) (by linarith)
        have e3 : h (j + 1) ≤ c * log (log (log ((j : ℝ) + 1))) / log ((j : ℝ) + 1) := by
          simp only [hh_def]
          rw [if_neg (by omega)]
          push_cast
          exact min_le_right _ _
        have hdl : 0 ≤ log ((j : ℝ) + 2) - log ((j : ℝ) + 1) := by
          have := Real.log_le_log (show (0 : ℝ) < (j : ℝ) + 1 by positivity)
            (show (j : ℝ) + 1 ≤ (j : ℝ) + 2 by linarith)
          linarith
        rw [e1, e2]
        calc h (j + 1) * (log ((j : ℝ) + 2) - log ((j : ℝ) + 1))
            ≤ c * log (log (log ((j : ℝ) + 1))) / log ((j : ℝ) + 1) *
                (log ((j : ℝ) + 2) - log ((j : ℝ) + 1)) := mul_le_mul_of_nonneg_right e3 hdl
          _ = c * (log (log (log ((j : ℝ) + 1))) / log ((j : ℝ) + 1) *
                (log ((j : ℝ) + 1 + 1) - log ((j : ℝ) + 1))) := by rw [e4]; ring
          _ ≤ c * (G ((j : ℝ) + 1 + 1) - G ((j : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_left hg (by linarith)
          _ = _ := by ring
    have htele := sum_le_tele _ D hstep m
    have hD0 : D 0 = 0 := by
      simp only [hD]
      rw [if_pos (by omega)]
      simp
    have hlogK : log (K : ℝ) ≤ L3 + 1 := by
      have h1 : (K : ℝ) ≤ exp 1 * L2 := by nlinarith [Real.add_one_le_exp (1 : ℝ)]
      have h2 := Real.log_le_log (by linarith : (0 : ℝ) < K) h1
      rw [Real.log_mul (Real.exp_pos 1).ne' hL2pos.ne', Real.log_exp, ← hL3] at h2
      linarith
    have hcnn : 0 ≤ c * (L3 * L4 - L3 + 1) := by
      apply mul_nonneg (by linarith)
      nlinarith
    have hDm : D m ≤ log 2 * (L3 + 1) + c * (L3 * L4 - L3 + 2) := by
      simp only [hD]
      split_ifs with hmK
      · have h1 : log ((m : ℝ) + 1) ≤ log (K : ℝ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast hmK)
        have h2 : log 2 * log ((m : ℝ) + 1) ≤ log 2 * (L3 + 1) :=
          mul_le_mul_of_nonneg_left (h1.trans hlogK) hlog2.le
        nlinarith
      · have hmK' : (K : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast (by omega : K ≤ m + 1)
        obtain ⟨h1, h2⟩ := hbig ((m : ℝ) + 1) (hK1.trans hmK')
        obtain ⟨h1K, h2K⟩ := hbig (K : ℝ) hK1
        have h3 : log (log ((m : ℝ) + 1)) ≤ L3 := by
          rw [hL3, hL2]
          apply Real.log_le_log (by linarith)
          exact Real.log_le_log (by positivity) hm
        have hP1 : Psi (log (log ((m : ℝ) + 1))) ≤ Psi L3 := by
          have := Psi_convex (v := log (log ((m : ℝ) + 1))) (w := L3) (by linarith) hL3pos
          have h4 : 0 ≤ (L3 - log (log ((m : ℝ) + 1))) * log (log (log ((m : ℝ) + 1))) := by
            apply mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
          linarith
        have hP2 : 0 ≤ Psi (log (log (K : ℝ))) := by
          unfold Psi
          have hv : exp 1 ≤ log (log (K : ℝ)) := by linarith
          have : 1 ≤ log (log (log (K : ℝ))) := (Real.le_log_iff_exp_le (by linarith)).mpr hv
          nlinarith
        have hG1 : G ((m : ℝ) + 1) ≤ Psi L3 := by
          unfold G
          have : 0 ≤ 1 / ((m : ℝ) + 1 - 1) := by
            have : (0 : ℝ) ≤ (m : ℝ) + 1 - 1 := by simp
            positivity
          linarith
        have hG2 : - G (K : ℝ) ≤ 1 := by
          unfold G
          have : 1 / ((K : ℝ) - 1) ≤ 1 := by
            rw [div_le_one (by linarith)]
            linarith
          linarith
        have hPsiL3 : Psi L3 = L3 * L4 - L3 := by unfold Psi; rw [← hL4]
        have h5 : c * (G ((m : ℝ) + 1) - G (K : ℝ)) ≤ c * (L3 * L4 - L3 + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          linarith
        have h6 : log 2 * log (K : ℝ) ≤ log 2 * (L3 + 1) :=
          mul_le_mul_of_nonneg_left hlogK hlog2.le
        nlinarith
    linarith
  have hrec := rec_bound hx hL2 hx1 hL2x h hanti hnn h0 hT _ hS
  have hx6 : 6 * L2 ^ 3 ≤ x := by rw [hxe]; exact exp_cube (by linarith)
  have hfin := final_step (x := x) (L2 := L2) hc hL3big hL (by linarith) (by linarith) hx6 hlog2
    (by linarith)
  have hNx : (0 : ℝ) ≤ (N : ℝ) / x := by positivity
  exact hrec.trans (mul_le_mul_of_nonneg_left hfin hNx)

set_option maxHeartbeats 800000 in
theorem main : ∀ r : ℕ, 1 ≤ r → ∀ N : ℕ, (∀ i ≤ 2 * r, 1 ≤ log^[i] (N : ℝ)) →
    (R N : ℝ) * log 2 ≤ N / log N * Q r N := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    intro N hN
    have h1 : 1 ≤ log (N : ℝ) := hN 1 (by norm_num)
    rw [Q_one]
    have e : (N : ℝ) / log N * log N = N := by field_simp
    rw [e]
    have hR : (R N : ℝ) ≤ N := by exact_mod_cast R_le N
    have hlog2 := Real.log_two_lt_d9
    have hlog2' : (0 : ℝ) < log 2 := Real.log_pos (by norm_num)
    nlinarith [Nat.cast_nonneg (α := ℝ) (R N)]
  | succ r hr ih =>
    intro N hN
    rcases Nat.eq_or_lt_of_le hr with h1 | h2
    · subst h1
      exact case_two (fun i hi => hN i (by omega))
    · have hr2 : 2 ≤ r := h2
      have hN1 : 1 ≤ log (N : ℝ) := hN 1 (by omega)
      have hN2 : 1 ≤ log (log (N : ℝ)) := hN 2 (by omega)
      have hN3 : 1 ≤ log (log (log (N : ℝ))) := hN 3 (by omega)
      have hN4 : 1 ≤ log (log (log (log (N : ℝ)))) := hN 4 (by omega)
      have hN5 : 1 ≤ log (log (log (log (log (N : ℝ))))) := hN 5 (by omega)
      have hN6 : 1 ≤ log (log (log (log (log (log (N : ℝ)))))) := hN 6 (by omega)
      have hL2i : ∀ i, i + 2 ≤ 2 * (r + 1) → 1 ≤ log^[i] (log (log (N : ℝ))) := by
        intro i hi
        have := hN (i + 2) hi
        rwa [Function.iterate_succ_apply, Function.iterate_succ_apply] at this
      rw [Q_succ hr2]
      set x := log (N : ℝ) with hx
      set L2 := log x with hL2
      set L3 := log L2 with hL3
      set L4 := log L3 with hL4
      have hL4big : 12 ≤ L4 := by
        have h5 : exp 1 ≤ log L4 := (Real.le_log_iff_exp_le (by linarith)).mp hN6
        have : exp (exp 1) ≤ L4 := (Real.le_log_iff_exp_le (by linarith)).mp h5
        linarith [exp_e_ge]
      have hL4pos : 0 < L4 := by linarith
      set c := Q r x / L4 with hc
      have hQx : Q r x = c * L4 := by rw [hc]; field_simp
      have hcr : 3 ≤ r → c = Q (r - 1) L2 := by
        intro hr3
        have e : Q r x = L4 * Q (r - 1) L2 := Q_pred hr3 x
        rw [hc, e]
        field_simp
      have hc1 : 1 ≤ c := by
        rcases Nat.eq_or_lt_of_le hr2 with h | h
        · rw [hc, ← h, Q_two, le_div_iff₀ hL4pos]
          have := Real.log_le_sub_one_of_pos (show 0 < L3 by linarith)
          linarith
        · rw [hcr h]
          exact Q_ge_one (fun j hj => hL2i j (by omega))
      have hstep := step (N := N) (c := c) hx hL2 hL3 hL4 hN1 hN2 hN3 hL4big hc1 (by
        intro k hk1 hk2
        have hkpos : (0 : ℝ) < k := by linarith
        have hki : ∀ i ≤ 2 * r, 1 ≤ log^[i] (k : ℝ) := by
          intro i hi
          have h1 := iter_log_mono i L2 k
            (fun j hj => by have := hL2i j (by omega); linarith) hk1
          have h2 := hL2i i (by omega)
          linarith
        have hih := ih k hki
        have hlk : 1 ≤ log (k : ℝ) := hki 1 (by omega)
        have hllk : 1 ≤ log (log (k : ℝ)) := hki 2 (by omega)
        have hlllk : 1 ≤ log (log (log (k : ℝ))) := hki 3 (by omega)
        have hQk : Q r k ≤ c * log (log (log (k : ℝ))) := by
          rcases Nat.eq_or_lt_of_le hr2 with h | h
          · rw [hc, ← h, Q_two, Q_two]
            have hv1 : L4 ≤ log (log (k : ℝ)) := by
              rw [hL4, hL3]
              apply Real.log_le_log (by linarith)
              exact Real.log_le_log (by linarith) hk1
            have hv2 : log (log (k : ℝ)) ≤ L3 := by
              rw [hL3, hL2]
              apply Real.log_le_log (by linarith)
              exact Real.log_le_log hkpos hk2
            have he3 : exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
            have hanti := Real.log_div_self_antitoneOn
              (Set.mem_Ici.mpr (show exp 1 ≤ log (log (k : ℝ)) by linarith))
              (Set.mem_Ici.mpr (show exp 1 ≤ L3 by linarith)) hv2
            simp only at hanti
            rw [← hL4, div_le_div_iff₀ (by linarith) (by linarith)] at hanti
            rw [div_mul_eq_mul_div, le_div_iff₀ hL4pos]
            linarith
          · rw [hcr h, Q_pred h, mul_comm]
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            apply Q_mono
            · intro j hj
              have := hki (j + 1) (by omega)
              rw [Function.iterate_succ_apply] at this
              linarith
            · exact Real.log_le_log hkpos hk2
        have hkl : (0 : ℝ) ≤ (k : ℝ) / log k := by positivity
        calc (R k : ℝ) * log 2 ≤ k / log k * Q r k := hih
          _ ≤ k / log k * (c * log (log (log (k : ℝ)))) := mul_le_mul_of_nonneg_left hQk hkl
          _ = k * (c * log (log (log (k : ℝ))) / log k) := by ring)
      calc (R N : ℝ) * log 2 ≤ N / x * (c * L3 * L4) := hstep
        _ = N / x * (L3 * Q r x) := by rw [hQx]; ring

end OMA.Helpers

theorem OMA.solution : type_of% @Erdos321.erdos_321.variants.upper := by
  intro N r hr hrN
  have h := OMA.Helpers.main r hr N hrN
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (Erdos321.R N : ℝ) ≤ (N / Real.log N * OMA.Helpers.Q r N) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    exact h
  calc (Erdos321.R N : ℝ) ≤ (N / Real.log N * OMA.Helpers.Q r N) / Real.log 2 := h1
    _ = 1 / Real.log 2 * Real.log^[r] N * N / Real.log N *
        ∏ i ∈ Finset.Icc 3 r, Real.log^[i] (N : ℝ) := by
      unfold OMA.Helpers.Q
      ring
