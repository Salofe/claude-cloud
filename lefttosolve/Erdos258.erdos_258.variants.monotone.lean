import FormalConjectures.ErdosProblems.«258»

/-!
# Erdős 258, monotone variant (Erdős–Straus): own formalisation

Let `2 ≤ a 1 ≤ a 2 ≤ ...` tend to infinity; then `∑ d(n) / (a 1 * ... * a n)` is irrational.

Assume the sum is `p / b`.  With `T N` the normalised tail, `I N = b * T N` is a positive
integer and `a (N + 1) * I N = b * d (N + 1) + I (N + 1)` (`Data`).

* First moments of the divisor function along arithmetic progressions: `sum_divisors_AP`
  (coprime residue, only divisors coprime to the modulus occur), `sum_divisors_AP_gcd`
  (general residue, extra factor `d (gcd)`), `coprime_harmonic` (the harmonic sum over
  integers coprime to `M!` is at most `(1 + log (M s)) / H_M`).
* `regimeG`: if `log m ≤ C * a m` for some large `m`, average `I N` over `N ∈ [m, 2m]`,
  `N ≡ 0 mod M!`; the average is `< 1`.
* `regimeCRT`: if `a` is constant `= t` on a long stretch, the Chinese remainder theorem gives
  a class of `N` with `t ^ k ∣ d (N + j)` for `1 ≤ j ≤ k` (`k` primes with exponent `t - 1`
  for each `j`), so `t ^ k ∣ I (N + k)`, while the average of `I (N + k)` over the class is
  `< t ^ k`.
* `crt_params`: if `320 * a n < log₂ n` eventually, monotonicity gives a stretch and
  suitable `t`, `k` (`exists_stretch`, `e_le`, `size_le`).
-/

open Filter Finset

namespace OMA.Helpers

/-- the product `a 1 * ... * a n` -/
def P (a : ℕ → ℕ) (n : ℕ) : ℕ := ∏ i ∈ Finset.Icc 1 n, a i

lemma P_zero (a : ℕ → ℕ) : P a 0 = 1 := by simp [P]

lemma P_succ (a : ℕ → ℕ) (n : ℕ) : P a (n + 1) = P a n * a (n + 1) := by
  unfold P
  rw [Finset.prod_Icc_succ_top (by omega)]

lemma P_pos (a : ℕ → ℕ) (h2 : ∀ n, 2 ≤ a n) (n : ℕ) : 0 < P a n := by
  unfold P
  exact Finset.prod_pos (fun i _ => by have := h2 i; omega)

lemma P_add_ge (a : ℕ → ℕ) (t N : ℕ) (h : ∀ j, N < j → t ≤ a j) (n : ℕ) :
    P a N * t ^ n ≤ P a (N + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, P_succ, pow_succ, ← mul_assoc]
    exact Nat.mul_le_mul ih (h _ (by omega))

/-- the `n`-th term of the series -/
noncomputable def term (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((n + 1).divisors.card : ℝ) / ((P a (n + 1) : ℕ) : ℝ)

lemma term_nonneg (a : ℕ → ℕ) (n : ℕ) : 0 ≤ term a n := by
  unfold term; positivity

lemma term_le (a : ℕ → ℕ) (t N : ℕ) (ht : 0 < t) (hN : 0 < P a N) (h : ∀ j, N < j → t ≤ a j)
    (n : ℕ) :
    term a (N + n) ≤ ((N + n + 1 : ℕ) : ℝ) / ((P a N : ℝ) * (t : ℝ) ^ (n + 1)) := by
  unfold term
  have h1 : ((N + n + 1).divisors.card : ℝ) ≤ ((N + n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.card_divisors_le_self _
  have h2 : (P a N : ℝ) * (t : ℝ) ^ (n + 1) ≤ (P a (N + n + 1) : ℝ) := by
    have := P_add_ge a t N h (n + 1)
    rw [← add_assoc] at this
    exact_mod_cast this
  have h3 : (0 : ℝ) < (P a N : ℝ) * (t : ℝ) ^ (n + 1) := by positivity
  gcongr

lemma summable_term (a : ℕ → ℕ) (h2 : ∀ n, 2 ≤ a n) : Summable (term a) := by
  have hs : Summable (fun n : ℕ => ((n : ℝ)) ^ 1 * ((1 : ℝ) / 2) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
  have hs' := (summable_nat_add_iff 1).mpr hs
  refine Summable.of_nonneg_of_le (term_nonneg a) (fun n => ?_) hs'
  have := term_le a 2 0 (by norm_num) (P_pos a h2 0) (fun j _ => h2 j) n
  simp only [zero_add, P_zero, Nat.cast_one, one_mul] at this
  refine this.trans (le_of_eq ?_)
  push_cast
  rw [pow_one, one_div, inv_pow]
  field_simp

/-- normalised tail -/
noncomputable def T (a : ℕ → ℕ) (N : ℕ) : ℝ := (P a N : ℝ) * ∑' n, term a (N + n)

lemma summable_shift (a : ℕ → ℕ) (h2 : ∀ n, 2 ≤ a n) (N : ℕ) :
    Summable (fun n => term a (N + n)) := by
  have := (summable_nat_add_iff N).mpr (summable_term a h2)
  simpa [add_comm] using this

lemma T_zero (a : ℕ → ℕ) : T a 0 = ∑' n, term a n := by
  simp [T, P_zero]

lemma T_rec (a : ℕ → ℕ) (h2 : ∀ n, 2 ≤ a n) (N : ℕ) :
    (a (N + 1) : ℝ) * T a N = ((N + 1).divisors.card : ℝ) + T a (N + 1) := by
  unfold T
  rw [(summable_shift a h2 N).tsum_eq_zero_add]
  have hP : (P a (N + 1) : ℝ) = (P a N : ℝ) * (a (N + 1) : ℝ) := by
    exact_mod_cast P_succ a N
  have hpos : (0 : ℝ) < (P a (N + 1) : ℝ) := by exact_mod_cast P_pos a h2 (N + 1)
  have e1 : (fun b : ℕ => term a (N + (b + 1))) = fun b => term a (N + 1 + b) := by
    funext b; congr 1; omega
  rw [e1, add_zero]
  have e2 : term a N * (P a (N + 1) : ℝ) = ((N + 1).divisors.card : ℝ) := by
    unfold term; field_simp
  rw [hP] at e2 ⊢
  linear_combination e2

lemma T_pos (a : ℕ → ℕ) (h2 : ∀ n, 2 ≤ a n) (N : ℕ) : 0 < T a N := by
  unfold T
  have hpos : (0 : ℝ) < (P a N : ℝ) := by exact_mod_cast P_pos a h2 N
  refine mul_pos hpos ?_
  refine (summable_shift a h2 N).tsum_pos (fun n => term_nonneg a _) 0 ?_
  unfold term
  have h1 : 0 < (N + 0 + 1).divisors.card := by
    rw [Finset.card_pos]; exact ⟨1, by simp⟩
  have h3 : (0 : ℝ) < (P a (N + 0 + 1) : ℝ) := by exact_mod_cast P_pos a h2 _
  positivity

lemma T_le (a : ℕ → ℕ) (h2 : ∀ n, 2 ≤ a n) (N : ℕ) (h4 : ∀ j, N < j → 4 ≤ a j) :
    T a N ≤ (N : ℝ) + 1 := by
  unfold T
  have hpos : (0 : ℝ) < (P a N : ℝ) := by exact_mod_cast P_pos a h2 N
  have hb : ∀ n : ℕ, term a (N + n) ≤ (((N : ℝ) + 1) / (4 * (P a N : ℝ))) * ((1 : ℝ) / 2) ^ n := by
    intro n
    refine (term_le a 4 N (by norm_num) (P_pos a h2 N) h4 n).trans ?_
    have hn : ((N + n + 1 : ℕ) : ℝ) ≤ ((N : ℝ) + 1) * 2 ^ n := by
      have h1 : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
      have h3 : N + n + 1 ≤ (N + 1) * 2 ^ n := by nlinarith
      exact_mod_cast h3
    rw [div_le_iff₀ (by positivity)]
    have e : ((N : ℝ) + 1) / (4 * (P a N : ℝ)) * ((1 : ℝ) / 2) ^ n * ((P a N : ℝ) * ((4 : ℕ) : ℝ) ^ (n + 1))
        = ((N : ℝ) + 1) * 2 ^ n := by
      have : ((4 : ℕ) : ℝ) ^ (n + 1) = 4 * (2 : ℝ) ^ n * 2 ^ n := by
        push_cast
        rw [pow_succ, show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]; ring
      rw [this, one_div, inv_pow]
      field_simp
    rw [e]; exact hn
  have hsum : Summable (fun n : ℕ => (((N : ℝ) + 1) / (4 * (P a N : ℝ))) * ((1 : ℝ) / 2) ^ n) :=
    summable_geometric_two.mul_left _
  have := (summable_shift a h2 N).tsum_le_tsum hb hsum
  rw [tsum_mul_left, tsum_geometric_two] at this
  calc (P a N : ℝ) * ∑' n, term a (N + n)
      ≤ (P a N : ℝ) * (((N : ℝ) + 1) / (4 * (P a N : ℝ)) * 2) := by gcongr
    _ = ((N : ℝ) + 1) / 2 := by field_simp; ring
    _ ≤ (N : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
      linarith

/-- at least half of the divisors are at most `sqrt X` -/
lemma card_divisors_le (n X : ℕ) (hn : n ≤ X) :
    n.divisors.card ≤ 2 * ((Finset.Icc 1 (Nat.sqrt X)).filter (fun l => l ∣ n)).card := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  set s := Nat.sqrt X with hs
  have h1 : (n.divisors.filter (fun l => l ≤ s)).card ≤
      ((Finset.Icc 1 s).filter (fun l => l ∣ n)).card := by
    apply Finset.card_le_card
    intro l hl
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc] at hl ⊢
    exact ⟨⟨Nat.pos_of_dvd_of_pos hl.1.1 hpos, hl.2⟩, hl.1.1⟩
  have h2 : (n.divisors.filter (fun l => ¬ l ≤ s)).card ≤
      ((Finset.Icc 1 s).filter (fun l => l ∣ n)).card := by
    apply Finset.card_le_card_of_injOn (fun l => n / l)
    · intro l hl
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_divisors, not_le] at hl
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq]
      obtain ⟨⟨hdvd, _⟩, hls⟩ := hl
      have hlpos : 0 < l := Nat.pos_of_dvd_of_pos hdvd hpos
      refine ⟨⟨Nat.div_pos (Nat.le_of_dvd hpos hdvd) hlpos, ?_⟩, Nat.div_dvd_of_dvd hdvd⟩
      have hX : X < (s + 1) * (s + 1) := Nat.lt_succ_sqrt X
      have : n / l < s + 1 := by
        rw [Nat.div_lt_iff_lt_mul hlpos]
        calc n ≤ X := hn
          _ < (s + 1) * (s + 1) := hX
          _ ≤ (s + 1) * l := Nat.mul_le_mul_left _ hls
      omega
    · intro l hl l' hl' h
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_divisors] at hl hl'
      have e1 := Nat.div_mul_cancel hl.1.1
      have e2 := Nat.div_mul_cancel hl'.1.1
      dsimp only at h
      rw [h] at e1
      have hq : 0 < n / l' :=
        Nat.div_pos (Nat.le_of_dvd hpos hl'.1.1) (Nat.pos_of_dvd_of_pos hl'.1.1 hpos)
      exact Nat.eq_of_mul_eq_mul_left hq (e1.trans e2.symm)
  have h3 := Finset.card_filter_add_card_filter_not (s := n.divisors) (fun l => l ≤ s)
  omega

/-- counting multiples of `l` in an arithmetic progression with coprime residue -/
lemma count_dvd_le (r A Z l : ℕ) (hl : 0 < l) (hco : Nat.Coprime r A) :
    ((Finset.range Z).filter (fun i => l ∣ r + i * A)).card ≤
      if Nat.Coprime l A then Z / l + 1 else 0 := by
  split_ifs with hlA
  · rcases Finset.eq_empty_or_nonempty ((Finset.range Z).filter (fun i => l ∣ r + i * A))
      with h | ⟨i₀, hi₀⟩
    · simp [h]
    · have hsub : (Finset.range Z).filter (fun i => l ∣ r + i * A) ⊆
          (Finset.range Z).filter (fun i => i ≡ i₀ [MOD l]) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi hi₀ ⊢
        refine ⟨hi.1, ?_⟩
        have h1 : r + i * A ≡ r + i₀ * A [MOD l] := by
          rw [Nat.ModEq, Nat.mod_eq_zero_of_dvd hi.2, Nat.mod_eq_zero_of_dvd hi₀.2]
        have h2 : i * A ≡ i₀ * A [MOD l] := Nat.ModEq.add_left_cancel' r h1
        exact Nat.ModEq.cancel_right_of_coprime hlA h2
      calc _ ≤ _ := Finset.card_le_card hsub
        _ = Nat.count (fun i => i ≡ i₀ [MOD l]) Z := (Nat.count_eq_card_filter_range _ _).symm
        _ = Z / l + if i₀ % l < Z % l then 1 else 0 := Nat.count_modEq_card Z hl i₀
        _ ≤ Z / l + 1 := by split_ifs <;> omega
  · rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ hdvd
    apply hlA
    have hg1 : Nat.gcd l A ∣ r := by
      have h1 : Nat.gcd l A ∣ r + i * A := (Nat.gcd_dvd_left l A).trans hdvd
      have h2 : Nat.gcd l A ∣ i * A := Dvd.dvd.mul_left (Nat.gcd_dvd_right l A) i
      exact (Nat.dvd_add_left h2).mp h1
    have : Nat.gcd l A ∣ Nat.gcd r A := Nat.dvd_gcd hg1 (Nat.gcd_dvd_right l A)
    rw [hco] at this
    exact Nat.dvd_one.mp this

/-- first moment of the divisor function along an arithmetic progression, coprime case -/
lemma sum_divisors_AP (r A Z X : ℕ) (hco : Nat.Coprime r A) (hX : ∀ i < Z, r + i * A ≤ X) :
    ∑ i ∈ Finset.range Z, ((r + i * A).divisors.card : ℝ) ≤
      2 * ∑ l ∈ (Finset.Icc 1 (Nat.sqrt X)).filter (fun l => Nat.Coprime l A),
        ((Z : ℝ) / l + 1) := by
  have hnat : ∑ i ∈ Finset.range Z, (r + i * A).divisors.card ≤
      2 * ∑ l ∈ (Finset.Icc 1 (Nat.sqrt X)).filter (fun l => Nat.Coprime l A), (Z / l + 1) := by
    calc ∑ i ∈ Finset.range Z, (r + i * A).divisors.card
        ≤ ∑ i ∈ Finset.range Z,
            2 * ((Finset.Icc 1 (Nat.sqrt X)).filter (fun l => l ∣ r + i * A)).card :=
          Finset.sum_le_sum (fun i hi => card_divisors_le _ X (hX i (Finset.mem_range.mp hi)))
      _ = 2 * ∑ l ∈ Finset.Icc 1 (Nat.sqrt X),
            ((Finset.range Z).filter (fun i => l ∣ r + i * A)).card := by
          rw [← Finset.mul_sum]; congr 1
          simp_rw [Finset.card_filter]
          exact Finset.sum_comm
      _ ≤ 2 * ∑ l ∈ Finset.Icc 1 (Nat.sqrt X), (if Nat.Coprime l A then Z / l + 1 else 0) := by
          gcongr with l hl
          exact count_dvd_le r A Z l (by simp only [Finset.mem_Icc] at hl; omega) hco
      _ = _ := by rw [Finset.sum_filter]
  calc ∑ i ∈ Finset.range Z, ((r + i * A).divisors.card : ℝ)
      = ((∑ i ∈ Finset.range Z, (r + i * A).divisors.card : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ ((2 * ∑ l ∈ (Finset.Icc 1 (Nat.sqrt X)).filter (fun l => Nat.Coprime l A),
          (Z / l + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ ≤ _ := by
        push_cast
        gcongr with l hl
        exact Nat.cast_div_le

lemma card_divisors_mul_le (m n : ℕ) :
    (m * n).divisors.card ≤ m.divisors.card * n.divisors.card := by
  rw [Nat.divisors_mul]; exact Finset.card_mul_le

/-- first moment of the divisor function along an arithmetic progression, general case -/
lemma sum_divisors_AP_gcd (r A Z X : ℕ) (hA : 0 < A) (hX : ∀ i < Z, r + i * A ≤ X) :
    ∑ i ∈ Finset.range Z, ((r + i * A).divisors.card : ℝ) ≤
      ((Nat.gcd r A).divisors.card : ℝ) *
        (2 * ∑ l ∈ Finset.Icc 1 (Nat.sqrt X), ((Z : ℝ) / l + 1)) := by
  have hg : 0 < Nat.gcd r A := Nat.gcd_pos_of_pos_right r hA
  have hr' : Nat.gcd r A * (r / Nat.gcd r A) = r := Nat.mul_div_cancel' (Nat.gcd_dvd_left r A)
  have hA' : Nat.gcd r A * (A / Nat.gcd r A) = A := Nat.mul_div_cancel' (Nat.gcd_dvd_right r A)
  have hco : Nat.Coprime (r / Nat.gcd r A) (A / Nat.gcd r A) := Nat.coprime_div_gcd_div_gcd hg
  generalize Nat.gcd r A = g at hg hr' hA' hco ⊢
  generalize r / g = r' at hr' hco
  generalize A / g = A' at hA' hco
  have hterm : ∀ i, r + i * A = g * (r' + i * A') := by
    intro i
    rw [← hr', ← hA']
    ring
  calc ∑ i ∈ Finset.range Z, ((r + i * A).divisors.card : ℝ)
      ≤ ∑ i ∈ Finset.range Z,
          (g.divisors.card : ℝ) * ((r' + i * A').divisors.card : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [hterm i]
        have h := card_divisors_mul_le g (r' + i * A')
        calc ((g * (r' + i * A')).divisors.card : ℝ)
            ≤ ((g.divisors.card * (r' + i * A').divisors.card : ℕ) : ℝ) := Nat.cast_le.mpr h
          _ = _ := by push_cast; ring
    _ = (g.divisors.card : ℝ) *
          ∑ i ∈ Finset.range Z, ((r' + i * A').divisors.card : ℝ) := by rw [Finset.mul_sum]
    _ ≤ _ := by
        gcongr
        refine (sum_divisors_AP r' A' Z X hco ?_).trans ?_
        · intro i hi
          have := hX i hi
          rw [hterm i] at this
          exact le_trans (Nat.le_mul_of_pos_left _ hg) this
        · exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun l _ _ => by positivity)) (by norm_num)

/-- harmonic sums over integers coprime to `M!` are small -/
lemma coprime_harmonic (M s : ℕ) :
    (∑ j ∈ Finset.Icc 1 M, (1 : ℝ) / j) *
      (∑ l ∈ (Finset.Icc 1 s).filter (fun l => Nat.Coprime l M.factorial), (1 : ℝ) / l)
      ≤ ∑ n ∈ Finset.Icc 1 (M * s), (1 : ℝ) / n := by
  classical
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  have himg : ∑ x ∈ Finset.Icc 1 M ×ˢ (Finset.Icc 1 s).filter
        (fun l => Nat.Coprime l M.factorial), (1 : ℝ) / x.1 * ((1 : ℝ) / x.2)
      = ∑ n ∈ (Finset.Icc 1 M ×ˢ (Finset.Icc 1 s).filter
        (fun l => Nat.Coprime l M.factorial)).image (fun x => x.1 * x.2), (1 : ℝ) / n := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro x _
      push_cast
      rw [one_div_mul_one_div]
    · intro x hx y hy hxy
      simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_Icc, Set.mem_prod,
        Finset.mem_coe, Set.mem_ofPred_eq] at hx hy
      obtain ⟨⟨hx1, hx1'⟩, ⟨hx2, _⟩, hxc⟩ := hx
      obtain ⟨⟨hy1, hy1'⟩, ⟨hy2, _⟩, hyc⟩ := hy
      dsimp only at hxy
      have hxd : x.1 ∣ M.factorial := Nat.dvd_factorial (by omega) hx1'
      have hyd : y.1 ∣ M.factorial := Nat.dvd_factorial (by omega) hy1'
      have c1 : Nat.Coprime x.1 y.2 := Nat.Coprime.coprime_dvd_left hxd hyc.symm
      have c2 : Nat.Coprime y.1 x.2 := Nat.Coprime.coprime_dvd_left hyd hxc.symm
      have d1 : x.1 ∣ y.1 := c1.dvd_of_dvd_mul_right (hxy ▸ Dvd.intro _ rfl)
      have d2 : y.1 ∣ x.1 := c2.dvd_of_dvd_mul_right (hxy ▸ Dvd.intro _ rfl)
      have e1 : x.1 = y.1 := Nat.dvd_antisymm d1 d2
      rw [e1] at hxy
      have e2 : x.2 = y.2 := Nat.eq_of_mul_eq_mul_left (by omega) hxy
      exact Prod.ext e1 e2
  rw [himg]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_filter, Finset.mem_Icc,
      Prod.exists] at hn
    obtain ⟨j, l, ⟨⟨hj1, hj2⟩, ⟨hl1, hl2⟩, _⟩, rfl⟩ := hn
    simp only [Finset.mem_Icc]
    exact ⟨Nat.mul_pos (by omega) (by omega), Nat.mul_le_mul hj2 hl2⟩
  · intro n _ _; positivity


/-- a strictly increasing sequence of primes above `P0` with `q n ≤ 2 ^ (n + 1) * P0` -/
lemma exists_primes (P0 : ℕ) (hP : 0 < P0) :
    ∃ q : ℕ → ℕ, (∀ n, (q n).Prime) ∧ StrictMono q ∧ (∀ n, P0 < q n) ∧
      ∀ n, q n ≤ 2 ^ (n + 1) * P0 := by
  have hB : ∀ m : ℕ, ∃ p, m = 0 ∨ (p.Prime ∧ m < p ∧ p ≤ 2 * m) := by
    intro m
    rcases Nat.eq_zero_or_pos m with h | h
    · exact ⟨0, Or.inl h⟩
    · obtain ⟨p, hp⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
      exact ⟨p, Or.inr hp⟩
  choose f hf' using hB
  have hf : ∀ m, 0 < m → ((f m).Prime ∧ m < f m ∧ f m ≤ 2 * m) :=
    fun m hm => (hf' m).resolve_left (by omega)
  have key : ∀ n, (f^[n + 1] P0).Prime ∧ P0 < f^[n + 1] P0 ∧ f^[n + 1] P0 ≤ 2 ^ (n + 1) * P0 := by
    intro n
    induction n with
    | zero =>
      obtain ⟨h1, h2, h3⟩ := hf P0 hP
      simpa using ⟨h1, h2, h3⟩
    | succ n ih =>
      obtain ⟨_, i2, i3⟩ := ih
      obtain ⟨h1, h2, h3⟩ := hf (f^[n + 1] P0) (by omega)
      rw [Function.iterate_succ_apply']
      refine ⟨h1, by omega, ?_⟩
      calc f (f^[n + 1] P0) ≤ 2 * f^[n + 1] P0 := h3
        _ ≤ 2 * (2 ^ (n + 1) * P0) := Nat.mul_le_mul_left _ i3
        _ = 2 ^ (n + 1 + 1) * P0 := by ring
  refine ⟨fun n => f^[n + 1] P0, fun n => (key n).1, ?_, fun n => (key n).2.1, fun n => (key n).2.2⟩
  apply strictMono_nat_of_lt_succ
  intro n
  have := (hf (f^[n + 1] P0) (by have := (key n).2.1; omega)).2.1
  show f^[n + 1] P0 < f^[n + 1 + 1] P0
  rw [Function.iterate_succ_apply' f (n + 1)]
  exact this

/-- the CRT system -/
lemma exists_crt (q : ℕ → ℕ) (hq : ∀ n, (q n).Prime) (hinj : StrictMono q) (t k α : ℕ) :
    ∃ x, ∀ n < k * k, x + α + (n / k + 1) ≡ q n ^ (t - 1) [MOD q n ^ t] := by
  have pp : Set.Pairwise (↑(Finset.range (k * k)) : Set ℕ)
      (Function.onFun Nat.Coprime (fun n => q n ^ t)) := by
    intro i _ j _ hij
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (hq i) (hq j)).mpr (hinj.injective.ne hij))
  obtain ⟨x, hx⟩ := Nat.chineseRemainderOfFinset
    (fun n => q n ^ (t - 1) + (q n ^ t - 1) * (α + (n / k + 1))) (fun n => q n ^ t)
    (Finset.range (k * k)) (fun i _ => pow_ne_zero _ (hq i).ne_zero) pp
  refine ⟨x, fun n hn => ?_⟩
  have h := hx n (Finset.mem_range.mpr hn)
  have h1 := h.add_right (α + (n / k + 1))
  have e : q n ^ (t - 1) + (q n ^ t - 1) * (α + (n / k + 1)) + (α + (n / k + 1))
      = q n ^ (t - 1) + q n ^ t * (α + (n / k + 1)) := by
    have h1 : 1 ≤ q n ^ t := Nat.one_le_pow _ _ (hq n).pos
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le h1
    rw [hc]
    simp only [Nat.add_sub_cancel_left]
    ring
  rw [e] at h1
  have h2 : q n ^ (t - 1) + q n ^ t * (α + (n / k + 1)) ≡ q n ^ (t - 1) [MOD q n ^ t] := by
    simp [Nat.ModEq, Nat.add_mul_mod_self_left]
  rw [← add_assoc] at h1
  exact h1.trans h2

lemma factorization_of_modEq (p t n : ℕ) (hp : p.Prime) (ht : 1 ≤ t)
    (h : n ≡ p ^ (t - 1) [MOD p ^ t]) : n ≠ 0 ∧ n.factorization p = t - 1 := by
  have hdvd : p ^ (t - 1) ∣ n := (h.dvd_iff (pow_dvd_pow p (Nat.sub_le t 1))).mpr dvd_rfl
  have hnd : ¬ p ^ t ∣ n := by
    intro hd
    have h1 : p ^ t ∣ p ^ (t - 1) := (h.dvd_iff dvd_rfl).mp hd
    have h2 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h1
    omega
  have hn : n ≠ 0 := by rintro rfl; exact hnd (dvd_zero _)
  refine ⟨hn, ?_⟩
  have h1 := (hp.pow_dvd_iff_le_factorization hn).mp hdvd
  have h2 : ¬ t ≤ n.factorization p := fun h' => hnd ((hp.pow_dvd_iff_le_factorization hn).mpr h')
  omega

lemma pow_dvd_card_divisors (n t : ℕ) (S : Finset ℕ) (hn : n ≠ 0) (ht : 2 ≤ t)
    (hS : ∀ p ∈ S, p.Prime ∧ n.factorization p = t - 1) : t ^ S.card ∣ n.divisors.card := by
  rw [Nat.card_divisors hn]
  have hsub : S ⊆ n.primeFactors := by
    intro p hp
    obtain ⟨hpp, hf⟩ := hS p hp
    rw [Nat.mem_primeFactors]
    exact ⟨hpp, (hpp.dvd_iff_one_le_factorization hn).mpr (by omega), hn⟩
  have h1 : ∏ p ∈ S, (n.factorization p + 1) = t ^ S.card := by
    rw [Finset.prod_congr rfl (fun p hp => by rw [(hS p hp).2]; omega :
      ∀ p ∈ S, n.factorization p + 1 = t), Finset.prod_const]
  rw [← h1]
  exact Finset.prod_dvd_prod_of_subset _ _ _ hsub

/-- all positions `1..k` get `k` primes, so `t ^ k ∣ d (x + j)` -/
lemma pow_dvd_of_crt (q : ℕ → ℕ) (hq : ∀ n, (q n).Prime) (hinj : StrictMono q) (t k x : ℕ)
    (ht : 2 ≤ t)
    (hx : ∀ n < k * k, x + (n / k + 1) ≡ q n ^ (t - 1) [MOD q n ^ t]) (j : ℕ) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) : t ^ k ∣ (x + j).divisors.card := by
  classical
  have hk : 0 < k := by omega
  set S : Finset ℕ := (Finset.range k).image (fun i => q ((j - 1) * k + i)) with hS
  have hcard : S.card = k := by
    rw [hS, Finset.card_image_of_injective, Finset.card_range]
    intro i i' h
    have := hinj.injective h
    omega
  have hidx : ∀ i < k, (j - 1) * k + i < k * k ∧ ((j - 1) * k + i) / k + 1 = j := by
    intro i hi
    constructor
    · calc (j - 1) * k + i < (j - 1) * k + k := by omega
        _ = (j - 1 + 1) * k := by ring
        _ ≤ k * k := Nat.mul_le_mul_right _ (by omega)
    · rw [Nat.mul_comm, Nat.mul_add_div hk, Nat.div_eq_of_lt hi]
      omega
  have hne : x + j ≠ 0 := by omega
  have := pow_dvd_card_divisors (x + j) t S hne ht (by
    intro p hp
    rw [hS, Finset.mem_image] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    rw [Finset.mem_range] at hi
    obtain ⟨h1, h2⟩ := hidx i hi
    have h3 := hx _ h1
    rw [h2] at h3
    exact ⟨hq _, (factorization_of_modEq _ t _ (hq _) (by omega) h3).2⟩)
  rwa [hcard] at this

/-- small shifts are coprime to the modulus -/
lemma coprime_shift (q : ℕ → ℕ) (hq : ∀ n, (q n).Prime) (t k P0 x w : ℕ) (ht : 2 ≤ t)
    (hP : ∀ n, P0 < q n)
    (hx : ∀ n < k * k, x + (n / k + 1) ≡ q n ^ (t - 1) [MOD q n ^ t])
    (hw1 : k < w) (hw : w ≤ P0 + 1) :
    Nat.Coprime (x + w) (∏ n ∈ Finset.range (k * k), q n ^ t) := by
  apply Nat.Coprime.prod_right
  intro n hn
  rw [Finset.mem_range] at hn
  apply Nat.Coprime.pow_right
  apply Nat.Coprime.symm
  rw [(hq n).coprime_iff_not_dvd]
  intro hd
  have h1 : q n ∣ x + (n / k + 1) :=
    ((hx n hn).dvd_iff (dvd_pow_self _ (by omega))).mpr (dvd_pow_self _ (by omega))
  have hjk : n / k + 1 ≤ k := by
    have : n / k < k := Nat.div_lt_of_lt_mul hn
    omega
  have hj1 : 1 ≤ n / k + 1 := Nat.le_add_left 1 _
  generalize n / k + 1 = j at h1 hjk hj1
  have h2 : q n ∣ (x + w) - (x + j) := Nat.dvd_sub hd h1
  have h3 : (x + w) - (x + j) = w - j := by omega
  rw [h3] at h2
  have h4 := Nat.le_of_dvd (by omega) h2
  have := hP n
  omega

lemma card_divisors_prod_le (s : Finset ℕ) (f : ℕ → ℕ) (c : ℕ)
    (h : ∀ n ∈ s, (f n).divisors.card ≤ c) : (∏ n ∈ s, f n).divisors.card ≤ c ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
    exact (card_divisors_mul_le _ _).trans
      (Nat.mul_le_mul (h a (Finset.mem_insert_self a s))
        (ih (fun n hn => h n (Finset.mem_insert_of_mem hn))))

lemma card_divisors_modulus (q : ℕ → ℕ) (hq : ∀ n, (q n).Prime) (t K : ℕ) :
    (∏ n ∈ Finset.range K, q n ^ t).divisors.card ≤ (t + 1) ^ K := by
  have := card_divisors_prod_le (Finset.range K) (fun n => q n ^ t) (t + 1) (by
    intro n _
    rw [Nat.divisors_prime_pow (hq n), Finset.card_map, Finset.card_range])
  simpa using this

lemma modulus_le (q : ℕ → ℕ) (P1 t K : ℕ) (hq : ∀ n < K, q n ≤ P1) :
    ∏ n ∈ Finset.range K, q n ^ t ≤ P1 ^ (t * K) := by
  calc ∏ n ∈ Finset.range K, q n ^ t ≤ ∏ _n ∈ Finset.range K, P1 ^ t :=
        Finset.prod_le_prod' (fun n hn => Nat.pow_le_pow_left (hq n (Finset.mem_range.mp hn)) t)
    _ = P1 ^ (t * K) := by rw [Finset.prod_const, Finset.card_range, ← pow_mul]

/-- the data extracted from a rational value of the series -/
structure Data (a : ℕ → ℕ) (b : ℕ) (I : ℕ → ℤ) : Prop where
  hb : 0 < b
  h2 : ∀ n, 2 ≤ a n
  mono : Monotone a
  pos : ∀ N, 1 ≤ I N
  recur : ∀ N, (a (N + 1) : ℤ) * I N = (b : ℤ) * ((N + 1).divisors.card : ℤ) + I (N + 1)
  le : ∀ N, (∀ j, N < j → 4 ≤ a j) → I N ≤ (b : ℤ) * ((N : ℤ) + 1)

lemma expand {a : ℕ → ℕ} {b : ℕ} {I : ℕ → ℤ} (D : Data a b I) (t N : ℕ) (ht : 4 ≤ t)
    (hge : ∀ j, N < j → t ≤ a j) (Y : ℕ) :
    (I N : ℝ) ≤ (b : ℝ) * ∑ y ∈ Finset.range Y,
        ((N + 1 + y).divisors.card : ℝ) / (t : ℝ) ^ (y + 1)
      + (I (N + Y) : ℝ) / (t : ℝ) ^ Y := by
  induction Y with
  | zero => simp
  | succ Y ih =>
    refine ih.trans ?_
    rw [Finset.sum_range_succ, mul_add]
    have hrec := D.recur (N + Y)
    have hrecR : (a (N + Y + 1) : ℝ) * (I (N + Y) : ℝ)
        = (b : ℝ) * ((N + Y + 1).divisors.card : ℝ) + (I (N + Y + 1) : ℝ) := by
      exact_mod_cast hrec
    have hta : (t : ℝ) ≤ (a (N + Y + 1) : ℝ) := by exact_mod_cast hge _ (by omega)
    have hIpos : (0 : ℝ) < (I (N + Y) : ℝ) := by
      have := D.pos (N + Y)
      exact_mod_cast (by omega : (0 : ℤ) < I (N + Y))
    have htpos : (0 : ℝ) < (t : ℝ) := by
      have : 0 < t := by omega
      exact_mod_cast this
    have h1 : (t : ℝ) * (I (N + Y) : ℝ)
        ≤ (b : ℝ) * ((N + Y + 1).divisors.card : ℝ) + (I (N + Y + 1) : ℝ) := by
      rw [← hrecR]; exact mul_le_mul_of_nonneg_right hta hIpos.le
    have e2 : N + 1 + Y = N + Y + 1 := by omega
    have h2 : (I (N + Y) : ℝ) / (t : ℝ) ^ Y
        ≤ (b : ℝ) * (((N + 1 + Y).divisors.card : ℝ) / (t : ℝ) ^ (Y + 1))
          + (I (N + (Y + 1)) : ℝ) / (t : ℝ) ^ (Y + 1) := by
      rw [div_le_iff₀ (by positivity)]
      have e : ((b : ℝ) * (((N + 1 + Y).divisors.card : ℝ) / (t : ℝ) ^ (Y + 1))
          + (I (N + (Y + 1)) : ℝ) / (t : ℝ) ^ (Y + 1)) * (t : ℝ) ^ Y
          = ((b : ℝ) * ((N + 1 + Y).divisors.card : ℝ) + (I (N + (Y + 1)) : ℝ)) / t := by
        rw [pow_succ]; field_simp
      rw [e, le_div_iff₀ htpos, e2, ← add_assoc N Y 1]
      linarith [h1]
    linarith

lemma expand' {a : ℕ → ℕ} {b : ℕ} {I : ℕ → ℤ} (D : Data a b I) (t N : ℕ) (ht : 4 ≤ t)
    (hge : ∀ j, N < j → t ≤ a j) (Y : ℕ) (hY : N + Y + 1 ≤ t ^ Y) :
    (I N : ℝ) ≤ (b : ℝ) * ∑ y ∈ Finset.range Y,
        ((N + 1 + y).divisors.card : ℝ) / (t : ℝ) ^ (y + 1) + (b : ℝ) := by
  refine (expand D t N ht hge Y).trans ?_
  have h1 : (I (N + Y) : ℝ) ≤ (b : ℝ) * (((N + Y : ℕ) : ℝ) + 1) := by
    have := D.le (N + Y) (fun j hj => le_trans ht (hge j (by omega)))
    exact_mod_cast this
  have htpos : (0 : ℝ) < (t : ℝ) ^ Y := by
    have : 0 < t := by omega
    positivity
  have h2 : (((N + Y : ℕ) : ℝ) + 1) ≤ (t : ℝ) ^ Y := by exact_mod_cast hY
  have h3 : (I (N + Y) : ℝ) / (t : ℝ) ^ Y ≤ (b : ℝ) := by
    rw [div_le_iff₀ htpos]
    calc (I (N + Y) : ℝ) ≤ (b : ℝ) * (((N + Y : ℕ) : ℝ) + 1) := h1
      _ ≤ (b : ℝ) * (t : ℝ) ^ Y := by gcongr
  linarith

lemma dvd_chain {a : ℕ → ℕ} {b : ℕ} {I : ℕ → ℤ} (D : Data a b I) (t N k : ℕ)
    (hconst : ∀ j, 1 ≤ j → j ≤ k → a (N + j) = t)
    (hd : ∀ j, 1 ≤ j → j ≤ k → t ^ k ∣ (N + j).divisors.card) :
    ((t : ℤ) ^ k) ∣ I (N + k) := by
  have key : ∀ j, j ≤ k → ((t : ℤ) ^ j) ∣ I (N + j) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have hrec := D.recur (N + j)
      have ha : a (N + j + 1) = t := hconst (j + 1) (by omega) hj
      rw [ha] at hrec
      have hI : I (N + (j + 1)) = (t : ℤ) * I (N + j)
          - (b : ℤ) * ((N + j + 1).divisors.card : ℤ) := by
        rw [← add_assoc]; linarith
      rw [hI]
      apply dvd_sub
      · rw [pow_succ']; exact mul_dvd_mul_left _ h1
      · apply Dvd.dvd.mul_left
        have := hd (j + 1) (by omega) hj
        have h2 : t ^ (j + 1) ∣ (N + (j + 1)).divisors.card := (pow_dvd_pow t hj).trans this
        exact_mod_cast h2
  exact key k le_rfl

lemma exists_stretch (a : ℕ → ℕ) (hmono : Monotone a) (m l V : ℕ)
    (hV : a (m + (V + 1) * l) ≤ V) :
    ∃ α, m ≤ α ∧ α + l ≤ m + (V + 1) * l ∧ ∀ n, α ≤ n → n < α + l → a n = a α := by
  by_contra h
  push Not at h
  have key : ∀ i, i ≤ V + 1 → i ≤ a (m + i * l) := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have hle : m + i * l + l ≤ m + (V + 1) * l := by
        have : (i + 1) * l ≤ (V + 1) * l := Nat.mul_le_mul_right l hi
        calc m + i * l + l = m + (i + 1) * l := by ring
          _ ≤ m + (V + 1) * l := by omega
      obtain ⟨n, hn1, hn2, hn3⟩ := h (m + i * l) (Nat.le_add_right _ _) hle
      have h2 : a (m + i * l) ≤ a n := hmono hn1
      have h3 : a n ≤ a (m + (i + 1) * l) := hmono (by
        calc n ≤ m + i * l + l := hn2.le
          _ = m + (i + 1) * l := by ring)
      omega
  have := key (V + 1) le_rfl
  omega

lemma geom_le (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (Y : ℕ) :
    ∑ y ∈ Finset.range Y, x ^ (y + 1) ≤ 2 * x := by
  have key : ∑ y ∈ Finset.range Y, x ^ (y + 1) ≤ 2 * x - 2 * x ^ (Y + 1) := by
    induction Y with
    | zero => simp
    | succ Y ih =>
      rw [Finset.sum_range_succ]
      have h1 : x ^ (Y + 1 + 1) = x ^ (Y + 1) * x := pow_succ _ _
      have h2 : 0 ≤ x ^ (Y + 1) := pow_nonneg hx0 _
      nlinarith
  have : 0 ≤ x ^ (Y + 1) := pow_nonneg hx0 _
  linarith

lemma harm_le (n : ℕ) : ∑ l ∈ Finset.Icc 1 n, (1 : ℝ) / l ≤ 1 + Real.log n := by
  have := harmonic_le_one_add_log n
  rw [harmonic_eq_sum_Icc] at this
  push_cast at this
  simpa [one_div] using this

lemma log_five_mul_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log ((5 * m : ℕ) : ℝ) ≤ (Nat.log 2 m : ℝ) + 3 := by
  have h1 : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have h2 : ((5 * m : ℕ) : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 m + 4) := by
    have h3 : 5 * m ≤ 2 ^ (Nat.log 2 m + 4) := by
      have : 2 ^ (Nat.log 2 m + 4) = 8 * 2 ^ (Nat.log 2 m + 1) := by ring
      omega
    exact_mod_cast h3
  have hpos : (0 : ℝ) < ((5 * m : ℕ) : ℝ) := by
    have : 0 < 5 * m := by omega
    exact_mod_cast this
  have h3 := Real.log_le_log hpos h2
  rw [Real.log_pow] at h3
  have hl2 : Real.log 2 ≤ 3 / 4 := by have := Real.log_two_lt_d9; linarith
  have hl0 : (0 : ℝ) ≤ (Nat.log 2 m : ℝ) := Nat.cast_nonneg _
  push_cast at h3 ⊢
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (Nat.log 2 m : ℝ) + 4)
    (by linarith : (0 : ℝ) ≤ 3 / 4 - Real.log 2)]

lemma log_sqrt_le (X : ℕ) (hX : 1 ≤ X) :
    Real.log (Nat.sqrt X : ℝ) ≤ Real.log (X : ℝ) / 2 := by
  have hs : 0 < Nat.sqrt X := Nat.sqrt_pos.mpr hX
  have h1 : Nat.sqrt X * Nat.sqrt X ≤ X := Nat.sqrt_le X
  have h2 : (Nat.sqrt X : ℝ) * (Nat.sqrt X : ℝ) ≤ (X : ℝ) := by exact_mod_cast h1
  have hpos : (0 : ℝ) < (Nat.sqrt X : ℝ) := by exact_mod_cast hs
  have h3 := Real.log_le_log (mul_pos hpos hpos) h2
  rw [Real.log_mul hpos.ne' hpos.ne'] at h3
  linarith

lemma W_le (Z X : ℕ) (hX : 1 ≤ X) (hZ : 2 * Nat.sqrt X ≤ Z) :
    2 * ∑ l ∈ Finset.Icc 1 (Nat.sqrt X), ((Z : ℝ) / l + 1)
      ≤ (Z : ℝ) * (3 + Real.log (X : ℝ)) := by
  rw [Finset.sum_add_distrib]
  have h1 : ∑ l ∈ Finset.Icc 1 (Nat.sqrt X), (Z : ℝ) / l
      = (Z : ℝ) * ∑ l ∈ Finset.Icc 1 (Nat.sqrt X), (1 : ℝ) / l := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring
  have h2 : ∑ _l ∈ Finset.Icc 1 (Nat.sqrt X), (1 : ℝ) = (Nat.sqrt X : ℝ) := by simp
  rw [h1, h2]
  have h3 := harm_le (Nat.sqrt X)
  have h4 := log_sqrt_le X hX
  have h5 : (2 * (Nat.sqrt X : ℝ)) ≤ (Z : ℝ) := by exact_mod_cast hZ
  have hZ0 : (0 : ℝ) ≤ (Z : ℝ) := Nat.cast_nonneg _
  have h6 := mul_le_mul_of_nonneg_left (h3.trans (add_le_add_right h4 1)) hZ0
  nlinarith

lemma sum_I_le {a : ℕ → ℕ} {b : ℕ} {I : ℕ → ℤ} (D : Data a b I) (t r A Z Y : ℕ) (ht : 4 ≤ t)
    (hge : ∀ j, r < j → t ≤ a j) (hY : ∀ i < Z, r + i * A + Y + 1 ≤ t ^ Y) :
    ∑ i ∈ Finset.range Z, (I (r + i * A) : ℝ) ≤
      (b : ℝ) * ∑ y ∈ Finset.range Y,
        (∑ i ∈ Finset.range Z, ((r + 1 + y + i * A).divisors.card : ℝ)) / (t : ℝ) ^ (y + 1)
      + (Z : ℝ) * b := by
  have hper : ∀ i ∈ Finset.range Z, (I (r + i * A) : ℝ) ≤
      (b : ℝ) * ∑ y ∈ Finset.range Y,
        ((r + 1 + y + i * A).divisors.card : ℝ) / (t : ℝ) ^ (y + 1) + (b : ℝ) := by
    intro i hi
    have h := expand' D t (r + i * A) ht
      (fun j hj => hge j (lt_of_le_of_lt (Nat.le_add_right _ _) hj)) Y
      (hY i (Finset.mem_range.mp hi))
    have e : ∀ y, r + i * A + 1 + y = r + 1 + y + i * A := by intro y; ring
    simpa only [e] using h
  refine (Finset.sum_le_sum hper).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
  simp only [Finset.sum_div, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma four_mul_le (m : ℕ) (hm : 1 ≤ m) : 4 * m + 2 ≤ 4 ^ (2 * m) := by
  have h1 : 2 * m < 2 ^ (2 * m) := Nat.lt_two_pow_self
  have h2 : 2 ≤ 2 ^ (2 * m) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (4 : ℕ) ^ (2 * m) = 2 ^ (2 * m) * 2 ^ (2 * m) := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, Nat.mul_pow]
  rw [h3]
  nlinarith

lemma regimeG_arith (b C0 t Z s g M L H Scop A1 S2 Tl : ℝ) (hb : 1 ≤ b) (hC0 : 1 ≤ C0)
    (hZ : 1 ≤ Z) (hs : 2 * s ≤ Z) (ht1 : 8 * b ≤ t)
    (ht2 : 16 * b * g * (C0 + 2) ≤ t) (ht3 : 5 + 2 * M ≤ t) (hg0 : 0 ≤ g) (hScop0 : 0 ≤ Scop)
    (hL : L ≤ C0 * t + 3)
    (hH : 8 * b * C0 ≤ H) (hcop : H * Scop ≤ 1 + (M + L / 2))
    (hsum1 : Z * t ≤ b * A1 + S2) (hsum2 : S2 ≤ b * Tl + Z * b)
    (hA1 : A1 ≤ 2 * (Z * Scop + s))
    (htail : Tl ≤ g * (Z * (3 + L)) * (2 * (1 / t))) : False := by
  have ht0 : 0 < t := by linarith
  have hZ0 : 0 ≤ Z := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hA : 8 * b * Scop ≤ t := by
    have h2 : 8 * b * C0 * Scop ≤ H * Scop := mul_le_mul_of_nonneg_right hH hScop0
    have h5 : t ≤ C0 * t := le_mul_of_one_le_left ht0.le hC0
    have h3 : C0 * (8 * b * Scop) ≤ C0 * t := by linarith
    exact le_of_mul_le_mul_left h3 (by linarith)
  have hC : b * Tl ≤ Z * t / 8 := by
    have h1 : (3 + L) ≤ (C0 + 2) * t := by linarith
    have h2 : Tl ≤ g * (Z * ((C0 + 2) * t)) * (2 * (1 / t)) := htail.trans (by gcongr)
    have h3 : g * (Z * ((C0 + 2) * t)) * (2 * (1 / t)) = 2 * g * Z * (C0 + 2) := by
      field_simp
    rw [h3] at h2
    have h4 : b * Tl ≤ b * (2 * g * Z * (C0 + 2)) := mul_le_mul_of_nonneg_left h2 hb0
    have h5 := mul_le_mul_of_nonneg_left ht2 hZ0
    linarith
  have p1 := mul_le_mul_of_nonneg_left hA hZ0
  have p2 := mul_le_mul_of_nonneg_left ht1 hZ0
  have p3 := mul_le_mul_of_nonneg_left hs hb0
  have p4 := mul_le_mul_of_nonneg_left hA1 hb0
  have p5 : 8 * 1 ≤ t * Z := mul_le_mul (by linarith) hZ (by norm_num) ht0.le
  linarith

/-- the regime `a m ≥ c log m` -/
lemma regimeG {a : ℕ → ℕ} {b : ℕ} {I : ℕ → ℤ} (D : Data a b I) (M C0 m : ℕ) (hC0 : 1 ≤ C0)
    (hM1 : 1 ≤ M)
    (hH : (8 * b * C0 : ℝ) ≤ ∑ j ∈ Finset.Icc 1 M, (1 : ℝ) / j)
    (hlog : Nat.log 2 m ≤ C0 * a m)
    (ht1 : 8 * b ≤ a m)
    (ht2 : 16 * b * (M.factorial).divisors.card * (C0 + 2) ≤ a m)
    (ht3 : 5 + 2 * M ≤ a m)
    (hm : 80 * M.factorial ^ 2 ≤ m) : False := by
  have hb := D.hb
  have hQpos : 0 < M.factorial := Nat.factorial_pos M
  have ht4 : 4 ≤ a m := by omega
  have hQ1 : 1 ≤ M.factorial ^ 2 := Nat.one_le_pow _ _ hQpos
  have hm1 : 1 ≤ m := by omega
  have hmQ : M.factorial ≤ m := by nlinarith
  have hsq : Nat.sqrt (5 * m) * Nat.sqrt (5 * m) ≤ 5 * m := Nat.sqrt_le _
  have hZs : 2 * Nat.sqrt (5 * m) ≤ m / M.factorial := by
    by_contra hcon
    push Not at hcon
    have h1 : m < M.factorial * (m / M.factorial + 1) := Nat.lt_mul_div_succ m hQpos
    have h3 : m < M.factorial * (2 * Nat.sqrt (5 * m)) :=
      lt_of_lt_of_le h1 (Nat.mul_le_mul_left _ hcon)
    have h4 : m * m < (M.factorial * (2 * Nat.sqrt (5 * m)))
        * (M.factorial * (2 * Nat.sqrt (5 * m))) := Nat.mul_self_lt_mul_self h3
    have h5 : (M.factorial * (2 * Nat.sqrt (5 * m))) * (M.factorial * (2 * Nat.sqrt (5 * m)))
        = 4 * M.factorial ^ 2 * (Nat.sqrt (5 * m) * Nat.sqrt (5 * m)) := by ring
    have h6 : 4 * M.factorial ^ 2 * (Nat.sqrt (5 * m) * Nat.sqrt (5 * m))
        ≤ 4 * M.factorial ^ 2 * (5 * m) := Nat.mul_le_mul_left _ hsq
    have h7 : 4 * M.factorial ^ 2 * (5 * m) = 20 * M.factorial ^ 2 * m := by ring
    have h8 : 20 * M.factorial ^ 2 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
    have h9 := calc m * m < _ := h4
      _ = _ := h5
      _ ≤ _ := h6
      _ = _ := h7
      _ ≤ m * m := h8
    exact lt_irrefl _ h9
  have hZ1 : 1 ≤ m / M.factorial := Nat.div_pos hmQ hQpos
  have hbase1 : m < M.factorial * (m / M.factorial + 1) := Nat.lt_mul_div_succ m hQpos
  have hbase2 : ∀ i, i < m / M.factorial →
      M.factorial * (m / M.factorial + 1) + i * M.factorial ≤ 2 * m := by
    intro i hi
    have h1 : M.factorial * (m / M.factorial) ≤ m := Nat.mul_div_le m _
    have h2 : i * M.factorial ≤ (m / M.factorial - 1) * M.factorial :=
      Nat.mul_le_mul_right _ (by omega)
    have h3 : M.factorial * (m / M.factorial + 1) + (m / M.factorial - 1) * M.factorial
        = 2 * (M.factorial * (m / M.factorial)) := by
      obtain ⟨z, hz⟩ : ∃ z, m / M.factorial = z + 1 := ⟨m / M.factorial - 1, by omega⟩
      rw [hz]; simp only [Nat.add_sub_cancel]; ring
    omega
  generalize hQ : M.factorial = Q at *
  generalize hZ : m / Q = Z at *
  generalize hbase : Q * (Z + 1) = base at *
  generalize ht : a m = t at *
  -- step 1: lower bound for each term
  have hI1 : ∀ i ∈ Finset.range Z, (t : ℝ) ≤
      (b : ℝ) * ((base + 1 + i * Q).divisors.card : ℝ) + (I (base + 1 + i * Q) : ℝ) := by
    intro i hi
    have hrec := D.recur (base + i * Q)
    have hpos := D.pos (base + i * Q)
    have hta : t ≤ a (base + i * Q + 1) := by rw [← ht]; exact D.mono (by omega)
    have e : base + i * Q + 1 = base + 1 + i * Q := by ring
    rw [e] at hrec hta
    have hrecR : (a (base + 1 + i * Q) : ℝ) * (I (base + i * Q) : ℝ)
        = (b : ℝ) * ((base + 1 + i * Q).divisors.card : ℝ) + (I (base + 1 + i * Q) : ℝ) := by
      exact_mod_cast hrec
    have h1 : (1 : ℝ) ≤ (I (base + i * Q) : ℝ) := by exact_mod_cast hpos
    have h2 : (t : ℝ) ≤ (a (base + 1 + i * Q) : ℝ) := by exact_mod_cast hta
    have h3 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
    have h4 : (t : ℝ) * 1 ≤ (a (base + 1 + i * Q) : ℝ) * (I (base + i * Q) : ℝ) :=
      mul_le_mul h2 h1 zero_le_one (h3.trans h2)
    linarith
  have hsum1 : (Z : ℝ) * t ≤
      (b : ℝ) * ∑ i ∈ Finset.range Z, ((base + 1 + i * Q).divisors.card : ℝ)
        + ∑ i ∈ Finset.range Z, (I (base + 1 + i * Q) : ℝ) := by
    have := Finset.sum_le_sum hI1
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum] at this
    exact this
  have hY : ∀ i < Z, base + 1 + i * Q + 2 * m + 1 ≤ t ^ (2 * m) := by
    intro i hi
    have h1 := hbase2 i hi
    calc base + 1 + i * Q + 2 * m + 1 ≤ 4 * m + 2 := by omega
      _ ≤ 4 ^ (2 * m) := four_mul_le m hm1
      _ ≤ t ^ (2 * m) := Nat.pow_le_pow_left ht4 _
  have hsum2 := sum_I_le D t (base + 1) Q Z (2 * m) ht4
    (fun j hj => by rw [← ht]; exact D.mono (by omega)) hY
  -- step 2: the first divisor sum
  have hco : Nat.Coprime (base + 1) Q := by
    rw [← hbase]
    have := (Nat.coprime_mul_right_add_left 1 Q (Z + 1)).mpr (Nat.coprime_one_left Q)
    rwa [Nat.mul_comm] at this
  have hA1 := sum_divisors_AP (base + 1) Q Z (5 * m) hco
    (fun i hi => by have := hbase2 i hi; omega)
  generalize hs : Nat.sqrt (5 * m) = s at *
  have hs1 : 1 ≤ s := by rw [← hs]; exact Nat.sqrt_pos.mpr (by omega)
  have hFsum : ∑ l ∈ (Finset.Icc 1 s).filter (fun l => Nat.Coprime l Q), ((Z : ℝ) / l + 1)
      ≤ (Z : ℝ) * ∑ l ∈ (Finset.Icc 1 s).filter (fun l => Nat.Coprime l Q), (1 : ℝ) / l
        + s := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    have h1 : ∑ l ∈ (Finset.Icc 1 s).filter (fun l => Nat.Coprime l Q), (Z : ℝ) / l
        = ∑ l ∈ (Finset.Icc 1 s).filter (fun l => Nat.Coprime l Q), (Z : ℝ) * (1 / l) :=
      Finset.sum_congr rfl (fun l _ => by ring)
    have h2 : ∑ _l ∈ (Finset.Icc 1 s).filter (fun l => Nat.Coprime l Q), (1 : ℝ) ≤ s := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      have : ((Finset.Icc 1 s).filter (fun l => Nat.Coprime l Q)).card ≤ s :=
        (Finset.card_filter_le _ _).trans (by simp)
      exact_mod_cast this
    rw [h1]; linarith
  have hcop := coprime_harmonic M s
  rw [hQ] at hcop
  have hhar := harm_le (M * s)
  have hL : Real.log ((5 * m : ℕ) : ℝ) ≤ (C0 : ℝ) * t + 3 := by
    have h1 := log_five_mul_le m hm1
    have h2 : (Nat.log 2 m : ℝ) ≤ (C0 : ℝ) * t := by exact_mod_cast hlog
    linarith
  have hL0 : 0 ≤ Real.log ((5 * m : ℕ) : ℝ) := by
    apply Real.log_nonneg
    have : 1 ≤ 5 * m := by omega
    exact_mod_cast this
  have hlogMs : Real.log ((M * s : ℕ) : ℝ) ≤ M + Real.log ((5 * m : ℕ) : ℝ) / 2 := by
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
    have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs1
    rw [Nat.cast_mul, Real.log_mul hMpos.ne' hspos.ne']
    have h1 := Real.log_le_self hMpos.le
    have h2 := log_sqrt_le (5 * m) (by omega)
    rw [hs] at h2
    linarith
  -- step 3: the other divisor sums
  have hA2 : ∀ y ∈ Finset.range (2 * m),
      ∑ i ∈ Finset.range Z, ((base + 1 + 1 + y + i * Q).divisors.card : ℝ)
        ≤ (Q.divisors.card : ℝ) * ((Z : ℝ) * (3 + Real.log ((5 * m : ℕ) : ℝ))) := by
    intro y hy
    have hy' := Finset.mem_range.mp hy
    have h := sum_divisors_AP_gcd (base + 1 + 1 + y) Q Z (5 * m) hQpos
      (fun i hi => by have := hbase2 i hi; omega)
    have hW := W_le Z (5 * m) (by omega) (by rw [hs]; exact hZs)
    rw [hs] at h hW
    have hg : ((Nat.gcd (base + 1 + 1 + y) Q).divisors.card : ℝ) ≤ (Q.divisors.card : ℝ) := by
      exact_mod_cast Finset.card_le_card
        (Nat.divisors_subset_of_dvd hQpos.ne' (Nat.gcd_dvd_right _ _))
    refine h.trans (mul_le_mul hg hW ?_ (Nat.cast_nonneg _))
    positivity
  have ht4R : (4 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht4
  have htail : ∑ y ∈ Finset.range (2 * m),
      (∑ i ∈ Finset.range Z, ((base + 1 + 1 + y + i * Q).divisors.card : ℝ))
        / (t : ℝ) ^ (y + 1)
      ≤ (Q.divisors.card : ℝ) * ((Z : ℝ) * (3 + Real.log ((5 * m : ℕ) : ℝ)))
        * (2 * (1 / (t : ℝ))) := by
    calc _ ≤ ∑ y ∈ Finset.range (2 * m),
          ((Q.divisors.card : ℝ) * ((Z : ℝ) * (3 + Real.log ((5 * m : ℕ) : ℝ))))
            * (1 / (t : ℝ)) ^ (y + 1) := by
          apply Finset.sum_le_sum
          intro y hy
          rw [div_eq_mul_one_div, ← one_div_pow]
          exact mul_le_mul_of_nonneg_right (hA2 y hy) (by positivity)
      _ = ((Q.divisors.card : ℝ) * ((Z : ℝ) * (3 + Real.log ((5 * m : ℕ) : ℝ))))
            * ∑ y ∈ Finset.range (2 * m), (1 / (t : ℝ)) ^ (y + 1) := by
          rw [Finset.mul_sum]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left (geom_le _ (by positivity) ?_ _) (by positivity)
          rw [div_le_div_iff₀ (by linarith) (by norm_num)]
          linarith
  -- final arithmetic
  have hScop0 : 0 ≤ ∑ l ∈ (Finset.Icc 1 s).filter (fun l => Nat.Coprime l Q), (1 : ℝ) / l :=
    Finset.sum_nonneg (fun l _ => by positivity)
  exact regimeG_arith (b : ℝ) C0 t Z s (Q.divisors.card : ℝ) M _ _ _ _ _ _
    (by exact_mod_cast hb) (by exact_mod_cast hC0) (by exact_mod_cast hZ1)
    (by exact_mod_cast hZs) (by exact_mod_cast ht1)
    (by exact_mod_cast ht2) (by exact_mod_cast ht3) (Nat.cast_nonneg _) hScop0 hL hH
    (hcop.trans (hhar.trans (by linarith))) hsum1 hsum2 (hA1.trans (by linarith)) htail

lemma four_sq_le (k : ℕ) (hk : 1 ≤ k) : 4 * k ^ 2 + k ≤ 2 ^ (2 * k + 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have e : 2 ^ (2 * (k + 1) + 1) = 4 * 2 ^ (2 * k + 1) := by ring
    rw [e]
    nlinarith

lemma regimeCRT_arith (b Z L W S T tk : ℝ) (hb : 1 ≤ b) (hZ : 1 ≤ Z) (hL0 : 0 ≤ L)
    (hlow : Z * tk ≤ S) (hup : S ≤ b * T + Z * b) (hT : T ≤ W) (hW : W ≤ Z * (3 + L))
    (hB : 8 * b * (4 + L) ≤ tk) : False := by
  have hZ0 : 0 ≤ Z := by linarith
  have hb0 : 0 ≤ b := by linarith
  have p1 := mul_le_mul_of_nonneg_left hB hZ0
  have p2 := mul_le_mul_of_nonneg_left (hT.trans hW) hb0
  have h1 : 1 * 1 ≤ Z * b := mul_le_mul hZ hb (by norm_num) hZ0
  have h2 : (Z * b) * 0 ≤ (Z * b) * L := mul_le_mul_of_nonneg_left hL0 (by linarith)
  linarith

/-- the regime of slow growth: a constant stretch and the Chinese remainder theorem -/
lemma regimeCRT {a : ℕ → ℕ} {b : ℕ} {I : ℕ → ℤ} (D : Data a b I) (m α l t k : ℕ)
    (hm1 : 1 ≤ m) (hαl : α + l ≤ 2 * m)
    (hconst : ∀ n, α ≤ n → n < α + l → a n = t)
    (ht : 4 ≤ t) (hk : 1 ≤ k)
    (hB : (8 * b : ℝ) * (4 + Real.log ((5 * m : ℕ) : ℝ)) ≤ (t : ℝ) ^ k)
    (hsize : 2 ^ (t * (k * k) * (k + 1) ^ 2) * (2 * Nat.sqrt (5 * m) + 1) + k + 1 ≤ l) :
    False := by
  have hb := D.hb
  obtain ⟨q, hqp, hqm, hqP, hqle⟩ := exists_primes (4 * k ^ 2 + k) (by positivity)
  -- the modulus
  have hApos : 0 < ∏ n ∈ Finset.range (k * k), q n ^ t :=
    Finset.prod_pos (fun n _ => pow_pos (hqp n).pos t)
  have hAle : ∏ n ∈ Finset.range (k * k), q n ^ t ≤ 2 ^ (t * (k * k) * (k + 1) ^ 2) := by
    have hP1 : ∀ n < k * k, q n ≤ 2 ^ ((k + 1) ^ 2) := by
      intro n hn
      calc q n ≤ 2 ^ (n + 1) * (4 * k ^ 2 + k) := hqle n
        _ ≤ 2 ^ (k * k) * 2 ^ (2 * k + 1) :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega)) (four_sq_le k hk)
        _ = 2 ^ ((k + 1) ^ 2) := by rw [← pow_add]; congr 1; ring
    calc ∏ n ∈ Finset.range (k * k), q n ^ t
        ≤ (2 ^ ((k + 1) ^ 2)) ^ (t * (k * k)) := modulus_le q _ t (k * k) hP1
      _ = 2 ^ (t * (k * k) * (k + 1) ^ 2) := by rw [← pow_mul]; congr 1; ring
  have hdA : (∏ n ∈ Finset.range (k * k), q n ^ t).divisors.card ≤ t ^ (2 * (k * k)) := by
    calc (∏ n ∈ Finset.range (k * k), q n ^ t).divisors.card
        ≤ (t + 1) ^ (k * k) := card_divisors_modulus q hqp t (k * k)
      _ ≤ (t ^ 2) ^ (k * k) := Nat.pow_le_pow_left (by nlinarith) _
      _ = t ^ (2 * (k * k)) := by rw [← pow_mul]
  -- the CRT solution
  obtain ⟨x, hx⟩ := exists_crt q hqp hqm t k α
  have hxr : ∀ i n, n < k * k →
      x % (∏ n ∈ Finset.range (k * k), q n ^ t) + α
        + i * (∏ n ∈ Finset.range (k * k), q n ^ t) + (n / k + 1)
        ≡ q n ^ (t - 1) [MOD q n ^ t] := by
    intro i n hn
    have hdvd : q n ^ t ∣ ∏ n ∈ Finset.range (k * k), q n ^ t :=
      Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hn)
    have h1 : x % (∏ n ∈ Finset.range (k * k), q n ^ t) ≡ x [MOD q n ^ t] :=
      (Nat.mod_modEq x _).of_dvd hdvd
    have h2 : i * (∏ n ∈ Finset.range (k * k), q n ^ t) ≡ 0 [MOD q n ^ t] :=
      (Nat.modEq_zero_iff_dvd).mpr (Dvd.dvd.mul_left hdvd i)
    have h3 := ((h1.add_right α).add h2).add_right (n / k + 1)
    simp only [add_zero] at h3
    exact h3.trans (hx n hn)
  have hrlt : x % (∏ n ∈ Finset.range (k * k), q n ^ t)
      < ∏ n ∈ Finset.range (k * k), q n ^ t := Nat.mod_lt x hApos
  generalize hA : ∏ n ∈ Finset.range (k * k), q n ^ t = A at *
  generalize hr : x % A + α = r at *
  have hr1 : α ≤ r := by omega
  have hr2 : r < α + A := by omega
  have hl : A * (2 * Nat.sqrt (5 * m) + 1) + k + 1 ≤ l :=
    le_trans (by gcongr) hsize
  have hZA : (l - k - 1) / A * A ≤ l - k - 1 := Nat.div_mul_le_self _ _
  have hZs : 2 * Nat.sqrt (5 * m) + 1 ≤ (l - k - 1) / A := by
    rw [Nat.le_div_iff_mul_le hApos]
    have : (2 * Nat.sqrt (5 * m) + 1) * A = A * (2 * Nat.sqrt (5 * m) + 1) := Nat.mul_comm _ _
    omega
  generalize hZ : (l - k - 1) / A = Z at *
  have hN : ∀ i, i < Z → r + i * A + k + 1 ≤ α + l := by
    intro i hi
    have h1 : (i + 1) * A ≤ Z * A := Nat.mul_le_mul_right _ hi
    have e : (i + 1) * A = i * A + A := by ring
    omega
  have hl0 : 0 < l := by omega
  have haα : a α = t := hconst α le_rfl (by omega)
  -- lower bound
  have hlow : ∀ i ∈ Finset.range Z, ((t : ℝ) ^ k) ≤ (I (r + k + i * A) : ℝ) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hNi := hN i hi'
    have hdvd := dvd_chain D t (r + i * A) k
      (fun j hj1 hjk => hconst _ (by omega) (by omega))
      (fun j hj1 hjk => pow_dvd_of_crt q hqp hqm t k (r + i * A) (by omega) (hxr i) j hj1 hjk)
    have hpos := D.pos (r + i * A + k)
    have hle : (t : ℤ) ^ k ≤ I (r + i * A + k) := Int.le_of_dvd (by omega) hdvd
    have e : r + i * A + k = r + k + i * A := by ring
    rw [e] at hle
    exact_mod_cast hle
  have hlow' : (Z : ℝ) * (t : ℝ) ^ k ≤ ∑ i ∈ Finset.range Z, (I (r + k + i * A) : ℝ) := by
    have := Finset.sum_le_sum hlow
    rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  -- upper bound
  have hge : ∀ j, r + k < j → t ≤ a j := by
    intro j hj
    rw [← haα]; exact D.mono (by omega)
  have hY : ∀ i < Z, r + k + i * A + 2 * m + 1 ≤ t ^ (2 * m) := by
    intro i hi
    have := hN i hi
    calc r + k + i * A + 2 * m + 1 ≤ 4 * m + 2 := by omega
      _ ≤ 4 ^ (2 * m) := four_mul_le m hm1
      _ ≤ t ^ (2 * m) := Nat.pow_le_pow_left ht _
  have hup := sum_I_le D t (r + k) A Z (2 * m) ht hge hY
  have hW := W_le Z (5 * m) (by omega) (by omega)
  have hW0 : (0 : ℝ) ≤ 2 * ∑ l ∈ Finset.Icc 1 (Nat.sqrt (5 * m)), ((Z : ℝ) / l + 1) := by
    positivity
  have hxr0 : ∀ n < k * k, r + (n / k + 1) ≡ q n ^ (t - 1) [MOD q n ^ t] := by
    intro n hn
    have := hxr 0 n hn
    simpa using this
  have htpos : (0 : ℝ) < (t : ℝ) := by
    have : 0 < t := by omega
    exact_mod_cast this
  have hSy : ∀ y ∈ Finset.range (2 * m),
      (∑ i ∈ Finset.range Z, ((r + k + 1 + y + i * A).divisors.card : ℝ)) / (t : ℝ) ^ (y + 1)
        ≤ (2 * ∑ l ∈ Finset.Icc 1 (Nat.sqrt (5 * m)), ((Z : ℝ) / l + 1))
          * (1 / 2 : ℝ) ^ (y + 1) := by
    intro y hy
    have hy' := Finset.mem_range.mp hy
    have h := sum_divisors_AP_gcd (r + k + 1 + y) A Z (5 * m) hApos
      (fun i hi => by have := hN i hi; omega)
    have hGnat : (Nat.gcd (r + k + 1 + y) A).divisors.card * 2 ^ (y + 1) ≤ t ^ (y + 1) := by
      by_cases hc : k + y ≤ 4 * k ^ 2 + k
      · have hcop := coprime_shift q hqp t k (4 * k ^ 2 + k) r (k + 1 + y) (by omega)
          hqP hxr0 (by omega) (by omega)
        rw [hA] at hcop
        have e : r + k + 1 + y = r + (k + 1 + y) := by ring
        rw [e, Nat.Coprime.gcd_eq_one hcop, Nat.divisors_one, Finset.card_singleton, one_mul]
        exact Nat.pow_le_pow_left (by omega) _
      · push Not at hc
        have hK : 4 * (k * k) + 2 ≤ y + 1 := by nlinarith
        obtain ⟨w, hw⟩ : ∃ w, y + 1 = 2 * (k * k) + w := ⟨y + 1 - 2 * (k * k), by omega⟩
        have hw2 : 2 * (k * k) ≤ w := by omega
        have h1 : (Nat.gcd (r + k + 1 + y) A).divisors.card ≤ t ^ (2 * (k * k)) :=
          (Finset.card_le_card (Nat.divisors_subset_of_dvd hApos.ne'
            (Nat.gcd_dvd_right _ _))).trans hdA
        have h2 : 2 ^ (y + 1) ≤ t ^ w := by
          calc 2 ^ (y + 1) = 2 ^ (2 * (k * k)) * 2 ^ w := by rw [hw, pow_add]
            _ ≤ 2 ^ w * 2 ^ w :=
              Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hw2)
            _ = 4 ^ w := by rw [← Nat.mul_pow]
            _ ≤ t ^ w := Nat.pow_le_pow_left ht _
        calc (Nat.gcd (r + k + 1 + y) A).divisors.card * 2 ^ (y + 1)
            ≤ t ^ (2 * (k * k)) * t ^ w := Nat.mul_le_mul h1 h2
          _ = t ^ (y + 1) := by rw [hw, pow_add]
    have hG : ((Nat.gcd (r + k + 1 + y) A).divisors.card : ℝ) / (t : ℝ) ^ (y + 1)
        ≤ (1 / 2 : ℝ) ^ (y + 1) := by
      rw [one_div_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      exact_mod_cast hGnat
    calc (∑ i ∈ Finset.range Z, ((r + k + 1 + y + i * A).divisors.card : ℝ))
          / (t : ℝ) ^ (y + 1)
        ≤ (((Nat.gcd (r + k + 1 + y) A).divisors.card : ℝ) *
            (2 * ∑ l ∈ Finset.Icc 1 (Nat.sqrt (5 * m)), ((Z : ℝ) / l + 1)))
              / (t : ℝ) ^ (y + 1) := div_le_div_of_nonneg_right h (by positivity)
      _ = (2 * ∑ l ∈ Finset.Icc 1 (Nat.sqrt (5 * m)), ((Z : ℝ) / l + 1)) *
            (((Nat.gcd (r + k + 1 + y) A).divisors.card : ℝ) / (t : ℝ) ^ (y + 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hG hW0
  have hT : ∑ y ∈ Finset.range (2 * m),
      (∑ i ∈ Finset.range Z, ((r + k + 1 + y + i * A).divisors.card : ℝ)) / (t : ℝ) ^ (y + 1)
        ≤ 2 * ∑ l ∈ Finset.Icc 1 (Nat.sqrt (5 * m)), ((Z : ℝ) / l + 1) := by
    refine (Finset.sum_le_sum hSy).trans ?_
    rw [← Finset.mul_sum]
    have := geom_le (1 / 2 : ℝ) (by norm_num) le_rfl (2 * m)
    calc _ ≤ (2 * ∑ l ∈ Finset.Icc 1 (Nat.sqrt (5 * m)), ((Z : ℝ) / l + 1)) * (2 * (1 / 2)) :=
          mul_le_mul_of_nonneg_left this hW0
      _ = _ := by ring
  have hL0 : 0 ≤ Real.log ((5 * m : ℕ) : ℝ) := by
    apply Real.log_nonneg
    have : 1 ≤ 5 * m := by omega
    exact_mod_cast this
  exact regimeCRT_arith (b : ℝ) Z _ _ _ _ _ (by exact_mod_cast hb)
    (by exact_mod_cast (by omega : 1 ≤ Z)) hL0 hlow' hup hT hW hB

lemma twenty_le (μ : ℕ) (h : 8 ≤ μ) : 20 * (μ + 1) ≤ 2 ^ μ := by
  induction μ, h using Nat.le_induction with
  | base => norm_num
  | succ μ h ih => rw [pow_succ]; omega

lemma exists_U0 (c : ℕ) : ∃ U0 : ℕ, ∀ u, U0 ≤ u → c * u ^ 8 ≤ 4 ^ u := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 8 (r := (4 : ℝ)) (by norm_num)
  have hε : (0 : ℝ) < 1 / ((c : ℝ) + 1) := by positivity
  have h2 := h.eventually (gt_mem_nhds hε)
  obtain ⟨U0, hU0⟩ := Filter.eventually_atTop.mp h2
  refine ⟨U0, fun u hu => ?_⟩
  have h3 := hU0 u hu
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at h3
  have h5 : (0 : ℝ) ≤ (u : ℝ) ^ 8 := by positivity
  have h4 : ((c * u ^ 8 : ℕ) : ℝ) ≤ ((4 ^ u : ℕ) : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast h4

lemma e_le (b U0 : ℕ) (hU0 : ∀ u, U0 ≤ u → (112 * b) ^ 2 * 16 * u ^ 8 ≤ 4 ^ u)
    (t V μ β₀ k : ℕ) (ht4 : 4 ≤ t) (htV : t ≤ V) (hV1 : 320 * V ≤ 4 * μ + 3) (hμ1 : 1 ≤ μ)
    (hμb : 112 * b * U0 ^ 8 ≤ μ) (hβμ : β₀ ≤ 112 * b * μ) (hk1 : 1 ≤ k)
    (hpred : t ^ (k - 1) < β₀) : t * (k * k) * (k + 1) ^ 2 ≤ μ := by
  rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | hk3
  · norm_num; omega
  · norm_num; omega
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have hpred' : t ^ (j + 2) < β₀ := by simpa using hpred
    have ht2 : t ^ 2 ≤ t ^ (j + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    have h4j : 4 ^ (j + 2) ≤ t ^ (j + 2) := Nat.pow_le_pow_left ht4 _
    have hu : 112 * b * (j + 4) ^ 8 ≤ μ := by
      rcases le_or_gt U0 (j + 4) with h | h
      · have h1 := hU0 (j + 4) h
        have h2 : 4 ^ (j + 4) = 16 * 4 ^ (j + 2) := by ring
        have h3 : (112 * b) ^ 2 * 16 * (j + 4) ^ 8 < 16 * (112 * b * μ) := by
          calc _ ≤ 4 ^ (j + 4) := h1
            _ = 16 * 4 ^ (j + 2) := h2
            _ < 16 * β₀ := by omega
            _ ≤ 16 * (112 * b * μ) := by omega
        have h4 : (16 * (112 * b)) * (112 * b * (j + 4) ^ 8) < (16 * (112 * b)) * μ := by
          calc (16 * (112 * b)) * (112 * b * (j + 4) ^ 8)
              = (112 * b) ^ 2 * 16 * (j + 4) ^ 8 := by ring
            _ < 16 * (112 * b * μ) := h3
            _ = (16 * (112 * b)) * μ := by ring
        exact (Nat.lt_of_mul_lt_mul_left h4).le
      · calc 112 * b * (j + 4) ^ 8 ≤ 112 * b * U0 ^ 8 :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h.le _)
          _ ≤ μ := hμb
    have hsq : (t * ((j + 3) * (j + 3)) * (j + 3 + 1) ^ 2) ^ 2 < μ ^ 2 := by
      have h1 : ((j + 3) * (j + 3)) ^ 2 * ((j + 3 + 1) ^ 2) ^ 2 ≤ (j + 4) ^ 8 := by
        have h0 : (j + 3) ≤ j + 4 := by omega
        calc ((j + 3) * (j + 3)) ^ 2 * ((j + 3 + 1) ^ 2) ^ 2
            = (j + 3) ^ 4 * (j + 4) ^ 4 := by ring
          _ ≤ (j + 4) ^ 4 * (j + 4) ^ 4 :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h0 4)
          _ = (j + 4) ^ 8 := by ring
      calc (t * ((j + 3) * (j + 3)) * (j + 3 + 1) ^ 2) ^ 2
          = t ^ 2 * (((j + 3) * (j + 3)) ^ 2 * ((j + 3 + 1) ^ 2) ^ 2) := by ring
        _ ≤ t ^ 2 * (j + 4) ^ 8 := Nat.mul_le_mul_left _ h1
        _ < β₀ * (j + 4) ^ 8 :=
          Nat.mul_lt_mul_of_pos_right (lt_of_le_of_lt ht2 hpred') (by positivity)
        _ ≤ (112 * b * μ) * (j + 4) ^ 8 := Nat.mul_le_mul_right _ hβμ
        _ = μ * (112 * b * (j + 4) ^ 8) := by ring
        _ ≤ μ * μ := Nat.mul_le_mul_left _ hu
        _ = μ ^ 2 := by ring
    exact (lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) hsq).le

lemma size_le (m lam μ e k l : ℕ) (hlow : 2 ^ lam ≤ m) (hupp : m < 2 ^ (lam + 1))
    (hlam1 : 4 * μ ≤ lam) (hlam2 : lam ≤ 4 * μ + 3) (hμ : 8 ≤ μ) (he : e ≤ μ) (hk : k ≤ μ)
    (hl : m / (μ + 1) ≤ l) :
    2 ^ e * (2 * Nat.sqrt (5 * m) + 1) + k + 1 ≤ l := by
  have h2e : 2 ^ e ≤ 2 ^ μ := Nat.pow_le_pow_right (by norm_num) he
  have hm16 : m < 16 * (2 ^ μ) ^ 4 := by
    calc m < 2 ^ (lam + 1) := hupp
      _ ≤ 2 ^ (4 * μ + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 16 * (2 ^ μ) ^ 4 := by rw [← pow_mul]; ring
  have hmlow : (2 ^ μ) ^ 4 ≤ m := by
    calc (2 ^ μ) ^ 4 = 2 ^ (4 * μ) := by rw [← pow_mul]; ring_nf
      _ ≤ 2 ^ lam := Nat.pow_le_pow_right (by norm_num) hlam1
      _ ≤ m := hlow
  have hs : Nat.sqrt (5 * m) ≤ 9 * (2 ^ μ) ^ 2 := by
    have h1 : 5 * m ≤ (9 * (2 ^ μ) ^ 2) ^ 2 := by
      have : (9 * (2 ^ μ) ^ 2) ^ 2 = 81 * (2 ^ μ) ^ 4 := by ring
      omega
    calc Nat.sqrt (5 * m) ≤ Nat.sqrt ((9 * (2 ^ μ) ^ 2) ^ 2) := Nat.sqrt_le_sqrt h1
      _ = 9 * (2 ^ μ) ^ 2 := Nat.sqrt_eq' _
  have hk2 : k + 1 ≤ 2 ^ μ := by
    have : μ < 2 ^ μ := Nat.lt_two_pow_self
    omega
  have h20 := twenty_le μ hμ
  have hD1 : 1 ≤ 2 ^ μ := Nat.one_le_two_pow
  generalize 2 ^ μ = Dd at *
  generalize 2 ^ e = E at *
  generalize Nat.sqrt (5 * m) = s at *
  have h3 : Dd ≤ Dd ^ 3 := by
    calc Dd = Dd ^ 1 := (pow_one _).symm
      _ ≤ Dd ^ 3 := Nat.pow_le_pow_right hD1 (by norm_num)
  have h2 : E * (2 * s + 1) ≤ 18 * Dd ^ 3 + Dd := by
    calc E * (2 * s + 1) ≤ Dd * (2 * (9 * Dd ^ 2) + 1) := Nat.mul_le_mul h2e (by omega)
      _ = 18 * Dd ^ 3 + Dd := by ring
  have h4 : 20 * Dd ^ 3 ≤ m / (μ + 1) := by
    rw [Nat.le_div_iff_mul_le (Nat.succ_pos μ)]
    calc 20 * Dd ^ 3 * (μ + 1) = Dd ^ 3 * (20 * (μ + 1)) := by ring
      _ ≤ Dd ^ 3 * Dd := Nat.mul_le_mul_left _ h20
      _ = Dd ^ 4 := by ring
      _ ≤ m := hmlow
  omega

/-- choice of the parameters in the slow regime -/
lemma crt_params (a : ℕ → ℕ) (hmono : Monotone a) (b : ℕ) (hb : 0 < b) (U0 : ℕ)
    (hU0 : ∀ u, U0 ≤ u → (112 * b) ^ 2 * 16 * u ^ 8 ≤ 4 ^ u) (m : ℕ)
    (hm4 : 4 ≤ a m) (hreg : 320 * a (2 * m) < Nat.log 2 (2 * m))
    (hμ10 : 10 ≤ Nat.log 2 m / 4) (hμb : 112 * b * U0 ^ 8 ≤ Nat.log 2 m / 4) :
    ∃ α l t k, m ≤ α ∧ α + l ≤ 2 * m ∧ (∀ n, α ≤ n → n < α + l → a n = t) ∧ 4 ≤ t ∧ 1 ≤ k ∧
      (8 * b : ℝ) * (4 + Real.log ((5 * m : ℕ) : ℝ)) ≤ (t : ℝ) ^ k ∧
      2 ^ (t * (k * k) * (k + 1) ^ 2) * (2 * Nat.sqrt (5 * m) + 1) + k + 1 ≤ l := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hμ10
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  have hlog2 : Nat.log 2 (2 * m) = Nat.log 2 m + 1 := by
    rw [Nat.mul_comm]; exact Nat.log_mul_base (by norm_num) hm0
  have hlog5 := log_five_mul_le m hm1
  have hlow : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hm0
  have hupp : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  rw [hlog2] at hreg
  generalize Nat.log 2 m = lam at *
  have hlam1 : 4 * (lam / 4) ≤ lam := by omega
  have hlam2 : lam ≤ 4 * (lam / 4) + 3 := by omega
  generalize lam / 4 = μ at *
  have hV1 : 320 * a (2 * m) ≤ 4 * μ + 3 := by omega
  have hVl : (a (2 * m) + 1) * (m / (a (2 * m) + 1)) ≤ m := Nat.mul_div_le m _
  have hlV : m / (μ + 1) ≤ m / (a (2 * m) + 1) :=
    Nat.div_le_div_left (by omega) (Nat.succ_pos _)
  generalize m / (a (2 * m) + 1) = l at *
  obtain ⟨α, hα1, hα2, hα3⟩ := exists_stretch a hmono m l (a (2 * m)) (hmono (by omega))
  have hαl : α + l ≤ 2 * m := by omega
  have ht4 : 4 ≤ a α := le_trans hm4 (hmono hα1)
  have htV : a α ≤ a (2 * m) := hmono (by omega)
  generalize a (2 * m) = V at *
  refine ⟨α, l, a α, Nat.clog (a α) (8 * b * (lam + 7)), hα1, hαl, hα3, ht4, ?_⟩
  generalize a α = t at *
  have hβ1 : 1 < 8 * b * (lam + 7) := by nlinarith
  have hβμ : 8 * b * (lam + 7) ≤ 112 * b * μ := by nlinarith
  have hBβ : (8 * b : ℝ) * (4 + Real.log ((5 * m : ℕ) : ℝ))
      ≤ ((8 * b * (lam + 7) : ℕ) : ℝ) := by
    have h0 : (0 : ℝ) ≤ 8 * (b : ℝ) := by positivity
    have h1 := mul_le_mul_of_nonneg_left
      (by linarith : 4 + Real.log ((5 * m : ℕ) : ℝ) ≤ (lam : ℝ) + 7) h0
    calc (8 * b : ℝ) * (4 + Real.log ((5 * m : ℕ) : ℝ)) ≤ 8 * (b : ℝ) * ((lam : ℝ) + 7) := h1
      _ = ((8 * b * (lam + 7) : ℕ) : ℝ) := by push_cast; ring
  generalize 8 * b * (lam + 7) = β₀ at *
  have hk1 : 1 ≤ Nat.clog t β₀ := Nat.clog_pos (by omega) hβ1
  have hpow : β₀ ≤ t ^ Nat.clog t β₀ := Nat.le_pow_clog (by omega) β₀
  have hpred : t ^ (Nat.clog t β₀ - 1) < β₀ := Nat.pow_pred_clog_lt_self (by omega) hβ1
  generalize Nat.clog t β₀ = k at *
  have he : t * (k * k) * (k + 1) ^ 2 ≤ μ :=
    e_le b U0 hU0 t V μ β₀ k ht4 htV hV1 (by omega) hμb hβμ hk1 hpred
  have hkμ : k ≤ μ := by
    have h1 : k ≤ k * k := Nat.le_mul_self k
    have h2 : k * k ≤ t * (k * k) := Nat.le_mul_of_pos_left _ (by omega)
    have h3 : t * (k * k) ≤ t * (k * k) * (k + 1) ^ 2 :=
      Nat.le_mul_of_pos_right _ (by positivity)
    omega
  refine ⟨hk1, ?_, ?_⟩
  · calc (8 * b : ℝ) * (4 + Real.log ((5 * m : ℕ) : ℝ)) ≤ ((β₀ : ℕ) : ℝ) := hBβ
      _ ≤ ((t ^ k : ℕ) : ℝ) := by exact_mod_cast hpow
      _ = (t : ℝ) ^ k := by push_cast; rfl
  · exact size_le m lam μ _ k l hlow hupp hlam1 hlam2 (by omega) he hkμ hlV

/-- the contradiction from the integer sequence -/
theorem core {a : ℕ → ℕ} {b : ℕ} {I : ℕ → ℤ} (D : Data a b I)
    (htend : Tendsto a atTop atTop) : False := by
  have hb := D.hb
  by_cases h : ∃ᶠ m in atTop, Nat.log 2 m ≤ 320 * a m
  · obtain ⟨M, hM1, hH⟩ : ∃ M : ℕ, 1 ≤ M ∧
        (8 * b * (320 : ℕ) : ℝ) ≤ ∑ j ∈ Finset.Icc 1 M, (1 : ℝ) / j := by
      refine ⟨⌈Real.exp (8 * b * 320)⌉₊, ?_, ?_⟩
      · exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (Real.exp_pos _)).ne'
      · have h1 := log_add_one_le_harmonic ⌈Real.exp (8 * b * 320)⌉₊
        rw [harmonic_eq_sum_Icc] at h1
        push_cast at h1
        have h2 : (8 * b * 320 : ℝ) ≤ Real.log ((⌈Real.exp (8 * b * 320)⌉₊ : ℝ) + 1) := by
          have h3 : Real.exp (8 * b * 320) ≤ (⌈Real.exp (8 * b * 320)⌉₊ : ℝ) + 1 :=
            (Nat.le_ceil _).trans (by linarith)
          have := Real.log_le_log (Real.exp_pos _) h3
          rwa [Real.log_exp] at this
        have h4 := h2.trans h1
        simpa [one_div] using h4
    have e1 := htend.eventually_ge_atTop
      (max (8 * b) (max (16 * b * (M.factorial).divisors.card * (320 + 2)) (5 + 2 * M)))
    have e2 := Filter.eventually_ge_atTop (80 * M.factorial ^ 2)
    obtain ⟨m, hm1, hm2, hm3⟩ := (h.and_eventually (e1.and e2)).exists
    exact regimeG D M 320 m (by norm_num) hM1 hH hm1 (le_trans (le_max_left _ _) hm2)
      (le_trans ((le_max_left _ _).trans (le_max_right _ _)) hm2)
      (le_trans ((le_max_right _ _).trans (le_max_right _ _)) hm2) hm3
  · rw [Filter.not_frequently] at h
    obtain ⟨U0, hU0⟩ := exists_U0 ((112 * b) ^ 2 * 16)
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp h
    have e1 := htend.eventually_ge_atTop 4
    have e2 := Filter.eventually_ge_atTop N0
    have e3 : ∀ᶠ m : ℕ in atTop, max 10 (112 * b * U0 ^ 8) ≤ Nat.log 2 m / 4 := by
      refine Filter.eventually_atTop.mpr ⟨2 ^ (4 * max 10 (112 * b * U0 ^ 8)), fun m hm => ?_⟩
      have : 4 * max 10 (112 * b * U0 ^ 8) ≤ Nat.log 2 m :=
        Nat.le_log_of_pow_le (by norm_num) hm
      omega
    obtain ⟨m, hm1, hm2, hm3⟩ := (e1.and (e2.and e3)).exists
    have hreg : 320 * a (2 * m) < Nat.log 2 (2 * m) := by
      have := hN0 (2 * m) (by omega)
      omega
    have hm0 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · simp at hm3
      · exact hpos
    obtain ⟨α, l, t, k, -, h2, h3, h4, h5, h6, h7⟩ := crt_params a D.mono b hb U0 hU0 m hm1 hreg
      (le_trans (le_max_left _ _) hm3) (le_trans (le_max_right _ _) hm3)
    exact regimeCRT D m α l t k hm0 h2 h3 h4 h5 h6 h7

theorem main_irrational (a : ℕ → ℕ) (h2 : ∀ n, 2 ≤ a n) (hmono : Monotone a)
    (htend : Tendsto a atTop atTop) :
    Irrational (∑' n : ℕ, (((n + 1).divisors.card : ℝ) /
      ((∏ i ∈ Finset.Icc 1 (n + 1), a i : ℕ) : ℝ))) := by
  rintro ⟨q, hq⟩
  have hq' : (q : ℝ) = ∑' n, term a n := hq
  have key : ∀ N, ∃ z : ℤ, (z : ℝ) = (q.den : ℝ) * T a N := by
    intro N
    induction N with
    | zero =>
      refine ⟨q.num, ?_⟩
      rw [T_zero, ← hq']
      have h : (q : ℝ) * (q.den : ℝ) = (q.num : ℝ) := by exact_mod_cast Rat.mul_den_eq_num q
      linarith
    | succ N ih =>
      obtain ⟨z, hz⟩ := ih
      refine ⟨(a (N + 1) : ℤ) * z - (q.den : ℤ) * ((N + 1).divisors.card : ℤ), ?_⟩
      push_cast
      have := T_rec a h2 N
      rw [hz]
      linear_combination (q.den : ℝ) * this
  choose I hI using key
  have hden : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.den_pos
  refine core (a := a) (b := q.den) (I := I) ⟨q.den_pos, h2, hmono, ?_, ?_, ?_⟩ htend
  · intro N
    have h1 : (0 : ℝ) < (I N : ℝ) := by rw [hI]; exact mul_pos hden (T_pos a h2 N)
    have h3 : (0 : ℤ) < I N := by exact_mod_cast h1
    omega
  · intro N
    have h1 := T_rec a h2 N
    have h3 : (((a (N + 1) : ℤ) * I N : ℤ) : ℝ)
        = (((q.den : ℤ) * ((N + 1).divisors.card : ℤ) + I (N + 1) : ℤ) : ℝ) := by
      push_cast
      rw [hI, hI]
      linear_combination (q.den : ℝ) * h1
    exact_mod_cast h3
  · intro N h4
    have h1 := T_le a h2 N h4
    have h3 : (I N : ℝ) ≤ (((q.den : ℤ) * ((N : ℤ) + 1) : ℤ) : ℝ) := by
      push_cast
      rw [hI]
      exact mul_le_mul_of_nonneg_left h1 hden.le
    exact_mod_cast h3


end OMA.Helpers

theorem OMA.solution : type_of% @Erdos258.erdos_258.variants.monotone := by
  intro a h2 hmono htend
  exact OMA.Helpers.main_irrational a h2 hmono htend
