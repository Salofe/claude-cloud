import OMAStatements.S_oeis_a072061
import Mathlib

/-!
Proof of the A072061 conjecture: a(2n)/a(2n-1) tends to k + sqrt(k^2 + 1) for every k > 0.

Write o(m) = a(2m-1) and e(m) = a(2m) = o(m) + floor(2km). The odd terms are the successive
smallest missing values, so they increase strictly and every positive integer below o(m) is an
earlier odd or even term; an even term never equals a later odd term and, once floor(2kj) >= 1,
never equals any odd term. Counting the integers below o(m) gives, with J the number of even
terms below o(m), m + J - j1 <= o(m) <= m + J, together with e(J) < o(m) <= e(J+1). With
alpha = 1 - k + s, beta = alpha + 2k and s = sqrt(k^2+1) one has beta (alpha - 1) = alpha and
beta - 2 = k + s - 1 > 0, and these inequalities bound |o(m) - alpha m| by strong induction.
Hence o(m)/m tends to alpha, floor(2km)/m tends to 2k, and e(m)/o(m) tends to
1 + 2k/alpha = k + s.
-/

namespace OMA.Helpers

open OMA.S_oeis_a072061 Filter Topology

/-- Odd-indexed terms: `o m = a (2m - 1)`. -/
def a072061_o (a : ℕ → ℕ) (m : ℕ) : ℕ := a (2 * m - 1)

/-- Even-indexed terms: `e m = a (2m)`. -/
def a072061_e (a : ℕ → ℕ) (m : ℕ) : ℕ := a (2 * m)

theorem a072061_o_succ (a : ℕ → ℕ) (m : ℕ) : a072061_o a (m + 1) = a (2 * m + 1) := by
  unfold a072061_o
  congr 1

theorem a072061_e_eq {k : ℝ} {a : ℕ → ℕ} (ha : IsGenSeq k a) (m : ℕ) (hm : 1 ≤ m) :
    a072061_e a m = a072061_o a m + ⌊k * (2 * m : ℝ)⌋₊ :=
  ha.2.1 m hm

theorem a072061_o_one {k : ℝ} {a : ℕ → ℕ} (ha : IsGenSeq k a) : a072061_o a 1 = 1 := ha.1

theorem a072061_o_pos {k : ℝ} {a : ℕ → ℕ} (ha : IsGenSeq k a) (m : ℕ) (hm : 1 ≤ m) :
    1 ≤ a072061_o a m := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rcases Nat.eq_zero_or_pos m with h0 | hm'
  · subst h0
    rw [a072061_o_one ha]
  · rw [a072061_o_succ]
    exact (ha.2.2 m hm').1

theorem a072061_o_lt_succ {k : ℝ} {a : ℕ → ℕ} (ha : IsGenSeq k a) (m : ℕ) (hm : 1 ≤ m) :
    a072061_o a m < a072061_o a (m + 1) := by
  rw [a072061_o_succ]
  obtain ⟨hpos, hne, -⟩ := ha.2.2 m hm
  by_contra hcon
  push Not at hcon
  rcases lt_or_eq_of_le hcon with hlt | heq
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rcases Nat.eq_zero_or_pos m' with h0 | hm'
    · subst h0
      rw [a072061_o_one ha] at hlt
      omega
    · rw [a072061_o_succ] at hlt
      obtain ⟨j, hj, hjv⟩ := (ha.2.2 m' hm').2.2 (a (2 * (m' + 1) + 1)) hpos hlt
      rw [Finset.mem_Icc] at hj
      exact hne j (by rw [Finset.mem_Icc]; omega) hjv
  · exact hne (2 * m - 1) (by rw [Finset.mem_Icc]; omega) heq.symm

theorem a072061_o_strict {k : ℝ} {a : ℕ → ℕ} (ha : IsGenSeq k a) {i j : ℕ} (hi : 1 ≤ i)
    (hij : i < j) : a072061_o a i < a072061_o a j := by
  have h' : i + 1 ≤ j := hij
  clear hij
  induction j, h' using Nat.le_induction with
  | base => exact a072061_o_lt_succ ha i hi
  | succ j hj ih => exact ih.trans (a072061_o_lt_succ ha j (by omega))

theorem a072061_o_ge {k : ℝ} {a : ℕ → ℕ} (ha : IsGenSeq k a) (m : ℕ) (hm : 1 ≤ m) :
    m ≤ a072061_o a m := by
  induction m, hm using Nat.le_induction with
  | base => exact a072061_o_pos ha 1 le_rfl
  | succ m hm ih =>
    have := a072061_o_lt_succ ha m hm
    omega

theorem a072061_e_strict {k : ℝ} {a : ℕ → ℕ} (hk : 0 < k) (ha : IsGenSeq k a) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i < j) : a072061_e a i < a072061_e a j := by
  rw [a072061_e_eq ha i hi, a072061_e_eq ha j (by omega)]
  have h1 := a072061_o_strict ha hi hij
  have h2 : ⌊k * (2 * i : ℝ)⌋₊ ≤ ⌊k * (2 * j : ℝ)⌋₊ := by
    apply Nat.floor_mono
    have : (i : ℝ) ≤ j := by exact_mod_cast hij.le
    nlinarith
  omega

theorem a072061_e_ne_o {k : ℝ} {a : ℕ → ℕ} (ha : IsGenSeq k a) {i j : ℕ} (hj : 1 ≤ j)
    (hji : j < i) : a072061_e a j ≠ a072061_o a i := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [a072061_o_succ]
  exact (ha.2.2 i' (by omega)).2.1 (2 * j) (by rw [Finset.mem_Icc]; omega)

theorem a072061_cover {k : ℝ} {a : ℕ → ℕ} (ha : IsGenSeq k a) {m v : ℕ} (hm : 2 ≤ m)
    (hv : 1 ≤ v) (hvm : v < a072061_o a m) :
    (∃ i ∈ Finset.Icc 1 (m - 1), a072061_o a i = v) ∨
      (∃ j ∈ Finset.Icc 1 (m - 1), a072061_e a j = v) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [a072061_o_succ] at hvm
  obtain ⟨j, hj, hjv⟩ := (ha.2.2 m' (by omega)).2.2 v hv hvm
  rw [Finset.mem_Icc] at hj
  rcases Nat.even_or_odd j with ⟨t, ht⟩ | ⟨t, ht⟩
  · right
    refine ⟨t, by rw [Finset.mem_Icc]; omega, ?_⟩
    show a (2 * t) = v
    rw [show 2 * t = j by omega]
    exact hjv
  · left
    refine ⟨t + 1, by rw [Finset.mem_Icc]; omega, ?_⟩
    rw [a072061_o_succ, show 2 * t + 1 = j by omega]
    exact hjv

theorem a072061_j1 {k : ℝ} (hk : 0 < k) :
    ∃ j1 : ℕ, 1 ≤ j1 ∧ ∀ j : ℕ, j1 ≤ j → 1 ≤ ⌊k * (2 * j : ℝ)⌋₊ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / k)
  refine ⟨N + 1, by omega, fun j hj => ?_⟩
  rw [Nat.one_le_floor_iff]
  have hj' : (N : ℝ) + 1 ≤ j := by exact_mod_cast hj
  have h1 : 1 < N * k := (div_lt_iff₀ hk).mp hN
  nlinarith

theorem a072061_count {k : ℝ} {a : ℕ → ℕ} (hk : 0 < k) (ha : IsGenSeq k a) {j1 : ℕ}
    (hj1 : 1 ≤ j1) (hfl : ∀ j : ℕ, j1 ≤ j → 1 ≤ ⌊k * (2 * j : ℝ)⌋₊) (m : ℕ) (hm : 2 ≤ m) :
    ∃ J : ℕ, J + 1 ≤ m ∧ a072061_o a m ≤ m + J ∧ m + J + 1 ≤ a072061_o a m + j1 ∧
      (1 ≤ J → a072061_e a J < a072061_o a m) ∧ a072061_o a m ≤ a072061_e a (J + 1) := by
  obtain ⟨J, hJ⟩ : ∃ J, J = Nat.findGreatest (fun j => a072061_e a j < a072061_o a m) (m - 1) :=
    ⟨_, rfl⟩
  have hom1 := a072061_o_pos ha m (by omega)
  have homm := a072061_o_ge ha m (by omega)
  have hJle : J ≤ m - 1 := by rw [hJ]; exact Nat.findGreatest_le _
  have hJspec : 1 ≤ J → a072061_e a J < a072061_o a m := fun h =>
    Nat.findGreatest_of_ne_zero (P := fun j => a072061_e a j < a072061_o a m) hJ.symm (by omega)
  have hJgt : ∀ j, J < j → j ≤ m - 1 → ¬ (a072061_e a j < a072061_o a m) := by
    intro j h1 h2
    rw [hJ] at h1
    exact Nat.findGreatest_is_greatest (P := fun j => a072061_e a j < a072061_o a m) h1 h2
  have hJnext : a072061_o a m ≤ a072061_e a (J + 1) := by
    by_cases h : J + 1 ≤ m - 1
    · exact not_lt.mp (hJgt (J + 1) (by omega) h)
    · rw [show J + 1 = m by omega, a072061_e_eq ha m (by omega)]
      exact Nat.le_add_right _ _
  have hupper : a072061_o a m - 1 ≤ (m - 1) + J := by
    have hsub : Finset.Icc 1 (a072061_o a m - 1) ⊆
        (Finset.Icc 1 (m - 1)).image (a072061_o a) ∪ (Finset.Icc 1 J).image (a072061_e a) := by
      intro v hv
      rw [Finset.mem_Icc] at hv
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
      rcases a072061_cover ha hm hv.1 (by omega) with ⟨i, hi, hiv⟩ | ⟨j, hj, hjv⟩
      · exact Or.inl ⟨i, hi, hiv⟩
      · right
        refine ⟨j, ?_, hjv⟩
        rw [Finset.mem_Icc] at hj ⊢
        refine ⟨hj.1, ?_⟩
        by_contra hcon
        exact hJgt j (by omega) hj.2 (by rw [hjv]; omega)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le ((Finset.Icc 1 (m - 1)).image (a072061_o a))
      ((Finset.Icc 1 J).image (a072061_e a))
    have h3 := Finset.card_image_le (s := Finset.Icc 1 (m - 1)) (f := a072061_o a)
    have h4 := Finset.card_image_le (s := Finset.Icc 1 J) (f := a072061_e a)
    simp only [Nat.card_Icc] at h1 h3 h4
    omega
  have hlower : (m - 1) + (J + 1 - j1) ≤ a072061_o a m - 1 := by
    have hdisj : Disjoint ((Finset.Icc 1 (m - 1)).image (a072061_o a))
        ((Finset.Icc j1 J).image (a072061_e a)) := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      rw [Finset.mem_image] at hv1 hv2
      obtain ⟨i, hi, rfl⟩ := hv1
      obtain ⟨j, hj, hji⟩ := hv2
      rw [Finset.mem_Icc] at hi hj
      rcases lt_trichotomy j i with h | h | h
      · exact a072061_e_ne_o ha (by omega) h hji
      · subst h
        rw [a072061_e_eq ha j (by omega)] at hji
        have := hfl j hj.1
        omega
      · have h1 := a072061_o_strict ha hi.1 h
        rw [a072061_e_eq ha j (by omega)] at hji
        omega
    have hsub : (Finset.Icc 1 (m - 1)).image (a072061_o a) ∪ (Finset.Icc j1 J).image (a072061_e a)
        ⊆ Finset.Icc 1 (a072061_o a m - 1) := by
      intro v hv
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hv
      rw [Finset.mem_Icc]
      rcases hv with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
      · rw [Finset.mem_Icc] at hi
        have h1 := a072061_o_strict ha hi.1 (show i < m by omega)
        have h2 := a072061_o_pos ha i hi.1
        omega
      · rw [Finset.mem_Icc] at hj
        have hJ1 : 1 ≤ J := by omega
        have h1 : a072061_e a j ≤ a072061_e a J := by
          rcases eq_or_lt_of_le hj.2 with h | h
          · rw [h]
          · exact (a072061_e_strict hk ha (by omega) h).le
        have h2 := hJspec hJ1
        have h3 : 1 ≤ a072061_e a j := by
          rw [a072061_e_eq ha j (by omega)]
          have := a072061_o_pos ha j (by omega)
          omega
        omega
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_eq_card_add_card.mpr hdisj, Finset.card_image_of_injOn,
      Finset.card_image_of_injOn] at hc
    · simp only [Nat.card_Icc] at hc
      omega
    · intro x hx y hy hxy
      rw [Finset.coe_Icc, Set.mem_Icc] at hx hy
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact absurd hxy (a072061_e_strict hk ha (by omega) h).ne
      · exact absurd hxy (a072061_e_strict hk ha (by omega) h).ne'
    · intro x hx y hy hxy
      rw [Finset.coe_Icc, Set.mem_Icc] at hx hy
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact absurd hxy (a072061_o_strict ha hx.1 h).ne
      · exact absurd hxy (a072061_o_strict ha hy.1 h).ne'
  refine ⟨J, by omega, by omega, ?_, hJspec, hJnext⟩
  omega

/-- The odd-indexed terms stay within a bounded distance of alpha * m, alpha = 1 - k + sqrt (k^2 + 1). -/
theorem a072061_bounded {k : ℝ} {a : ℕ → ℕ} (hk : 0 < k) (ha : IsGenSeq k a) :
    ∃ R : ℝ, ∀ m : ℕ, 1 ≤ m →
      |(a072061_o a m : ℝ) - (1 - k + Real.sqrt (k ^ 2 + 1)) * m| ≤ R := by
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (k ^ 2 + 1) := ⟨_, rfl⟩
  rw [← hs]
  have hs2 : s ^ 2 = k ^ 2 + 1 := by rw [hs]; exact Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hsk : k < s := by nlinarith
  have hs1 : 1 < s := by nlinarith
  have hks : s ≤ 1 + k := by nlinarith
  obtain ⟨α, hα⟩ : ∃ α, α = 1 - k + s := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = α + 2 * k := ⟨_, rfl⟩
  rw [← hα]
  have hαβ : β * (α - 1) = α := by
    rw [hβ, hα]
    linear_combination hs2
  have hα1 : 1 ≤ α := by rw [hα]; linarith
  have hβ2 : 0 < β - 2 := by rw [hβ, hα]; linarith
  obtain ⟨j1, hj1, hfl⟩ := a072061_j1 hk
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = β * j1 + 1 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = max |(a072061_o a 1 : ℝ) - α * 1| (max (C / (β - 2)) j1) :=
    ⟨_, rfl⟩
  have hR1 : |(a072061_o a 1 : ℝ) - α * 1| ≤ R := by rw [hR]; exact le_max_left _ _
  have hR0 : 0 ≤ R := le_trans (abs_nonneg _) hR1
  have hRj : (j1 : ℝ) ≤ R := by rw [hR]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hRC : C ≤ (β - 2) * R := by
    have h1 : C / (β - 2) ≤ R := by rw [hR]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    rw [div_le_iff₀ hβ2] at h1
    linarith
  refine ⟨R, ?_⟩
  intro m hm
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rcases eq_or_lt_of_le hm with h | h
  · subst h
    simpa using hR1
  obtain ⟨J, hJm, hA, hB, hCJ, hD⟩ := a072061_count hk ha hj1 hfl m h
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (a072061_o a m : ℝ) - α * m := ⟨_, rfl⟩
  rw [← hx]
  have hA' : (a072061_o a m : ℝ) ≤ m + J := by exact_mod_cast hA
  have hB' : (m : ℝ) + J + 1 ≤ a072061_o a m + j1 := by exact_mod_cast hB
  have hβ0 : 0 < β := by linarith
  rw [abs_le]
  constructor
  · -- lower bound
    rw [a072061_e_eq ha (J + 1) (by omega)] at hD
    have hfle : (⌊k * (2 * ((J + 1 : ℕ) : ℝ))⌋₊ : ℝ) ≤ k * (2 * ((J + 1 : ℕ) : ℝ)) :=
      Nat.floor_le (by positivity)
    have hD' : (a072061_o a m : ℝ) ≤ a072061_o a (J + 1) + 2 * k * ((J : ℝ) + 1) := by
      have : ((a072061_o a m : ℕ) : ℝ) ≤ ((a072061_o a (J + 1) + ⌊k * (2 * ((J + 1 : ℕ) : ℝ))⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast hD
      push_cast at this hfle
      linarith
    rcases eq_or_lt_of_le hJm with hJe | hJl
    · -- J + 1 = m
      have hmJ : (m : ℝ) = J + 1 := by exact_mod_cast hJe.symm
      have : 0 ≤ (1 + k - s) * m := mul_nonneg (by linarith) (Nat.cast_nonneg m)
      rw [hx, hα]
      nlinarith
    · have hIH := ih (J + 1) hJl (by omega)
      rw [abs_le] at hIH
      have t1 : (a072061_o a (J + 1) : ℝ) ≤ α * ((J + 1 : ℕ) : ℝ) + R := by linarith [hIH.2]
      push_cast at t1
      have t2 : β * ((J : ℝ) + 1) ≤ β * ((a072061_o a m : ℝ) + j1 - m) :=
        mul_le_mul_of_nonneg_left (by linarith) hβ0.le
      have t3 : β * ((a072061_o a m : ℝ) + j1 - m) = α * m + β * x + β * j1 := by
        linear_combination (m : ℝ) * hαβ - β * hx
      have t4 : β * ((J : ℝ) + 1) = α * ((J : ℝ) + 1) + 2 * k * ((J : ℝ) + 1) := by
        rw [hβ]; ring
      have key : -(β * j1 + R) ≤ (β - 1) * x := by nlinarith
      by_contra hneg
      push Not at hneg
      have : (β - 1) * x < (β - 1) * (-R) := mul_lt_mul_of_pos_left hneg (by linarith)
      nlinarith
  · -- upper bound
    rcases Nat.eq_zero_or_pos J with hJ0 | hJpos
    · subst hJ0
      have : (1 - α) * (m : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg m)
      rw [hx]
      push_cast at hA'
      nlinarith
    · have hC' := hCJ hJpos
      rw [a072061_e_eq ha J hJpos] at hC'
      have hflt : k * (2 * (J : ℝ)) < (⌊k * (2 * (J : ℝ))⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have hC'' : (a072061_o a J : ℝ) + 2 * k * J - 1 < a072061_o a m := by
        have : ((a072061_o a J + ⌊k * (2 * (J : ℝ))⌋₊ : ℕ) : ℝ) < ((a072061_o a m : ℕ) : ℝ) := by
          exact_mod_cast hC'
        push_cast at this
        linarith
      have hIH := ih J (by omega) hJpos
      rw [abs_le] at hIH
      have s1 : β * J < (a072061_o a m : ℝ) + R + 1 := by
        have : β * J = α * J + 2 * k * J := by rw [hβ]; ring
        linarith [hIH.1]
      have s2 : β * ((a072061_o a m : ℝ) - m) ≤ β * J :=
        mul_le_mul_of_nonneg_left (by linarith) hβ0.le
      have s3 : β * ((a072061_o a m : ℝ) - m) = α * m + β * x := by
        linear_combination (m : ℝ) * hαβ - β * hx
      have key : (β - 1) * x < R + 1 := by nlinarith
      by_contra hpos
      push Not at hpos
      have : (β - 1) * R < (β - 1) * x := mul_lt_mul_of_pos_left hpos (by linarith)
      have hbj : 0 ≤ β * (j1 : ℝ) := mul_nonneg hβ0.le (Nat.cast_nonneg _)
      linarith

theorem a072061_o_tendsto {k : ℝ} {a : ℕ → ℕ} (hk : 0 < k) (ha : IsGenSeq k a) :
    Tendsto (fun m : ℕ => (a072061_o a m : ℝ) / m) atTop
      (𝓝 (1 - k + Real.sqrt (k ^ 2 + 1))) := by
  obtain ⟨R, hR⟩ := a072061_bounded hk ha
  obtain ⟨α, hα⟩ : ∃ α, α = 1 - k + Real.sqrt (k ^ 2 + 1) := ⟨_, rfl⟩
  rw [← hα] at hR ⊢
  have hlow : Tendsto (fun m : ℕ => α - R * (1 / (m : ℝ))) atTop (𝓝 α) := by
    have := (tendsto_const_nhds (x := α)).sub
      ((tendsto_const_nhds (x := R)).mul tendsto_one_div_atTop_nhds_zero_nat)
    rwa [mul_zero, sub_zero] at this
  have hup : Tendsto (fun m : ℕ => α + R * (1 / (m : ℝ))) atTop (𝓝 α) := by
    have := (tendsto_const_nhds (x := α)).add
      ((tendsto_const_nhds (x := R)).mul tendsto_one_div_atTop_nhds_zero_nat)
    rwa [mul_zero, add_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have h1 := (abs_le.mp (hR m hm)).1
    rw [le_div_iff₀ hmR]
    have e : (α - R * (1 / (m : ℝ))) * m = α * m - R := by field_simp
    rw [e]
    linarith
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have h1 := (abs_le.mp (hR m hm)).2
    rw [div_le_iff₀ hmR]
    have e : (α + R * (1 / (m : ℝ))) * m = α * m + R := by field_simp
    rw [e]
    linarith

theorem a072061_floor_tendsto {k : ℝ} (hk : 0 < k) :
    Tendsto (fun m : ℕ => (⌊k * (2 * m : ℝ)⌋₊ : ℝ) / m) atTop (𝓝 (2 * k)) := by
  have hlow : Tendsto (fun m : ℕ => 2 * k - 1 / (m : ℝ)) atTop (𝓝 (2 * k)) := by
    have := (tendsto_const_nhds (x := 2 * k)).sub tendsto_one_div_atTop_nhds_zero_nat
    rwa [sub_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have h := Nat.lt_floor_add_one (k * (2 * (m : ℝ)))
    rw [le_div_iff₀ hmR]
    have e : (2 * k - 1 / (m : ℝ)) * m = k * (2 * m) - 1 := by field_simp
    rw [e]
    linarith
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have h := Nat.floor_le (show 0 ≤ k * (2 * (m : ℝ)) by positivity)
    rw [div_le_iff₀ hmR]
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a072061.main := by
  intro k hk a ha
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (k ^ 2 + 1) := ⟨_, rfl⟩
  have hs2 : s ^ 2 = k ^ 2 + 1 := by rw [hs]; exact Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hsk : k < s := by nlinarith
  have hα0 : 0 < 1 - k + s := by linarith
  have ho := OMA.Helpers.a072061_o_tendsto hk ha
  rw [← hs] at ho ⊢
  have hf := OMA.Helpers.a072061_floor_tendsto hk
  have hlim := (tendsto_const_nhds (x := (1 : ℝ))).add (hf.div ho hα0.ne')
  have hval : 1 + 2 * k / (1 - k + s) = k + s := by
    field_simp
    nlinarith [hs2]
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hmR : (0 : ℝ) < n := by exact_mod_cast hn
  have hopos : (0 : ℝ) < OMA.Helpers.a072061_o a n := by
    exact_mod_cast OMA.Helpers.a072061_o_pos ha n hn
  have he : (a (2 * n) : ℝ) = OMA.Helpers.a072061_o a n + ⌊k * (2 * n : ℝ)⌋₊ := by
    exact_mod_cast OMA.Helpers.a072061_e_eq ha n hn
  have ho' : (a (2 * n - 1) : ℝ) = OMA.Helpers.a072061_o a n := rfl
  show 1 + (⌊k * (2 * n : ℝ)⌋₊ : ℝ) / n / ((OMA.Helpers.a072061_o a n : ℝ) / n) =
    (a (2 * n) : ℝ) / (a (2 * n - 1) : ℝ)
  rw [he, ho']
  field_simp
