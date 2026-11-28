import OMAStatements.S_oeis_a396102
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a396102 Finset

section Gen

variable {R : Type*} [CommRing R]

theorem powSeq_map {S : Type*} [CommRing S] (φ : R →+* S) (g : ℕ → R) (k n : ℕ) :
    powSeq (fun i => φ (g i)) k n = φ (powSeq g k n) := by
  induction k generalizing n with
  | zero => simp only [powSeq]; split_ifs <;> simp
  | succ k ih => simp only [powSeq, map_sum, map_mul, ih]

theorem comp_map {S : Type*} [CommRing S] (φ : R →+* S) (f g : ℕ → R) (n : ℕ) :
    comp (fun i => φ (f i)) (fun i => φ (g i)) n = φ (comp f g n) := by
  simp only [comp, map_sum, map_mul, powSeq_map]

theorem iterComp_map {S : Type*} [CommRing S] (φ : R →+* S) (f : ℕ → R) (r n : ℕ) :
    iterComp (fun i => φ (f i)) r n = φ (iterComp f r n) := by
  induction r generalizing n with
  | zero => simp only [iterComp]; split_ifs <;> simp
  | succ r ih =>
    simp only [iterComp]
    rw [show iterComp (fun i => φ (f i)) r = fun i => φ (iterComp f r i) from funext ih]
    exact comp_map φ f _ n

theorem powSeq_eq_zero (g : ℕ → R) (h0 : g 0 = 0) (k : ℕ) :
    ∀ m, m < k → powSeq g k m = 0 := by
  induction k with
  | zero => intro m hm; omega
  | succ k ih =>
    intro m hm
    simp only [powSeq]
    refine Finset.sum_eq_zero ?_
    intro i hi
    simp only [Finset.mem_range] at hi
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simp [h0]
    · rw [ih (m - i) (by omega), mul_zero]

theorem powSeq_one (g : ℕ → R) (n : ℕ) : powSeq g 1 n = g n := by
  simp only [powSeq]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b hb hne
    have : n - b ≠ 0 := by simp at hb; omega
    simp [this]
  · intro h; simp at h

theorem powSeq_self (g : ℕ → R) (h0 : g 0 = 0) (h1 : g 1 = 1) (k : ℕ) : powSeq g k k = 1 := by
  induction k with
  | zero => simp [powSeq]
  | succ k ih =>
    simp only [powSeq]
    rw [Finset.sum_eq_single 1]
    · simp [h1, ih]
    · intro b hb hne
      rcases Nat.eq_zero_or_pos b with h | h
      · subst h; simp [h0]
      · rw [powSeq_eq_zero g h0 k (k + 1 - b) (by simp at hb; omega), mul_zero]
    · intro h; simp at h

theorem powSeq_congr (g g' : ℕ → R) (m : ℕ) (h : ∀ i ≤ m, g i = g' i) (k : ℕ) :
    ∀ n ≤ m, powSeq g k n = powSeq g' k n := by
  induction k with
  | zero => intro n _; rfl
  | succ k ih =>
    intro n hn
    simp only [powSeq]
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp at hi
    rw [h i (by omega), ih (n - i) (by omega)]

theorem powSeq_top (g g' : ℕ → R) (h0 : g 0 = 0) (h0' : g' 0 = 0) (n : ℕ)
    (h : ∀ i < n, g i = g' i) (k : ℕ) (hk : 2 ≤ k) : powSeq g k n = powSeq g' k n := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [powSeq]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp at hi
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · subst hi0; simp [h0, h0']
  · rcases Nat.lt_or_ge i n with hin | hin
    · rw [h i hin, powSeq_congr g g' (n - 1) (fun l hl => h l (by omega)) j (n - i) (by omega)]
    · have : n - i = 0 := by omega
      rw [this, powSeq_eq_zero g h0 j 0 (by omega), powSeq_eq_zero g' h0' j 0 (by omega),
        mul_zero, mul_zero]

theorem comp_zero (f g : ℕ → R) (hf0 : f 0 = 0) : comp f g 0 = 0 := by
  simp [comp, hf0]

theorem comp_one' (f g : ℕ → R) (hf0 : f 0 = 0) (hf1 : f 1 = 1) (hg1 : g 1 = 1) :
    comp f g 1 = 1 := by
  simp [comp, Finset.sum_range_succ, hf0, hf1, powSeq_one, hg1]

theorem comp_low (f f' g g' : ℕ → R) (n : ℕ) (hf : ∀ i < n, f i = f' i) (hg : ∀ i < n, g i = g' i)
    (m : ℕ) (hm : m < n) : comp f g m = comp f' g' m := by
  simp only [comp]
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp at hk
  rw [hf k (by omega), powSeq_congr g g' m (fun i hi => hg i (by omega)) k m le_rfl]

theorem comp_diff (f f' g g' : ℕ → R) (hf0 : f 0 = 0) (hf0' : f' 0 = 0) (hf1 : f 1 = 1)
    (hf1' : f' 1 = 1) (hg0 : g 0 = 0) (hg0' : g' 0 = 0) (hg1 : g 1 = 1) (hg1' : g' 1 = 1)
    (n : ℕ) (hn : 2 ≤ n) (hf : ∀ i < n, f i = f' i) (hg : ∀ i < n, g i = g' i) :
    comp f g n - comp f' g' n = (f n - f' n) + (g n - g' n) := by
  simp only [comp]
  rw [← Finset.sum_sub_distrib]
  have key : ∀ k ∈ range (n + 1), f k * powSeq g k n - f' k * powSeq g' k n =
      (if k = n then f n - f' n else 0) + (if k = 1 then g n - g' n else 0) := by
    intro k hk
    simp at hk
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · simp [hf0, hf0']; omega
      · have : (1 : ℕ) ≠ n := by omega
        simp [hf1, hf1', powSeq_one, this]
    · rcases Nat.lt_or_ge k n with hkn | hkn
      · have h1 : k ≠ n := by omega
        have h2 : k ≠ 1 := by omega
        simp only [h1, h2, if_false, add_zero]
        rw [hf k hkn, powSeq_top g g' hg0 hg0' n hg k hk2, sub_self]
      · have h1 : k = n := by omega
        have h2 : k ≠ 1 := by omega
        subst h1
        simp only [h2, if_true, if_false, add_zero]
        rw [powSeq_self g hg0 hg1, powSeq_self g' hg0' hg1']
        ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp
  omega

theorem iterComp_zero (f : ℕ → R) (hf0 : f 0 = 0) (r : ℕ) : iterComp f r 0 = 0 := by
  cases r with
  | zero => simp [iterComp]
  | succ r => exact comp_zero _ _ hf0

theorem iterComp_one (f : ℕ → R) (hf0 : f 0 = 0) (hf1 : f 1 = 1) (r : ℕ) :
    iterComp f r 1 = 1 := by
  induction r with
  | zero => simp [iterComp]
  | succ r ih => exact comp_one' _ _ hf0 hf1 ih

theorem iterComp_diff (a b : ℕ → R) (ha0 : a 0 = 0) (hb0 : b 0 = 0) (ha1 : a 1 = 1)
    (hb1 : b 1 = 1) (n : ℕ) (hn : 2 ≤ n) (hab : ∀ i < n, a i = b i) (r : ℕ) :
    (∀ m < n, iterComp a r m = iterComp b r m) ∧
      iterComp a r n - iterComp b r n = (r : R) * (a n - b n) := by
  induction r with
  | zero => simp [iterComp]
  | succ r ih =>
    refine ⟨fun m hm => comp_low a b _ _ n hab ih.1 m hm, ?_⟩
    simp only [iterComp]
    rw [comp_diff a b (iterComp a r) (iterComp b r) ha0 hb0 ha1 hb1 (iterComp_zero a ha0 r)
      (iterComp_zero b hb0 r) (iterComp_one a ha0 ha1 r) (iterComp_one b hb0 hb1 r) n hn hab ih.1,
      ih.2]
    push_cast
    ring

/-- The series `x / (1 - x)`. -/
def cS : ℕ → R := fun n => if n = 0 then 0 else 1

/-- The series `x / (1 - t x)`. -/
def hS (t : R) : ℕ → R := fun n => if n = 0 then 0 else t ^ (n - 1)

theorem powSeq_coeff (g : ℕ → R) (k n : ℕ) :
    powSeq g k n = PowerSeries.coeff n ((PowerSeries.mk g) ^ k) := by
  induction k generalizing n with
  | zero => simp [powSeq, PowerSeries.coeff_one]
  | succ k ih =>
    rw [pow_succ', PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i (PowerSeries.mk g) * PowerSeries.coeff j (PowerSeries.mk g ^ k))]
    simp only [powSeq, PowerSeries.coeff_mk, ih]

theorem comp_cS_hS (t : R) (n : ℕ) : comp cS (hS t) n = hS (t + 1) n := by
  set G : PowerSeries R := PowerSeries.mk (hS t) with hGdef
  have hG : G * (1 - PowerSeries.C t * PowerSeries.X) = PowerSeries.X := by
    ext m
    rw [mul_sub, mul_one, map_sub]
    rcases m with _ | m
    · simp [hGdef, hS]
    · rw [show G * (PowerSeries.C t * PowerSeries.X) = PowerSeries.C t * (G * PowerSeries.X) by ring,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_X]
      simp only [hGdef, PowerSeries.coeff_mk, hS]
      rcases m with _ | m
      · simp
      · simp [pow_succ]; ring
  set Gs : PowerSeries R := ∑ k ∈ range n, G ^ k with hGs
  set S : PowerSeries R := G * Gs with hS'
  have hgeom : Gs * (1 - G) = 1 - G ^ n := geom_sum_mul_neg G n
  have hid : S - PowerSeries.C (t + 1) * (S * PowerSeries.X) = PowerSeries.X * (1 - G ^ n) := by
    rw [map_add, map_one, hS']
    linear_combination (G * (1 - PowerSeries.C t * PowerSeries.X)) * hgeom +
      (G * Gs + 1 - G ^ n) * hG
  have hGn : ∀ m < n, PowerSeries.coeff m (G ^ n) = 0 := by
    intro m hm
    rw [← powSeq_coeff]
    exact powSeq_eq_zero _ (by simp [hS]) n m hm
  have hu0 : PowerSeries.coeff 0 S = 0 := by
    have := congrArg (PowerSeries.coeff 0) hid
    rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_mul_X,
      PowerSeries.coeff_zero_X_mul] at this
    simpa using this
  have hus : ∀ m < n, PowerSeries.coeff (m + 1) S =
      (t + 1) * PowerSeries.coeff m S + (if m = 0 then 1 else 0) := by
    intro m hm
    have := congrArg (PowerSeries.coeff (m + 1)) hid
    rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_mul_X,
      PowerSeries.coeff_succ_X_mul, map_sub, PowerSeries.coeff_one, hGn m hm] at this
    linear_combination this
  have hu : ∀ m ≤ n, PowerSeries.coeff m S = hS (t + 1) m := by
    intro m
    induction m with
    | zero => intro _; simp [hu0, hS]
    | succ m ih =>
      intro hm
      rw [hus m (by omega), ih (by omega)]
      rcases m with _ | m
      · simp [hS]
      · simp [hS, pow_succ]; ring
  rw [← hu n le_rfl]
  simp only [comp, powSeq_coeff]
  rw [hS', hGs, Finset.mul_sum, map_sum, Finset.sum_range_succ']
  simp only [cS, if_pos, Nat.add_one_ne_zero, if_false, one_mul, zero_mul, add_zero]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [pow_succ']

theorem iterComp_cS (r n : ℕ) : iterComp (cS : ℕ → R) r n = hS (r : R) n := by
  induction r generalizing n with
  | zero =>
    simp only [iterComp, hS, Nat.cast_zero]
    rcases n with _ | _ | n <;> simp
  | succ r ih =>
    simp only [iterComp]
    rw [show iterComp (cS : ℕ → R) r = hS (r : R) from funext ih, comp_cS_hS]
    push_cast
    rfl

end Gen

theorem cS_eq (n : ℕ) :
    iterComp (cS : ℕ → ZMod 3) 3 (n + 1) =
      iterComp (cS : ℕ → ZMod 3) 2 (n + 1) + iterComp (cS : ℕ → ZMod 3) 2 n := by
  rw [iterComp_cS, iterComp_cS, iterComp_cS]
  have h3 : ((3 : ℕ) : ZMod 3) = 0 := by decide
  rcases n with _ | m
  · simp [hS]
  · simp only [hS, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, h3]
    have : ((2 : ℕ) : ZMod 3) ^ (m + 1) + ((2 : ℕ) : ZMod 3) ^ m =
        ((2 : ℕ) : ZMod 3) ^ m * ((3 : ℕ) : ZMod 3) := by push_cast; ring
    rw [this, h3]
    simp

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a396102.main := by
  intro a ha0 ha1 heq
  set b : ℕ → ZMod 3 := fun n => (Int.castRingHom (ZMod 3)) (a n) with hb
  have hbeq : ∀ n, OMA.S_oeis_a396102.iterComp b 3 (n + 1) =
      OMA.S_oeis_a396102.iterComp b 2 (n + 1) + OMA.S_oeis_a396102.iterComp b 2 n := by
    intro n
    simp only [hb, OMA.Helpers.iterComp_map, heq n, map_add]
  have hb0 : b 0 = 0 := by simp [hb, ha0]
  have hb1 : b 1 = 1 := by simp [hb, ha1]
  have hc0 : (OMA.Helpers.cS : ℕ → ZMod 3) 0 = 0 := by simp [OMA.Helpers.cS]
  have hc1 : (OMA.Helpers.cS : ℕ → ZMod 3) 1 = 1 := by simp [OMA.Helpers.cS]
  have hall : ∀ n, b n = OMA.Helpers.cS n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.lt_or_ge n 2 with hn | hn
      · interval_cases n
        · rw [hb0, hc0]
        · rw [hb1, hc1]
      · have d3 := (OMA.Helpers.iterComp_diff b OMA.Helpers.cS hb0 hc0 hb1 hc1 n hn ih 3)
        have d2 := (OMA.Helpers.iterComp_diff b OMA.Helpers.cS hb0 hc0 hb1 hc1 n hn ih 2)
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        have e1 := hbeq m
        have e2 := OMA.Helpers.cS_eq m
        have e3 := d2.1 m (by omega)
        have := d3.2
        have := d2.2
        push_cast at d3 d2
        linear_combination (-1 : ZMod 3) * d3.2 + d2.2 + e1 - e2 + e3
  intro n hn
  have h := hall n
  simp only [hb, OMA.Helpers.cS, show n ≠ 0 by omega, if_false] at h
  have h2 : ((a n : ℤ) : ZMod 3) = ((1 : ℤ) : ZMod 3) := by simpa using h
  exact (ZMod.intCast_eq_intCast_iff (a n) 1 3).1 h2
