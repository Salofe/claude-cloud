import OMAStatements.S_oeis_a049980
import Mathlib

/-!
Proof of the divisor-sum formula for OEIS A049980.

A progression with k >= 2 terms, first term a and difference d has sum n iff
k(2a + d(k - 1)) = 2n. For odd k = 2h + 1 this says k divides n and a + dh = n / k, so the
progressions are indexed by 1 <= d <= (n / k - 1) / h = floor(2(n - k) / (k(k - 1))). For even
k = 2m it says m divides n and 2a + d(2m - 1) = q := n / m, so d has the parity of q and
d(2m - 1) <= q - 2; writing d = 2e or d = 2e + 1 gives the floor terms of the second sum. The
proof builds these families as explicit finsets, shows that their union is the set in the
statement, and evaluates each floor as a natural-number quotient.
-/

namespace OMA.Helpers

open OMA.S_oeis_a049980 Finset

/-- Number of odd-length progressions with `m` terms (`m` odd, `m > 1`, `m ∣ n`). -/
def Dodd (n m : ℕ) : ℕ := (n / m - 1) / (m / 2)

/-- Even-length progressions with `2m` terms when `n / m` is even. -/
def Ev (n m : ℕ) : ℕ := (n / m - 2) / (2 * (2 * m - 1))

/-- Even-length progressions with `2m` terms when `n / m` is odd. -/
def Od (n m : ℕ) : ℕ := (n / m + 2 * m - 3) / (2 * (2 * m - 1))

def Dev (n m : ℕ) : ℕ := if Even (n / m) then Ev n m else Od n m

/-- The progressions with `m` terms, `m` odd, indexed by their difference `d`. -/
def fo (n m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Icc 1 (Dodd n m)).image fun d => (n / m - d * (m / 2), d, m)

/-- The progressions with `2m` terms, indexed by `e` with difference `2e` or `2e + 1`. -/
def fe (n m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  if Even (n / m) then
    (Icc 1 (Ev n m)).image fun e => ((n / m - 2 * e * (2 * m - 1)) / 2, 2 * e, 2 * m)
  else
    (range (Od n m)).image fun e => ((n / m - (2 * e + 1) * (2 * m - 1)) / 2, 2 * e + 1, 2 * m)

def Uo (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (n.divisors.filter (fun m => Odd m ∧ 1 < m)).biUnion (fo n)

def Ue (n : ℕ) : Finset (ℕ × ℕ × ℕ) := n.divisors.biUnion (fe n)

theorem fo_third {n m : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ fo n m) : t.2.2 = m := by
  unfold fo at ht
  obtain ⟨d, -, rfl⟩ := mem_image.1 ht
  rfl

theorem fe_third {n m : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ fe n m) : t.2.2 = 2 * m := by
  unfold fe at ht
  split_ifs at ht
  · obtain ⟨d, -, rfl⟩ := mem_image.1 ht
    rfl
  · obtain ⟨d, -, rfl⟩ := mem_image.1 ht
    rfl

theorem card_fo (n m : ℕ) : (fo n m).card = Dodd n m := by
  unfold fo
  rw [card_image_of_injective _ (fun d d' h => by simpa using congrArg (fun t => t.2.1) h),
    Nat.card_Icc]
  omega

theorem card_fe (n m : ℕ) : (fe n m).card = Dev n m := by
  unfold fe Dev
  split_ifs
  · rw [card_image_of_injective _ (fun e e' h => by
      have := congrArg (fun t => t.2.1) h
      simp only at this
      omega), Nat.card_Icc]
    omega
  · rw [card_image_of_injective _ (fun e e' h => by
      have := congrArg (fun t => t.2.1) h
      simp only at this
      omega), card_range]

theorem card_Uo (n : ℕ) :
    (Uo n).card = ∑ m ∈ n.divisors.filter (fun m => Odd m ∧ 1 < m), Dodd n m := by
  unfold Uo
  rw [card_biUnion]
  · exact sum_congr rfl fun m _ => card_fo n m
  · intro x _ y _ hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro t h1 h2
    exact hxy ((fo_third h1).symm.trans (fo_third h2))

theorem card_Ue (n : ℕ) : (Ue n).card = ∑ m ∈ n.divisors, Dev n m := by
  unfold Ue
  rw [card_biUnion]
  · exact sum_congr rfl fun m _ => card_fe n m
  · intro x _ y _ hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro t h1 h2
    have := (fe_third h1).symm.trans (fe_third h2)
    exact hxy (by omega)

theorem disj_UoUe (n : ℕ) : Disjoint (Uo n) (Ue n) := by
  rw [Finset.disjoint_left]
  intro t h1 h2
  obtain ⟨m, hm, ht⟩ := mem_biUnion.1 h1
  obtain ⟨m', -, ht'⟩ := mem_biUnion.1 h2
  have e1 := fo_third ht
  have e2 := fe_third ht'
  obtain ⟨h, rfl⟩ := (mem_filter.1 hm).2.1
  omega


theorem mem_odd {n a d h : ℕ} (ha : 1 ≤ a) (hd : 1 ≤ d) (hh : 1 ≤ h)
    (hn : n = (2 * h + 1) * (a + d * h)) : (a, d, 2 * h + 1) ∈ Uo n := by
  have hn0 : n ≠ 0 := by
    rw [hn]
    positivity
  have hdiv : n / (2 * h + 1) = a + d * h := by rw [hn, Nat.mul_div_cancel_left _ (by omega)]
  have h2 : (2 * h + 1) / 2 = h := by omega
  unfold Uo
  rw [mem_biUnion]
  refine ⟨2 * h + 1, ?_, ?_⟩
  · rw [mem_filter, Nat.mem_divisors]
    exact ⟨⟨⟨a + d * h, hn⟩, hn0⟩, ⟨h, rfl⟩, by omega⟩
  · unfold fo
    rw [mem_image]
    refine ⟨d, ?_, ?_⟩
    · rw [mem_Icc]
      refine ⟨hd, ?_⟩
      unfold Dodd
      rw [hdiv, h2, Nat.le_div_iff_mul_le (by omega)]
      omega
    · rw [hdiv, h2, Nat.add_sub_cancel]

theorem mem_even_e {n a e m : ℕ} (ha : 1 ≤ a) (he : 1 ≤ e)
    (hn : n = (m + 1) * (2 * a + 2 * e * (2 * m + 1))) : (a, 2 * e, 2 * (m + 1)) ∈ Ue n := by
  have hn0 : n ≠ 0 := by
    rw [hn]
    positivity
  have hdiv : n / (m + 1) = 2 * a + 2 * e * (2 * m + 1) := by
    rw [hn, Nat.mul_div_cancel_left _ (by omega)]
  have hev : Even (2 * a + 2 * e * (2 * m + 1)) := ⟨a + e * (2 * m + 1), by ring⟩
  have hs : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  unfold Ue
  rw [mem_biUnion]
  refine ⟨m + 1, Nat.mem_divisors.2 ⟨⟨_, hn⟩, hn0⟩, ?_⟩
  unfold fe
  rw [hdiv, if_pos hev, mem_image]
  refine ⟨e, ?_, ?_⟩
  · rw [mem_Icc]
    refine ⟨he, ?_⟩
    unfold Ev
    rw [hdiv, hs, Nat.le_div_iff_mul_le (by omega)]
    have : e * (2 * (2 * m + 1)) = 2 * e * (2 * m + 1) := by ring
    omega
  · rw [hs, Nat.add_sub_cancel]
    simp only [Prod.mk.injEq, and_true]
    omega

theorem mem_even_o {n a e m : ℕ} (ha : 1 ≤ a)
    (hn : n = (m + 1) * (2 * a + (2 * e + 1) * (2 * m + 1))) :
    (a, 2 * e + 1, 2 * (m + 1)) ∈ Ue n := by
  have hn0 : n ≠ 0 := by
    rw [hn]
    positivity
  have hdiv : n / (m + 1) = 2 * a + (2 * e + 1) * (2 * m + 1) := by
    rw [hn, Nat.mul_div_cancel_left _ (by omega)]
  have hodd : ¬ Even (2 * a + (2 * e + 1) * (2 * m + 1)) := by
    rw [Nat.not_even_iff_odd]
    exact ⟨a + 2 * e * m + e + m, by ring⟩
  have hs : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  unfold Ue
  rw [mem_biUnion]
  refine ⟨m + 1, Nat.mem_divisors.2 ⟨⟨_, hn⟩, hn0⟩, ?_⟩
  unfold fe
  rw [hdiv, if_neg hodd, mem_image]
  refine ⟨e, ?_, ?_⟩
  · rw [mem_range]
    unfold Od
    rw [hdiv, hs, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega)]
    have h1 : (e + 1) * (2 * (2 * m + 1)) = (2 * e + 1) * (2 * m + 1) + (2 * m + 1) := by ring
    omega
  · rw [hs, Nat.add_sub_cancel]
    simp only [Prod.mk.injEq, and_true]
    omega

/-- The predicate defining the set in the statement. -/
def Pr (n : ℕ) (t : ℕ × ℕ × ℕ) : Prop :=
  1 ≤ t.1 ∧ 1 ≤ t.2.1 ∧ 2 ≤ t.2.2 ∧ 2 * t.2.2 * t.1 + t.2.1 * t.2.2 * (t.2.2 - 1) = 2 * n

theorem pr_of_Uo {n : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ Uo n) : Pr n t := by
  unfold Uo at ht
  obtain ⟨m, hm, ht⟩ := mem_biUnion.1 ht
  rw [mem_filter, Nat.mem_divisors] at hm
  obtain ⟨⟨⟨q, hq⟩, hn0⟩, ⟨h, rfl⟩, h1⟩ := hm
  unfold fo at ht
  obtain ⟨d, hd, rfl⟩ := mem_image.1 ht
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (by rintro rfl; simp at hq; exact hn0 hq)
  have hdiv : n / (2 * h + 1) = q := by rw [hq, Nat.mul_div_cancel_left _ (by omega)]
  have h2 : (2 * h + 1) / 2 = h := by omega
  rw [mem_Icc] at hd
  unfold Dodd at hd
  rw [hdiv, h2, Nat.le_div_iff_mul_le (by omega)] at hd
  obtain ⟨hd1, hd2⟩ := hd
  rw [hdiv, h2]
  obtain ⟨A, hA⟩ : ∃ A, q = A + d * h := ⟨q - d * h, by omega⟩
  have hA1 : 1 ≤ A := by omega
  rw [hA, Nat.add_sub_cancel]
  show 1 ≤ A ∧ 1 ≤ d ∧ 2 ≤ 2 * h + 1 ∧
    2 * (2 * h + 1) * A + d * (2 * h + 1) * (2 * h + 1 - 1) = 2 * n
  refine ⟨hA1, hd1, by omega, ?_⟩
  rw [hq, hA, show 2 * h + 1 - 1 = 2 * h by omega]
  ring

theorem pr_of_Ue {n : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ Ue n) : Pr n t := by
  unfold Ue at ht
  obtain ⟨m, hm, ht⟩ := mem_biUnion.1 ht
  rw [Nat.mem_divisors] at hm
  obtain ⟨⟨q, hq⟩, hn0⟩ := hm
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp at hq
      exact absurd hq hn0
    · omega⟩
  have hdiv : n / (m + 1) = q := by rw [hq, Nat.mul_div_cancel_left _ (by omega)]
  have hs : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  unfold fe at ht
  rw [hdiv, hs] at ht
  split_ifs at ht with hev
  · obtain ⟨e, he, rfl⟩ := mem_image.1 ht
    rw [mem_Icc] at he
    unfold Ev at he
    rw [hdiv, hs, Nat.le_div_iff_mul_le (by omega)] at he
    obtain ⟨he1, he2⟩ := he
    obtain ⟨r, hr⟩ := hev
    have hX1 : e * (2 * (2 * m + 1)) = 2 * (e * (2 * m + 1)) := by ring
    have hX2 : 2 * e * (2 * m + 1) = 2 * (e * (2 * m + 1)) := by ring
    have hXpos : 1 ≤ e * (2 * m + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    rw [hX1] at he2
    rw [hX2]
    obtain ⟨A, hA⟩ : ∃ A, q = 2 * A + 2 * (e * (2 * m + 1)) :=
      ⟨(q - 2 * (e * (2 * m + 1))) / 2, by omega⟩
    have hA1 : 1 ≤ A := by omega
    have hsub : (q - 2 * (e * (2 * m + 1))) / 2 = A := by omega
    rw [hsub]
    show 1 ≤ A ∧ 1 ≤ 2 * e ∧ 2 ≤ 2 * (m + 1) ∧
      2 * (2 * (m + 1)) * A + 2 * e * (2 * (m + 1)) * (2 * (m + 1) - 1) = 2 * n
    refine ⟨hA1, by omega, by omega, ?_⟩
    rw [hq, hA, hs]
    ring
  · obtain ⟨e, he, rfl⟩ := mem_image.1 ht
    rw [mem_range] at he
    unfold Od at he
    rw [hdiv, hs, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega)] at he
    rw [Nat.not_even_iff_odd] at hev
    obtain ⟨r, hr⟩ := hev
    have hX : (e + 1) * (2 * (2 * m + 1)) = 4 * (e * m) + 2 * e + 4 * m + 2 := by ring
    have hY : (2 * e + 1) * (2 * m + 1) = 4 * (e * m) + 2 * e + 2 * m + 1 := by ring
    rw [hX] at he
    rw [hY]
    obtain ⟨A, hA⟩ : ∃ A, q = 2 * A + (4 * (e * m) + 2 * e + 2 * m + 1) :=
      ⟨(q - (4 * (e * m) + 2 * e + 2 * m + 1)) / 2, by omega⟩
    have hA1 : 1 ≤ A := by omega
    have hsub : (q - (4 * (e * m) + 2 * e + 2 * m + 1)) / 2 = A := by omega
    rw [hsub]
    show 1 ≤ A ∧ 1 ≤ 2 * e + 1 ∧ 2 ≤ 2 * (m + 1) ∧
      2 * (2 * (m + 1)) * A + (2 * e + 1) * (2 * (m + 1)) * (2 * (m + 1) - 1) = 2 * n
    refine ⟨hA1, by omega, by omega, ?_⟩
    rw [hq, hA, hs]
    ring

theorem set_eq (n : ℕ) : {t : ℕ × ℕ × ℕ | Pr n t} = ↑(Uo n ∪ Ue n) := by
  ext ⟨a, d, k⟩
  simp only [Set.mem_ofPred_eq, coe_union, Set.mem_union, mem_coe]
  constructor
  · rintro ⟨ha, hd, hk, he⟩
    simp only at ha hd hk he
    rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨h, hh⟩
    · right
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hk' : k = 2 * (m + 1) := by omega
      subst hk'
      rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega] at he
      rcases Nat.even_or_odd d with ⟨e, rfl⟩ | ⟨e, rfl⟩
      · have he1 : 1 ≤ e := by omega
        have hn : n = (m + 1) * (2 * a + 2 * e * (2 * m + 1)) := by
          have : 2 * n = 2 * ((m + 1) * (2 * a + 2 * e * (2 * m + 1))) := by rw [← he]; ring
          omega
        have := mem_even_e ha he1 hn
        rwa [show e + e = 2 * e by ring]
      · have hn : n = (m + 1) * (2 * a + (2 * e + 1) * (2 * m + 1)) := by
          have : 2 * n = 2 * ((m + 1) * (2 * a + (2 * e + 1) * (2 * m + 1))) := by
            rw [← he]; ring
          omega
        exact mem_even_o ha hn
    · left
      subst hh
      rw [show 2 * h + 1 - 1 = 2 * h by omega] at he
      have hn : n = (2 * h + 1) * (a + d * h) := by
        have : 2 * n = 2 * ((2 * h + 1) * (a + d * h)) := by rw [← he]; ring
        omega
      exact mem_odd ha hd (by omega) hn
  · rintro (h | h)
    · exact pr_of_Uo h
    · exact pr_of_Ue h


theorem floor_odd_aux (h q : ℕ) (hq1 : 1 ≤ q) (hh : 1 ≤ h) :
    Int.floor ((2 * ((((2 * h + 1) * q : ℕ) : ℚ) - ((2 * h + 1 : ℕ) : ℚ))) /
      (((2 * h + 1 : ℕ) : ℚ) * (((2 * h + 1 : ℕ) : ℚ) - 1))) = (((q - 1) / h : ℕ) : ℤ) := by
  have hh' : (0 : ℚ) < h := by exact_mod_cast hh
  have e : (2 * ((((2 * h + 1) * q : ℕ) : ℚ) - ((2 * h + 1 : ℕ) : ℚ))) /
      (((2 * h + 1 : ℕ) : ℚ) * (((2 * h + 1 : ℕ) : ℚ) - 1)) = ((q - 1 : ℕ) : ℚ) / (h : ℚ) := by
    rw [div_eq_div_iff (by push_cast; nlinarith) (by positivity)]
    push_cast [Nat.cast_sub hq1]
    ring
  rw [e, Rat.floor_natCast_div_natCast]
  push_cast
  rfl

theorem floor_odd {n m : ℕ} (hm : m ∈ n.divisors.filter (fun m => Odd m ∧ 1 < m)) :
    Int.floor ((2 * ((n : ℚ) - (m : ℚ))) / ((m : ℚ) * ((m : ℚ) - 1))) = (Dodd n m : ℤ) := by
  rw [mem_filter, Nat.mem_divisors] at hm
  obtain ⟨⟨⟨q, rfl⟩, hn0⟩, ⟨h, rfl⟩, h1⟩ := hm
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (by rintro rfl; simp at hn0)
  have hD : Dodd ((2 * h + 1) * q) (2 * h + 1) = (q - 1) / h := by
    unfold Dodd
    rw [Nat.mul_div_cancel_left _ (by omega), show (2 * h + 1) / 2 = h by omega]
  rw [hD]
  exact floor_odd_aux h q hq1 (by omega)

theorem floor_even_aux (m q : ℕ) (hq1 : 1 ≤ q) :
    Int.floor (((((m + 1) * q : ℕ) : ℚ) - ((m + 1 : ℕ) : ℚ) * (5 - (-1 : ℚ) ^ q) / 2 +
      ((m + 1 : ℕ) : ℚ) ^ 2 * (1 - (-1 : ℚ) ^ q)) /
      (2 * ((m + 1 : ℕ) : ℚ) * (2 * ((m + 1 : ℕ) : ℚ) - 1))) =
      (Dev ((m + 1) * q) (m + 1) : ℤ) := by
  have hdiv : (m + 1) * q / (m + 1) = q := Nat.mul_div_cancel_left _ (by omega)
  have hs : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  unfold Dev Ev Od
  rw [hdiv, hs]
  rcases Nat.even_or_odd q with hq | hq
  · rw [if_pos hq, hq.neg_one_pow]
    have hq2 : 2 ≤ q := by obtain ⟨r, hr⟩ := hq; omega
    have e : ((((m + 1) * q : ℕ) : ℚ) - ((m + 1 : ℕ) : ℚ) * (5 - 1) / 2 +
        ((m + 1 : ℕ) : ℚ) ^ 2 * (1 - 1)) / (2 * ((m + 1 : ℕ) : ℚ) * (2 * ((m + 1 : ℕ) : ℚ) - 1)) =
        ((q - 2 : ℕ) : ℚ) / ((2 * (2 * m + 1) : ℕ) : ℚ) := by
      rw [div_eq_div_iff (by push_cast; nlinarith) (by positivity)]
      push_cast [Nat.cast_sub hq2]
      ring
    rw [e, Rat.floor_natCast_div_natCast]
    push_cast
    rfl
  · rw [if_neg (Nat.not_even_iff_odd.2 hq), hq.neg_one_pow]
    rw [show q + 2 * (m + 1) - 3 = (q - 1) + 2 * m by omega]
    have e : ((((m + 1) * q : ℕ) : ℚ) - ((m + 1 : ℕ) : ℚ) * (5 - -1) / 2 +
        ((m + 1 : ℕ) : ℚ) ^ 2 * (1 - -1)) / (2 * ((m + 1 : ℕ) : ℚ) * (2 * ((m + 1 : ℕ) : ℚ) - 1)) =
        ((q - 1 + 2 * m : ℕ) : ℚ) / ((2 * (2 * m + 1) : ℕ) : ℚ) := by
      rw [div_eq_div_iff (by push_cast; nlinarith) (by positivity)]
      push_cast [Nat.cast_sub hq1]
      ring
    rw [e, Rat.floor_natCast_div_natCast]
    push_cast
    rfl

theorem floor_even {n m : ℕ} (hm : m ∈ n.divisors) :
    Int.floor (((n : ℚ) - (m : ℚ) * (5 - (-1 : ℚ) ^ (n / m)) / 2 +
      (m : ℚ) ^ 2 * (1 - (-1 : ℚ) ^ (n / m))) / (2 * (m : ℚ) * (2 * (m : ℚ) - 1))) =
      (Dev n m : ℤ) := by
  rw [Nat.mem_divisors] at hm
  obtain ⟨⟨q, rfl⟩, hn0⟩ := hm
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp at hn0
    · omega⟩
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (by rintro rfl; simp at hn0)
  rw [Nat.mul_div_cancel_left _ (by omega)]
  exact floor_even_aux m q hq1

end OMA.Helpers

open OMA.S_oeis_a049980 in
theorem OMA.solution : type_of% @OMA.S_oeis_a049980.main := by
  intro n hn
  unfold a
  have hS : {t : ℕ × ℕ × ℕ | 1 ≤ t.1 ∧ 1 ≤ t.2.1 ∧ 2 ≤ t.2.2 ∧
      2 * t.2.2 * t.1 + t.2.1 * t.2.2 * (t.2.2 - 1) = 2 * n} =
      ↑(OMA.Helpers.Uo n ∪ OMA.Helpers.Ue n) := OMA.Helpers.set_eq n
  rw [hS, Set.ncard_coe_finset, Finset.card_union_of_disjoint (OMA.Helpers.disj_UoUe n),
    OMA.Helpers.card_Uo, OMA.Helpers.card_Ue,
    Finset.sum_congr rfl (fun m hm => OMA.Helpers.floor_odd hm),
    Finset.sum_congr rfl (fun m hm => OMA.Helpers.floor_even hm)]
  push_cast
  ring
