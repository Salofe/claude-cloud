import OMAStatements.S_oeis_a330910

/-!
Proof of Barker's two conjectures for OEIS A330910.

Let `T m` be the family of all subsets of {1, ..., m} (the empty set and singletons included)
whose elements pairwise differ by at least 5, and `t m` its size. Splitting by whether `m + 5`
belongs to the set gives `t (m + 5) = t (m + 4) + t m` (removing `m + 5` leaves a subset of
{1, ..., m}), and `t m = m + 1` for `m ≤ 4`. The sets with at most one element are `m + 1` in
number, so `a n + (n + 6) = t (n + 5)`. The recurrence of `a` then follows from that of `t`
(the denominator is `(1 - x)^2 (1 - x - x^5)`), and the generating function by comparing
coefficients, with `a(0..6) = 0, 1, 3, 6, 10, 15, 22`.
-/

namespace OMA.Helpers

open OMA.S_oeis_a330910 Finset PowerSeries

/-- All subsets of {1, ..., m} whose elements pairwise differ by at least 5. -/
def a330910T (m : ℕ) : Finset (Finset ℕ) :=
  (Icc 1 m).powerset.filter fun S => ∀ x ∈ S, ∀ y ∈ S, x < y → x + 5 ≤ y

theorem a330910_T_succ_notMem (m : ℕ) :
    (a330910T (m + 5)).filter (fun S => ¬ (m + 5 ∈ S)) = a330910T (m + 4) := by
  ext S
  simp only [a330910T, mem_filter, mem_powerset]
  constructor
  · rintro ⟨⟨hsub, hgap⟩, hnot⟩
    refine ⟨?_, hgap⟩
    intro x hx
    have h1 := hsub hx
    have h2 : x ≠ m + 5 := fun h => hnot (h ▸ hx)
    rw [mem_Icc] at h1 ⊢
    omega
  · rintro ⟨hsub, hgap⟩
    refine ⟨⟨fun x hx => ?_, hgap⟩, fun hm => ?_⟩
    · have h1 := hsub hx
      rw [mem_Icc] at h1 ⊢
      omega
    · have h1 := hsub hm
      rw [mem_Icc] at h1
      omega

theorem a330910_T_succ_mem (m : ℕ) :
    ((a330910T (m + 5)).filter (fun S => m + 5 ∈ S)).card = (a330910T m).card := by
  apply Finset.card_nbij' (fun S => S.erase (m + 5)) (fun S => insert (m + 5) S)
  · intro S hS
    rw [mem_coe] at hS ⊢
    simp only [a330910T, mem_filter, mem_powerset] at hS ⊢
    obtain ⟨⟨hsub, hgap⟩, hm⟩ := hS
    refine ⟨fun x hx => ?_, fun x hx y hy hxy => hgap x (mem_of_mem_erase hx) y
      (mem_of_mem_erase hy) hxy⟩
    have hne := ne_of_mem_erase hx
    have hxS := mem_of_mem_erase hx
    have h1 := hsub hxS
    rw [mem_Icc] at h1 ⊢
    have h2 := hgap x hxS (m + 5) hm (by omega)
    omega
  · intro S hS
    rw [mem_coe] at hS ⊢
    simp only [a330910T, mem_filter, mem_powerset] at hS ⊢
    obtain ⟨hsub, hgap⟩ := hS
    refine ⟨⟨?_, ?_⟩, mem_insert_self _ _⟩
    · intro x hx
      rw [mem_insert] at hx
      rcases hx with rfl | hx
      · rw [mem_Icc]; omega
      · have h1 := hsub hx
        rw [mem_Icc] at h1 ⊢
        omega
    · intro x hx y hy hxy
      rw [mem_insert] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · omega
      · have h1 := hsub hy
        rw [mem_Icc] at h1
        omega
      · have h1 := hsub hx
        rw [mem_Icc] at h1
        omega
      · exact hgap x hx y hy hxy
  · intro S hS
    rw [mem_coe] at hS
    simp only [a330910T, mem_filter] at hS
    exact insert_erase hS.2
  · intro S hS
    rw [mem_coe] at hS
    simp only [a330910T, mem_filter, mem_powerset] at hS
    apply erase_insert
    intro hm
    have h1 := hS.1 hm
    rw [mem_Icc] at h1
    omega

theorem a330910_T_rec (m : ℕ) :
    (a330910T (m + 5)).card = (a330910T (m + 4)).card + (a330910T m).card := by
  rw [← card_filter_add_card_filter_not (s := a330910T (m + 5)) (fun S => m + 5 ∈ S),
    a330910_T_succ_mem, a330910_T_succ_notMem, add_comm]

theorem a330910_T_small : (a330910T 0).card = 1 ∧ (a330910T 1).card = 2 ∧
    (a330910T 2).card = 3 ∧ (a330910T 3).card = 4 ∧ (a330910T 4).card = 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem a330910_small_sets (m : ℕ) :
    ((Icc 1 m).powerset.filter fun S : Finset ℕ => S.card ≤ 1).card = m + 1 := by
  have e : ((Icc 1 m).powerset.filter fun S : Finset ℕ => S.card ≤ 1) =
      powersetCard 0 (Icc 1 m) ∪ powersetCard 1 (Icc 1 m) := by
    ext S
    simp only [mem_filter, mem_powerset, mem_union, mem_powersetCard]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_or_ge S.card 1 with h | h
      · exact Or.inl ⟨h1, by omega⟩
      · exact Or.inr ⟨h1, by omega⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨h1, by omega⟩
  rw [e, card_union_of_disjoint, card_powersetCard, card_powersetCard, Nat.card_Icc,
    Nat.choose_zero_right, Nat.choose_one_right]
  · omega
  · rw [disjoint_left]
    intro S h1 h2
    rw [mem_powersetCard] at h1 h2
    omega

theorem a330910_a_eq (n : ℕ) : a n + (n + 6) = (a330910T (n + 5)).card := by
  have e1 : sets (n + 5) = (a330910T (n + 5)).filter (fun S => 2 ≤ S.card) := by
    ext S
    simp only [sets, a330910T, mem_filter]
    tauto
  have e2 : (a330910T (n + 5)).filter (fun S => ¬ 2 ≤ S.card) =
      (Icc 1 (n + 5)).powerset.filter fun S : Finset ℕ => S.card ≤ 1 := by
    ext S
    simp only [a330910T, mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, ?_⟩, by omega⟩
      intro x hx y hy hxy
      have := (card_le_one.mp h2) x hx y hy
      omega
  rw [← card_filter_add_card_filter_not (s := a330910T (n + 5)) (fun S => 2 ≤ S.card), e2,
    a330910_small_sets, ← e1]
  rfl

theorem a330910_rec (n : ℕ) (hn : 6 < n) : (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) +
    a (n - 3) + a (n - 5) - 2 * a (n - 6) + a (n - 7) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
    show m + 7 - 3 = m + 4 by omega, show m + 7 - 5 = m + 2 by omega,
    show m + 7 - 6 = m + 1 by omega, show m + 7 - 7 = m by omega]
  have r0 : (a330910T (m + 12)).card = (a330910T (m + 11)).card + (a330910T (m + 7)).card :=
    a330910_T_rec (m + 7)
  have r1 : (a330910T (m + 11)).card = (a330910T (m + 10)).card + (a330910T (m + 6)).card :=
    a330910_T_rec (m + 6)
  have r2 : (a330910T (m + 10)).card = (a330910T (m + 9)).card + (a330910T (m + 5)).card :=
    a330910_T_rec (m + 5)
  have b0 : a m + (m + 6) = (a330910T (m + 5)).card := a330910_a_eq m
  have b1 : a (m + 1) + (m + 7) = (a330910T (m + 6)).card := a330910_a_eq (m + 1)
  have b2 : a (m + 2) + (m + 8) = (a330910T (m + 7)).card := a330910_a_eq (m + 2)
  have b4 : a (m + 4) + (m + 10) = (a330910T (m + 9)).card := a330910_a_eq (m + 4)
  have b5 : a (m + 5) + (m + 11) = (a330910T (m + 10)).card := a330910_a_eq (m + 5)
  have b6 : a (m + 6) + (m + 12) = (a330910T (m + 11)).card := a330910_a_eq (m + 6)
  have b7 : a (m + 7) + (m + 13) = (a330910T (m + 12)).card := a330910_a_eq (m + 7)
  omega

theorem a330910_vals : a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 6 ∧ a 4 = 10 ∧ a 5 = 15 ∧
    a 6 = 22 := by
  obtain ⟨t0, t1, t2, t3, t4⟩ := a330910_T_small
  have t5 := a330910_T_rec 0
  have t6 := a330910_T_rec 1
  have t7 := a330910_T_rec 2
  have t8 := a330910_T_rec 3
  have t9 := a330910_T_rec 4
  have t10 := a330910_T_rec 5
  have t11 := a330910_T_rec 6
  have b0 := a330910_a_eq 0
  have b1 := a330910_a_eq 1
  have b2 := a330910_a_eq 2
  have b3 := a330910_a_eq 3
  have b4 := a330910_a_eq 4
  have b5 := a330910_a_eq 5
  have b6 := a330910_a_eq 6
  norm_num at t5 t6 t7 t8 t9 t10 t11 b0 b1 b2 b3 b4 b5 b6
  omega

theorem a330910_gf :
    gf = X * ((1 - X) ^ 2 * (1 - X + X ^ 2) * (1 - X ^ 2 - X ^ 3))⁻¹ := by
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := a330910_vals
  have e1 : gf * ((1 - X) ^ 2 * (1 - X + X ^ 2) * (1 - X ^ 2 - X ^ 3))
      = gf - PowerSeries.C (3 : ℚ) * (gf * X ^ 1) + PowerSeries.C (3 : ℚ) * (gf * X ^ 2)
        - gf * X ^ 3 - gf * X ^ 5 + PowerSeries.C (2 : ℚ) * (gf * X ^ 6) - gf * X ^ 7 := by
    simp only [map_ofNat]
    ring
  rw [e1]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', gf,
    PowerSeries.coeff_mk, PowerSeries.coeff_X]
  rcases Nat.lt_or_ge k 7 with hk | hk
  · interval_cases k
    · norm_num [h0]
    · norm_num [h0, h1]
    · norm_num [h0, h1, h2]
    · norm_num [h0, h1, h2, h3]
    · norm_num [h0, h1, h2, h3, h4]
    · norm_num [h0, h1, h2, h3, h4, h5]
    · norm_num [h0, h1, h2, h3, h4, h5, h6]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 7 := ⟨k - 7, by omega⟩
    have hr := a330910_rec (m + 7) (by omega)
    simp only [show 1 ≤ m + 7 by omega, show 2 ≤ m + 7 by omega, show 3 ≤ m + 7 by omega,
      show 5 ≤ m + 7 by omega, show 6 ≤ m + 7 by omega, show 7 ≤ m + 7 by omega,
      show m + 7 ≠ 1 by omega, if_true, if_false]
    have hq : ((a (m + 7) : ℤ) : ℚ) = ((3 * a (m + 7 - 1) - 3 * a (m + 7 - 2) +
        a (m + 7 - 3) + a (m + 7 - 5) - 2 * a (m + 7 - 6) + a (m + 7 - 7) : ℤ) : ℚ) := by
      rw [hr]
    push_cast at hq
    simp only [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
      show m + 7 - 3 = m + 4 by omega, show m + 7 - 5 = m + 2 by omega,
      show m + 7 - 6 = m + 1 by omega, show m + 7 - 7 = m by omega]
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a330910.main :=
  ⟨OMA.Helpers.a330910_gf, OMA.Helpers.a330910_rec⟩
