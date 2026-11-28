import OMAStatements.S_oeis_a183624

/-!
Proof of the three formulas of OEIS A183624 ((n+1) X 2 arrays over 0..2 with every 2 X 2
subblock summing to 4).

With two columns, the subblocks are the pairs of consecutive rows, so the condition says that the
row sums r_0, r_1, ... satisfy r_i + r_(i+1) = 4: the row sums alternate s, 4 - s, s, ...
The number c(s) of rows (two entries in 0..2) with sum s is 1, 2, 3, 2, 1 for s = 0..4, and
c(4 - s) = c(s). Splitting off the first row gives F(n+1, s) = c(s) * F(n, 4 - s) for the number
F(n, s) of valid arrays whose first row sums to s, hence F(n, s) = c(s)^(n+1), and summing over s
gives a(n) = 2 + 2^(n+2) + 3^(n+1). The recurrence and the generating function follow.
-/

namespace OMA.Helpers

open OMA.S_oeis_a183624

def a183624_rs (r : Fin 2 → Fin 3) : ℕ := (r 0).val + (r 1).val

def a183624_c (s : ℕ) : ℕ :=
  (Finset.univ.filter (fun r : Fin 2 → Fin 3 => a183624_rs r = s)).card

def a183624_F (n s : ℕ) : ℕ :=
  (Finset.univ.filter (fun g : Grid n => IsValid g ∧ a183624_rs (g 0) = s)).card

theorem a183624_c0 : a183624_c 0 = 1 := by decide
theorem a183624_c1 : a183624_c 1 = 2 := by decide
theorem a183624_c2 : a183624_c 2 = 3 := by decide
theorem a183624_c3 : a183624_c 3 = 2 := by decide
theorem a183624_c4 : a183624_c 4 = 1 := by decide

theorem a183624_c_symm (s : ℕ) (hs : s ≤ 4) : a183624_c (4 - s) = a183624_c s := by
  interval_cases s <;> simp [a183624_c0, a183624_c1, a183624_c2, a183624_c3, a183624_c4]

theorem a183624_rs_le (r : Fin 2 → Fin 3) : a183624_rs r ≤ 4 := by
  unfold a183624_rs
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  omega

theorem a183624_valid_cons {n : ℕ} (g : Grid (n + 1)) :
    IsValid g ↔ a183624_rs (g 0) + a183624_rs (Fin.tail g 0) = 4 ∧ IsValid (Fin.tail g) := by
  unfold IsValid a183624_rs
  rw [Fin.forall_fin_succ]
  simp only [Fin.tail, Fin.succ_castSucc]
  have e : (Fin.castSucc (0 : Fin (n + 1))) = 0 := rfl
  rw [e]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩

theorem a183624_F_zero (s : ℕ) : a183624_F 0 s = a183624_c s := by
  unfold a183624_F a183624_c
  apply Finset.card_equiv (Equiv.funUnique (Fin 1) (Fin 2 → Fin 3))
  intro g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.funUnique_apply]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    exact ⟨fun i => i.elim0, h⟩

theorem a183624_F_succ (n s : ℕ) :
    a183624_F (n + 1) s = a183624_c s * a183624_F n (4 - s) := by
  unfold a183624_F a183624_c
  rw [← Finset.card_product]
  apply Finset.card_equiv (Fin.consEquiv (fun _ => Fin 2 → Fin 3)).symm
  intro g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
    Fin.consEquiv_symm_apply]
  rw [a183624_valid_cons]
  have := a183624_rs_le (g 0)
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h3, h2, by omega⟩
  · rintro ⟨h3, h2, h4⟩
    exact ⟨⟨by omega, h2⟩, h3⟩

theorem a183624_F_closed (n s : ℕ) (hs : s ≤ 4) : a183624_F n s = a183624_c s ^ (n + 1) := by
  induction n generalizing s with
  | zero => rw [a183624_F_zero, zero_add, pow_one]
  | succ m ih =>
    rw [a183624_F_succ, ih (4 - s) (by omega), a183624_c_symm s hs, pow_succ' _ (m + 1)]

theorem a183624_card (n : ℕ) :
    (Finset.univ.filter (fun g : Grid (n + 1) => IsValid g)).card
      = 2 + 2 ^ (n + 3) + 3 ^ (n + 2) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g : Grid (n + 1) => a183624_rs (g 0))
    (t := Finset.range 5) (fun g _ => by
      simp only [Finset.coe_range, Set.mem_Iio]
      have := a183624_rs_le (g 0)
      omega)]
  have e : ∀ b ∈ Finset.range 5,
      ((Finset.univ.filter (fun g : Grid (n + 1) => IsValid g)).filter
        (fun g => a183624_rs (g 0) = b)).card = a183624_c b ^ (n + 2) := by
    intro b hb
    rw [Finset.filter_filter, ← a183624_F_closed (n + 1) b (by simp at hb; omega)]
    rfl
  rw [Finset.sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, a183624_c0, a183624_c1, a183624_c2,
    a183624_c3, a183624_c4]
  ring

theorem a183624_closed (m : ℕ) : a (m + 1) = 2 + 2 ^ (m + 3) + 3 ^ (m + 2) := by
  show ((Finset.univ.filter (fun g : Grid (m + 1) => IsValid g)).card : ℤ) = _
  rw [a183624_card]
  push_cast
  ring

theorem a183624_zero : a 0 = 0 := rfl

theorem a183624_rec (n : ℕ) (hn : 4 ≤ n) :
    a n = 6 * a (n - 1) - 11 * a (n - 2) + 6 * a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = (m + 2) + 1 by omega, show m + 4 - 2 = (m + 1) + 1 by omega,
    show m + 4 - 3 = m + 1 by omega, show m + 4 = (m + 3) + 1 by omega]
  rw [a183624_closed, a183624_closed, a183624_closed, a183624_closed]
  ring

theorem a183624_gf :
    PowerSeries.mk a * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X))
      = PowerSeries.X * (19 - 69 * PowerSeries.X + 54 * PowerSeries.X ^ 2) := by
  set p : PowerSeries ℤ := PowerSeries.mk a with hp
  have e1 : p * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X)) =
      p - PowerSeries.C (6 : ℤ) * (p * PowerSeries.X ^ 1)
        + PowerSeries.C (11 : ℤ) * (p * PowerSeries.X ^ 2)
        - PowerSeries.C (6 : ℤ) * (p * PowerSeries.X ^ 3) := by
    rw [map_ofNat, map_ofNat]
    ring
  have e2 : (PowerSeries.X * (19 - 69 * PowerSeries.X + 54 * PowerSeries.X ^ 2) : PowerSeries ℤ)
      = PowerSeries.C (19 : ℤ) * PowerSeries.X ^ 1 - PowerSeries.C (69 : ℤ) * PowerSeries.X ^ 2
        + PowerSeries.C (54 : ℤ) * PowerSeries.X ^ 3 := by
    rw [map_ofNat, map_ofNat, map_ofNat]
    ring
  rw [e1, e2]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul_X_pow]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', hp, PowerSeries.coeff_mk]
  by_cases hk : k < 4
  · interval_cases k
    · simp [a183624_zero]
    · simp [a183624_zero, show a 1 = 19 from a183624_closed 0]
    · simp [a183624_zero, show a 1 = 19 from a183624_closed 0, show a 2 = 45 from a183624_closed 1]
    · simp [a183624_zero, show a 1 = 19 from a183624_closed 0, show a 2 = 45 from a183624_closed 1,
        show a 3 = 115 from a183624_closed 2]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
    rw [if_pos (show 1 ≤ j + 4 by omega), if_pos (show 2 ≤ j + 4 by omega),
      if_pos (show 3 ≤ j + 4 by omega), if_neg (show ¬ (j + 4 = 1) by omega),
      if_neg (show ¬ (j + 4 = 2) by omega), if_neg (show ¬ (j + 4 = 3) by omega)]
    rw [a183624_rec (j + 4) (by omega)]
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a183624.main := by
  refine ⟨fun n hn => ?_, OMA.Helpers.a183624_rec, OMA.Helpers.a183624_gf⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [OMA.Helpers.a183624_closed]
  ring
