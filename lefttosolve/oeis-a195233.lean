import OMAStatements.S_oeis_a195233

/-!
Proof of Barker's conjectures for A195233 (lower triangles of a 3 X 3 array with entries in 0..n,
each entry differing from all of its diagonal, vertical, antidiagonal and horizontal neighbors by
one or less).

Any two cells of the triangle are equal, adjacent, or have a common neighbor (`near`), so in a good
array any two entries differ by at most 2 (`good_le_two`). Split the good arrays with entries in
0..m+2 by whether they take the value m + 2:
* those that do not are exactly the good arrays with entries in 0..m+1 (`card_low`);
* those that do have all their entries at least m, and subtracting m from every entry is a
  bijection onto the good arrays with entries in 0..2 that take the value 2 (`card_high`). There
  are 91 of these (`K_eq`, a finite check over the 3^6 arrays).
Hence a(m+2) = a(m+1) + 91 (`step`), and with a(1) = 64 (`a_one`, a finite check: all 2^6 arrays
with entries in 0..1 are good) we get a(n) = 91 n - 27 for n ≥ 1 (`closed`). The recurrence and the generating function follow by comparing
coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a195233 Finset

instance decAdj (p q : Fin 3 × Fin 3) : Decidable (Adj p q) := by
  unfold Adj
  infer_instance

instance decGood {n : ℕ} (f : Cell → Fin (n + 1)) : Decidable (Good f) := by
  unfold Good
  infer_instance

/-- Any two cells of the triangle are equal, adjacent, or have a common neighbor. -/
theorem near : ∀ c d : Cell, c = d ∨ Adj c.1 d.1 ∨ ∃ e : Cell, Adj c.1 e.1 ∧ Adj e.1 d.1 := by
  decide +kernel

/-- In a good array any two entries differ by at most 2. -/
theorem good_le_two {n : ℕ} {f : Cell → Fin (n + 1)} (hf : Good f) (c d : Cell) :
    |(f c : ℤ) - f d| ≤ 2 := by
  rcases near c d with h | h | ⟨e, h1, h2⟩
  · subst h
    simp
  · have := hf c d h
    linarith
  · have h1' := abs_le.1 (hf c e h1)
    have h2' := abs_le.1 (hf e d h2)
    rw [abs_le]
    constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]

/-- Goodness only depends on the entries up to a common shift. -/
theorem good_of_shift {n k : ℕ} {f : Cell → Fin (n + 1)} {g : Cell → Fin (k + 1)} (t : ℤ)
    (h : ∀ c, (g c : ℤ) = f c + t) (hf : Good f) : Good g := by
  intro p q hpq
  rw [h p, h q, add_sub_add_right_eq_sub]
  exact hf p q hpq

/-- `a n` as the number of good arrays in a filtered `Finset`, with a decidable test. -/
theorem a_eq_card (n : ℕ) : a n = #(univ.filter (fun f : Cell → Fin (n + 1) => Good f)) := by
  unfold a
  convert Fintype.card_subtype (fun f : Cell → Fin (n + 1) => Good f)

/-- The good arrays with entries in 0..m+2 avoiding the value m + 2 are the good arrays with
entries in 0..m+1. -/
theorem card_low (m : ℕ) :
    #(univ.filter (fun f : Cell → Fin (m + 2 + 1) => Good f ∧ ¬ ∃ c, (f c : ℕ) = m + 2)) =
      #(univ.filter (fun g : Cell → Fin (m + 1 + 1) => Good g)) := by
  refine card_nbij' (fun f c => ⟨min (f c : ℕ) (m + 1), by omega⟩)
    (fun g c => ⟨g c, by have := (g c).isLt; omega⟩) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hf ⊢
    obtain ⟨hg, hno⟩ := hf
    refine good_of_shift 0 (fun c => ?_) hg
    have h1 := (f c).isLt
    have h2 : (f c : ℕ) ≠ m + 2 := fun h => hno ⟨c, h⟩
    show ((min (f c : ℕ) (m + 1) : ℕ) : ℤ) = (f c : ℤ) + 0
    omega
  · intro g hg
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hg ⊢
    refine ⟨good_of_shift 0 (fun c => ?_) hg, ?_⟩
    · show ((g c : ℕ) : ℤ) = (g c : ℤ) + 0
      omega
    · rintro ⟨c, hc⟩
      have h1 := (g c).isLt
      have h2 : (g c : ℕ) = m + 2 := hc
      omega
  · intro f hf
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hf
    funext c
    apply Fin.ext
    have h1 := (f c).isLt
    have h2 : (f c : ℕ) ≠ m + 2 := fun h => hf.2 ⟨c, h⟩
    show min (f c : ℕ) (m + 1) = f c
    omega
  · intro g hg
    funext c
    apply Fin.ext
    have := (g c).isLt
    show min (g c : ℕ) (m + 1) = g c
    omega

/-- A good array with entries in 0..m+2 that takes the value m + 2 has all its entries at least
m. -/
theorem low_bound {m : ℕ} {f : Cell → Fin (m + 2 + 1)} (hf : Good f)
    (hc : ∃ c, (f c : ℕ) = m + 2) (d : Cell) : m ≤ (f d : ℕ) := by
  obtain ⟨c, hc⟩ := hc
  have h := abs_le.1 (good_le_two hf d c)
  rw [hc] at h
  push_cast at h
  omega

/-- The good arrays with entries in 0..m+2 taking the value m + 2 are the shifts by m of the good
arrays with entries in 0..2 taking the value 2. -/
theorem card_high (m : ℕ) :
    #(univ.filter (fun f : Cell → Fin (m + 2 + 1) => Good f ∧ ∃ c, (f c : ℕ) = m + 2)) =
      #(univ.filter (fun g : Cell → Fin 3 => Good g ∧ ∃ c, (g c : ℕ) = 2)) := by
  refine card_nbij' (fun f c => ⟨(f c : ℕ) - m, by have := (f c).isLt; omega⟩)
    (fun g c => ⟨g c + m, by have := (g c).isLt; omega⟩) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hf ⊢
    obtain ⟨hg, c, hc⟩ := hf
    have hl := low_bound hg ⟨c, hc⟩
    refine ⟨good_of_shift (-(m : ℤ)) (fun d => ?_) hg, c, ?_⟩
    · have := hl d
      show (((f d : ℕ) - m : ℕ) : ℤ) = (f d : ℤ) + -(m : ℤ)
      omega
    · show (f c : ℕ) - m = 2
      omega
  · intro g hg
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hg ⊢
    obtain ⟨hg, c, hc⟩ := hg
    refine ⟨good_of_shift (m : ℤ) (fun d => ?_) hg, c, ?_⟩
    · show (((g d : ℕ) + m : ℕ) : ℤ) = (g d : ℤ) + (m : ℤ)
      omega
    · show (g c : ℕ) + m = m + 2
      omega
  · intro f hf
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hf
    funext d
    apply Fin.ext
    have := low_bound hf.1 hf.2 d
    show (f d : ℕ) - m + m = f d
    omega
  · intro g hg
    funext d
    apply Fin.ext
    show (g d : ℕ) + m - m = g d
    omega

/-- There are 91 good arrays with entries in 0..2 that take the value 2. -/
theorem K_eq : #(univ.filter (fun g : Cell → Fin 3 => Good g ∧ ∃ c, (g c : ℕ) = 2)) = 91 := by
  decide +kernel

/-- All 2^6 arrays with entries in 0..1 are good. -/
theorem a_one : a 1 = 64 := by
  rw [a_eq_card]
  decide +kernel

/-- Splitting by whether the value m + 2 is taken: a(m+2) = a(m+1) + 91. -/
theorem step (m : ℕ) : a (m + 2) = a (m + 1) + 91 := by
  rw [a_eq_card, a_eq_card, ← card_filter_add_card_filter_not (fun f => ∃ c, (f c : ℕ) = m + 2),
    filter_filter, filter_filter, card_high, card_low, K_eq, add_comm]

/-- The closed form a(n) = 91 n - 27 for n ≥ 1. -/
theorem closed (n : ℕ) (hn : 1 ≤ n) : a n = 91 * n - 27 := by
  induction n, hn using Nat.le_induction with
  | base => rw [a_one]
  | succ n hn ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [step, ih]
    omega

theorem closedQ (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = 91 * n - 27 := by
  rw [closed n hn]
  have h : 27 ≤ 91 * n := by omega
  push_cast [h]
  ring

theorem recurrence (n : ℕ) (hn : 2 < n) : (a n : ℤ) = 2 * a (n - 1) - a (n - 2) := by
  rw [closed n (by omega), closed (n - 1) (by omega), closed (n - 2) (by omega)]
  omega

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 2 =
      X * (64 + 27 * X) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  have key : PowerSeries.mk F * (1 - X) ^ 2 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 2 * (PowerSeries.mk F * X ^ 1) +
        C 1 * (PowerSeries.mk F * X ^ 2) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (64 + 27 * X) = C 64 * X ^ 1 + C 27 * X ^ 2 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 3
  · interval_cases k <;> norm_num [hF, closedQ]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    simp only [show 0 ≤ j + 3 by omega, show 1 ≤ j + 3 by omega, show 2 ≤ j + 3 by omega,
      show j + 3 - 0 = j + 3 by omega, show j + 3 - 1 = j + 2 by omega,
      show j + 3 - 2 = j + 1 by omega, show ¬ (j + 3 = 1) by omega, show ¬ (j + 3 = 2) by omega,
      show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega,
      if_true, if_false, hF]
    rw [closedQ (j + 3) (by omega), closedQ (j + 2) (by omega), closedQ (j + 1) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a195233.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
