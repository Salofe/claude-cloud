import OMAStatements.S_oeis_a195249

/-!
Proof of Barker's conjectures for A195249 (lower triangles of a 3 X 3 array with entries in 0..n,
each entry differing from all of its diagonal, vertical, antidiagonal and horizontal neighbors by
two or less).

Any two cells of the triangle are equal, adjacent, or have a common neighbor (`near_cells`), so in
a good array any two entries differ by at most 4 (`good_le_four`). Split the good arrays with
entries in 0..m+4 by whether they take the value m + 4:
* those that do not are exactly the good arrays with entries in 0..m+3 (`card_low`);
* those that do have all their entries at least m, and subtracting m from every entry is a
  bijection onto the good arrays with entries in 0..4 that take the value 4 (`card_high`); let `K`
  be their number.
Hence a(m+4) = a(m+3) + K (`step`). The small values a(1), ..., a(4) = 64, 729, 1682, 2729 are
finite checks, done on 6-tuples of naturals (`a_eq_T`: an array is the same as the 6-tuple of its
entries, and goodness is a test on the 10 pairs of neighbors). Then K = a(4) - a(3) = 1047
(`K_eq`) and a(n) = 1047 n - 1459 for n ≥ 3 (`closed`). The recurrence and the generating
function follow by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a195249 Finset

instance decAdj (p q : Fin 3 × Fin 3) : Decidable (Adj p q) := by
  unfold Adj
  infer_instance

instance decGood {n : ℕ} (f : Cell → Fin (n + 1)) : Decidable (Good f) := by
  unfold Good
  infer_instance

/-- Any two cells of the triangle are equal, adjacent, or have a common neighbor. -/
theorem near_cells :
    ∀ c d : Cell, c = d ∨ Adj c.1 d.1 ∨ ∃ e : Cell, Adj c.1 e.1 ∧ Adj e.1 d.1 := by
  decide +kernel

/-- In a good array any two entries differ by at most 4. -/
theorem good_le_four {n : ℕ} {f : Cell → Fin (n + 1)} (hf : Good f) (c d : Cell) :
    |(f c : ℤ) - f d| ≤ 4 := by
  rcases near_cells c d with h | h | ⟨e, h1, h2⟩
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

/-- The good arrays with entries in 0..m+4 avoiding the value m + 4 are the good arrays with
entries in 0..m+3. -/
theorem card_low (m : ℕ) :
    #(univ.filter (fun f : Cell → Fin (m + 4 + 1) => Good f ∧ ¬ ∃ c, (f c : ℕ) = m + 4)) =
      #(univ.filter (fun g : Cell → Fin (m + 3 + 1) => Good g)) := by
  refine card_nbij' (fun f c => ⟨min (f c : ℕ) (m + 3), by omega⟩)
    (fun g c => ⟨g c, by have := (g c).isLt; omega⟩) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hf ⊢
    obtain ⟨hg, hno⟩ := hf
    refine good_of_shift 0 (fun c => ?_) hg
    have h1 := (f c).isLt
    have h2 : (f c : ℕ) ≠ m + 4 := fun h => hno ⟨c, h⟩
    show ((min (f c : ℕ) (m + 3) : ℕ) : ℤ) = (f c : ℤ) + 0
    omega
  · intro g hg
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hg ⊢
    refine ⟨good_of_shift 0 (fun c => ?_) hg, ?_⟩
    · show ((g c : ℕ) : ℤ) = (g c : ℤ) + 0
      omega
    · rintro ⟨c, hc⟩
      have h1 := (g c).isLt
      have h2 : (g c : ℕ) = m + 4 := hc
      omega
  · intro f hf
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hf
    funext c
    apply Fin.ext
    have h1 := (f c).isLt
    have h2 : (f c : ℕ) ≠ m + 4 := fun h => hf.2 ⟨c, h⟩
    show min (f c : ℕ) (m + 3) = f c
    omega
  · intro g hg
    funext c
    apply Fin.ext
    have := (g c).isLt
    show min (g c : ℕ) (m + 3) = g c
    omega

/-- A good array with entries in 0..m+4 that takes the value m + 4 has all its entries at least
m. -/
theorem low_bound {m : ℕ} {f : Cell → Fin (m + 4 + 1)} (hf : Good f)
    (hc : ∃ c, (f c : ℕ) = m + 4) (d : Cell) : m ≤ (f d : ℕ) := by
  obtain ⟨c, hc⟩ := hc
  have h := abs_le.1 (good_le_four hf d c)
  rw [hc] at h
  push_cast at h
  omega

/-- The good arrays with entries in 0..m+4 taking the value m + 4 are the shifts by m of the good
arrays with entries in 0..4 taking the value 4. -/
theorem card_high (m : ℕ) :
    #(univ.filter (fun f : Cell → Fin (m + 4 + 1) => Good f ∧ ∃ c, (f c : ℕ) = m + 4)) =
      #(univ.filter (fun g : Cell → Fin 5 => Good g ∧ ∃ c, (g c : ℕ) = 4)) := by
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
    · show (f c : ℕ) - m = 4
      omega
  · intro g hg
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hg ⊢
    obtain ⟨hg, c, hc⟩ := hg
    refine ⟨good_of_shift (m : ℤ) (fun d => ?_) hg, c, ?_⟩
    · show (((g d : ℕ) + m : ℕ) : ℤ) = (g d : ℤ) + (m : ℤ)
      omega
    · show (g c : ℕ) + m = m + 4
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

/-- The number of good arrays with entries in 0..4 that take the value 4. -/
noncomputable def K : ℕ := #(univ.filter (fun g : Cell → Fin 5 => Good g ∧ ∃ c, (g c : ℕ) = 4))

/-- Splitting by whether the value m + 4 is taken: a(m+4) = a(m+3) + K. -/
theorem step (m : ℕ) : a (m + 4) = a (m + 3) + K := by
  rw [a_eq_card, a_eq_card, ← card_filter_add_card_filter_not (fun f => ∃ c, (f c : ℕ) = m + 4),
    filter_filter, filter_filter, card_high, card_low, K, add_comm]

/-! ### Small values: arrays as 6-tuples of naturals -/

/-- The six cells of the triangle. -/
def c00 : Cell := ⟨(0, 0), by decide⟩
def c10 : Cell := ⟨(1, 0), by decide⟩
def c11 : Cell := ⟨(1, 1), by decide⟩
def c20 : Cell := ⟨(2, 0), by decide⟩
def c21 : Cell := ⟨(2, 1), by decide⟩
def c22 : Cell := ⟨(2, 2), by decide⟩

theorem cell_cases (c : Cell) :
    c = c00 ∨ c = c10 ∨ c = c11 ∨ c = c20 ∨ c = c21 ∨ c = c22 := by
  revert c
  decide

/-- `x` and `y` differ by at most 2. -/
def near (x y : ℕ) : Bool := x ≤ y + 2 && y ≤ x + 2

theorem near_iff (x y : ℕ) : near x y = true ↔ |(x : ℤ) - y| ≤ 2 := by
  unfold near
  rw [abs_le]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- The goodness test on the entries at (0,0), (1,0), (1,1), (2,0), (2,1), (2,2): one test for
each of the 10 pairs of neighbors. -/
def P (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  near t.1 t.2.1 && near t.1 t.2.2.1 && near t.2.1 t.2.2.1 && near t.2.1 t.2.2.2.1 &&
  near t.2.1 t.2.2.2.2.1 && near t.2.2.1 t.2.2.2.1 && near t.2.2.1 t.2.2.2.2.1 &&
  near t.2.2.1 t.2.2.2.2.2 && near t.2.2.2.1 t.2.2.2.2.1 && near t.2.2.2.2.1 t.2.2.2.2.2

/-- The entries of an array, as a 6-tuple of naturals. -/
def enc {n : ℕ} (f : Cell → Fin (n + 1)) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  ((f c00 : ℕ), (f c10 : ℕ), (f c11 : ℕ), (f c20 : ℕ), (f c21 : ℕ), (f c22 : ℕ))

theorem good_iff {n : ℕ} (f : Cell → Fin (n + 1)) : Good f ↔ P (enc f) = true := by
  simp only [P, enc, Bool.and_eq_true, near_iff, and_assoc]
  constructor
  · intro hf
    exact ⟨hf c00 c10 (by decide), hf c00 c11 (by decide), hf c10 c11 (by decide),
      hf c10 c20 (by decide), hf c10 c21 (by decide), hf c11 c20 (by decide),
      hf c11 c21 (by decide), hf c11 c22 (by decide), hf c20 c21 (by decide),
      hf c21 c22 (by decide)⟩
  · rintro ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ p q hpq
    rcases cell_cases p with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases cell_cases q with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd hpq (by decide)
    | assumption
    | (rw [abs_sub_comm]; assumption)

/-- Reading a 6-tuple as an array. -/
def sel (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (c : Cell) : ℕ :=
  if c = c00 then t.1 else if c = c10 then t.2.1 else if c = c11 then t.2.2.1
  else if c = c20 then t.2.2.2.1 else if c = c21 then t.2.2.2.2.1 else t.2.2.2.2.2

theorem sel00 (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : sel t c00 = t.1 := rfl
theorem sel10 (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : sel t c10 = t.2.1 := rfl
theorem sel11 (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : sel t c11 = t.2.2.1 := rfl
theorem sel20 (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : sel t c20 = t.2.2.2.1 := rfl
theorem sel21 (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : sel t c21 = t.2.2.2.2.1 := rfl
theorem sel22 (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : sel t c22 = t.2.2.2.2.2 := rfl

/-- The array with entries in 0..n read from a 6-tuple (entries reduced mod n + 1). -/
def dec (n : ℕ) (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : Cell → Fin (n + 1) :=
  fun c => ⟨sel t c % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

/-- The 6-tuples with entries in 0..n passing the goodness test. -/
def T (n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1) ×ˢ
    range (n + 1)).filter (fun t => P t = true)

theorem enc_dec (n : ℕ) (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (h0 : t.1 < n + 1) (h1 : t.2.1 < n + 1)
    (h2 : t.2.2.1 < n + 1) (h3 : t.2.2.2.1 < n + 1) (h4 : t.2.2.2.2.1 < n + 1)
    (h5 : t.2.2.2.2.2 < n + 1) : enc (dec n t) = t := by
  simp only [enc, dec, sel00, sel10, sel11, sel20, sel21, sel22, Nat.mod_eq_of_lt h0,
    Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4,
    Nat.mod_eq_of_lt h5]

theorem dec_enc {n : ℕ} (f : Cell → Fin (n + 1)) : dec n (enc f) = f := by
  funext c
  apply Fin.ext
  rcases cell_cases c with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [dec, enc, sel00, sel10, sel11, sel20, sel21, sel22, Nat.mod_eq_of_lt (Fin.isLt _)]

/-- `a n` is the number of 6-tuples with entries in 0..n passing the goodness test. -/
theorem a_eq_T (n : ℕ) : a n = #(T n) := by
  rw [a_eq_card]
  refine card_nbij' enc (dec n) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hf
    simp only [T, mem_coe, mem_filter, mem_product, mem_range]
    exact ⟨⟨(f c00).isLt, (f c10).isLt, (f c11).isLt, (f c20).isLt, (f c21).isLt,
      (f c22).isLt⟩, (good_iff f).1 hf⟩
  · intro t ht
    simp only [T, mem_coe, mem_filter, mem_product, mem_range] at ht
    obtain ⟨⟨h0, h1, h2, h3, h4, h5⟩, hP⟩ := ht
    simp only [mem_coe, mem_filter, mem_univ, true_and]
    rw [good_iff, enc_dec n t h0 h1 h2 h3 h4 h5]
    exact hP
  · intro f _
    exact dec_enc f
  · intro t ht
    simp only [T, mem_coe, mem_filter, mem_product, mem_range] at ht
    obtain ⟨⟨h0, h1, h2, h3, h4, h5⟩, _⟩ := ht
    exact enc_dec n t h0 h1 h2 h3 h4 h5

theorem T_one : #(T 1) = 64 := by
  decide +kernel

theorem T_two : #(T 2) = 729 := by
  decide +kernel

theorem T_three : #(T 3) = 1682 := by
  decide +kernel

theorem T_four : #(T 4) = 2729 := by
  decide +kernel

theorem a_one : a 1 = 64 := by
  rw [a_eq_T, T_one]

theorem a_two : a 2 = 729 := by
  rw [a_eq_T, T_two]

theorem a_three : a 3 = 1682 := by
  rw [a_eq_T, T_three]

theorem a_four : a 4 = 2729 := by
  rw [a_eq_T, T_four]

theorem K_eq : K = 1047 := by
  have h := step 0
  rw [a_four, a_three] at h
  omega

/-- The closed form a(n) = 1047 n - 1459 for n ≥ 3. -/
theorem closed (n : ℕ) (hn : 3 ≤ n) : a n = 1047 * n - 1459 := by
  induction n, hn using Nat.le_induction with
  | base => rw [a_three]
  | succ n hn ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 + 1 = m + 4 by omega, step, K_eq, ih]
    omega

theorem closedQ (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = 1047 * n - 1459 := by
  rw [closed n hn]
  have h : 1459 ≤ 1047 * n := by omega
  push_cast [h]
  ring

theorem recurrence (n : ℕ) (hn : 4 < n) : (a n : ℤ) = 2 * a (n - 1) - a (n - 2) := by
  rw [closed n (by omega), closed (n - 1) (by omega), closed (n - 2) (by omega)]
  omega

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 2 =
      X * (64 + 601 * X + 288 * X ^ 2 + 94 * X ^ 3) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  have key : PowerSeries.mk F * (1 - X) ^ 2 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 2 * (PowerSeries.mk F * X ^ 1) +
        C 1 * (PowerSeries.mk F * X ^ 2) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (64 + 601 * X + 288 * X ^ 2 + 94 * X ^ 3) =
      C 64 * X ^ 1 + C 601 * X ^ 2 + C 288 * X ^ 3 + C 94 * X ^ 4 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 5
  · interval_cases k <;> norm_num [hF, a_one, a_two, a_three, a_four]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
    simp only [show 0 ≤ j + 5 by omega, show 1 ≤ j + 5 by omega, show 2 ≤ j + 5 by omega,
      show j + 5 - 0 = j + 5 by omega, show j + 5 - 1 = j + 4 by omega,
      show j + 5 - 2 = j + 3 by omega, show ¬ (j + 5 = 1) by omega, show ¬ (j + 5 = 2) by omega,
      show ¬ (j + 5 = 3) by omega, show ¬ (j + 5 = 4) by omega,
      show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega, show ¬ (j + 3 = 0) by omega,
      if_true, if_false, hF]
    rw [closedQ (j + 5) (by omega), closedQ (j + 4) (by omega), closedQ (j + 3) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a195249.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
