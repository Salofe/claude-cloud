import OMAStatements.S_oeis_a202785

/-!
Proof of Barker's conjectures for A202785 (3 X 3 arrays with entries in 0..n whose three row
sums and three column sums are all equal).

Parametrization. For triples `x = (x0, x1, x2)` and `y = (y0, y1, y2)` of naturals, the array
whose entry in row `i`, column `j` is `x (j - i) + y (i + j)` (indices mod 3; `toArr`) has every
line sum equal to `x0 + x1 + x2 + y0 + y1 + y2`: it is the combination of the three cyclic and
the three anti-cyclic permutation matrices with weights `x` and `y`. Conversely, every array of
naturals with all line sums equal arises from exactly one such pair `(x, y)` in which some `x_k`
is zero. Writing `aij` for the entries, the parameters are
  `x0 = max (a22 - a01) (a22 - a10)` (truncated subtraction), `x1 = x0 + a01 - a22`,
  `x2 = x0 + a10 - a22`, `y0 = a00 - x0`, `y1 = a22 - x0`, `y2 = a11 - x0` (`toPar`),
and every identity needed is linear arithmetic in the entries and the line sums (`x0of_spec`,
`toArr_toPar`, `toPar_toArr`, `toArr_good`). Each pair `(x_k, y_l)` occurs in exactly one cell,
so all entries are at most `n` iff `max x + max y ≤ n`. Hence `a n` is the number of pairs
`(x, y)` with a zero coordinate in `x` and `max x + max y ≤ n` (`a_eq_card`).

Counting. Fix `y` with `max y = v`. The admissible `x` are the triples in `{0..n-v}^3` with a
zero coordinate, `(n - v + 1)^3 - (n - v)^3` of them (`card_zero_le`), and the triples `y` with
`max y = v` number `(v + 1)^3 - v^3` (`card_mx_eq`). So, with `h(t) = (t + 1)^3 - t^3`,
  `a(n) = Sum_{v = 0..n} h(v) h(n - v)` (`card_T`),
and this convolution sums to `(3n^5 + 15n^4 + 35n^3 + 45n^2 + 32n + 10)/10` (`conv_sum`,
`a_formula`). The recurrence follows since the sixth difference of a polynomial of degree 5
vanishes, and the generating function by comparing coefficients: from `x^7` on they vanish by
the recurrence, and those of `x^0, ..., x^6` follow from `a(1..6) = 14, 87, 340, 1001, 2442, 5215`.
-/

namespace OMA.Helpers

open OMA.S_oeis_a202785 Finset

/-- The largest coordinate of a triple. -/
def mx (x : ℕ × ℕ × ℕ) : ℕ := max x.1 (max x.2.1 x.2.2)

/-- The box `{0, ..., n}^3`. -/
def box (n : ℕ) : Finset (ℕ × ℕ × ℕ) := range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1)

/-- The parameter set: pairs `(x, y)` of triples with a zero coordinate in `x` and
`max x + max y ≤ n`. -/
def T (n : ℕ) : Finset ((ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) :=
  (box n ×ˢ box n).filter
    (fun p => (p.1.1 = 0 ∨ p.1.2.1 = 0 ∨ p.1.2.2 = 0) ∧ mx p.1 + mx p.2 ≤ n)

/-- The natural number `v`, capped at `n`, as an entry in `0..n`. -/
def cap (n v : ℕ) : Fin (n + 1) := ⟨min v n, Nat.lt_succ_of_le (min_le_right v n)⟩

/-- The array with parameters `(x, y)`: its entry `(i, j)` is `x (j - i) + y (i + j)`, the
indices taken mod 3. -/
def toArr (n : ℕ) (p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) : Fin 3 → Fin 3 → Fin (n + 1) :=
  ![![cap n (p.1.1 + p.2.1), cap n (p.1.2.1 + p.2.2.1), cap n (p.1.2.2 + p.2.2.2)],
    ![cap n (p.1.2.2 + p.2.2.1), cap n (p.1.1 + p.2.2.2), cap n (p.1.2.1 + p.2.1)],
    ![cap n (p.1.2.1 + p.2.2.2), cap n (p.1.2.2 + p.2.1), cap n (p.1.1 + p.2.2.1)]]

/-- The first parameter of an array. -/
def x0of {n : ℕ} (A : Fin 3 → Fin 3 → Fin (n + 1)) : ℕ :=
  max ((A 2 2 : ℕ) - A 0 1) ((A 2 2 : ℕ) - A 1 0)

/-- The parameters of an array. -/
def toPar {n : ℕ} (A : Fin 3 → Fin 3 → Fin (n + 1)) : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) :=
  ((x0of A, x0of A + A 0 1 - A 2 2, x0of A + A 1 0 - A 2 2),
    ((A 0 0 : ℕ) - x0of A, (A 2 2 : ℕ) - x0of A, (A 1 1 : ℕ) - x0of A))

/-- The six line sums of an array with all line sums equal. -/
theorem good_lines {n : ℕ} {A : Fin 3 → Fin 3 → Fin (n + 1)} (h : Good A) :
    ∃ s : ℕ, (A 0 0 : ℕ) + A 0 1 + A 0 2 = s ∧ (A 1 0 : ℕ) + A 1 1 + A 1 2 = s ∧
      (A 2 0 : ℕ) + A 2 1 + A 2 2 = s ∧ (A 0 0 : ℕ) + A 1 0 + A 2 0 = s ∧
      (A 0 1 : ℕ) + A 1 1 + A 2 1 = s ∧ (A 0 2 : ℕ) + A 1 2 + A 2 2 = s := by
  obtain ⟨s, hr, hc⟩ := h
  have r0 := hr 0
  have r1 := hr 1
  have r2 := hr 2
  have c0 := hc 0
  have c1 := hc 1
  have c2 := hc 2
  simp only [Fin.sum_univ_three] at r0 r1 r2 c0 c1 c2
  exact ⟨s, r0, r1, r2, c0, c1, c2⟩

/-- What omega needs to know about the first parameter of an array with equal line sums. -/
theorem x0of_spec {n : ℕ} {A : Fin 3 → Fin 3 → Fin (n + 1)} (h : Good A) :
    (A 2 2 : ℕ) ≤ x0of A + A 0 1 ∧ (A 2 2 : ℕ) ≤ x0of A + A 1 0 ∧
      x0of A ≤ A 0 0 ∧ x0of A ≤ A 1 1 ∧ x0of A ≤ A 2 2 ∧
      (x0of A = 0 ∨ x0of A + A 0 1 = A 2 2 ∨ x0of A + A 1 0 = A 2 2) := by
  obtain ⟨s, r0, r1, r2, c0, c1, c2⟩ := good_lines h
  unfold x0of
  omega

/-- `toArr` undoes `toPar` on arrays with all line sums equal. -/
theorem toArr_toPar {n : ℕ} {A : Fin 3 → Fin 3 → Fin (n + 1)} (h : Good A) :
    toArr n (toPar A) = A := by
  obtain ⟨s, r0, r1, r2, c0, c1, c2⟩ := good_lines h
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := x0of_spec h
  have b00 := (A 0 0).isLt
  have b01 := (A 0 1).isLt
  have b02 := (A 0 2).isLt
  have b10 := (A 1 0).isLt
  have b11 := (A 1 1).isLt
  have b12 := (A 1 2).isLt
  have b20 := (A 2 0).isLt
  have b21 := (A 2 1).isLt
  have b22 := (A 2 2).isLt
  funext i j
  apply Fin.ext
  fin_cases i <;> fin_cases j <;> simp [toArr, toPar, cap] <;> omega

/-- The parameters of an array with all line sums equal lie in `T n`. -/
theorem toPar_mem {n : ℕ} {A : Fin 3 → Fin 3 → Fin (n + 1)} (h : Good A) :
    toPar A ∈ T n := by
  obtain ⟨s, r0, r1, r2, c0, c1, c2⟩ := good_lines h
  have b00 := (A 0 0).isLt
  have b01 := (A 0 1).isLt
  have b02 := (A 0 2).isLt
  have b10 := (A 1 0).isLt
  have b11 := (A 1 1).isLt
  have b12 := (A 1 2).isLt
  have b20 := (A 2 0).isLt
  have b21 := (A 2 1).isLt
  have b22 := (A 2 2).isLt
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := x0of_spec h
  rw [T, mem_filter]
  simp only [box, mx, toPar, mem_product, mem_range]
  omega

/-- The coordinates of a point of `T n`: one of `x0, x1, x2` is zero and every `x_k + y_l` is at
most `n`. -/
theorem T_bounds {n : ℕ} {p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)} (hp : p ∈ T n) :
    (p.1.1 = 0 ∨ p.1.2.1 = 0 ∨ p.1.2.2 = 0) ∧
    p.1.1 + p.2.1 ≤ n ∧ p.1.1 + p.2.2.1 ≤ n ∧ p.1.1 + p.2.2.2 ≤ n ∧
    p.1.2.1 + p.2.1 ≤ n ∧ p.1.2.1 + p.2.2.1 ≤ n ∧ p.1.2.1 + p.2.2.2 ≤ n ∧
    p.1.2.2 + p.2.1 ≤ n ∧ p.1.2.2 + p.2.2.1 ≤ n ∧ p.1.2.2 + p.2.2.2 ≤ n := by
  rw [T, mem_filter] at hp
  obtain ⟨-, hz, hm⟩ := hp
  simp only [mx] at hm
  exact ⟨hz, by omega⟩

/-- `toPar` undoes `toArr` on `T n`. -/
theorem toPar_toArr {n : ℕ} {p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)} (hp : p ∈ T n) :
    toPar (toArr n p) = p := by
  obtain ⟨hz, h00, h01, h02, h10, h11, h12, h20, h21, h22⟩ := T_bounds hp
  obtain ⟨⟨x0, x1, x2⟩, ⟨y0, y1, y2⟩⟩ := p
  simp only at hz h00 h01 h02 h10 h11 h12 h20 h21 h22
  simp [toPar, toArr, x0of, cap, min_eq_left h00, min_eq_left h01, min_eq_left h02,
    min_eq_left h10, min_eq_left h11, min_eq_left h12, min_eq_left h20, min_eq_left h21,
    min_eq_left h22]
  omega

/-- The array with parameters in `T n` has all line sums equal to `Sum x + Sum y`. -/
theorem toArr_good {n : ℕ} {p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)} (hp : p ∈ T n) :
    Good (toArr n p) := by
  obtain ⟨hz, h00, h01, h02, h10, h11, h12, h20, h21, h22⟩ := T_bounds hp
  obtain ⟨⟨x0, x1, x2⟩, ⟨y0, y1, y2⟩⟩ := p
  simp only at hz h00 h01 h02 h10 h11 h12 h20 h21 h22
  refine ⟨x0 + x1 + x2 + y0 + y1 + y2, fun i => ?_, fun j => ?_⟩
  · fin_cases i <;>
    simp [Fin.sum_univ_three, toArr, cap, min_eq_left h00, min_eq_left h01, min_eq_left h02,
      min_eq_left h10, min_eq_left h11, min_eq_left h12, min_eq_left h20, min_eq_left h21,
      min_eq_left h22] <;> omega
  · fin_cases j <;>
    simp [Fin.sum_univ_three, toArr, cap, min_eq_left h00, min_eq_left h01, min_eq_left h02,
      min_eq_left h10, min_eq_left h11, min_eq_left h12, min_eq_left h20, min_eq_left h21,
      min_eq_left h22] <;> omega

/-- `a n` counts the parameter set `T n`. -/
theorem a_eq_card (n : ℕ) : a n = (T n).card := by
  let e : {A : Fin 3 → Fin 3 → Fin (n + 1) // Good A} ≃ {p // p ∈ T n} :=
    { toFun := fun A => ⟨toPar A.1, toPar_mem A.2⟩
      invFun := fun p => ⟨toArr n p.1, toArr_good p.2⟩
      left_inv := fun A => Subtype.ext (toArr_toPar A.2)
      right_inv := fun p => Subtype.ext (toPar_toArr p.2) }
  rw [a, Nat.card_congr e, Nat.card_eq_finsetCard]

theorem card_box (m : ℕ) : (box m).card = (m + 1) ^ 3 := by
  simp only [box, card_product, card_range]
  ring

/-- The triples of `box n` with largest coordinate at most `m ≤ n` form `box m`. -/
theorem box_filter_le {n m : ℕ} (hm : m ≤ n) : (box n).filter (fun y => mx y ≤ m) = box m := by
  ext ⟨y0, y1, y2⟩
  rw [mem_filter]
  simp only [box, mx, mem_product, mem_range]
  omega

/-- The triples of `box n` with largest coordinate below `v ≤ n + 1`. -/
theorem box_filter_lt {n v : ℕ} (hv : v ≤ n + 1) :
    (box n).filter (fun y => mx y < v) = range v ×ˢ range v ×ˢ range v := by
  ext ⟨y0, y1, y2⟩
  rw [mem_filter]
  simp only [box, mx, mem_product, mem_range]
  omega

/-- The triples of `box n` with largest coordinate exactly `v ≤ n`: `(v + 1)^3 - v^3` of them. -/
theorem card_mx_eq {n v : ℕ} (hv : v ≤ n) :
    ((box n).filter (fun y => mx y = v)).card + v ^ 3 = (v + 1) ^ 3 := by
  have h := card_filter_add_card_filter_not (s := (box n).filter (fun y => mx y ≤ v))
    (fun y => mx y = v)
  rw [filter_filter, filter_filter, box_filter_le hv, card_box] at h
  have e1 : (box n).filter (fun y => mx y ≤ v ∧ mx y = v) =
      (box n).filter (fun y => mx y = v) := by
    refine filter_congr (fun y _ => ?_)
    omega
  have e2 : (box n).filter (fun y => mx y ≤ v ∧ ¬ mx y = v) =
      (box n).filter (fun y => mx y < v) := by
    refine filter_congr (fun y _ => ?_)
    omega
  rw [e1, e2, box_filter_lt (by omega), card_product, card_product, card_range] at h
  rw [← h]
  ring

/-- The triples of `box n` with a zero coordinate and largest coordinate at most `m ≤ n`:
`(m + 1)^3 - m^3` of them. -/
theorem card_zero_le {n m : ℕ} (hm : m ≤ n) :
    ((box n).filter (fun x => (x.1 = 0 ∨ x.2.1 = 0 ∨ x.2.2 = 0) ∧ mx x ≤ m)).card + m ^ 3 =
      (m + 1) ^ 3 := by
  have h := card_filter_add_card_filter_not (s := box m)
    (fun x => x.1 = 0 ∨ x.2.1 = 0 ∨ x.2.2 = 0)
  rw [card_box] at h
  have e1 : (box n).filter (fun x => (x.1 = 0 ∨ x.2.1 = 0 ∨ x.2.2 = 0) ∧ mx x ≤ m) =
      (box m).filter (fun x => x.1 = 0 ∨ x.2.1 = 0 ∨ x.2.2 = 0) := by
    ext ⟨x0, x1, x2⟩
    rw [mem_filter, mem_filter]
    simp only [box, mx, mem_product, mem_range]
    omega
  have e2 : (box m).filter (fun x => ¬ (x.1 = 0 ∨ x.2.1 = 0 ∨ x.2.2 = 0)) =
      Icc 1 m ×ˢ Icc 1 m ×ˢ Icc 1 m := by
    ext ⟨x0, x1, x2⟩
    rw [mem_filter]
    simp only [box, mem_product, mem_range, mem_Icc]
    omega
  rw [e2, card_product, card_product, Nat.card_Icc] at h
  rw [e1, ← h, Nat.add_sub_cancel]
  ring

/-- The fibre count over `v = max y`:
`#T n = Sum_{v ≤ n} #{y | max y = v} * #{x | some x_k = 0, max x ≤ n - v}`. -/
theorem card_T (n : ℕ) : (T n).card = ∑ v ∈ range (n + 1),
    ((box n).filter (fun y => mx y = v)).card *
      ((box n).filter (fun x => (x.1 = 0 ∨ x.2.1 = 0 ∨ x.2.2 = 0) ∧ mx x ≤ n - v)).card := by
  rw [T, card_filter, sum_product_right]
  have h1 : ∀ y ∈ box n, (∑ x ∈ box n,
      (if (x.1 = 0 ∨ x.2.1 = 0 ∨ x.2.2 = 0) ∧ mx x + mx y ≤ n then 1 else 0)) =
      ((box n).filter (fun x => (x.1 = 0 ∨ x.2.1 = 0 ∨ x.2.2 = 0) ∧ mx x ≤ n - mx y)).card := by
    intro y hy
    have hyn : mx y ≤ n := by
      simp only [box, mem_product, mem_range] at hy
      simp only [mx]
      omega
    rw [card_filter]
    refine sum_congr rfl (fun x _ => ?_)
    congr 1
    apply propext
    omega
  rw [sum_congr rfl h1]
  rw [← sum_fiberwise_of_maps_to' (g := mx) (t := range (n + 1))
    (fun y hy => by
      rw [mem_range]
      simp only [box, mem_product, mem_range] at hy
      simp only [mx]
      omega)
    (fun v => ((box n).filter (fun x => (x.1 = 0 ∨ x.2.1 = 0 ∨ x.2.2 = 0) ∧ mx x ≤ n - v)).card)]
  refine sum_congr rfl (fun v _ => ?_)
  rw [sum_const, smul_eq_mul]

theorem card_mx_eq_q {n v : ℕ} (hv : v ≤ n) :
    (((box n).filter (fun y => mx y = v)).card : ℚ) = ((v : ℚ) + 1) ^ 3 - (v : ℚ) ^ 3 := by
  rw [eq_sub_iff_add_eq]
  exact_mod_cast card_mx_eq hv

theorem card_zero_le_q {n m : ℕ} (hm : m ≤ n) :
    (((box n).filter (fun x => (x.1 = 0 ∨ x.2.1 = 0 ∨ x.2.2 = 0) ∧ mx x ≤ m)).card : ℚ) =
      ((m : ℚ) + 1) ^ 3 - (m : ℚ) ^ 3 := by
  rw [eq_sub_iff_add_eq]
  exact_mod_cast card_zero_le hm

/-- The convolution sum `Sum_{v < k} h(v) h(m - v)`, `h(t) = (t + 1)^3 - t^3`, in closed form. -/
theorem conv_sum (m : ℚ) (k : ℕ) :
    ∑ v ∈ range k, (((v : ℚ) + 1) ^ 3 - (v : ℚ) ^ 3) * ((m - v + 1) ^ 3 - (m - v) ^ 3) =
      k * (18 * k ^ 4 - 45 * k ^ 3 * m - 45 * k ^ 3 + 30 * k ^ 2 * m ^ 2 + 60 * k ^ 2 * m +
        20 * k ^ 2 + 15 * k * m + 15 * k + 2) / 10 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- The closed form `a(n) = (3n^5 + 15n^4 + 35n^3 + 45n^2 + 32n + 10)/10`. -/
theorem a_formula (n : ℕ) :
    (a n : ℚ) = (3 * n ^ 5 + 15 * n ^ 4 + 35 * n ^ 3 + 45 * n ^ 2 + 32 * n + 10) / 10 := by
  calc (a n : ℚ) = ∑ v ∈ range (n + 1), (((v : ℚ) + 1) ^ 3 - (v : ℚ) ^ 3) *
        (((n : ℚ) - v + 1) ^ 3 - ((n : ℚ) - v) ^ 3) := by
        rw [a_eq_card, card_T]
        push_cast
        refine sum_congr rfl (fun v hv => ?_)
        rw [mem_range] at hv
        rw [card_mx_eq_q (by omega), card_zero_le_q (by omega), Nat.cast_sub (by omega)]
    _ = _ := by
        rw [conv_sum]
        push_cast
        ring

/-- Barker's recurrence. -/
theorem recurrence (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) -
      15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  have hQ : (a n : ℚ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) -
      15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
    rw [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega,
      show k + 7 - 3 = k + 4 by omega, show k + 7 - 4 = k + 3 by omega,
      show k + 7 - 5 = k + 2 by omega, show k + 7 - 6 = k + 1 by omega]
    rw [a_formula (k + 7), a_formula (k + 6), a_formula (k + 5), a_formula (k + 4),
      a_formula (k + 3), a_formula (k + 2), a_formula (k + 1)]
    push_cast
    ring
  exact_mod_cast hQ

theorem a_one : a 1 = 14 := by
  have h := a_formula 1
  norm_num at h
  exact_mod_cast h

theorem a_two : a 2 = 87 := by
  have h := a_formula 2
  norm_num at h
  exact_mod_cast h

theorem a_three : a 3 = 340 := by
  have h := a_formula 3
  norm_num at h
  exact_mod_cast h

theorem a_four : a 4 = 1001 := by
  have h := a_formula 4
  norm_num at h
  exact_mod_cast h

theorem a_five : a 5 = 2442 := by
  have h := a_formula 5
  norm_num at h
  exact_mod_cast h

theorem a_six : a 6 = 5215 := by
  have h := a_formula 6
  norm_num at h
  exact_mod_cast h

open PowerSeries in
/-- Barker's generating function, with the denominator `(1 - x)^6` cleared. -/
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * (1 - X) ^ 6 =
      X * (C 7 - C 2 * X + X ^ 2) * (C 2 + X + C 4 * X ^ 2 - X ^ 3) := by
  set A : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ))
    with hA
  have key : A * (1 - X) ^ 6 =
      A * X ^ 0 - C (6 : ℤ) * (A * X ^ 1) + C (15 : ℤ) * (A * X ^ 2) - C (20 : ℤ) * (A * X ^ 3) +
        C (15 : ℤ) * (A * X ^ 4) - C (6 : ℤ) * (A * X ^ 5) + A * X ^ 6 := by
    simp only [map_ofNat]
    ring
  have hrhs : (X : PowerSeries ℤ) * (C 7 - C 2 * X + X ^ 2) * (C 2 + X + C 4 * X ^ 2 - X ^ 3) =
      C (14 : ℤ) * X ^ 1 + C (3 : ℤ) * X ^ 2 + C (28 : ℤ) * X ^ 3 - C (14 : ℤ) * X ^ 4 +
        C (6 : ℤ) * X ^ 5 - C (1 : ℤ) * X ^ 6 := by
    simp only [map_ofNat, map_one]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hA, coeff_mk]
  by_cases hk : k < 7
  · interval_cases k <;> simp [a_one, a_two, a_three, a_four, a_five, a_six]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 7 := ⟨k - 7, by omega⟩
    have hrec := recurrence (j + 7) (by omega)
    simp only [show 0 ≤ j + 7 by omega, show 1 ≤ j + 7 by omega, show 2 ≤ j + 7 by omega,
      show 3 ≤ j + 7 by omega, show 4 ≤ j + 7 by omega, show 5 ≤ j + 7 by omega,
      show 6 ≤ j + 7 by omega,
      show j + 7 - 0 = j + 7 by omega, show j + 7 - 1 = j + 6 by omega,
      show j + 7 - 2 = j + 5 by omega, show j + 7 - 3 = j + 4 by omega,
      show j + 7 - 4 = j + 3 by omega, show j + 7 - 5 = j + 2 by omega,
      show j + 7 - 6 = j + 1 by omega,
      show ¬ (j + 7 = 0) by omega, show ¬ (j + 6 = 0) by omega, show ¬ (j + 5 = 0) by omega,
      show ¬ (j + 4 = 0) by omega, show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega,
      show ¬ (j + 1 = 0) by omega, if_true, if_false] at hrec ⊢
    linear_combination hrec

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a202785.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
