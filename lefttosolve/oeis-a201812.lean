import OMAStatements.S_oeis_a201812

/-!
Proof of Barker's conjectures for A201812 (arrays of 4 integers in -n..n with sum zero and equal
numbers of elements greater than zero and less than zero).

Since the number of positive entries minus the number of negative entries is the sum of the
signs, an array qualifies exactly when both its sum and its sign sum vanish (`balance`), so `a n`
is a fourfold sum over `[-n, n]^4` of that indicator (`a_eq_sum`). Splitting each coordinate
range into `0`, the positive values `k + 1` and the negative values `-(k + 1)` (`k < n`, `split`)
gives 81 sign patterns. The 62 patterns with unequal numbers of positive and negative entries
contribute nothing, the zero array contributes 1, each of the 12 patterns with one positive and
one negative entry contributes `n` (`two_sum`), and each of the 6 patterns with two positive and
two negative entries contributes `T n`, the number of `(a, b, c, d)` in `[0, n)^4` with
`a + b = c + d` (`T1`, `T2`, `T3`). Fixing `a` and `c`, the pairs `(b, d)` number `n - |a - c|`
(`D_eq`), and summing (`S_add_U`, `U_formula`) gives `3 T(n) = 2 n^3 + n` (`T_formula`). Hence
  a(n) = 1 + 12 n + 6 T(n) = 4 n^3 + 14 n + 1   for every n (`a_formula`).
The recurrence and the generating function follow by comparing coefficients: the fourth
difference of a cubic polynomial vanishes.
-/

namespace OMA.Helpers

open OMA.S_oeis_a201812 Finset

/-- The summand: a 4-tuple is counted when its sum and its sign sum both vanish. -/
def F (x0 x1 x2 x3 : ℤ) : ℕ :=
  if x0 + x1 + x2 + x3 = 0 ∧ x0.sign + x1.sign + x2.sign + x3.sign = 0 then 1 else 0

theorem sign_eq (x : ℤ) : (x.sign : ℤ) = (if 0 < x then 1 else 0) - (if x < 0 then 1 else 0) := by
  rcases lt_trichotomy x 0 with h | h | h
  · simp [h, Int.sign_eq_neg_one_of_neg h, not_lt.mpr h.le]
  · simp [h]
  · simp [h, Int.sign_eq_one_of_pos h, not_lt.mpr h.le]

theorem balance (f : Fin 4 → ℤ) :
    (univ.filter fun i => 0 < f i).card = (univ.filter fun i => f i < 0).card ↔
      (f 0).sign + (f 1).sign + (f 2).sign + (f 3).sign = 0 := by
  have h1 : (((univ.filter fun i => 0 < f i).card : ℕ) : ℤ) = ∑ i, if 0 < f i then 1 else 0 := by
    rw [natCast_card_filter]
  have h2 : (((univ.filter fun i => f i < 0).card : ℕ) : ℤ) = ∑ i, if f i < 0 then 1 else 0 := by
    rw [natCast_card_filter]
  have h3 : (f 0).sign + (f 1).sign + (f 2).sign + (f 3).sign = ∑ i, (f i).sign := by
    rw [Fin.sum_univ_four]
  rw [h3, sum_congr rfl (fun i _ => sign_eq (f i)), sum_sub_distrib, ← h1, ← h2]
  omega

theorem a_eq_prod (n : ℕ) : a n = ∑ x ∈ Icc (-(n : ℤ)) n ×ˢ Icc (-(n : ℤ)) n ×ˢ
    Icc (-(n : ℤ)) n ×ˢ Icc (-(n : ℤ)) n, F x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  unfold a
  rw [card_filter]
  refine sum_nbij' (fun f => (f 0, f 1, f 2, f 3)) (fun x => ![x.1, x.2.1, x.2.2.1, x.2.2.2])
    ?_ ?_ ?_ ?_ ?_
  · intro f hf
    simp only [Fintype.mem_piFinset] at hf
    simp only [mem_product]
    exact ⟨hf 0, hf 1, hf 2, hf 3⟩
  · intro x hx
    simp only [mem_product] at hx
    simp only [Fintype.mem_piFinset]
    intro i
    fin_cases i
    · exact hx.1
    · exact hx.2.1
    · exact hx.2.2.1
    · exact hx.2.2.2
  · intro f _
    funext i
    fin_cases i <;> rfl
  · intro x _
    rfl
  · intro f _
    simp only [F, Fin.sum_univ_four, balance f]

theorem a_eq_sum (n : ℕ) : a n = ∑ x0 ∈ Icc (-(n : ℤ)) n, ∑ x1 ∈ Icc (-(n : ℤ)) n,
    ∑ x2 ∈ Icc (-(n : ℤ)) n, ∑ x3 ∈ Icc (-(n : ℤ)) n, F x0 x1 x2 x3 := by
  rw [a_eq_prod]
  simp only [sum_product]

theorem split (n : ℕ) (g : ℤ → ℕ) :
    ∑ x ∈ Icc (-(n : ℤ)) n, g x =
      g 0 + ∑ k ∈ range n, g ((k : ℤ) + 1) + ∑ k ∈ range n, g (-((k : ℤ) + 1)) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hI : Icc (-((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ) =
        insert ((m : ℤ) + 1) (insert (-((m : ℤ) + 1)) (Icc (-(m : ℤ)) m)) := by
      ext x
      simp only [mem_Icc, mem_insert]
      push_cast
      omega
    rw [hI, sum_insert (by simp only [mem_insert, mem_Icc]; omega),
      sum_insert (by simp only [mem_Icc]; omega), ih, sum_range_succ, sum_range_succ]
    ring

theorem c_pn (x k : ℕ) : ((x : ℤ) + 1 + -((k : ℤ) + 1) = 0) ↔ x = k := by omega
theorem c_np (x k : ℕ) : (-((x : ℤ) + 1) + ((k : ℤ) + 1) = 0) ↔ x = k := by omega
theorem c_ppnn (a b c d : ℕ) :
    ((a : ℤ) + 1 + ((b : ℤ) + 1) + -((c : ℤ) + 1) + -((d : ℤ) + 1) = 0) ↔ a + b = c + d := by
  omega
theorem c_nnpp (a b c d : ℕ) :
    (-((a : ℤ) + 1) + -((b : ℤ) + 1) + ((c : ℤ) + 1) + ((d : ℤ) + 1) = 0) ↔ a + b = c + d := by
  omega
theorem c_pnpn (a b c d : ℕ) :
    ((a : ℤ) + 1 + -((b : ℤ) + 1) + ((c : ℤ) + 1) + -((d : ℤ) + 1) = 0) ↔ a + c = b + d := by
  omega
theorem c_npnp (a b c d : ℕ) :
    (-((a : ℤ) + 1) + ((b : ℤ) + 1) + -((c : ℤ) + 1) + ((d : ℤ) + 1) = 0) ↔ a + c = b + d := by
  omega
theorem c_pnnp (a b c d : ℕ) :
    ((a : ℤ) + 1 + -((b : ℤ) + 1) + -((c : ℤ) + 1) + ((d : ℤ) + 1) = 0) ↔ a + d = b + c := by
  omega
theorem c_nppn (a b c d : ℕ) :
    (-((a : ℤ) + 1) + ((b : ℤ) + 1) + ((c : ℤ) + 1) + -((d : ℤ) + 1) = 0) ↔ a + d = b + c := by
  omega

theorem two_sum (n : ℕ) : ∑ x ∈ range n, ∑ k ∈ range n, (if x = k then 1 else 0) = n := by
  have h : ∀ x ∈ range n, ∑ k ∈ range n, (if x = k then 1 else 0) = 1 := by
    intro x hx
    rw [sum_ite_eq, if_pos hx]
  rw [sum_congr rfl h]
  simp

/-- The number of 4-tuples `(a, b, c, d)` in `[0, n)` with `a + b = c + d`. -/
def T (n : ℕ) : ℕ := ∑ a ∈ range n, ∑ b ∈ range n, ∑ c ∈ range n, ∑ d ∈ range n,
  if a + b = c + d then 1 else 0

theorem T1 (n : ℕ) : ∑ a ∈ range n, ∑ b ∈ range n, ∑ c ∈ range n, ∑ d ∈ range n,
    (if a + b = c + d then 1 else 0) = T n := rfl

theorem T2 (n : ℕ) : ∑ a ∈ range n, ∑ b ∈ range n, ∑ c ∈ range n, ∑ d ∈ range n,
    (if a + c = b + d then 1 else 0) = T n := by
  unfold T
  refine sum_congr rfl (fun a _ => ?_)
  exact sum_comm

theorem T3 (n : ℕ) : ∑ a ∈ range n, ∑ b ∈ range n, ∑ c ∈ range n, ∑ d ∈ range n,
    (if a + d = b + c then 1 else 0) = T n := by
  unfold T
  refine sum_congr rfl (fun a _ => ?_)
  have h : ∀ b, ∑ c ∈ range n, ∑ d ∈ range n, (if a + d = b + c then 1 else 0) =
      ∑ d ∈ range n, ∑ c ∈ range n, (if a + d = b + c then 1 else 0) := fun b => sum_comm
  rw [sum_congr rfl (fun b _ => h b)]
  exact sum_comm

theorem two_e (n e : ℕ) :
    ∑ b ∈ range n, ∑ d ∈ range n, (if d = b + e then 1 else 0) = n - e := by
  simp only [sum_ite_eq', mem_range]
  rw [sum_boole]
  have : (range n).filter (fun b => b + e < n) = range (n - e) := by
    ext b
    simp only [mem_filter, mem_range]
    omega
  rw [this, card_range]
  simp

/-- The distance `|a - c|` of two naturals, written with truncated subtraction. -/
def gd (a c : ℕ) : ℕ := (a - c) + (c - a)

theorem D_eq (n a c : ℕ) :
    ∑ b ∈ range n, ∑ d ∈ range n, (if a + b = c + d then 1 else 0) = n - gd a c := by
  unfold gd
  by_cases h : c ≤ a
  · have e : ∀ b d : ℕ, (a + b = c + d) ↔ (d = b + (a - c)) := fun b d => by omega
    simp only [e, two_e]
    omega
  · have e : ∀ b d : ℕ, (a + b = c + d) ↔ (b = d + (c - a)) := fun b d => by omega
    simp only [e]
    rw [sum_comm, two_e]
    omega

theorem T_eq (n : ℕ) : T n = ∑ a ∈ range n, ∑ c ∈ range n, (n - gd a c) := by
  unfold T
  refine sum_congr rfl (fun a _ => ?_)
  rw [sum_comm]
  exact sum_congr rfl (fun c _ => D_eq n a c)

theorem S_add_U (n : ℕ) : ∑ a ∈ range n, ∑ c ∈ range n, (n - gd a c) +
    ∑ a ∈ range n, ∑ c ∈ range n, gd a c = n ^ 3 := by
  rw [← sum_add_distrib]
  have h : ∀ a ∈ range n, ∑ c ∈ range n, (n - gd a c) + ∑ c ∈ range n, gd a c =
      ∑ c ∈ range n, n := by
    intro a ha
    rw [← sum_add_distrib]
    refine sum_congr rfl (fun c hc => ?_)
    simp only [mem_range] at ha hc
    unfold gd
    omega
  rw [sum_congr rfl h]
  simp only [sum_const, card_range, smul_eq_mul]
  ring

theorem gauss_rev (n : ℕ) : 2 * ∑ a ∈ range n, (n - a) = n ^ 2 + n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, sum_congr rfl (fun a ha => show m + 1 - a = (m - a) + 1 by
      simp only [mem_range] at ha; omega), sum_add_distrib]
    simp only [sum_const, card_range, smul_eq_mul, mul_one, Nat.add_sub_cancel_left]
    rw [mul_add, mul_add, ih]
    ring

theorem U_formula (n : ℕ) : 3 * (∑ a ∈ range n, ∑ c ∈ range n, gd a c) + n = n ^ 3 := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h1 : ∑ a ∈ range (m + 1), ∑ c ∈ range (m + 1), gd a c =
        ∑ a ∈ range m, ∑ c ∈ range m, gd a c + 2 * ∑ a ∈ range m, (m - a) := by
      simp only [sum_range_succ]
      rw [sum_add_distrib]
      have e1 : ∑ a ∈ range m, gd a m = ∑ a ∈ range m, (m - a) :=
        sum_congr rfl (fun a ha => by simp only [mem_range] at ha; unfold gd; omega)
      have e2 : ∑ c ∈ range m, gd m c = ∑ c ∈ range m, (m - c) :=
        sum_congr rfl (fun c hc => by simp only [mem_range] at hc; unfold gd; omega)
      have e3 : gd m m = 0 := by unfold gd; omega
      rw [e1, e2, e3]
      ring
    rw [h1]
    nlinarith [ih, gauss_rev m]

theorem T_formula (n : ℕ) : 3 * T n = 2 * n ^ 3 + n := by
  have h1 := S_add_U n
  have h2 := U_formula n
  rw [T_eq]
  omega

theorem a_formula (n : ℕ) : (a n : ℤ) = 4 * n ^ 3 + 14 * n + 1 := by
  rw [a_eq_sum]
  simp only [split]
  simp only [sum_add_distrib]
  simp only [F, Int.sign_zero, Int.sign_natCast_add_one, Int.sign_neg, add_zero, zero_add,
    Int.reduceAdd, Int.reduceNeg, Int.reduceEq, and_false, and_true, if_false, sum_const_zero]
  simp only [c_pn, c_np, c_ppnn, c_nnpp, c_pnpn, c_npnp, c_pnnp, c_nppn, two_sum, T1, T2, T3,
    ite_true]
  have hT := T_formula n
  have hT' : (3 : ℤ) * T n = 2 * n ^ 3 + n := by exact_mod_cast hT
  push_cast
  linarith

theorem recurrence (n : ℕ) (hn : n > 4) :
    (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  rw [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega]
  rw [a_formula (k + 5), a_formula (k + 4), a_formula (k + 3), a_formula (k + 2),
    a_formula (k + 1)]
  push_cast
  ring

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * (1 - X) ^ 4 =
      X * (19 - 15 * X + 21 * X ^ 2 - X ^ 3) := by
  set A : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) with hA
  have key : A * (1 - X) ^ 4 =
      A * X ^ 0 - C (4 : ℤ) * (A * X ^ 1) + C (6 : ℤ) * (A * X ^ 2) - C (4 : ℤ) * (A * X ^ 3) +
        A * X ^ 4 := by
    simp only [map_ofNat]
    ring
  have hrhs : (X : PowerSeries ℤ) * (19 - 15 * X + 21 * X ^ 2 - X ^ 3) =
      C (19 : ℤ) * X ^ 1 - C (15 : ℤ) * X ^ 2 + C (21 : ℤ) * X ^ 3 - C (1 : ℤ) * X ^ 4 := by
    simp only [map_ofNat, map_one]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hA, coeff_mk]
  by_cases hk : k < 5
  · interval_cases k <;> norm_num [a_formula]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
    simp only [show 0 ≤ j + 5 by omega, show 1 ≤ j + 5 by omega, show 2 ≤ j + 5 by omega,
      show 3 ≤ j + 5 by omega, show 4 ≤ j + 5 by omega,
      show j + 5 - 0 = j + 5 by omega, show j + 5 - 1 = j + 4 by omega,
      show j + 5 - 2 = j + 3 by omega, show j + 5 - 3 = j + 2 by omega,
      show j + 5 - 4 = j + 1 by omega,
      show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega, show ¬ (j + 3 = 0) by omega,
      show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega, if_true, if_false]
    rw [a_formula (j + 5), a_formula (j + 4), a_formula (j + 3), a_formula (j + 2),
      a_formula (j + 1)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a201812.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
