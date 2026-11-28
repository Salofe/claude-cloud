import OMAStatements.S_oeis_a162024

/-!
Proof of Barker's conjectures for A162024: n X n binary arrays whose rows and columns, read as
binary numbers, are nondecreasing, and whose entries off the outermost rows and columns vanish.

For `n = m + 3`, write `N = m + 2` for the last index. A good array is determined by
* `c = A 1 0`, which equals `A 0 1`. The corner `A 0 0` is `0`. If `c = 1`, the rest of the first
  row and of the first column is `1`; if `c = 0`, they vanish except possibly at index `N`.
* `p` with `c ≤ p ≤ N`: the right column is `0` on the rows `c, ..., p - 1` and `1` on the rows
  `p, ..., N - 1`.
* `q` with `c ≤ q ≤ N`: likewise for the bottom row.
* `b = A N N`, where `b = 0` is possible only when `p < N ↔ q < N`.
Conversely every such choice gives a good array (`mk`), and different choices give different
arrays. Counting the choices gives `(N + 1)^2 + (N^2 + 1) + N^2 + ((N - 1)^2 + 1) = 4 N^2 + 4`,
that is `a n = 4 (2 - 2 n + n^2)` for `n ≥ 3`. With `a 2 = 7` (a finite check) the generating
function follows by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a162024 Finset

/-- A row of length `n` read as a binary number, most significant bit first. -/
def bval {n : ℕ} (r : Fin n → Fin 2) : ℕ :=
  ∑ j : Fin n, (r j : ℕ) * 2 ^ (n - 1 - (j : ℕ))

theorem rowVal_eq {n : ℕ} (A : Fin n → Fin n → Fin 2) (i : Fin n) :
    rowVal A i = bval (A i) := rfl

theorem colVal_eq {n : ℕ} (A : Fin n → Fin n → Fin 2) (j : Fin n) :
    colVal A j = bval (fun i => A i j) := rfl

/-- The transpose of an array. -/
def tr {n : ℕ} (A : Fin n → Fin n → Fin 2) : Fin n → Fin n → Fin 2 := fun i j => A j i

theorem rowVal_tr {n : ℕ} (A : Fin n → Fin n → Fin 2) : rowVal (tr A) = colVal A := rfl

theorem good_tr {n : ℕ} {A : Fin n → Fin n → Fin 2} (h : Good A) : Good (tr A) :=
  ⟨h.2.1, h.1, fun i j hi hi' hj hj' => h.2.2 j i hj hj' hi hi'⟩

theorem fin2_le (x : Fin 2) : (x : ℕ) ≤ 1 := by
  have := x.isLt
  omega

theorem fin2_cases (x : Fin 2) : (x : ℕ) = 0 ∨ (x : ℕ) = 1 := by
  have := x.isLt
  omega

/-- A binary number with `k` digits is less than `2 ^ k`. -/
theorem bin_lt (k : ℕ) (g : Fin k → ℕ) (hg : ∀ j, g j ≤ 1) :
    ∑ j : Fin k, g j * 2 ^ (k - 1 - (j : ℕ)) < 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    have h1 := ih (fun j => g j.succ) (fun j => hg _)
    have h2 : ∑ j : Fin k, g j.succ * 2 ^ (k + 1 - 1 - ((j.succ : Fin (k + 1)) : ℕ)) =
        ∑ j : Fin k, g j.succ * 2 ^ (k - 1 - (j : ℕ)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Fin.val_succ]
      congr 2
      omega
    rw [h2]
    have h3 : g 0 * 2 ^ k ≤ 1 * 2 ^ k := Nat.mul_le_mul_right _ (hg 0)
    simp only [Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero, pow_succ] at h1 h3 ⊢
    omega

/-- Splitting off the leading digit. -/
theorem bval_succ (k : ℕ) (r : Fin (k + 1) → Fin 2) :
    bval r = (r 0 : ℕ) * 2 ^ k + ∑ j : Fin k, (r j.succ : ℕ) * 2 ^ (k - 1 - (j : ℕ)) := by
  unfold bval
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero, Fin.val_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  omega

theorem bval_lt_of_head (k : ℕ) (r : Fin (k + 1) → Fin 2) (h : r 0 = 0) : bval r < 2 ^ k := by
  rw [bval_succ, h]
  simpa using bin_lt k (fun j => (r j.succ : ℕ)) (fun j => fin2_le _)

theorem single_le_bval {n : ℕ} (r : Fin n → Fin 2) (k : Fin n) :
    (r k : ℕ) * 2 ^ (n - 1 - (k : ℕ)) ≤ bval r := by
  unfold bval
  exact Finset.single_le_sum (f := fun j : Fin n => (r j : ℕ) * 2 ^ (n - 1 - (j : ℕ)))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

theorem pair_le_bval {n : ℕ} (r : Fin n → Fin 2) (k k' : Fin n) (hk : k ≠ k') :
    (r k : ℕ) * 2 ^ (n - 1 - (k : ℕ)) + (r k' : ℕ) * 2 ^ (n - 1 - (k' : ℕ)) ≤ bval r := by
  unfold bval
  rw [← Finset.sum_pair (f := fun j : Fin n => (r j : ℕ) * 2 ^ (n - 1 - (j : ℕ))) hk]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- A row whose entries vanish except possibly the first and the last. -/
theorem bval_ends (k : ℕ) (r : Fin (k + 2) → Fin 2)
    (h : ∀ j : Fin (k + 2), (j : ℕ) ≠ 0 → (j : ℕ) ≠ k + 1 → r j = 0) :
    bval r = (r 0 : ℕ) * 2 ^ (k + 1) + (r (Fin.last (k + 1)) : ℕ) := by
  unfold bval
  rw [Fintype.sum_eq_add 0 (Fin.last (k + 1))]
  · simp
  · intro h'
    have := congrArg Fin.val h'
    simp at this
  · intro x hx
    rw [h x, Fin.val_zero, zero_mul]
    · intro h0
      exact hx.1 (Fin.ext (by simpa using h0))
    · intro h1
      exact hx.2 (Fin.ext (by simpa using h1))

/-- A function on `[lo, lo + d)` with values in `{0, 1}` that is nondecreasing is a step
function: it is `0` before some `p` and `1` from `p` on. -/
theorem step_exists (lo : ℕ) (g : ℕ → ℕ) : ∀ d : ℕ,
    (∀ i, lo ≤ i → i < lo + d → g i ≤ 1) →
    (∀ i i', lo ≤ i → i ≤ i' → i' < lo + d → g i ≤ g i') →
    ∃ p, lo ≤ p ∧ p ≤ lo + d ∧
      ∀ i, lo ≤ i → i < lo + d → g i = if p ≤ i then 1 else 0
  | 0 => fun _ _ => ⟨lo, le_refl _, by omega, fun i h1 h2 => absurd h2 (by omega)⟩
  | d + 1 => by
    intro h01 hmono
    obtain ⟨p, hp1, hp2, hp3⟩ := step_exists lo g d (fun i h1 h2 => h01 i h1 (by omega))
      (fun i i' h1 h2 h3 => hmono i i' h1 h2 (by omega))
    by_cases hg : g (lo + d) = 0
    · refine ⟨lo + d + 1, by omega, by omega, fun i h1 h2 => ?_⟩
      have := hmono i (lo + d) h1 (by omega) (by omega)
      rw [if_neg (by omega)]
      omega
    · have hg1 : g (lo + d) = 1 := by
        have := h01 (lo + d) (by omega) (by omega)
        omega
      refine ⟨p, hp1, by omega, fun i h1 h2 => ?_⟩
      rcases Nat.lt_or_ge i (lo + d) with h | h
      · exact hp3 i h1 h
      · have hi : i = lo + d := by omega
        subst hi
        rw [if_pos hp2]
        exact hg1

theorem two_le_pow (k : ℕ) (hk : 1 ≤ k) : 2 ≤ 2 ^ k := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

variable {m : ℕ}

/-- A middle row of a good array: only its first and last entries can be nonzero. -/
theorem rowVal_mid {A : Fin (m + 3) → Fin (m + 3) → Fin 2} (hA : Good A) (i : Fin (m + 3))
    (hi : 0 < (i : ℕ)) (hi' : (i : ℕ) < m + 2) :
    rowVal A i = (A i 0 : ℕ) * 2 ^ (m + 2) + (A i (Fin.last (m + 2)) : ℕ) := by
  rw [rowVal_eq]
  exact bval_ends (m + 1) (A i) (fun j hj hj' => hA.2.2 i j hi (by omega) (by omega) (by omega))

/-- In a good array the top left entry is zero. -/
theorem corner_zero {A : Fin (m + 3) → Fin (m + 3) → Fin 2} (hA : Good A) : A 0 0 = 0 := by
  by_contra h
  have h1 : (A 0 0 : ℕ) = 1 := by
    have h' : (A 0 0 : ℕ) ≠ 0 := fun h' => h (Fin.ext h')
    have := fin2_le (A 0 0)
    omega
  have hP : 2 ≤ 2 ^ (m + 1) := two_le_pow _ (by omega)
  have hP2 : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
  -- row 0 is at least 2^(m+2)
  have r0 : 2 ^ (m + 2) ≤ rowVal A 0 := by
    have := single_le_bval (A 0) 0
    rw [h1] at this
    rw [rowVal_eq]
    simpa using this
  have r01 : rowVal A 0 ≤ rowVal A ⟨1, by omega⟩ := hA.1 (Fin.zero_le _)
  have e1 := rowVal_mid hA ⟨1, by omega⟩ (by simp) (by simp)
  have hx1 : (A ⟨1, by omega⟩ 0 : ℕ) = 1 := by
    rcases fin2_cases (A ⟨1, by omega⟩ 0) with h' | h'
    · exfalso
      have := fin2_le (A ⟨1, by omega⟩ (Fin.last (m + 2)))
      rw [h', zero_mul, zero_add] at e1
      omega
    · exact h'
  -- column 0 is at least 2^(m+2) + 2^(m+1)
  have c0 : 2 ^ (m + 2) + 2 ^ (m + 1) ≤ colVal A 0 := by
    have := pair_le_bval (fun i => A i 0) 0 ⟨1, by omega⟩ (by simp)
    simp only [h1, hx1, Fin.val_zero, one_mul] at this
    rw [colVal_eq]
    simpa using this
  have c01 : colVal A 0 ≤ colVal A ⟨1, by omega⟩ := hA.2.1 (Fin.zero_le _)
  have e2 := rowVal_mid (good_tr hA) ⟨1, by omega⟩ (by simp) (by simp)
  rw [rowVal_tr] at e2
  have hu := fin2_le (tr A ⟨1, by omega⟩ 0)
  have hv := fin2_le (tr A ⟨1, by omega⟩ (Fin.last (m + 2)))
  have : (tr A ⟨1, by omega⟩ 0 : ℕ) * 2 ^ (m + 2) ≤ 1 * 2 ^ (m + 2) :=
    Nat.mul_le_mul_right _ hu
  omega

/-- If the entry below the top left corner is one, so is the entry to its right. -/
theorem below_imp_right {A : Fin (m + 3) → Fin (m + 3) → Fin 2} (hA : Good A)
    (h : (A ⟨1, by omega⟩ 0 : ℕ) = 1) : (A 0 ⟨1, by omega⟩ : ℕ) = 1 := by
  have hP : 2 ≤ 2 ^ (m + 1) := two_le_pow _ (by omega)
  have c0 : 2 ^ (m + 1) ≤ colVal A 0 := by
    have := single_le_bval (fun i => A i 0) ⟨1, by omega⟩
    simp only [h, one_mul] at this
    rw [colVal_eq]
    simpa using this
  have c01 : colVal A 0 ≤ colVal A ⟨1, by omega⟩ := hA.2.1 (Fin.zero_le _)
  have e2 := rowVal_mid (good_tr hA) ⟨1, by omega⟩ (by simp) (by simp)
  rw [rowVal_tr] at e2
  have hv := fin2_le (tr A ⟨1, by omega⟩ (Fin.last (m + 2)))
  rcases fin2_cases (tr A ⟨1, by omega⟩ 0) with h' | h'
  · rw [h', zero_mul, zero_add] at e2
    omega
  · exact h'

theorem below_eq_right {A : Fin (m + 3) → Fin (m + 3) → Fin 2} (hA : Good A) :
    (A ⟨1, by omega⟩ 0 : ℕ) = (A 0 ⟨1, by omega⟩ : ℕ) := by
  rcases fin2_cases (A ⟨1, by omega⟩ 0) with h | h
  · rcases fin2_cases (A 0 ⟨1, by omega⟩) with h' | h'
    · rw [h, h']
    · have := below_imp_right (good_tr hA) h'
      exact absurd this (by simp only [tr]; omega)
  · rw [h, below_imp_right hA h]

/-- If the entry below the corner is zero, the top row vanishes except its last entry. -/
theorem top_zero {A : Fin (m + 3) → Fin (m + 3) → Fin 2} (hA : Good A)
    (h : (A ⟨1, by omega⟩ 0 : ℕ) = 0) (j : Fin (m + 3)) (hj : (j : ℕ) ≠ m + 2) :
    A 0 j = 0 := by
  apply Fin.ext
  have e1 := rowVal_mid hA ⟨1, by omega⟩ (by simp) (by simp)
  rw [h, zero_mul, zero_add] at e1
  have hy := fin2_le (A ⟨1, by omega⟩ (Fin.last (m + 2)))
  have r01 : rowVal A 0 ≤ rowVal A ⟨1, by omega⟩ := hA.1 (Fin.zero_le _)
  have hs := single_le_bval (A 0) j
  rw [← rowVal_eq] at hs
  have hj' := j.isLt
  have hpow : 2 ≤ 2 ^ (m + 3 - 1 - (j : ℕ)) := two_le_pow _ (by omega)
  rcases fin2_cases (A 0 j) with h' | h'
  · exact h'
  · rw [h', one_mul] at hs
    omega

/-- If the entry below the corner is one, the whole first column is one below the corner. -/
theorem left_one {A : Fin (m + 3) → Fin (m + 3) → Fin 2} (hA : Good A)
    (h : (A ⟨1, by omega⟩ 0 : ℕ) = 1) (i : Fin (m + 3)) (hi : (i : ℕ) ≠ 0) :
    (A i 0 : ℕ) = 1 := by
  have r1 : 2 ^ (m + 2) ≤ rowVal A ⟨1, by omega⟩ := by
    have := single_le_bval (A ⟨1, by omega⟩) 0
    rw [h] at this
    rw [rowVal_eq]
    simpa using this
  have r1i : rowVal A ⟨1, by omega⟩ ≤ rowVal A i := hA.1 (by rw [Fin.le_def]; simp; omega)
  rcases fin2_cases (A i 0) with h' | h'
  · exfalso
    have := bval_lt_of_head (m + 2) (A i) (Fin.ext h')
    rw [← rowVal_eq] at this
    omega
  · exact h'

/-- On the middle rows the first column equals `A 1 0`. -/
theorem left_mid {A : Fin (m + 3) → Fin (m + 3) → Fin 2} (hA : Good A) (i : Fin (m + 3))
    (hi : 0 < (i : ℕ)) (hi' : (i : ℕ) < m + 2) :
    (A i 0 : ℕ) = (A ⟨1, by omega⟩ 0 : ℕ) := by
  rcases fin2_cases (A ⟨1, by omega⟩ 0) with h | h
  · have h' : (tr A ⟨1, by omega⟩ 0 : ℕ) = 0 := by
      show (A 0 ⟨1, by omega⟩ : ℕ) = 0
      rw [← below_eq_right hA]
      exact h
    have := top_zero (good_tr hA) h' i (by omega)
    rw [h]
    show ((tr A 0 i : Fin 2) : ℕ) = 0
    rw [this]
    rfl
  · rw [h]
    exact left_one hA h i (by omega)

/-- The right column is a step function on the rows `c, ..., m + 1`, where `c = A 1 0`. -/
theorem exists_p {A : Fin (m + 3) → Fin (m + 3) → Fin 2} (hA : Good A) :
    ∃ p, (A ⟨1, by omega⟩ 0 : ℕ) ≤ p ∧ p ≤ m + 2 ∧
      ∀ i : Fin (m + 3), (A ⟨1, by omega⟩ 0 : ℕ) ≤ (i : ℕ) → (i : ℕ) < m + 2 →
        (A i (Fin.last (m + 2)) : ℕ) = if p ≤ (i : ℕ) then 1 else 0 := by
  have hc1 : (A ⟨1, by omega⟩ 0 : ℕ) ≤ 1 := fin2_le _
  let g : ℕ → ℕ := fun i =>
    if h : i < m + 3 then (A ⟨i, h⟩ (Fin.last (m + 2)) : ℕ) else 0
  have hg : ∀ i (h : i < m + 3), g i = (A ⟨i, h⟩ (Fin.last (m + 2)) : ℕ) := by
    intro i h
    simp only [g, dif_pos h]
  have hg1 : ∀ i, g i ≤ 1 := by
    intro i
    simp only [g]
    split_ifs
    · exact fin2_le _
    · omega
  -- the middle rows
  have hmid : ∀ i i' : Fin (m + 3), 0 < (i : ℕ) → (i : ℕ) ≤ i' → (i' : ℕ) < m + 2 →
      (A i (Fin.last (m + 2)) : ℕ) ≤ (A i' (Fin.last (m + 2)) : ℕ) := by
    intro i i' h1 h2 h3
    have hr : rowVal A i ≤ rowVal A i' := hA.1 (Fin.le_def.2 h2)
    rw [rowVal_mid hA i h1 (by omega), rowVal_mid hA i' (by omega) h3,
      left_mid hA i h1 (by omega), left_mid hA i' (by omega) h3] at hr
    omega
  -- the top row, when `c = 0`
  have htop : (A ⟨1, by omega⟩ 0 : ℕ) = 0 →
      (A 0 (Fin.last (m + 2)) : ℕ) ≤ (A ⟨1, by omega⟩ (Fin.last (m + 2)) : ℕ) := by
    intro h0
    have r01 : rowVal A 0 ≤ rowVal A ⟨1, by omega⟩ := hA.1 (Fin.zero_le _)
    have e0 : rowVal A 0 = (A 0 0 : ℕ) * 2 ^ (m + 2) + (A 0 (Fin.last (m + 2)) : ℕ) := by
      rw [rowVal_eq]
      exact bval_ends (m + 1) (A 0) (fun j hj hj' => top_zero hA h0 j hj')
    have e1 := rowVal_mid hA ⟨1, by omega⟩ (by simp) (by simp)
    rw [e0, e1, corner_zero hA, h0] at r01
    simpa using r01
  obtain ⟨p, hp1, hp2, hp3⟩ := step_exists (A ⟨1, by omega⟩ 0 : ℕ) g
    (m + 2 - (A ⟨1, by omega⟩ 0 : ℕ)) (fun i _ _ => hg1 i) (by
      intro i i' h1 h2 h3
      rw [hg i (by omega), hg i' (by omega)]
      rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · subst hi0
        rcases Nat.eq_zero_or_pos i' with hi0' | hi0'
        · subst hi0'
          exact le_refl _
        · have ht := htop (by omega)
          have hm := hmid ⟨1, by omega⟩ ⟨i', by omega⟩ (by show 0 < 1; omega)
            (by show 1 ≤ i'; omega) (by show i' < m + 2; omega)
          exact le_trans ht hm
      · exact hmid ⟨i, by omega⟩ ⟨i', by omega⟩ hi0 h2 (by show i' < m + 2; omega))
  refine ⟨p, hp1, by omega, fun i hi1 hi2 => ?_⟩
  have := hp3 i hi1 (by omega)
  rw [hg i i.isLt] at this
  exact this

/-- The array with parameters `c, p, q, b`. -/
def mk (m c p q b : ℕ) : Fin (m + 3) → Fin (m + 3) → Fin 2 := fun i j =>
  if (i : ℕ) = m + 2 ∧ (j : ℕ) = m + 2 then (if b = 1 then 1 else 0)
  else if c = 1 ∧ (i : ℕ) = 0 ∧ (j : ℕ) = 0 then 0
  else if c = 1 ∧ ((i : ℕ) = 0 ∨ (j : ℕ) = 0) then 1
  else if (j : ℕ) = m + 2 then (if p ≤ (i : ℕ) then 1 else 0)
  else if (i : ℕ) = m + 2 then (if q ≤ (j : ℕ) then 1 else 0)
  else 0

theorem mk_val (m c p q b : ℕ) (i j : Fin (m + 3)) : (mk m c p q b i j : ℕ) =
    if (i : ℕ) = m + 2 ∧ (j : ℕ) = m + 2 then (if b = 1 then 1 else 0)
    else if c = 1 ∧ (i : ℕ) = 0 ∧ (j : ℕ) = 0 then 0
    else if c = 1 ∧ ((i : ℕ) = 0 ∨ (j : ℕ) = 0) then 1
    else if (j : ℕ) = m + 2 then (if p ≤ (i : ℕ) then 1 else 0)
    else if (i : ℕ) = m + 2 then (if q ≤ (j : ℕ) then 1 else 0)
    else 0 := by
  unfold mk
  split_ifs <;> rfl

theorem tr_mk (m c p q b : ℕ) : tr (mk m c p q b) = mk m c q p b := by
  funext i j
  apply Fin.ext
  show (mk m c p q b j i : ℕ) = (mk m c q p b i j : ℕ)
  rw [mk_val, mk_val]
  split_ifs <;> omega

theorem mk_mid_row (m c p q b : ℕ) (hc : c < 2) (i : Fin (m + 3)) (hi : 0 < (i : ℕ))
    (hi' : (i : ℕ) < m + 2) :
    rowVal (mk m c p q b) i = c * 2 ^ (m + 2) + (if p ≤ (i : ℕ) then 1 else 0) := by
  rw [rowVal_eq, bval_ends (m + 1) (mk m c p q b i)]
  · rw [mk_val, mk_val]
    simp only [Fin.val_zero, Fin.val_last, and_true, or_true, ite_true]
    obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
    · split_ifs <;> first | omega | simp_all
    · split_ifs <;> first | omega | simp_all
  · intro j hj hj'
    apply Fin.ext
    rw [mk_val]
    simp only [Fin.val_zero]
    split_ifs <;> omega

theorem mk_corner (m c p q b : ℕ) : (mk m c p q b 0 0 : ℕ) = 0 := by
  rw [mk_val]
  simp only [Fin.val_zero, and_true, or_true]
  split_ifs <;> first | omega | simp_all

theorem bval_ge_one (r : Fin (m + 3) → Fin 2) (k : Fin (m + 3)) (h1 : (r k : ℕ) = 1) :
    1 ≤ bval r := by
  have := single_le_bval r k
  rw [h1, one_mul] at this
  have : 1 ≤ 2 ^ (m + 3 - 1 - (k : ℕ)) := Nat.one_le_two_pow
  omega

theorem bval_ge_head (r : Fin (m + 3) → Fin 2) (h0 : (r 0 : ℕ) = 1) :
    2 ^ (m + 2) ≤ bval r := by
  have := single_le_bval r 0
  rw [h0, one_mul] at this
  have e1 : m + 3 - 1 - ((0 : Fin (m + 3)) : ℕ) = m + 2 := by simp
  rw [e1] at this
  exact this

theorem bval_ge_head_one (r : Fin (m + 3) → Fin 2) (k : Fin (m + 3)) (hk : (k : ℕ) ≠ 0)
    (h0 : (r 0 : ℕ) = 1) (h1 : (r k : ℕ) = 1) : 2 ^ (m + 2) + 1 ≤ bval r := by
  have := pair_le_bval r 0 k (fun h => hk (by rw [← h]; rfl))
  rw [h0, h1, one_mul, one_mul] at this
  have e1 : m + 3 - 1 - ((0 : Fin (m + 3)) : ℕ) = m + 2 := by simp
  rw [e1] at this
  have : 1 ≤ 2 ^ (m + 3 - 1 - (k : ℕ)) := Nat.one_le_two_pow
  omega

/-- The rows of `mk` are nondecreasing when the parameters are admissible. -/
theorem mk_rows_mono (m c p q b : ℕ) (hc : c < 2) (hcp : c ≤ p) (hpN : p ≤ m + 2)
    (hcq : c ≤ q) (_hqN : q ≤ m + 2) (hb : b < 2) (hex : b = 0 → (p < m + 2 ↔ q < m + 2)) :
    Monotone (rowVal (mk m c p q b)) := by
  rw [Fin.monotone_iff_le_succ]
  intro k
  have hk := k.isLt
  rcases Nat.eq_zero_or_pos (k : ℕ) with hk0 | hk0
  · -- the top row and the row below it
    have e1 : Fin.castSucc k = 0 := Fin.ext (by simp [hk0])
    have e2 : Fin.succ k = ⟨1, by omega⟩ := Fin.ext (by simp [hk0])
    rw [e1, e2, mk_mid_row m c p q b hc ⟨1, by omega⟩ (by simp) (by simp)]
    obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
    · rw [rowVal_eq, bval_ends (m + 1) (mk m 0 p q b 0)]
      · rw [mk_corner, mk_val]
        simp only [Fin.val_zero, Fin.val_last, true_and, and_true, true_or, ite_true]
        split_ifs <;> first | omega | simp_all
      · intro j hj hj'
        apply Fin.ext
        rw [mk_val]
        simp only [Fin.val_zero, true_and, and_true, true_or]
        split_ifs <;> omega
    · have := bval_lt_of_head (m + 2) (mk m 1 p q b 0) (Fin.ext (mk_corner m 1 p q b))
      rw [← rowVal_eq] at this
      omega
  rcases Nat.lt_or_ge ((k : ℕ) + 1) (m + 2) with hk1 | hk1
  · -- two middle rows
    rw [mk_mid_row m c p q b hc (Fin.castSucc k) (by show 0 < (k : ℕ); omega)
        (by show (k : ℕ) < m + 2; omega),
      mk_mid_row m c p q b hc (Fin.succ k) (by show 0 < (k : ℕ) + 1; omega)
        (by show (k : ℕ) + 1 < m + 2; omega)]
    simp only [Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega
  · -- the row above the bottom row, and the bottom row
    have hkv : (k : ℕ) = m + 1 := by omega
    have e1 : Fin.castSucc k = ⟨m + 1, by omega⟩ := Fin.ext (by simp [hkv])
    have e2 : Fin.succ k = Fin.last (m + 2) := Fin.ext (by simp [hkv])
    rw [e1, e2, mk_mid_row m c p q b hc ⟨m + 1, by omega⟩ (by simp) (by simp), rowVal_eq]
    have hN0 : c = 1 → (mk m c p q b (Fin.last (m + 2)) 0 : ℕ) = 1 := by
      intro hc1
      rw [mk_val]
      simp only [Fin.val_zero, Fin.val_last, true_and, and_true, or_true, ite_true]
      split_ifs <;> first | omega | simp_all
    rcases Nat.lt_or_ge p (m + 2) with hp | hp
    · have hp' : p ≤ ((⟨m + 1, by omega⟩ : Fin (m + 3)) : ℕ) := by show p ≤ m + 1; omega
      rw [if_pos hp']
      -- some entry of the bottom row is one (and it is not the first entry when `c = 1`)
      obtain ⟨k', hk'0, hk'1⟩ : ∃ k' : Fin (m + 3), (c = 1 → (k' : ℕ) ≠ 0) ∧
          (mk m c p q b (Fin.last (m + 2)) k' : ℕ) = 1 := by
        rcases Nat.lt_or_ge b 1 with hb0 | hb1
        · have hq : q < m + 2 := (hex (by omega)).1 hp
          refine ⟨⟨q, by omega⟩, fun hc1 => by show q ≠ 0; omega, ?_⟩
          rw [mk_val]
          simp only [Fin.val_last, true_and, ite_true]
          split_ifs <;> omega
        · refine ⟨Fin.last (m + 2), fun _ => by simp, ?_⟩
          rw [mk_val]
          simp only [Fin.val_last, and_true, ite_true]
          split_ifs <;> omega
      obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
      · have := bval_ge_one _ k' hk'1
        omega
      · have := bval_ge_head_one _ k' (hk'0 rfl) (hN0 rfl) hk'1
        omega
    · have hp' : ¬ p ≤ ((⟨m + 1, by omega⟩ : Fin (m + 3)) : ℕ) := by
        show ¬ p ≤ m + 1; omega
      rw [if_neg hp']
      obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
      · simp
      · have := bval_ge_head _ (hN0 rfl)
        omega

/-- `mk` with admissible parameters is a good array. -/
theorem mk_good (m c p q b : ℕ) (hc : c < 2) (hcp : c ≤ p) (hpN : p ≤ m + 2)
    (hcq : c ≤ q) (hqN : q ≤ m + 2) (hb : b < 2) (hex : b = 0 → (p < m + 2 ↔ q < m + 2)) :
    Good (mk m c p q b) := by
  refine ⟨mk_rows_mono m c p q b hc hcp hpN hcq hqN hb hex, ?_, ?_⟩
  · rw [← rowVal_tr, tr_mk]
    exact mk_rows_mono m c q p b hc hcq hqN hcp hpN hb (fun h => (hex h).symm)
  · intro i j hi hi' hj hj'
    apply Fin.ext
    rw [mk_val]
    simp only [Fin.val_zero]
    split_ifs <;> omega

/-- The excluded parameters do not give good arrays. -/
theorem excl {A : Fin (m + 3) → Fin (m + 3) → Fin 2} (hA : Good A) {c p q b : ℕ}
    (heq : A = mk m c p q b) (hc : c < 2) (hb0 : b = 0) (hp : p < m + 2) (hq : q = m + 2) :
    False := by
  subst heq
  have h1 : rowVal (mk m c p q b) ⟨m + 1, by omega⟩ ≤
      rowVal (mk m c p q b) (Fin.last (m + 2)) :=
    hA.1 (Fin.le_def.2 (by show m + 1 ≤ m + 2; omega))
  rw [mk_mid_row m c p q b hc ⟨m + 1, by omega⟩ (by simp) (by simp), rowVal_eq,
    bval_ends (m + 1) (mk m c p q b (Fin.last (m + 2)))] at h1
  · rw [mk_val, mk_val] at h1
    simp only [Fin.val_zero, Fin.val_last, true_and, and_true, or_true, ite_true] at h1
    obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
    · split_ifs at h1 <;> first | omega | simp_all
    · split_ifs at h1 <;> first | omega | simp_all
  · intro j hj hj'
    apply Fin.ext
    rw [mk_val]
    simp only [Fin.val_zero, Fin.val_last, true_and, ite_true]
    split_ifs <;> first | omega | simp_all

/-- Every good array is some `mk` with admissible parameters. -/
theorem good_eq_mk {A : Fin (m + 3) → Fin (m + 3) → Fin 2} (hA : Good A) :
    ∃ c p q b : ℕ, c < 2 ∧ c ≤ p ∧ p ≤ m + 2 ∧ c ≤ q ∧ q ≤ m + 2 ∧ b < 2 ∧
      (b = 0 → (p < m + 2 ↔ q < m + 2)) ∧ A = mk m c p q b := by
  obtain ⟨c, hcdef⟩ : ∃ c, (A ⟨1, by omega⟩ 0 : ℕ) = c := ⟨_, rfl⟩
  have hcc : ((tr A) ⟨1, by omega⟩ 0 : ℕ) = c := (below_eq_right hA).symm.trans hcdef
  obtain ⟨p, hp1, hp2, hp3⟩ := exists_p hA
  obtain ⟨q, hq1, hq2, hq3⟩ := exists_p (good_tr hA)
  rw [hcdef] at hp1 hp3
  rw [hcc] at hq1 hq3
  have hc : c ≤ 1 := hcdef ▸ fin2_le _
  obtain ⟨b, hbdef⟩ : ∃ b, (A (Fin.last (m + 2)) (Fin.last (m + 2)) : ℕ) = b := ⟨_, rfl⟩
  have hb : b < 2 := hbdef ▸ (A (Fin.last (m + 2)) (Fin.last (m + 2))).isLt
  have heq : A = mk m c p q b := by
    funext i j
    apply Fin.ext
    rw [mk_val]
    by_cases h1 : (i : ℕ) = m + 2 ∧ (j : ℕ) = m + 2
    · rw [if_pos h1]
      have hi : i = Fin.last (m + 2) := Fin.ext h1.1
      have hj : j = Fin.last (m + 2) := Fin.ext h1.2
      subst hi
      subst hj
      rw [hbdef]
      split_ifs <;> omega
    rw [if_neg h1]
    by_cases h2 : c = 1 ∧ (i : ℕ) = 0 ∧ (j : ℕ) = 0
    · rw [if_pos h2]
      have hi : i = 0 := Fin.ext h2.2.1
      have hj : j = 0 := Fin.ext h2.2.2
      subst hi
      subst hj
      rw [corner_zero hA]
      rfl
    rw [if_neg h2]
    by_cases h3 : c = 1 ∧ ((i : ℕ) = 0 ∨ (j : ℕ) = 0)
    · rw [if_pos h3]
      rcases h3.2 with hi | hj
      · have hj : (j : ℕ) ≠ 0 := fun hj => h2 ⟨h3.1, hi, hj⟩
        have hi' : i = 0 := Fin.ext hi
        subst hi'
        exact left_one (good_tr hA) (hcc.trans h3.1) j hj
      · have hi : (i : ℕ) ≠ 0 := fun hi => h2 ⟨h3.1, hi, hj⟩
        have hj' : j = 0 := Fin.ext hj
        subst hj'
        exact left_one hA (hcdef.trans h3.1) i hi
    rw [if_neg h3]
    by_cases h4 : (j : ℕ) = m + 2
    · rw [if_pos h4]
      have hi : (i : ℕ) < m + 2 := by
        have := i.isLt
        omega
      have hci : c ≤ (i : ℕ) := by omega
      have hj : j = Fin.last (m + 2) := Fin.ext h4
      subst hj
      exact hp3 i hci hi
    rw [if_neg h4]
    by_cases h5 : (i : ℕ) = m + 2
    · rw [if_pos h5]
      have hj : (j : ℕ) < m + 2 := by
        have := j.isLt
        omega
      have hcj : c ≤ (j : ℕ) := by omega
      have hi : i = Fin.last (m + 2) := Fin.ext h5
      subst hi
      exact hq3 j hcj hj
    rw [if_neg h5]
    have hi : (i : ℕ) < m + 2 := by
      have := i.isLt
      omega
    have hj : (j : ℕ) < m + 2 := by
      have := j.isLt
      omega
    rcases Nat.eq_zero_or_pos (i : ℕ) with hi0 | hi0
    · have hc0 : (A ⟨1, by omega⟩ 0 : ℕ) = 0 := by omega
      have hi' : i = 0 := Fin.ext hi0
      subst hi'
      rw [top_zero hA hc0 j (by omega)]
      rfl
    rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hj0
    · have h0' : ((tr A) ⟨1, by omega⟩ 0 : ℕ) = 0 := by omega
      have hj' : j = 0 := Fin.ext hj0
      subst hj'
      have := top_zero (good_tr hA) h0' i (by omega)
      show ((tr A 0 i : Fin 2) : ℕ) = 0
      rw [this]
      rfl
    rw [hA.2.2 i j hi0 (by omega) hj0 (by omega)]
    rfl
  refine ⟨c, p, q, b, by omega, hp1, hp2, hq1, hq2, hb,
    fun hb0 => ⟨fun hp => ?_, fun hq => ?_⟩, heq⟩
  · by_contra hq
    exact excl hA heq (by omega) hb0 hp (by omega)
  · by_contra hp
    have heq' : tr A = mk m c q p b := by rw [heq, tr_mk]
    exact excl (good_tr hA) heq' (by omega) hb0 hq (by omega)

theorem mk_p_inj {c p q b p' q' b' : ℕ} (h : mk m c p q b = mk m c p' q' b')
    (hcp : c ≤ p) (hpN : p ≤ m + 2) (hcp' : c ≤ p') (hpN' : p' ≤ m + 2) : p = p' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := congrArg (fun A => (A ⟨p, by omega⟩ (Fin.last (m + 2)) : ℕ)) h
    simp only [mk_val, Fin.val_last, and_true, ite_true] at this
    split_ifs at this <;> first | omega | simp_all
  · have := congrArg (fun A => (A ⟨p', by omega⟩ (Fin.last (m + 2)) : ℕ)) h
    simp only [mk_val, Fin.val_last, and_true, ite_true] at this
    split_ifs at this <;> first | omega | simp_all

theorem mk_inj {c p q b c' p' q' b' : ℕ} (h : mk m c p q b = mk m c' p' q' b')
    (hc : c < 2) (hc' : c' < 2) (hb : b < 2) (hb' : b' < 2)
    (hcp : c ≤ p) (hpN : p ≤ m + 2) (hcq : c ≤ q) (hqN : q ≤ m + 2)
    (hcp' : c' ≤ p') (hpN' : p' ≤ m + 2) (hcq' : c' ≤ q') (hqN' : q' ≤ m + 2) :
    c = c' ∧ p = p' ∧ q = q' ∧ b = b' := by
  have hcc : c = c' := by
    have := congrArg (fun A => (A ⟨1, by omega⟩ 0 : ℕ)) h
    simp only [mk_val, Fin.val_zero, and_true, or_true] at this
    split_ifs at this <;> first | omega | simp_all
  subst hcc
  have hbb : b = b' := by
    have := congrArg (fun A => (A (Fin.last (m + 2)) (Fin.last (m + 2)) : ℕ)) h
    simp only [mk_val, Fin.val_last, and_true, ite_true] at this
    split_ifs at this <;> omega
  subst hbb
  refine ⟨rfl, mk_p_inj h hcp hpN hcp' hpN', ?_, rfl⟩
  have h' := congrArg tr h
  rw [tr_mk, tr_mk] at h'
  exact mk_p_inj h' hcq hqN hcq' hqN'

/-- The parameter set: the pair `(c, b)`, then the pair `(p, q)`. -/
def S (m : ℕ) : Finset (Σ _ : ℕ × ℕ, ℕ × ℕ) :=
  (range 2 ×ˢ range 2).sigma (fun cb => if cb.2 = 1 then Icc cb.1 (m + 2) ×ˢ Icc cb.1 (m + 2)
    else insert (m + 2, m + 2) (Ico cb.1 (m + 2) ×ˢ Ico cb.1 (m + 2)))

theorem mem_S (m c b p q : ℕ) : (⟨(c, b), (p, q)⟩ : Σ _ : ℕ × ℕ, ℕ × ℕ) ∈ S m ↔
    c < 2 ∧ b < 2 ∧ c ≤ p ∧ p ≤ m + 2 ∧ c ≤ q ∧ q ≤ m + 2 ∧
      (b = 0 → (p < m + 2 ↔ q < m + 2)) := by
  simp only [S, Finset.mem_sigma, Finset.mem_product, Finset.mem_range]
  split_ifs with hb
  · simp only [Finset.mem_product, Finset.mem_Icc]
    omega
  · simp only [Finset.mem_insert, Finset.mem_product, Finset.mem_Ico, Prod.mk.injEq]
    omega

theorem card_S (m : ℕ) : (S m).card = 4 * (m + 2) ^ 2 + 4 := by
  rw [S, Finset.card_sigma, Finset.sum_product]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [show ¬ ((0 : ℕ) = 1) by omega, if_true, if_false]
  rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp)]
  simp only [Finset.card_product, Nat.card_Icc, Nat.card_Ico]
  have e1 : m + 2 + 1 - 1 = m + 2 := by omega
  have e2 : m + 2 - 1 = m + 1 := by omega
  rw [e1, e2, Nat.sub_zero, Nat.sub_zero]
  ring

/-- The closed form for `n = m + 3`. -/
theorem a_eq (m : ℕ) : a (m + 3) = 4 * (m + 2) ^ 2 + 4 := by
  classical
  let F : (Σ _ : ℕ × ℕ, ℕ × ℕ) → (Fin (m + 3) → Fin (m + 3) → Fin 2) :=
    fun s => mk m s.1.1 s.2.1 s.2.2 s.1.2
  have key : ∀ A, A ∈ (S m).image F ↔ Good A := by
    intro A
    rw [Finset.mem_image]
    constructor
    · rintro ⟨⟨⟨c, b⟩, ⟨p, q⟩⟩, hs, rfl⟩
      rw [mem_S] at hs
      obtain ⟨hc, hb, hcp, hpN, hcq, hqN, hex⟩ := hs
      exact mk_good m c p q b hc hcp hpN hcq hqN hb hex
    · intro hA
      obtain ⟨c, p, q, b, hc, hcp, hpN, hcq, hqN, hb, hex, rfl⟩ := good_eq_mk hA
      exact ⟨⟨(c, b), (p, q)⟩,
        (mem_S m c b p q).2 ⟨hc, hb, hcp, hpN, hcq, hqN, hex⟩, rfl⟩
  have hinj : Set.InjOn F (S m) := by
    rintro ⟨⟨c, b⟩, ⟨p, q⟩⟩ hs ⟨⟨c', b'⟩, ⟨p', q'⟩⟩ hs' h
    rw [Finset.mem_coe, mem_S] at hs hs'
    obtain ⟨hc, hb, hcp, hpN, hcq, hqN, -⟩ := hs
    obtain ⟨hc', hb', hcp', hpN', hcq', hqN', -⟩ := hs'
    obtain ⟨h1, h2, h3, h4⟩ := mk_inj h hc hc' hb hb' hcp hpN hcq hqN hcp' hpN' hcq' hqN'
    subst h1 h2 h3 h4
    rfl
  unfold a
  rw [Fintype.card_of_subtype _ key, Finset.card_image_of_injOn hinj, card_S]

theorem a_two : a 2 = 7 := by
  classical
  have key : ∀ A : Fin 2 → Fin 2 → Fin 2,
      A ∈ (Finset.univ.filter (fun A : Fin 2 → Fin 2 → Fin 2 =>
        rowVal A 0 ≤ rowVal A 1 ∧ colVal A 0 ≤ colVal A 1)) ↔ Good A := by
    intro A
    rw [Finset.mem_filter]
    unfold Good
    rw [Fin.monotone_iff_le_succ, Fin.monotone_iff_le_succ]
    simp only [Finset.mem_univ, true_and, Fin.forall_fin_one, Fin.castSucc_zero,
      Fin.succ_zero_eq_one]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2, fun i j hi hi' => absurd hi' (by omega)⟩
    · rintro ⟨h1, h2, -⟩
      exact ⟨h1, h2⟩
  unfold a
  rw [Fintype.card_of_subtype _ key]
  decide

theorem closed_int (n : ℕ) (hn : 2 < n) : (a n : ℤ) = 4 * (2 - 2 * n + n ^ 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [a_eq]
  push_cast
  ring

theorem a_closedQ (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = 4 * (n : ℚ) ^ 2 - 8 * n + 8 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [a_eq]
  push_cast
  ring

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n < 2 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 3 =
      X ^ 2 * (7 - X + X ^ 2 + X ^ 3) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n < 2 then (0 : ℚ) else (a n : ℚ)) with hA
  have hcube : ((1 : ℚ⟦X⟧) - X) ^ 3 =
      1 - X ^ 1 - X ^ 1 - X ^ 1 + X ^ 2 + X ^ 2 + X ^ 2 - X ^ 3 := by
    ring
  have hrhs : (X : ℚ⟦X⟧) ^ 2 * (7 - X + X ^ 2 + X ^ 3) =
      C (7 : ℚ) * X ^ 2 - C (1 : ℚ) * X ^ 3 + C (1 : ℚ) * X ^ 4 + C (1 : ℚ) * X ^ 5 := by
    simp only [map_ofNat, map_one]
    ring
  rw [hcube, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mul_X_pow', hA, coeff_mk]
  have h2 : (a 2 : ℚ) = 7 := by rw [a_two]; norm_num
  rcases k with _ | _ | _ | _ | _ | _ | j
  · simp
  · simp
  · norm_num [h2]
  · norm_num [h2, a_closedQ]
  · norm_num [h2, a_closedQ]
  · norm_num [h2, a_closedQ]
  · simp only [show ¬ (j + 6 < 2) by omega, show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega,
      show 3 ≤ j + 6 by omega, show j + 6 - 1 = j + 5 by omega, show j + 6 - 2 = j + 4 by omega,
      show j + 6 - 3 = j + 3 by omega, show ¬ (j + 5 < 2) by omega, show ¬ (j + 4 < 2) by omega,
      show ¬ (j + 3 < 2) by omega, show ¬ (j + 6 = 2) by omega, show ¬ (j + 6 = 3) by omega,
      show ¬ (j + 6 = 4) by omega, show ¬ (j + 6 = 5) by omega, if_true, if_false]
    rw [a_closedQ (j + 6) (by omega), a_closedQ (j + 5) (by omega), a_closedQ (j + 4) (by omega),
      a_closedQ (j + 3) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a162024.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.closed_int⟩
