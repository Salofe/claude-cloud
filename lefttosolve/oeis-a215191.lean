import OMAStatements.S_oeis_a215191

/-!
Proof of Barker's conjectures for A215191 (arrays of 4 integers in 0..n with no two adjacent
equal-length blocks of equal sum).

For an array (x0, x1, x2, x3) the condition says x0 /= x1, x1 /= x2, x2 /= x3 and
x0 + x1 /= x2 + x3. Fix the middle pair (b, c) = (x1, x2) with b /= c. Among the n^2 pairs
(x0, x3) with x0 /= b and x3 /= c, the bad ones satisfy x0 - x3 = c - b; there are
n + 1 - |b - c| such pairs in the box, of which (b, 2b - c) and (2c - b, c) are excluded when they
lie in the box. Summing over (b, c): the n^2 terms give (n+1) n^3, the terms n + 1 - |b - c| give
(n+1)^3 - D(n) - (n+1)^2 with 3 D(n) = n (n+1) (n+2), and each family of boundary terms gives
2 M(n) with M(n) = Sum_b min(b, n - b) and 4 M(n) = n^2 - (n mod 2). Hence
a(n) = (3n^4 + n^3 - n)/3 - (n mod 2), which gives both closed forms and the g.f.
-/

namespace OMA.Helpers

open OMA.S_oeis_a215191 Finset

theorem a215191_good_iff (x : Fin 4 → ℕ) :
    good x ↔ x 0 ≠ x 1 ∧ x 1 ≠ x 2 ∧ x 2 ≠ x 3 ∧ x 0 + x 1 ≠ x 2 + x 3 := by
  have g0 : get x 0 = x 0 := rfl
  have g1 : get x 1 = x 1 := rfl
  have g2 : get x 2 = x 2 := rfl
  have g3 : get x 3 = x 3 := rfl
  constructor
  · intro h
    have h01 := h 0 1 (by norm_num) (by norm_num)
    have h11 := h 1 1 (by norm_num) (by norm_num)
    have h21 := h 2 1 (by norm_num) (by norm_num)
    have h02 := h 0 2 (by norm_num) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero] at h01 h11 h21 h02
    norm_num [g0, g1, g2, g3] at h01 h11 h21 h02
    exact ⟨h01, h11, h21, h02⟩
  · rintro ⟨h1, h2, h3, h4⟩ i k hk hik
    have hk2 : k ≤ 2 := by omega
    interval_cases k
    · have : i ≤ 2 := by omega
      interval_cases i <;>
        simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero, g0, g1, g2, g3]
    · have : i = 0 := by omega
      subst this
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero]
      norm_num [g0, g1, g2, g3]
      exact h4

/-- The good tuples, written as ((x1, x2), (x0, x3)). -/
def a215191T (n : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (((range (n + 1)) ×ˢ (range (n + 1))) ×ˢ ((range (n + 1)) ×ˢ (range (n + 1)))).filter
    (fun p => p.2.1 ≠ p.1.1 ∧ p.1.1 ≠ p.1.2 ∧ p.1.2 ≠ p.2.2 ∧ p.2.1 + p.1.1 ≠ p.1.2 + p.2.2)

theorem a215191_ncard (n : ℕ) : a n = (a215191T n).card := by
  unfold a
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_congr (fun x _ => ((x 1, x 2), (x 0, x 3)))
  · intro x hx
    obtain ⟨hle, hg⟩ := hx
    rw [a215191_good_iff] at hg
    have := hle 0
    have := hle 1
    have := hle 2
    have := hle 3
    simp only [a215191T, coe_filter, mem_product, mem_range, Set.mem_setOf_eq]
    omega
  · intro x y _ _ h
    simp only [Prod.mk.injEq] at h
    funext i
    fin_cases i <;> simp_all
  · intro p hp
    simp only [a215191T, coe_filter, mem_product, mem_range, Set.mem_setOf_eq] at hp
    refine ⟨![p.2.1, p.1.1, p.1.2, p.2.2], ⟨?_, ?_⟩, ?_⟩
    · intro i
      fin_cases i <;> simp <;> omega
    · rw [a215191_good_iff]
      simp
      omega
    · simp

theorem a215191_card_filter_prod {α β : Type*} (s : Finset α) (t : Finset β)
    (P : α × β → Prop) [DecidablePred P] :
    ((s ×ˢ t).filter P).card = ∑ x ∈ s, (t.filter (fun y => P (x, y))).card := by
  rw [card_eq_sum_ones, sum_filter, sum_product]
  refine sum_congr rfl (fun x _ => ?_)
  rw [card_eq_sum_ones, sum_filter]

theorem a215191_L1 (n c e : ℕ) (hc : c ≤ n) :
    (((range (n + 1)).filter (fun d => c ≠ d ∧ e ≠ c + d)).card : ℤ) =
      n - (if c ≤ e ∧ e ≤ c + n ∧ e ≠ 2 * c then 1 else 0) := by
  split_ifs with h
  · have hs : (range (n + 1)).filter (fun d => c ≠ d ∧ e ≠ c + d) =
        ((range (n + 1)).erase c).erase (e - c) := by
      ext d
      simp only [mem_filter, mem_range, mem_erase]
      omega
    have m1 : c ∈ range (n + 1) := by simp; omega
    have m2 : e - c ∈ (range (n + 1)).erase c := by simp; omega
    rw [hs, card_erase_of_mem m2, card_erase_of_mem m1, card_range]
    omega
  · have hs : (range (n + 1)).filter (fun d => c ≠ d ∧ e ≠ c + d) = (range (n + 1)).erase c := by
      ext d
      simp only [mem_filter, mem_range, mem_erase]
      omega
    have m1 : c ∈ range (n + 1) := by simp; omega
    rw [hs, card_erase_of_mem m1, card_range]
    omega

theorem a215191_L2 (n b c : ℕ) (hb : b ≤ n) (hc : c ≤ n) (hbc : b ≠ c) :
    (((range (n + 1)).filter
      (fun a => a ≠ b ∧ c ≤ a + b ∧ a + b ≤ c + n ∧ a + b ≠ 2 * c)).card : ℤ) =
      ((n : ℤ) + 1 - ((b - c : ℕ) : ℤ) - ((c - b : ℕ) : ℤ)) -
        (if c ≤ 2 * b ∧ 2 * b ≤ c + n then 1 else 0) -
        (if b ≤ 2 * c ∧ 2 * c ≤ b + n then 1 else 0) := by
  split_ifs with h1 h2 h2
  · have hs : (range (n + 1)).filter
        (fun a => a ≠ b ∧ c ≤ a + b ∧ a + b ≤ c + n ∧ a + b ≠ 2 * c) =
        ((Icc (c - b) (n - (b - c))).erase b).erase (2 * c - b) := by
      ext a
      simp only [mem_filter, mem_range, mem_erase, mem_Icc]
      omega
    have m1 : b ∈ Icc (c - b) (n - (b - c)) := by simp; omega
    have m2 : 2 * c - b ∈ (Icc (c - b) (n - (b - c))).erase b := by simp; omega
    rw [hs, card_erase_of_mem m2, card_erase_of_mem m1, Nat.card_Icc]
    omega
  · have hs : (range (n + 1)).filter
        (fun a => a ≠ b ∧ c ≤ a + b ∧ a + b ≤ c + n ∧ a + b ≠ 2 * c) =
        (Icc (c - b) (n - (b - c))).erase b := by
      ext a
      simp only [mem_filter, mem_range, mem_erase, mem_Icc]
      omega
    have m1 : b ∈ Icc (c - b) (n - (b - c)) := by simp; omega
    rw [hs, card_erase_of_mem m1, Nat.card_Icc]
    omega
  · have hs : (range (n + 1)).filter
        (fun a => a ≠ b ∧ c ≤ a + b ∧ a + b ≤ c + n ∧ a + b ≠ 2 * c) =
        (Icc (c - b) (n - (b - c))).erase (2 * c - b) := by
      ext a
      simp only [mem_filter, mem_range, mem_erase, mem_Icc]
      omega
    have m2 : 2 * c - b ∈ Icc (c - b) (n - (b - c)) := by simp; omega
    rw [hs, card_erase_of_mem m2, Nat.card_Icc]
    omega
  · have hs : (range (n + 1)).filter
        (fun a => a ≠ b ∧ c ≤ a + b ∧ a + b ≤ c + n ∧ a + b ≠ 2 * c) =
        Icc (c - b) (n - (b - c)) := by
      ext a
      simp only [mem_filter, mem_range, mem_Icc]
      omega
    rw [hs, Nat.card_Icc]
    omega

theorem a215191_sum_ne (n b : ℕ) (hb : b ≤ n) (K : ℤ) :
    ∑ c ∈ range (n + 1), (if b = c then (0 : ℤ) else K) = n * K := by
  have h1 : ∀ c ∈ range (n + 1), (if b = c then (0 : ℤ) else K) =
      K - (if b = c then K else 0) := by
    intro c _
    split_ifs <;> ring
  rw [sum_congr rfl h1, sum_sub_distrib, sum_ite_eq, if_pos (by simp; omega), sum_const,
    card_range, nsmul_eq_mul]
  push_cast
  ring

theorem a215191_inner (n b c : ℕ) (hb : b ≤ n) (hc : c ≤ n) :
    ((((range (n + 1)) ×ˢ (range (n + 1))).filter
      (fun q : ℕ × ℕ => q.1 ≠ b ∧ b ≠ c ∧ c ≠ q.2 ∧ q.1 + b ≠ c + q.2)).card : ℤ) =
      (if b = c then 0 else (n : ℤ) * n) -
        (((n : ℤ) + 1 - ((b - c : ℕ) : ℤ) - ((c - b : ℕ) : ℤ)) -
          (if b = c then (n : ℤ) + 1 else 0)) +
        (if b = c then 0 else (if c ≤ 2 * b ∧ 2 * b ≤ c + n then 1 else 0)) +
        (if b = c then 0 else (if b ≤ 2 * c ∧ 2 * c ≤ b + n then 1 else 0)) := by
  rw [a215191_card_filter_prod]
  push_cast
  by_cases hbc : b = c
  · subst hbc
    simp
  · simp only [hbc, if_false, sub_zero]
    have key : ∀ x ∈ range (n + 1),
        (((range (n + 1)).filter
          (fun y => (x, y).1 ≠ b ∧ b ≠ c ∧ c ≠ (x, y).2 ∧ (x, y).1 + b ≠ c + (x, y).2)).card : ℤ) =
          (if b = x then 0 else (n : ℤ)) -
            (if x ≠ b ∧ c ≤ x + b ∧ x + b ≤ c + n ∧ x + b ≠ 2 * c then 1 else 0) := by
      intro x _
      by_cases hx : b = x
      · subst hx
        simp
      · have hf : (range (n + 1)).filter
            (fun y => (x, y).1 ≠ b ∧ b ≠ c ∧ c ≠ (x, y).2 ∧ (x, y).1 + b ≠ c + (x, y).2) =
            (range (n + 1)).filter (fun d => c ≠ d ∧ x + b ≠ c + d) := by
          apply filter_congr
          intro y _
          simp only [ne_eq]
          constructor
          · intro h; exact ⟨h.2.2.1, h.2.2.2⟩
          · intro h; exact ⟨fun e => hx e.symm, hbc, h.1, h.2⟩
        rw [hf, a215191_L1 n c (x + b) hc]
        simp only [hx, if_false, Ne.symm hx, not_false_eq_true, true_and, ne_eq]
    rw [sum_congr rfl key, sum_sub_distrib, a215191_sum_ne n b hb, sum_boole]
    rw [a215191_L2 n b c hb hc hbc]
    ring

theorem a215191_tri (n : ℕ) :
    2 * ∑ b ∈ range (n + 1), ((n + 1 - b : ℕ) : ℤ) = ((n : ℤ) + 1) * ((n : ℤ) + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ']
    have h : ∀ b ∈ range (n + 1), ((n + 1 + 1 - (b + 1) : ℕ) : ℤ) = ((n + 1 - b : ℕ) : ℤ) := by
      intro b _
      congr 1
      omega
    rw [sum_congr rfl h, mul_add, ih]
    push_cast
    ring

/-- The sum of |b - c| over 0 <= b, c <= n. -/
def a215191D (n : ℕ) : ℤ :=
  ∑ b ∈ range (n + 1), ∑ c ∈ range (n + 1), (((b - c : ℕ) : ℤ) + ((c - b : ℕ) : ℤ))

theorem a215191_D (n : ℕ) : 3 * a215191D n = (n : ℤ) * (n + 1) * (n + 2) := by
  induction n with
  | zero => simp [a215191D]
  | succ n ih =>
    have e1 : a215191D (n + 1) = a215191D n +
        ∑ b ∈ range (n + 1), (((b - (n + 1) : ℕ) : ℤ) + ((n + 1 - b : ℕ) : ℤ)) +
        ∑ c ∈ range (n + 1), ((((n + 1) - c : ℕ) : ℤ) + ((c - (n + 1) : ℕ) : ℤ)) := by
      unfold a215191D
      rw [sum_range_succ, sum_range_succ]
      simp only [sum_range_succ, sum_add_distrib, Nat.sub_self]
      push_cast
      ring
    have e2 : ∀ b ∈ range (n + 1), (((b - (n + 1) : ℕ) : ℤ) + ((n + 1 - b : ℕ) : ℤ)) =
        ((n + 1 - b : ℕ) : ℤ) := by
      intro b hb
      simp only [mem_range] at hb
      rw [Nat.sub_eq_zero_of_le (by omega)]
      simp
    have e3 : ∀ c ∈ range (n + 1), ((((n + 1) - c : ℕ) : ℤ) + ((c - (n + 1) : ℕ) : ℤ)) =
        ((n + 1 - c : ℕ) : ℤ) := by
      intro c hc
      simp only [mem_range] at hc
      rw [Nat.sub_eq_zero_of_le (show c ≤ n + 1 by omega)]
      simp
    rw [e1, sum_congr rfl e2, sum_congr rfl e3]
    have t := a215191_tri n
    push_cast
    linear_combination ih + 3 * t

/-- Sum of min b (n - b). -/
def a215191M (n : ℕ) : ℕ := ∑ b ∈ range (n + 1), min b (n - b)

theorem a215191_M_step (n : ℕ) : a215191M (n + 2) = a215191M n + n + 1 := by
  unfold a215191M
  rw [sum_range_succ', sum_range_succ]
  have h : ∀ b ∈ range (n + 1), min (b + 1) (n + 2 - (b + 1)) = min b (n - b) + 1 := by
    intro b hb
    simp only [mem_range] at hb
    omega
  rw [sum_congr rfl h, sum_add_distrib]
  simp
  omega

theorem a215191_M (n : ℕ) : 4 * a215191M n + n % 2 = n * n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [a215191M]
    · simp [a215191M, sum_range_succ]
    · rw [a215191_M_step]
      have := ih n (by omega)
      have h2 : (n + 2) % 2 = n % 2 := by omega
      rw [h2]
      nlinarith

theorem a215191_Kb (n b : ℕ) (hb : b ≤ n) :
    ∑ c ∈ range (n + 1), (if b = c then (0 : ℤ) else
      (if c ≤ 2 * b ∧ 2 * b ≤ c + n then 1 else 0)) = 2 * (min b (n - b) : ℕ) := by
  have h1 : ∀ c ∈ range (n + 1), (if b = c then (0 : ℤ) else
      (if c ≤ 2 * b ∧ 2 * b ≤ c + n then 1 else 0)) =
      if (b ≠ c ∧ c ≤ 2 * b ∧ 2 * b ≤ c + n) then 1 else 0 := by
    intro c _
    by_cases h : b = c
    · simp [h]
    · simp [h]
  rw [sum_congr rfl h1, sum_boole]
  have hs : (range (n + 1)).filter (fun c => b ≠ c ∧ c ≤ 2 * b ∧ 2 * b ≤ c + n) =
      (Icc (2 * b - n) (min n (2 * b))).erase b := by
    ext c
    simp only [mem_filter, mem_range, mem_erase, mem_Icc]
    omega
  have m : b ∈ Icc (2 * b - n) (min n (2 * b)) := by simp; omega
  rw [hs, card_erase_of_mem m, Nat.card_Icc]
  omega

theorem a215191_count (n : ℕ) :
    (a n : ℤ) = ((n : ℤ) + 1) * n * (n * n) -
      (((n : ℤ) + 1) ^ 3 - a215191D n - ((n : ℤ) + 1) * (n + 1)) +
      4 * (a215191M n : ℤ) := by
  rw [a215191_ncard, a215191T, a215191_card_filter_prod, sum_product]
  push_cast
  have h1 : ∀ b ∈ range (n + 1), ∀ c ∈ range (n + 1),
      ((((range (n + 1)) ×ˢ (range (n + 1))).filter (fun y : ℕ × ℕ =>
        ((b, c), y).2.1 ≠ ((b, c), y).1.1 ∧ ((b, c), y).1.1 ≠ ((b, c), y).1.2 ∧
        ((b, c), y).1.2 ≠ ((b, c), y).2.2 ∧
        ((b, c), y).2.1 + ((b, c), y).1.1 ≠ ((b, c), y).1.2 + ((b, c), y).2.2)).card : ℤ) =
      (if b = c then 0 else (n : ℤ) * n) -
        (((n : ℤ) + 1 - ((b - c : ℕ) : ℤ) - ((c - b : ℕ) : ℤ)) -
          (if b = c then (n : ℤ) + 1 else 0)) +
        (if b = c then 0 else (if c ≤ 2 * b ∧ 2 * b ≤ c + n then 1 else 0)) +
        (if b = c then 0 else (if b ≤ 2 * c ∧ 2 * c ≤ b + n then 1 else 0)) := by
    intro b hb c hc
    simp only [mem_range] at hb hc
    exact a215191_inner n b c (by omega) (by omega)
  rw [sum_congr rfl (fun b hb => sum_congr rfl (h1 b hb))]
  simp only [sum_add_distrib, sum_sub_distrib]
  have s1 : ∑ b ∈ range (n + 1), ∑ c ∈ range (n + 1), (if b = c then (0 : ℤ) else (n : ℤ) * n) =
      ((n : ℤ) + 1) * n * (n * n) := by
    rw [sum_congr rfl (fun b hb => a215191_sum_ne n b (by simp at hb; omega) _)]
    simp
    ring
  have s3 : ∑ b ∈ range (n + 1), ∑ c ∈ range (n + 1), (if b = c then (n : ℤ) + 1 else 0) =
      ((n : ℤ) + 1) * (n + 1) := by
    rw [sum_congr rfl (fun b hb => by rw [sum_ite_eq, if_pos hb])]
    simp
  have s4 : ∑ b ∈ range (n + 1), ∑ c ∈ range (n + 1),
      (if b = c then (0 : ℤ) else (if c ≤ 2 * b ∧ 2 * b ≤ c + n then 1 else 0)) =
      2 * (a215191M n : ℤ) := by
    rw [sum_congr rfl (fun b hb => a215191_Kb n b (by simp at hb; omega)), a215191M]
    push_cast
    rw [mul_sum]
  have s5 : ∑ b ∈ range (n + 1), ∑ c ∈ range (n + 1),
      (if b = c then (0 : ℤ) else (if b ≤ 2 * c ∧ 2 * c ≤ b + n then 1 else 0)) =
      2 * (a215191M n : ℤ) := by
    rw [sum_comm, ← s4]
    refine sum_congr rfl (fun b _ => sum_congr rfl (fun c _ => ?_))
    by_cases h : b = c
    · simp [h]
    · simp [h, Ne.symm h]
  rw [s1, s3, s4, s5]
  have hD : a215191D n = ∑ b ∈ range (n + 1), ∑ c ∈ range (n + 1), ((b - c : ℕ) : ℤ) +
      ∑ b ∈ range (n + 1), ∑ c ∈ range (n + 1), ((c - b : ℕ) : ℤ) := by
    unfold a215191D
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun b _ => sum_add_distrib)
  rw [hD]
  simp only [sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

theorem a215191_closed (n : ℕ) :
    (a n : ℚ) = (3 * (n : ℚ) ^ 4 + (n : ℚ) ^ 3 - n) / 3 - ((n % 2 : ℕ) : ℚ) := by
  have h := a215191_count n
  have hD := a215191_D n
  have hM := a215191_M n
  have h' : (a n : ℚ) = ((n : ℚ) + 1) * n * (n * n) -
      (((n : ℚ) + 1) ^ 3 - (a215191D n : ℚ) - ((n : ℚ) + 1) * (n + 1)) +
      4 * (a215191M n : ℚ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) h
  have hD' : 3 * (a215191D n : ℚ) = (n : ℚ) * (n + 1) * (n + 2) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hD
  have hM' : 4 * (a215191M n : ℚ) + ((n % 2 : ℕ) : ℚ) = (n : ℚ) * n := by
    exact_mod_cast hM
  linear_combination h' + (1 / 3 : ℚ) * hD' + hM'

/-- The quasi-polynomial a(n) = (3n^4 + n^3 - n)/3 + ((-1)^n - 1)/2 (also 0 at n = 0). -/
noncomputable def a215191Q (n : ℕ) : ℚ :=
  (3 * (n : ℚ) ^ 4 + (n : ℚ) ^ 3 - n) / 3 + ((-1 : ℚ) ^ n - 1) / 2

theorem a215191_Q (n : ℕ) : (if n = 0 then (0 : ℚ) else (a n : ℚ)) = a215191Q n := by
  split_ifs with h
  · subst h
    simp [a215191Q]
  · rw [a215191_closed, a215191Q]
    rcases Nat.even_or_odd n with he | ho
    · rw [Nat.even_iff.mp he, he.neg_one_pow]
      simp
    · rw [Nat.odd_iff.mp ho, ho.neg_one_pow]
      push_cast
      ring

open PowerSeries in
theorem a215191_gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X)) =
      2 * X ^ 2 * (9 + 8 * X + 7 * X ^ 2) := by
  have hm : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
      PowerSeries.mk a215191Q := by
    ext n
    simp only [coeff_mk]
    exact a215191_Q n
  rw [hm]
  set A : ℚ⟦X⟧ := PowerSeries.mk a215191Q with hA
  have hl : A * ((1 - X) ^ 5 * (1 + X)) =
      A - C (4 : ℚ) * (A * X ^ 1) + C (5 : ℚ) * (A * X ^ 2) - C (5 : ℚ) * (A * X ^ 4) +
        C (4 : ℚ) * (A * X ^ 5) - A * X ^ 6 := by
    simp only [map_ofNat]
    ring
  have hr : (2 : ℚ⟦X⟧) * X ^ 2 * (9 + 8 * X + 7 * X ^ 2) =
      C (18 : ℚ) * X ^ 2 + C (16 : ℚ) * X ^ 3 + C (14 : ℚ) * X ^ 4 := by
    simp only [map_ofNat]
    ring
  rw [hl, hr]
  ext k
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow]
  simp only [coeff_mul_X_pow', hA, coeff_mk]
  rcases k with _ | _ | _ | _ | _ | _ | j
  · simp [a215191Q]
  · norm_num [a215191Q]
  · norm_num [a215191Q]
  · norm_num [a215191Q]
  · norm_num [a215191Q]
  · norm_num [a215191Q]
  · have e : j + 1 + 1 + 1 + 1 + 1 + 1 = j + 6 := rfl
    simp only [e, show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega, show 4 ≤ j + 6 by omega,
      show 5 ≤ j + 6 by omega, show 6 ≤ j + 6 by omega,
      show j + 6 - 1 = j + 5 by omega, show j + 6 - 2 = j + 4 by omega,
      show j + 6 - 4 = j + 2 by omega, show j + 6 - 5 = j + 1 by omega,
      show j + 6 - 6 = j by omega,
      show ¬ (j + 6 = 2) by omega, show ¬ (j + 6 = 3) by omega,
      show ¬ (j + 6 = 4) by omega, if_true, if_false]
    simp only [a215191Q]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a215191.main := by
  refine ⟨OMA.Helpers.a215191_gf, ?_, ?_⟩
  · intro n _ hn
    rw [OMA.Helpers.a215191_closed, hn]
    push_cast
    ring
  · intro n hn
    rw [OMA.Helpers.a215191_closed, hn]
    push_cast
    ring
