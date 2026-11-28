import OMAStatements.S_oeis_a198717
import Mathlib

namespace OMA.Helpers.A198717

open OMA.S_oeis_a198717 Finset

/-- The extension count only depends on the number of colors introduced so far. -/
def E : ℕ → ℕ → ℤ
  | 0, _ => 1
  | n + 1, t => ((t : ℤ) + 1 + (t : ℤ) * t) * E n t +
      (if t + 2 < 7 then 2 * ((t : ℤ) + 1) * E n (t + 1) else 0) +
      (if t + 3 < 7 then E n (t + 2) else 0)

theorem sum_const_of {s : Finset ℕ} {f : ℕ → ℤ} {c : ℤ} (h : ∀ x ∈ s, f x = c) :
    ∑ x ∈ s, f x = (s.card : ℤ) * c := by
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]

theorem card_erase_range {t b : ℕ} (hb : b < t + 2) : ((range (t + 2)).erase b).card = t + 1 := by
  rw [card_erase_of_mem (mem_range.2 hb), card_range]
  omega

theorem card_erase_erase_range {t a b : ℕ} (ha : a < t + 2) (hb : b < t + 2) (hab : a ≠ b) :
    (((range (t + 2)).erase a).erase b).card = t := by
  rw [card_erase_of_mem (mem_erase.2 ⟨Ne.symm hab, mem_range.2 hb⟩), card_erase_range ha]
  omega

theorem ext_eq (n : ℕ) : ∀ t a b, a < t + 2 → b < t + 2 → a ≠ b → extensions 7 n t a b = E n t := by
  induction n with
  | zero => intro t a b _ _ _; rfl
  | succ n ih =>
    intro t a b ha hb hab
    have e1 : ∑ y ∈ (range (t + 2)).erase b, extensions 7 n t b y = ((t : ℤ) + 1) * E n t := by
      rw [sum_const_of (c := E n t) (fun y hy => by
        obtain ⟨h1, h2⟩ := mem_erase.1 hy
        exact ih t b y hb (mem_range.1 h2) (Ne.symm h1)), card_erase_range hb]
      push_cast
      ring
    have e2 : ∑ x ∈ ((range (t + 2)).erase a).erase b,
        ∑ y ∈ ((range (t + 2)).erase b).erase x, extensions 7 n t x y =
        (t : ℤ) * ((t : ℤ) * E n t) := by
      rw [sum_const_of (c := (t : ℤ) * E n t) (fun x hx => by
        obtain ⟨hx1, hx2⟩ := mem_erase.1 hx
        obtain ⟨hx3, hx4⟩ := mem_erase.1 hx2
        have hxr := mem_range.1 hx4
        rw [sum_const_of (c := E n t) (fun y hy => by
          obtain ⟨hy1, hy2⟩ := mem_erase.1 hy
          obtain ⟨_, hy4⟩ := mem_erase.1 hy2
          exact ih t x y hxr (mem_range.1 hy4) (Ne.symm hy1)),
          card_erase_erase_range hb hxr (Ne.symm hx1)]),
        card_erase_erase_range ha hb hab]
    have e3 : ∑ y ∈ (range (t + 2)).erase b, extensions 7 n (t + 1) (t + 2) y =
        ((t : ℤ) + 1) * E n (t + 1) := by
      rw [sum_const_of (c := E n (t + 1)) (fun y hy => by
        obtain ⟨_, h2⟩ := mem_erase.1 hy
        have := mem_range.1 h2
        exact ih (t + 1) (t + 2) y (by omega) (by omega) (by omega)), card_erase_range hb]
      push_cast
      ring
    have e4 : ∑ x ∈ (range (t + 2)).erase a, extensions 7 n (t + 1) x (t + 2) =
        ((t : ℤ) + 1) * E n (t + 1) := by
      rw [sum_const_of (c := E n (t + 1)) (fun x hx => by
        obtain ⟨_, h2⟩ := mem_erase.1 hx
        have := mem_range.1 h2
        exact ih (t + 1) x (t + 2) (by omega) (by omega) (by omega)), card_erase_range ha]
      push_cast
      ring
    have e5 : extensions 7 n (t + 2) (t + 2) (t + 3) = E n (t + 2) :=
      ih (t + 2) (t + 2) (t + 3) (by omega) (by omega) (by omega)
    simp only [extensions]
    rw [e1, e2, e3, e4, e5]
    simp only [E]
    split_ifs <;> ring

theorem E5 (n : ℕ) : E n 5 = 31 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [E]; norm_num [ih]; ring

theorem E4 (n : ℕ) : E n 4 = 31 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [E]; norm_num [ih, E5]; ring

theorem E3 (n : ℕ) : 2 * E n 3 = 31 ^ n + 13 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [E]
    norm_num [E4, E5]
    linear_combination 13 * ih

theorem E2 (n : ℕ) : 6 * E n 2 = 31 ^ n + 3 * 13 ^ n + 2 * 7 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [E]
    norm_num [E4]
    linear_combination 7 * ih + 18 * E3 n

theorem E1 (n : ℕ) : 24 * E n 1 = 31 ^ n + 6 * 13 ^ n + 8 * 7 ^ n + 9 * 3 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [E]
    norm_num
    linear_combination 3 * ih + 16 * E2 n + 12 * E3 n

theorem E0 (n : ℕ) : 120 * E n 0 = 44 + 45 * 3 ^ n + 20 * 7 ^ n + 10 * 13 ^ n + 31 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [E]
    norm_num
    linear_combination ih + 10 * E1 n + 20 * E2 n

theorem seq_succ (m : ℕ) : 120 * sequence (m + 1) = 44 + 45 * 3 ^ m + 20 * 7 ^ m + 10 * 13 ^ m + 31 ^ m := by
  have : sequence (m + 1) = E m 0 := ext_eq m 0 0 1 (by omega) (by omega) (by omega)
  rw [this, E0]

end OMA.Helpers.A198717

open OMA.Helpers.A198717 OMA.S_oeis_a198717 in
theorem OMA.solution : type_of% @OMA.S_oeis_a198717.main := by
  refine ⟨fun m => by rw [seq_succ]; ring, fun n => ?_⟩
  have s0 : sequence 0 = 0 := rfl
  have s1 : sequence 1 = 1 := by have := seq_succ 0; norm_num at this; omega
  have s2 : sequence 2 = 4 := by have := seq_succ 1; norm_num at this; omega
  have s3 : sequence 3 = 34 := by have := seq_succ 2; norm_num at this; omega
  have s4 : sequence 4 = 499 := by have := seq_succ 3; norm_num at this; omega
  have s5 : sequence 5 = 10507 := by have := seq_succ 4; norm_num at this; omega
  rcases Nat.lt_or_ge n 6 with hn | hn
  · interval_cases n <;> simp [delayed, numerator, s0, s1, s2, s3, s4, s5]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
    have d0 : delayed 0 (k + 6) = sequence (k + 5 + 1) := by
      simp only [delayed]; rw [if_pos (by omega)]; congr 1
    have d1 : delayed 1 (k + 6) = sequence (k + 4 + 1) := by
      simp only [delayed]; rw [if_pos (by omega)]; congr 1
    have d2 : delayed 2 (k + 6) = sequence (k + 3 + 1) := by
      simp only [delayed]; rw [if_pos (by omega)]; congr 1
    have d3 : delayed 3 (k + 6) = sequence (k + 2 + 1) := by
      simp only [delayed]; rw [if_pos (by omega)]; congr 1
    have d4 : delayed 4 (k + 6) = sequence (k + 1 + 1) := by
      simp only [delayed]; rw [if_pos (by omega)]; congr 1
    have d5 : delayed 5 (k + 6) = sequence (k + 0 + 1) := by
      simp only [delayed]; rw [if_pos (by omega)]; congr 1
    have hnum : numerator (k + 6) = 0 := by
      simp only [numerator]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
    rw [d0, d1, d2, d3, d4, d5, hnum]
    have h0 := seq_succ (k + 5)
    have h1 := seq_succ (k + 4)
    have h2 := seq_succ (k + 3)
    have h3 := seq_succ (k + 2)
    have h4 := seq_succ (k + 1)
    have h5 := seq_succ (k + 0)
    have key : (120 : ℤ) * (sequence (k + 5 + 1) - 55 * sequence (k + 4 + 1) +
        918 * sequence (k + 3 + 1) - 5818 * sequence (k + 2 + 1) +
        13417 * sequence (k + 1 + 1) - 8463 * sequence (k + 0 + 1)) = 0 := by
      linear_combination h0 - 55 * h1 + 918 * h2 - 5818 * h3 + 13417 * h4 - 8463 * h5
    omega
