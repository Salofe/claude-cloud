import OMAStatements.S_oeis_a000392
import Mathlib

namespace OMA.Helpers

open Finset

theorem pow23_inj {i j a b : ℕ} (h : 2 ^ i * 3 ^ j = 2 ^ a * 3 ^ b) : i = a ∧ j = b := by
  have h2 := congrArg (fun x => Nat.factorization x 2) h
  have h3 := congrArg (fun x => Nat.factorization x 3) h
  simp [Nat.factorization_mul, Nat.factorization_pow, Nat.Prime.factorization Nat.prime_two,
    Nat.Prime.factorization Nat.prime_three] at h2 h3
  exact ⟨h2, h3⟩

/-- The layer of numbers `2^i * 3^j` with `i + j = m`. -/
def layer (m : ℕ) : Finset ℕ := (antidiagonal m).image (fun p => 2 ^ p.1 * 3 ^ p.2)

theorem mem_layer (m x : ℕ) : x ∈ layer m ↔ ∃ i j, i + j = m ∧ 2 ^ i * 3 ^ j = x := by
  simp [layer, Finset.HasAntidiagonal.mem_antidiagonal]

theorem mem_S (n x : ℕ) :
    x ∈ OMA.S_oeis_a000392.S (n + 1) ↔ ∃ i j, i + j ≤ n ∧ 2 ^ i * 3 ^ j = x := by
  induction n generalizing x with
  | zero =>
    simp only [OMA.S_oeis_a000392.S, mem_singleton]
    constructor
    · rintro rfl
      exact ⟨0, 0, le_refl _, by norm_num⟩
    · rintro ⟨i, j, hij, rfl⟩
      have hi : i = 0 := by omega
      have hj : j = 0 := by omega
      subst hi hj
      norm_num
  | succ n ih =>
    show x ∈ OMA.S_oeis_a000392.S (n + 1) ∪ (OMA.S_oeis_a000392.S (n + 1)).image (fun x => 2 * x) ∪
      (OMA.S_oeis_a000392.S (n + 1)).image (fun x => 3 * x) ↔ _
    simp only [mem_union, mem_image, ih]
    constructor
    · rintro ((⟨i, j, hij, rfl⟩ | ⟨y, ⟨i, j, hij, rfl⟩, rfl⟩) | ⟨y, ⟨i, j, hij, rfl⟩, rfl⟩)
      · exact ⟨i, j, by omega, rfl⟩
      · exact ⟨i + 1, j, by omega, by ring⟩
      · exact ⟨i, j + 1, by omega, by ring⟩
    · rintro ⟨i, j, hij, rfl⟩
      by_cases h : i + j ≤ n
      · exact Or.inl (Or.inl ⟨i, j, h, rfl⟩)
      · rcases Nat.eq_zero_or_pos i with hi | hi
        · subst hi
          obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
          exact Or.inr ⟨2 ^ 0 * 3 ^ j', ⟨0, j', by omega, rfl⟩, by ring⟩
        · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
          exact Or.inl (Or.inr ⟨2 ^ i' * 3 ^ j, ⟨i', j, by omega, rfl⟩, by ring⟩)

theorem S_succ (n : ℕ) :
    OMA.S_oeis_a000392.S (n + 2) = OMA.S_oeis_a000392.S (n + 1) ∪ layer (n + 1) := by
  ext x
  rw [mem_union, mem_S (n + 1), mem_S n, mem_layer]
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    by_cases h : i + j ≤ n
    · exact Or.inl ⟨i, j, h, rfl⟩
    · exact Or.inr ⟨i, j, by omega, rfl⟩
  · rintro (⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩)
    · exact ⟨i, j, by omega, rfl⟩
    · exact ⟨i, j, by omega, rfl⟩

theorem disj (n : ℕ) : Disjoint (OMA.S_oeis_a000392.S (n + 1)) (layer (n + 1)) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [mem_S] at hx
  rw [mem_layer] at hx'
  obtain ⟨i, j, hij, rfl⟩ := hx
  obtain ⟨a, b, hab, h⟩ := hx'
  obtain ⟨h1, h2⟩ := pow23_inj h
  omega

theorem sum_layer (m : ℕ) : ∑ x ∈ layer m, x = ∑ p ∈ antidiagonal m, 2 ^ p.1 * 3 ^ p.2 := by
  rw [layer, Finset.sum_image]
  intro p _ q _ h
  obtain ⟨h1, h2⟩ := pow23_inj h
  exact Prod.ext h1 h2

theorem sum_antidiag (m : ℕ) :
    (∑ p ∈ antidiagonal m, 2 ^ p.1 * 3 ^ p.2) + 2 ^ (m + 1) = 3 ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.Nat.sum_antidiagonal_succ]
    have : ∑ p ∈ antidiagonal m, 2 ^ (p.1 + 1) * 3 ^ p.2 =
        2 * ∑ p ∈ antidiagonal m, 2 ^ p.1 * 3 ^ p.2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p _ => by ring)
    rw [this]
    simp only [pow_succ] at ih ⊢
    omega

theorem sum_S (n : ℕ) :
    2 * (∑ x ∈ OMA.S_oeis_a000392.S (n + 1), x) + 2 ^ (n + 3) = 3 ^ (n + 2) + 1 := by
  induction n with
  | zero => simp [OMA.S_oeis_a000392.S]
  | succ n ih =>
    rw [S_succ, Finset.sum_union (disj n), sum_layer]
    have h := sum_antidiag (n + 1)
    simp only [pow_succ] at ih h ⊢
    omega

theorem stirling2 (n : ℕ) : Nat.stirlingSecond (n + 2) 2 + 1 = 2 ^ (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by ring, Nat.stirlingSecond_succ_succ,
      show (1 : ℕ) + 1 = 2 by rfl, Nat.stirlingSecond_one_right]
    rw [pow_succ]
    omega

theorem stirling3 (n : ℕ) : 2 * Nat.stirlingSecond (n + 3) 3 + 2 ^ (n + 3) = 3 ^ (n + 2) + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h3 : Nat.stirlingSecond (n + 1 + 3) 3 =
        3 * Nat.stirlingSecond (n + 3) 3 + Nat.stirlingSecond (n + 3) 2 :=
      Nat.stirlingSecond_succ_succ (n + 3) 2
    rw [h3]
    have h2 : Nat.stirlingSecond (n + 3) 2 + 1 = 2 ^ (n + 2) := stirling2 (n + 1)
    simp only [pow_succ] at ih h2 ⊢
    omega

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a000392.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := OMA.Helpers.stirling3 m
  have h2 := OMA.Helpers.sum_S m
  show Nat.stirlingSecond (m + 1 + 2) 3 = _
  rw [show m + 1 + 2 = m + 3 by ring]
  omega
