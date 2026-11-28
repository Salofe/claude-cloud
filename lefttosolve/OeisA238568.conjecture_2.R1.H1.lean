import OMAReductions.R_OeisA238568_conjecture_2_R1
import Mathlib

/-! The seven listed indices have count one. Primality is decided by trial division
up to the integer square root, and the prime counting function by a running count,
both proved equal to the Mathlib notions; the kernel then evaluates the counts. -/

namespace OMA.Helpers

open Finset

def noDiv (n : ℕ) : ℕ → Bool
  | 0 => true
  | 1 => true
  | k+2 => (n % (k+2) != 0) && noDiv n (k+1)

theorem noDiv_iff (n : ℕ) : ∀ k, noDiv n k = true ↔ ∀ m, 2 ≤ m → m ≤ k → ¬ m ∣ n
  | 0 => by simp only [noDiv, true_iff]; intro m h1 h2; omega
  | 1 => by simp only [noDiv, true_iff]; intro m h1 h2; omega
  | k+2 => by
    simp only [noDiv, Bool.and_eq_true, bne_iff_ne, ne_eq, noDiv_iff n (k+1)]
    constructor
    · rintro ⟨h, h'⟩ m hm1 hm2 hd
      rcases Nat.lt_or_ge m (k+2) with hlt | hge
      · exact h' m hm1 (by omega) hd
      · have e : m = k+2 := by omega
        subst e
        exact h (Nat.mod_eq_zero_of_dvd hd)
    · intro h
      exact ⟨fun hmod => h (k+2) (by omega) le_rfl (Nat.dvd_of_mod_eq_zero hmod),
        fun m hm1 hm2 => h m hm1 (by omega)⟩

def isPr (n : ℕ) : Bool := decide (2 ≤ n) && noDiv n (Nat.sqrt n)

theorem isPr_iff (n : ℕ) : isPr n = true ↔ Nat.Prime n := by
  rw [Nat.prime_def_le_sqrt, isPr, Bool.and_eq_true, decide_eq_true_iff, noDiv_iff]

def cnt : ℕ → ℕ
  | 0 => 0
  | k+1 => cnt k + if isPr k then 1 else 0

theorem cnt_eq (m : ℕ) : cnt m = Nat.count Nat.Prime m := by
  induction m with
  | zero => simp [cnt]
  | succ k ih =>
    rw [cnt, Nat.count_succ, ih]
    by_cases h : Nat.Prime k
    · simp [h, (isPr_iff k).mpr h]
    · have hf : isPr k = false := by
        rcases hb : isPr k
        · rfl
        · exact absurd ((isPr_iff k).mp hb) h
      simp [h, hf]

theorem pc_eq (m : ℕ) : Nat.primeCounting m = cnt (m+1) := by
  rw [cnt_eq]; rfl

theorem a_eq (n : ℕ) : OeisA238568.a n =
    ((Ico 1 n).filter fun k => isPr (n ^ 2 - cnt (k * n + 1)) = true).card := by
  unfold OeisA238568.a
  congr 1
  apply Finset.filter_congr
  intro k _
  rw [pc_eq, isPr_iff]

end OMA.Helpers

theorem OMA.solution : OMA.R_OeisA238568_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (rw [OMA.Helpers.a_eq]; decide +kernel)
