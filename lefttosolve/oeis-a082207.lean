import OMAStatements.S_oeis_a082207
import Mathlib

namespace OMA.Helpers

/-- Digit list `1...1 777 1...1` with `k` ones on each side. -/
def L (k : ℕ) : List ℕ := List.replicate k 1 ++ [7, 7, 7] ++ List.replicate k 1

theorem L_lt (k : ℕ) : ∀ l ∈ L k, l < 10 := by
  intro l hl
  simp [L] at hl
  omega

theorem L_last (k : ℕ) (h : L k ≠ []) : (L k).getLast h ≠ 0 := by
  have hm : (L k).getLast h ∈ L k := List.getLast_mem h
  generalize (L k).getLast h = x at hm ⊢
  simp [L] at hm
  omega

theorem digits_L (k : ℕ) : Nat.digits 10 (Nat.ofDigits 10 (L k)) = L k :=
  Nat.digits_ofDigits 10 (by norm_num) (L k) (L_lt k) (L_last k)

theorem L_rev (k : ℕ) : (L k).reverse = L k := by
  simp [L, List.reverse_append, List.reverse_replicate]

theorem L_prod (k : ℕ) : (L k).prod = 343 := by
  simp [L, List.prod_append, List.prod_replicate]

theorem L_len (k : ℕ) : (L k).length = 2 * k + 3 := by
  simp [L]; ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a082207.main := by
  have hinj : Function.Injective (fun k => Nat.ofDigits 10 (OMA.Helpers.L k)) := by
    intro a b h
    have h2 := congrArg (Nat.digits 10) h
    simp only [OMA.Helpers.digits_L] at h2
    have h3 := congrArg List.length h2
    rw [OMA.Helpers.L_len, OMA.Helpers.L_len] at h3
    omega
  refine Set.infinite_of_injective_forall_mem hinj ?_
  intro k
  simp only [Set.mem_ofPred_eq, OMA.S_oeis_a082207.isPalindrome, OMA.S_oeis_a082207.digitProd,
    OMA.Helpers.digits_L, OMA.Helpers.L_rev, OMA.Helpers.L_prod]
  refine ⟨trivial, by norm_num, ?_⟩
  norm_num
