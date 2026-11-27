import OMAReductions.R_OeisA67599_conjecture_R1

/-!
# Step H2 of the reduction OeisA67599.conjecture.R1

For a prime q greater than 7, the prime factor list of 2401 * q = 7 ^ 4 * q is [7, 7, 7, 7, q].
Removing duplicates leaves [7, q] with multiplicities 4 and 1, so the decimal encoding
concatenates 7, 4, q and 1, which is 740 * 10 ^ (number of decimal digits of q) + 10 * q + 1.

Only the upstream definitions `OeisA67599.a` and `OeisA67599.concatenateNats` are used (no
upstream theorem). The factor list is pinned down by uniqueness of prime factorization up to
permutation, together with the fact that `Nat.primeFactorsList` is sorted.
-/

namespace OMA.Helpers

theorem a67599_pfl_eq (q : ℕ) (hq7 : 7 < q) (hq : q.Prime) :
    (2401 * q).primeFactorsList = [7, 7, 7, 7, q] := by
  have h7 : Nat.Prime 7 := by norm_num
  have hperm : [7, 7, 7, 7, q].Perm (2401 * q).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · simp
      ring
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with h | h | h | h | h <;> subst h <;> assumption
  refine (List.Perm.eq_of_sortedLE (Nat.primeFactorsList_sorted _) ?_ hperm.symm)
  rw [List.sortedLE_iff_pairwise]
  simp [List.pairwise_cons]
  omega

end OMA.Helpers

theorem OMA.solution : OMA.R_OeisA67599_conjecture_R1.H2 := by
  intro q hq7 hq
  unfold OeisA67599.a
  rw [if_neg (by omega)]
  simp only [OMA.Helpers.a67599_pfl_eq q hq7 hq]
  have hne : (7 : ℕ) ≠ q := by omega
  have hd : [7, 7, 7, 7, q].dedup = [7, q] := by
    rw [List.dedup_cons_of_mem (by simp), List.dedup_cons_of_mem (by simp),
      List.dedup_cons_of_mem (by simp), List.dedup_cons_of_notMem (by simp [hne]),
      List.dedup_cons_of_notMem (by simp)]
    simp
  rw [hd]
  have c7 : [7, 7, 7, 7, q].count 7 = 4 := by
    simp [hne.symm]
  have cq : [7, 7, 7, 7, q].count q = 1 := by
    simp [hne]
  simp only [List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    List.append_nil, c7, cq, List.foldl_cons, List.foldl_nil, OeisA67599.concatenateNats]
  norm_num
  ring
