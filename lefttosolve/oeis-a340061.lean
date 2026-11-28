import OMAStatements.S_oeis_a340061
import Mathlib

namespace OMA.Helpers

open Finset

/-- Removing `k` copies of the part `d`. -/
def partStrip340061 (n d k : ℕ) (hd : 0 < d) (hk : k * d ≤ n) :
    {p : Nat.Partition n // Multiset.replicate k d ≤ p.parts} ≃ Nat.Partition (n - k * d) where
  toFun p := ⟨p.1.parts - Multiset.replicate k d,
    fun hi => p.1.parts_pos (Multiset.mem_of_le (Multiset.sub_le_self _ _) hi),
    by
      have h1 := congrArg Multiset.sum (tsub_add_cancel_of_le p.2)
      rw [Multiset.sum_add, Multiset.sum_replicate, p.1.parts_sum, smul_eq_mul] at h1
      omega⟩
  invFun q := ⟨⟨q.parts + Multiset.replicate k d, fun hi => by
      rcases Multiset.mem_add.mp hi with h | h
      · exact q.parts_pos h
      · rw [Multiset.eq_of_mem_replicate h]; exact hd,
    by rw [Multiset.sum_add, Multiset.sum_replicate, q.parts_sum, smul_eq_mul]; omega⟩,
    Multiset.le_add_left _ _⟩
  left_inv p := Subtype.ext (Nat.Partition.ext (tsub_add_cancel_of_le p.2))
  right_inv q := Nat.Partition.ext (add_tsub_cancel_right _ _)

lemma count_mul_le340061 {n d : ℕ} (p : Nat.Partition n) :
    p.parts.count d * d ≤ n := by
  have h1 := Multiset.le_count_iff_replicate_le.mp (le_refl (p.parts.count d))
  have h2 := congrArg Multiset.sum (tsub_add_cancel_of_le h1)
  rw [Multiset.sum_add, Multiset.sum_replicate, p.parts_sum, smul_eq_mul] at h2
  omega

lemma card_filter340061 (n d k : ℕ) (hd : 0 < d) :
    (univ.filter (fun p : Nat.Partition n => k ≤ p.parts.count d)).card =
      if k * d ≤ n then Fintype.card (Nat.Partition (n - k * d)) else 0 := by
  classical
  split_ifs with hk
  · rw [← Fintype.card_congr (partStrip340061 n d k hd hk), Fintype.card_subtype]
    congr 1
    ext p
    simp [Multiset.le_count_iff_replicate_le]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ hp
    apply hk
    have h3 := count_mul_le340061 (d := d) p
    have h4 : k * d ≤ p.parts.count d * d := Nat.mul_le_mul_right d hp
    omega

lemma rhs340061 (n d : ℕ) (hd : 0 < d) :
    Multiset.count d ((univ : Finset (Nat.Partition n)).val.bind (fun p => p.parts)) =
      ∑ k ∈ range n, if (k + 1) * d ≤ n then
        Fintype.card (Nat.Partition (n - (k + 1) * d)) else 0 := by
  classical
  rw [Multiset.count_bind]
  change ∑ p : Nat.Partition n, Multiset.count d p.parts = _
  have hc : ∀ p : Nat.Partition n, Multiset.count d p.parts =
      ∑ k ∈ range n, if k + 1 ≤ Multiset.count d p.parts then 1 else 0 := by
    intro p
    have hle : Multiset.count d p.parts ≤ n := by
      have h3 := count_mul_le340061 (d := d) p
      have h4 : Multiset.count d p.parts ≤ Multiset.count d p.parts * d :=
        Nat.le_mul_of_pos_right _ hd
      omega
    rw [Finset.sum_boole]
    have h5 : (range n).filter (fun k => k + 1 ≤ Multiset.count d p.parts) =
        range (Multiset.count d p.parts) := by
      ext k
      simp only [mem_filter, mem_range]
      omega
    rw [h5, card_range, Nat.cast_id]
  rw [Finset.sum_congr rfl (fun p _ => hc p), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← card_filter340061 n d (k + 1) hd, Finset.sum_boole, Nat.cast_id]

lemma lhs340061 (n d : ℕ) :
    Multiset.count d (((OMA.S_oeis_a340061.row n : List ℕ) : Multiset ℕ).bind
        (fun t => (Nat.divisors t).val)) =
      ∑ i ∈ range n, if d ∣ i + 1 then OMA.S_oeis_a340061.A000041 (n - (i + 1)) else 0 := by
  classical
  unfold OMA.S_oeis_a340061.row
  rw [← Multiset.coe_bind, Multiset.bind_assoc, Multiset.count_bind]
  change ∑ i ∈ range n, _ = _
  apply Finset.sum_congr rfl
  intro i _
  rw [Multiset.coe_replicate, Multiset.count_bind, Multiset.map_replicate, Multiset.sum_replicate,
    Multiset.count_eq_of_nodup (Finset.nodup _), smul_eq_mul]
  by_cases h : d ∣ i + 1
  · simp [h, Nat.mem_divisors]
  · simp [h, Nat.mem_divisors]

lemma reindex340061 (n d : ℕ) (hd : 0 < d) (f : ℕ → ℕ) :
    (∑ i ∈ range n, if d ∣ i + 1 then f (i + 1) else 0) =
      ∑ k ∈ range n, if (k + 1) * d ≤ n then f ((k + 1) * d) else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun i => (i + 1) / d - 1) (fun k => (k + 1) * d - 1) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [mem_filter, mem_range] at hi ⊢
    obtain ⟨hi1, c, hc⟩ := hi
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · rw [h] at hc; omega
      · exact h
    rw [hc, Nat.mul_div_cancel_left c hd, Nat.sub_add_cancel hc1, mul_comm, ← hc]
    have : c ≤ d * c := Nat.le_mul_of_pos_left c hd
    omega
  · intro k hk
    simp only [mem_filter, mem_range] at hk ⊢
    obtain ⟨hk1, hk2⟩ := hk
    have hpos : 1 ≤ (k + 1) * d := Nat.mul_pos (Nat.succ_pos k) hd
    rw [Nat.sub_add_cancel hpos]
    exact ⟨by omega, Dvd.intro_left _ rfl⟩
  · intro i hi
    simp only [mem_filter, mem_range] at hi
    obtain ⟨hi1, c, hc⟩ := hi
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · rw [h] at hc; omega
      · exact h
    show ((i + 1) / d - 1 + 1) * d - 1 = i
    rw [hc, Nat.mul_div_cancel_left c hd, Nat.sub_add_cancel hc1, mul_comm, ← hc]
    omega
  · intro k hk
    have hpos : 1 ≤ (k + 1) * d := Nat.mul_pos (Nat.succ_pos k) hd
    show ((k + 1) * d - 1 + 1) / d - 1 = k
    rw [Nat.sub_add_cancel hpos, Nat.mul_div_cancel _ hd]
    omega
  · intro i hi
    simp only [mem_filter, mem_range] at hi
    obtain ⟨hi1, c, hc⟩ := hi
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · rw [h] at hc; omega
      · exact h
    show f (i + 1) = f (((i + 1) / d - 1 + 1) * d)
    rw [hc, Nat.mul_div_cancel_left c hd, Nat.sub_add_cancel hc1, mul_comm]

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a340061.main := by
  intro n _
  ext d
  by_cases hd : d = 0
  · subst hd
    rw [Multiset.count_eq_zero.mpr, Multiset.count_eq_zero.mpr]
    · intro h
      obtain ⟨p, _, hp⟩ := Multiset.mem_bind.mp h
      exact lt_irrefl 0 (p.parts_pos hp)
    · intro h
      obtain ⟨t, _, ht⟩ := Multiset.mem_bind.mp h
      simp at ht
  · rw [OMA.Helpers.lhs340061, OMA.Helpers.rhs340061 n d (Nat.pos_of_ne_zero hd)]
    exact OMA.Helpers.reindex340061 n d (Nat.pos_of_ne_zero hd)
      (fun j => OMA.S_oeis_a340061.A000041 (n - j))
