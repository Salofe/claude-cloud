import OMAStatements.S_oeis_a391629
import Mathlib

/-!
Proof of the conjecture for A391629: `a(n) = A000041(n) - A368684(n)` for `n >= 1`.

The first sums of a weakly decreasing sequence `a, b, ...` are weakly decreasing, and their first
entry `a + b` is their maximum (`zip_le391629`). If they equal the weakly increasing list of parts
of `q`, whose first entry is the minimum, then all parts are equal to `a + b`. With `k` parts:
`k = 1` forces `a + b = n >= 2`, and `k >= 2` gives `a + b = b + d` with `a >= b >= d`, so the part
`a + b = 2 b` is even. Conversely `[n - 1, 1]` and the constant sequence `e, ..., e` (`k + 1`
terms) realize these partitions. Hence `q` is a first-sums partition iff its parts are `k` copies
of `n / k` with `k | n` and (`k = 1`, `n >= 2`) or (`k >= 2`, `n / k` even). These `k` are exactly
the elements of the set counted by A368684 (`of_memS391629`, `memS_of391629`), and `q` corresponds
to its number of parts (`card_first391629`).
-/

namespace OMA.Helpers

open OMA.S_oeis_a391629

/-- The set counted by A368684. -/
def S391629 (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (n / 2)).filter (fun s => s ∣ n ∧ s ∣ n / 2)

theorem of_memS391629 {n k : ℕ} (h : k ∈ S391629 n) :
    k ∣ n ∧ ((k = 1 ∧ 2 ≤ n) ∨ (2 ≤ k ∧ 2 ∣ n / k)) := by
  simp only [S391629, Finset.mem_filter, Finset.mem_Icc] at h
  obtain ⟨⟨hk1, hk2⟩, hkn, hkn2⟩ := h
  refine ⟨hkn, ?_⟩
  rcases Nat.lt_or_ge k 2 with hk | hk
  · left
    exact ⟨by omega, by omega⟩
  · right
    refine ⟨hk, ?_⟩
    obtain ⟨t, ht⟩ := hkn2
    have hmod : n % 2 = 0 := by
      by_contra hne
      have hn : n = 2 * (k * t) + 1 := by omega
      have h1 : k ∣ 2 * (k * t) := ⟨2 * t, by ring⟩
      rw [hn] at hkn
      have := Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp hkn)
      omega
    have hn : n = k * (2 * t) := by
      have h2 : n = 2 * (n / 2) := by omega
      rw [h2, ht]
      ring
    rw [hn, Nat.mul_div_cancel_left _ (by omega)]
    exact ⟨t, by ring⟩

theorem memS_of391629 {n k : ℕ} (hn : 1 ≤ n) (hk : k ∣ n)
    (h : (k = 1 ∧ 2 ≤ n) ∨ (2 ≤ k ∧ 2 ∣ n / k)) : k ∈ S391629 n := by
  simp only [S391629, Finset.mem_filter, Finset.mem_Icc]
  rcases h with ⟨rfl, h2⟩ | ⟨hk2, t, ht⟩
  · exact ⟨⟨le_refl 1, by omega⟩, one_dvd _, one_dvd _⟩
  · obtain ⟨c, rfl⟩ := hk
    rw [Nat.mul_div_cancel_left _ (by omega)] at ht
    subst ht
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        simp at hn
      · exact h0
    have e : k * (2 * t) / 2 = k * t := by
      rw [show k * (2 * t) = 2 * (k * t) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [e]
    exact ⟨⟨by omega, Nat.le_mul_of_pos_right k ht1⟩, ⟨2 * t, rfl⟩, dvd_mul_right _ _⟩

/-- The partition of `n` into `k` equal parts. -/
def mkPart391629 (n k : ℕ) (hk : k ∣ n) (hn : 0 < n) : Nat.Partition n where
  parts := Multiset.replicate k (n / k)
  parts_pos := by
    intro i hi
    rw [Multiset.eq_of_mem_replicate hi]
    exact Nat.div_pos (Nat.le_of_dvd hn hk) (Nat.pos_of_dvd_of_pos hk hn)
  parts_sum := by
    rw [Multiset.sum_replicate, smul_eq_mul, Nat.mul_div_cancel' hk]

theorem sort_replicate391629 (k d : ℕ) :
    (Multiset.replicate k d).sort (· ≤ ·) = List.replicate k d := by
  rw [List.eq_replicate_iff]
  refine ⟨by rw [Multiset.length_sort, Multiset.card_replicate], fun b hb => ?_⟩
  rw [Multiset.mem_sort] at hb
  exact Multiset.eq_of_mem_replicate hb

theorem zip_le391629 (A B : ℕ) : ∀ (l l' : List ℕ), (∀ u ∈ l, u ≤ A) → (∀ v ∈ l', v ≤ B) →
    ∀ y ∈ List.zipWith (· + ·) l l', y ≤ A + B
  | [], _, _, _, y, hy => by simp at hy
  | _ :: _, [], _, _, y, hy => by simp at hy
  | a :: l, b :: l', hl, hl', y, hy => by
    simp only [List.zipWith_cons_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact Nat.add_le_add (hl a (by simp)) (hl' b (by simp))
    · exact zip_le391629 A B l l' (fun u hu => hl u (by simp [hu]))
        (fun v hv => hl' v (by simp [hv])) y hy

theorem forward391629 {n : ℕ} (hn : 1 ≤ n) (q : Nat.Partition n)
    (h : IsFirstSumsOfPartition q) :
    Multiset.card q.parts ∈ S391629 n ∧
      q.parts = Multiset.replicate (Multiset.card q.parts) (n / Multiset.card q.parts) := by
  obtain ⟨p, hpos, hpw, hfs⟩ := h
  have hsorted : (partsAsc q).Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hcoe : ((partsAsc q : List ℕ) : Multiset ℕ) = q.parts := Multiset.sort_eq _ _
  have hlen : (partsAsc q).length = Multiset.card q.parts := Multiset.length_sort _
  have hne : partsAsc q ≠ [] := by
    intro h0
    have h1 : q.parts = 0 := by rw [← hcoe, h0]; rfl
    have h2 := q.parts_sum
    rw [h1, Multiset.sum_zero] at h2
    omega
  match p, hpos, hpw, hfs with
  | [], _, _, hfs => exact absurd hfs.symm hne
  | [_], _, _, hfs => exact absurd hfs.symm hne
  | a :: b :: rest, hpos, hpw, hfs =>
    have hfs' : (a + b) :: List.zipWith (· + ·) (b :: rest) rest = partsAsc q := hfs
    have hpa : ∀ u ∈ b :: rest, u ≤ a := fun u hu => (List.pairwise_cons.mp hpw).1 u hu
    have hpb : ∀ v ∈ rest, v ≤ b := fun v hv =>
      (List.pairwise_cons.mp (List.pairwise_cons.mp hpw).2).1 v hv
    have hall : ∀ y ∈ partsAsc q, y = a + b := by
      intro y hy
      have h1 : y ≤ a + b := by
        rw [← hfs] at hy
        refine zip_le391629 a b (a :: b :: rest) (b :: rest) (fun u hu => ?_) (fun v hv => ?_) y hy
        · rcases List.mem_cons.mp hu with rfl | hu
          · exact le_rfl
          · exact hpa u hu
        · rcases List.mem_cons.mp hv with rfl | hv
          · exact le_rfl
          · exact hpb v hv
      have h2 : a + b ≤ y := by
        rw [← hfs'] at hy hsorted
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact le_rfl
        · exact (List.pairwise_cons.mp hsorted).1 y hy'
      omega
    have hLrep : partsAsc q = List.replicate (partsAsc q).length (a + b) :=
      List.eq_replicate_iff.mpr ⟨rfl, hall⟩
    have hk : (partsAsc q).length = rest.length + 1 := by
      rw [← hfs', List.length_cons, List.length_zipWith, List.length_cons]
      omega
    generalize hkg : (partsAsc q).length = k at hk hLrep hlen
    have hparts : q.parts = Multiset.replicate k (a + b) := by
      rw [← hcoe, ← Multiset.coe_replicate]
      exact congrArg (fun l : List ℕ => (l : Multiset ℕ)) hLrep
    have hn' : k * (a + b) = n := by
      rw [← q.parts_sum, hparts, Multiset.sum_replicate, smul_eq_mul]
    have hdiv : n / k = a + b := by
      rw [← hn', Nat.mul_div_cancel_left _ (by omega)]
    rw [← hlen, hdiv]
    refine ⟨memS_of391629 hn (Dvd.intro _ hn') ?_, hparts⟩
    rw [hdiv]
    have ha : 0 < a := hpos a (by simp)
    have hb : 0 < b := hpos b (by simp)
    match rest, hk, hpb, hfs' with
    | [], hk, _, _ =>
      left
      simp only [List.length_nil, zero_add] at hk
      subst hk
      refine ⟨rfl, ?_⟩
      omega
    | d :: rest', hk, hpb, hfs' =>
      right
      have hmem : b + d ∈ partsAsc q := by
        rw [← hfs']
        simp
      have h1 := hall _ hmem
      have h2 : b ≤ a := hpa b (by simp)
      have h3 : d ≤ b := hpb d (by simp)
      simp only [List.length_cons] at hk
      exact ⟨by omega, ⟨b, by omega⟩⟩

theorem backward391629 {n : ℕ} (hn : 1 ≤ n) (q : Nat.Partition n) (k : ℕ)
    (hk : k ∈ S391629 n) (hq : q.parts = Multiset.replicate k (n / k)) :
    IsFirstSumsOfPartition q := by
  obtain ⟨hkn, hcase⟩ := of_memS391629 hk
  have hL : partsAsc q = List.replicate k (n / k) := by
    unfold partsAsc
    rw [hq]
    exact sort_replicate391629 k (n / k)
  rcases hcase with ⟨rfl, h2⟩ | ⟨hk2, e, he⟩
  · refine ⟨[n - 1, 1], ?_, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      omega
    · refine List.Pairwise.cons (fun a' ha' => ?_) (List.pairwise_singleton _ _)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
      show n - 1 ≥ a'
      omega
    · rw [hL]
      simp only [firstSums, List.tail_cons, List.zipWith_cons_cons, List.zipWith_nil_right,
        Nat.div_one, List.replicate_one]
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
  · have hpos : 0 < n / k := Nat.div_pos (Nat.le_of_dvd hn hkn) (by omega)
    refine ⟨List.replicate (k + 1) e, ?_, ?_, ?_⟩
    · intro x hx
      rw [List.eq_of_mem_replicate hx]
      omega
    · rw [List.pairwise_replicate]
      right
      exact le_refl e
    · rw [hL, he]
      unfold firstSums
      rw [List.tail_replicate, List.zipWith_replicate]
      congr 1 <;> omega

theorem card_first391629 {n : ℕ} (hn : 1 ≤ n)
    [DecidablePred (fun q : Nat.Partition n => IsFirstSumsOfPartition q)] :
    (Finset.univ.filter (fun q : Nat.Partition n => IsFirstSumsOfPartition q)).card =
      (S391629 n).card := by
  refine Finset.card_bij' (fun q _ => Multiset.card q.parts)
    (fun k hk => mkPart391629 n k (of_memS391629 hk).1 (by omega)) ?_ ?_ ?_ ?_
  · intro q hq
    exact (forward391629 hn q (Finset.mem_filter.mp hq).2).1
  · intro k hk
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, backward391629 hn _ k hk rfl⟩
  · intro q hq
    apply Nat.Partition.ext
    exact (forward391629 hn q (Finset.mem_filter.mp hq).2).2.symm
  · intro k hk
    show Multiset.card (Multiset.replicate k (n / k)) = k
    exact Multiset.card_replicate _ _

theorem main391629 (n : ℕ) (hn : 1 ≤ n) : a n = A000041 n - A368684 n := by
  classical
  have h1 : (Finset.univ.filter (fun q : Nat.Partition n => IsFirstSumsOfPartition q)).card +
      a n = Fintype.card (Nat.Partition n) := by
    unfold a
    rw [← Finset.card_univ]
    convert Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun q : Nat.Partition n => IsFirstSumsOfPartition q)
  have h2 := card_first391629 hn (n := n)
  have h3 : A368684 n = (S391629 n).card := rfl
  unfold A000041
  omega

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a391629.main :=
  fun n hn => OMA.Helpers.main391629 n hn
