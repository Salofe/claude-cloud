import OMAReductions.R_Erdos695_erdos_695_variants_upperBound_R1

/-!
# Step H1 of the reduction Erdos695.erdos_695.variants.upperBound.R1

A compactness (König) argument. In the product space of sequences of naturals (each coordinate
discrete), the sequences bounded by `cap` form a compact set by Tychonoff. For each `N`, the
bounded sequences whose first `N + 1` terms form a valid prime chain form a closed, nonempty set
(truncate a given prefix by zeros), and these sets decrease in `N`. Their intersection is
nonempty, and any point in it is the required infinite chain.
-/

namespace OMA.Helpers

theorem erdos695_isClosed_coord (P : ℕ → Prop) (k : ℕ) :
    IsClosed {q : ℕ → ℕ | P (q k)} :=
  IsClosed.preimage (continuous_apply k) (isClosed_discrete {n : ℕ | P n})

theorem erdos695_isClosed_pair (R : ℕ → ℕ → Prop) (k : ℕ) :
    IsClosed {q : ℕ → ℕ | R (q k) (q (k + 1))} := by
  have hc : Continuous (fun q : ℕ → ℕ => (q k, q (k + 1))) :=
    (continuous_apply k).prodMk (continuous_apply (k + 1))
  exact IsClosed.preimage hc (isClosed_discrete {x : ℕ × ℕ | R x.1 x.2})

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos695_erdos_695_variants_upperBound_R1.H1 := by
  intro cap hpre
  let B : Set (ℕ → ℕ) := Set.pi Set.univ (fun k => Set.Iic (cap k))
  let t : ℕ → Set (ℕ → ℕ) := fun N =>
    B ∩ ({q | ∀ k ≤ N, (q k).Prime} ∩
      {q | ∀ k < N, q k < q (k + 1) ∧ q (k + 1) % q k = 1})
  have hBc : IsCompact B := isCompact_univ_pi (fun k => (Set.finite_Iic (cap k)).isCompact)
  have hBcl : IsClosed B := isClosed_set_pi (fun k _ => isClosed_discrete _)
  have hcl : ∀ N, IsClosed (t N) := by
    intro N
    refine hBcl.inter (IsClosed.inter ?_ ?_)
    · have : {q : ℕ → ℕ | ∀ k ≤ N, (q k).Prime} =
          ⋂ k, ⋂ (_ : k ≤ N), {q : ℕ → ℕ | (q k).Prime} := by
        ext q; simp
      rw [this]
      exact isClosed_iInter (fun k => isClosed_iInter
        (fun _ => OMA.Helpers.erdos695_isClosed_coord (fun n => n.Prime) k))
    · have : {q : ℕ → ℕ | ∀ k < N, q k < q (k + 1) ∧ q (k + 1) % q k = 1} =
          ⋂ k, ⋂ (_ : k < N), {q : ℕ → ℕ | q k < q (k + 1) ∧ q (k + 1) % q k = 1} := by
        ext q; simp
      rw [this]
      exact isClosed_iInter (fun k => isClosed_iInter
        (fun _ => OMA.Helpers.erdos695_isClosed_pair (fun x y => x < y ∧ y % x = 1) k))
  have hsub : ∀ N, t (N + 1) ⊆ t N := by
    intro N q hq
    refine ⟨hq.1, fun k hk => hq.2.1 k (by omega), fun k hk => hq.2.2 k (by omega)⟩
  have hne : ∀ N, (t N).Nonempty := by
    intro N
    obtain ⟨q, hq, hs⟩ := hpre N
    refine ⟨fun k => if k ≤ N then q k else 0, ?_, ?_, ?_⟩
    · intro k _
      change (if k ≤ N then q k else 0) ≤ cap k
      split_ifs with h
      · exact (hq k h).2
      · exact Nat.zero_le _
    · intro k hk
      change (if k ≤ N then q k else 0).Prime
      rw [if_pos hk]
      exact (hq k hk).1
    · intro k hk
      change (if k ≤ N then q k else 0) < (if k + 1 ≤ N then q (k + 1) else 0) ∧
        (if k + 1 ≤ N then q (k + 1) else 0) % (if k ≤ N then q k else 0) = 1
      rw [if_pos (by omega), if_pos (by omega)]
      exact hs k hk
  have ht0 : IsCompact (t 0) := hBc.of_isClosed_subset (hcl 0) Set.inter_subset_left
  obtain ⟨q, hq⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t hsub hne ht0 hcl
  rw [Set.mem_iInter] at hq
  refine ⟨q, strictMono_nat_of_lt_succ (fun k => ((hq (k + 1)).2.2 k (by omega)).1),
    fun k => (hq k).2.1 k le_rfl, fun k => ((hq (k + 1)).2.2 k (by omega)).2,
    fun k => (hq 0).1 k (Set.mem_univ k)⟩
