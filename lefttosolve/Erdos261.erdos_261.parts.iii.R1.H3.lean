import OMAReductions.R_Erdos261_erdos_261_parts_iii_R1

/-!
# Step H3 of the reduction Erdos261.erdos_261.parts.iii.R1

An injective family, indexed by binary sequences, of infinite sets `A` of positive integers with
`HasSum (A.indicator (a / 2^a)) 1` in the reals yields continuum many representations of `1`
in the sense of `Erdos261.Erdos261InfiniteRepresentation`.

Each set is enumerated increasingly by `Nat.nth`, which is strictly monotone with range `A`.
Reindexing along this injection turns the real sum into a sum over the enumeration, and the sum
transfers to the rationals because the cast from the rationals to the reals is inducing. The set
is recovered as the range of its enumeration, so the map from binary sequences is injective.
-/

open scoped Cardinal

namespace OMA.Helpers

/-- The increasing enumeration of an infinite set of positive integers whose weighted sum is `1`
is a representation of `1`. -/
theorem erdos261_rep_of_set (A : Set ℕ) (hinf : A.Infinite) (hpos : ∀ a ∈ A, 1 ≤ a)
    (hs : HasSum (A.indicator (fun a : ℕ => (a : ℝ) / 2 ^ a)) 1) :
    Erdos261.Erdos261InfiniteRepresentation 1 (Nat.nth (· ∈ A)) := by
  have hinf' : (Set.ofPred (· ∈ A)).Infinite := hinf
  have hmono := Nat.nth_strictMono hinf'
  have hrange : Set.range (Nat.nth (· ∈ A)) = A := Nat.range_nth_of_infinite hinf'
  have hmem : ∀ n, Nat.nth (· ∈ A) n ∈ A := Nat.nth_mem_of_infinite hinf'
  have hR : HasSum (fun k => ((Nat.nth (· ∈ A) k : ℕ) : ℝ) / 2 ^ (Nat.nth (· ∈ A) k)) 1 := by
    have h1 := (hmono.injective.hasSum_iff (f := A.indicator (fun a : ℕ => (a : ℝ) / 2 ^ a))
      (a := 1) (fun x hx => by
        rw [hrange] at hx
        exact Set.indicator_of_notMem hx _)).2 hs
    refine h1.congr_fun ?_
    intro k
    simp [Function.comp, Set.indicator_of_mem (hmem k)]
  have hQ : HasSum (fun k => ((Nat.nth (· ∈ A) k : ℕ) : ℚ) / 2 ^ (Nat.nth (· ∈ A) k)) 1 := by
    have hind : Topology.IsInducing (Rat.castHom ℝ) :=
      Rat.isUniformEmbedding_coe_real.isUniformInducing.isInducing
    rw [← hind.hasSum_iff]
    convert hR using 1
    · funext k; simp
    · simp
  exact ⟨hmono, fun n => hpos _ (hmem n), hQ.summable, hQ.tsum_eq.symm⟩

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos261_erdos_261_parts_iii_R1.H3 := by
  rintro ⟨A, hAinj, hA⟩
  classical
  let F : (ℕ → Bool) → {a : ℕ → ℕ | Erdos261.Erdos261InfiniteRepresentation 1 a} :=
    fun b => ⟨Nat.nth (· ∈ A b), OMA.Helpers.erdos261_rep_of_set (A b) (hA b).1 (hA b).2.1
      (hA b).2.2⟩
  have hF : Function.Injective F := by
    intro b c hbc
    apply hAinj
    have h := congrArg Subtype.val hbc
    simp only [F] at h
    have hb : Set.range (Nat.nth (· ∈ A b)) = A b :=
      Nat.range_nth_of_infinite (p := (· ∈ A b)) (hA b).1
    have hc : Set.range (Nat.nth (· ∈ A c)) = A c :=
      Nat.range_nth_of_infinite (p := (· ∈ A c)) (hA c).1
    rw [← hb, ← hc, h]
  have hle := Cardinal.mk_le_of_injective hF
  have hc : #(ℕ → Bool) = 𝔠 := by
    rw [Cardinal.mk_arrow]; simp
  rw [hc] at hle
  exact hle
