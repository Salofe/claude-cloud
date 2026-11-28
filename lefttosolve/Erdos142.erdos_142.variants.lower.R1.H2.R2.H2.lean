import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R2

/-! Step H2 of reduction Erdos142.erdos_142.variants.lower.R1.H2.R2: a covering lemma.
Choose q shifts in [0, 2N) independently and uniformly. A fixed target x + N is missed by
one shift with probability 1 - |S| / 2N, so the expected number of uncovered targets is at
most N (1 - |S| / 2N)^q < N exp(-q |S| / 2N) < 1. We run this as a counting argument on
the finite set of shift tuples. -/

namespace OMA.Helpers

open Finset

/-- The union bound: N bad events, each of probability (1 - s / 2N)^q, cover less than everything. -/
theorem count_bound (N q s : ℕ) (hN : 0 < N) (hsN : s ≤ N)
    (h : 2 * (N : ℝ) * Real.log (N : ℝ) < (q : ℝ) * (s : ℝ)) :
    N * (2 * N - s) ^ q < (2 * N) ^ q := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsr : (s : ℝ) ≤ N := by exact_mod_cast hsN
  have hMpos : (0 : ℝ) < 2 * N := by positivity
  set a : ℝ := (s : ℝ) / (2 * N) with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one hMpos]
    linarith
  have hcast : (((2 * N - s : ℕ)) : ℝ) = (2 * N) * (1 - a) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rw [ha]
    field_simp
  have hexp : (1 - a) ^ q ≤ Real.exp (-(q * a)) := by
    calc (1 - a) ^ q ≤ Real.exp (-a) ^ q := by
          apply pow_le_pow_left₀ (by linarith)
          linarith [Real.add_one_le_exp (-a)]
      _ = Real.exp (-(q * a)) := by
          rw [← Real.exp_nat_mul]
          ring_nf
  have hlog : Real.log N < q * a := by
    rw [ha, mul_div_assoc', lt_div_iff₀ hMpos]
    linarith
  have hlt : Real.exp (-(q * a)) < 1 / N := by
    have h1 : Real.exp (-(q * a)) < Real.exp (-Real.log N) :=
      Real.exp_lt_exp.mpr (by linarith)
    have h2 : Real.exp (-Real.log N) = 1 / N := by
      rw [Real.exp_neg, Real.exp_log hNr, one_div]
    rwa [h2] at h1
  have hkey : (N : ℝ) * (1 - a) ^ q < 1 := by
    calc (N : ℝ) * (1 - a) ^ q ≤ N * Real.exp (-(q * a)) :=
          mul_le_mul_of_nonneg_left hexp hNr.le
      _ < N * (1 / N) := mul_lt_mul_of_pos_left hlt hNr
      _ = 1 := by field_simp
  have hreal : ((N * (2 * N - s) ^ q : ℕ) : ℝ) < (((2 * N) ^ q : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow, hcast, mul_pow, Nat.cast_pow]
    have hpow : (0 : ℝ) < (2 * N) ^ q := by positivity
    have e2 : (((2 * N : ℕ)) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
    rw [e2]
    calc (N : ℝ) * ((2 * N) ^ q * (1 - a) ^ q) = (2 * N) ^ q * ((N : ℝ) * (1 - a) ^ q) := by ring
      _ < (2 * N) ^ q * 1 := mul_lt_mul_of_pos_left hkey hpow
      _ = (2 * N) ^ q := mul_one _
  exact_mod_cast hreal

theorem cover (N q : ℕ) (S : Finset ℕ) (hN : 0 < N) (hS : S ⊆ Icc 1 N)
    (h : 2 * (N : ℝ) * Real.log (N : ℝ) < (q : ℝ) * (S.card : ℝ)) :
    ∃ shifts : Fin q → ℕ, ∀ x ∈ Icc 1 N, ∃ t : Fin q, ∃ b ∈ S, x + N = shifts t + b := by
  have hsN : S.card ≤ N := by
    have := card_le_card hS
    simpa using this
  let A : ℕ → Finset (Fin (2 * N)) := fun x =>
    univ.filter (fun r : Fin (2 * N) => ∀ b ∈ S, r.val + b ≠ x + N)
  have hA : ∀ x ∈ Icc 1 N, (A x).card ≤ 2 * N - S.card := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_Icc.mp hx
    let C := univ.filter (fun r : Fin (2 * N) => ¬ ∀ b ∈ S, r.val + b ≠ x + N)
    have hC : S.card ≤ C.card := by
      apply card_le_card_of_injOn
        (fun b => (⟨(x + N - b) % (2 * N), Nat.mod_lt _ (by omega)⟩ : Fin (2 * N)))
      · intro b hb
        rw [mem_coe] at hb
        have hb' := mem_Icc.mp (hS hb)
        rw [mem_coe, mem_filter]
        refine ⟨mem_univ _, ?_⟩
        intro hall
        apply hall b hb
        simp only
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      · intro b hb b' hb' heq
        rw [mem_coe] at hb hb'
        have h1 := mem_Icc.mp (hS hb)
        have h2 := mem_Icc.mp (hS hb')
        have hv := congrArg Fin.val heq
        simp only at hv
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
        omega
    have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * N))))
      (fun r : Fin (2 * N) => ∀ b ∈ S, r.val + b ≠ x + N)
    rw [card_univ, Fintype.card_fin] at hsum
    change (A x).card + C.card = 2 * N at hsum
    omega
  let Bad : ℕ → Finset (Fin q → Fin (2 * N)) := fun x => Fintype.piFinset (fun _ => A x)
  let U := (Icc 1 N).biUnion Bad
  have hU : U.card < (univ : Finset (Fin q → Fin (2 * N))).card := by
    calc U.card ≤ ∑ x ∈ Icc 1 N, (Bad x).card := card_biUnion_le
      _ ≤ ∑ x ∈ Icc 1 N, (2 * N - S.card) ^ q := by
          apply sum_le_sum
          intro x hx
          change (Fintype.piFinset fun _ : Fin q => A x).card ≤ _
          rw [Fintype.card_piFinset_const]
          exact Nat.pow_le_pow_left (hA x hx) q
      _ = N * (2 * N - S.card) ^ q := by
          rw [sum_const, Nat.card_Icc, smul_eq_mul]
          simp
      _ < (2 * N) ^ q := count_bound N q S.card hN hsN h
      _ = (univ : Finset (Fin q → Fin (2 * N))).card := by
          rw [card_univ]
          simp
  obtain ⟨f, -, hf⟩ := exists_mem_notMem_of_card_lt_card hU
  refine ⟨fun t => (f t).val, ?_⟩
  intro x hx
  have hnot : f ∉ Bad x := fun hmem => hf (mem_biUnion.mpr ⟨x, hx, hmem⟩)
  rw [Fintype.mem_piFinset] at hnot
  push Not at hnot
  obtain ⟨t, ht⟩ := hnot
  simp only [A, mem_filter, mem_univ, true_and, not_forall, not_not] at ht
  obtain ⟨b, hb, hbeq⟩ := ht
  exact ⟨t, b, hb, hbeq.symm⟩

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2.H2 := by
  intro N q S hN _ hS h
  exact OMA.Helpers.cover N q S hN hS h
