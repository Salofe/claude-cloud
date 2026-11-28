import OMAStatements.S_mo_66493
import Mathlib

/-! Proof for mo-66493: twisted Vandermonde determinants over finite fields. -/

namespace OMA.Helpers

open Polynomial

theorem mo66493_hadamard_example :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, 0 < A.det ∧ 0 < B.det ∧ (A.hadamard B).det = 0 := by
  refine ⟨!![1, 1; -1, 1], !![1, 1; -1, 1], ?_, ?_, ?_⟩ <;>
    simp [Matrix.det_fin_two, Matrix.hadamard]

theorem mo66493_repeated {F : Type} [Field F] (n : ℕ) (d : Fin n → ℕ)
    (hd : ¬ Function.Injective d) (K : Type) [Field K] [Algebra F K] (x : Fin n → K) :
    (OMA.S_mo_66493.twisted d (fun _ _ => (1:F)) x).det = 0 := by
  unfold Function.Injective at hd
  push_neg at hd
  obtain ⟨i, j, hij, hne⟩ := hd
  apply Matrix.det_zero_of_row_eq hne
  funext k
  simp [OMA.S_mo_66493.twisted, hij]

/-- Strict rearrangement inequality for a permutation of distinct naturals. -/
theorem mo66493_rearr_le {n : ℕ} (d : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    ∑ i, d i * d (σ i) ≤ ∑ i, d i ^ 2 := by
  have h1 : ∑ i, 2 * (d i * d (σ i)) ≤ ∑ i, (d i ^ 2 + d (σ i) ^ 2) := by
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg ((d i : ℤ) - d (σ i))]
  have h2 : ∑ i, (d i ^ 2 + d (σ i) ^ 2) = 2 * ∑ i, d i ^ 2 := by
    rw [Finset.sum_add_distrib, Equiv.sum_comp σ (fun i => d i ^ 2)]
    ring
  rw [← Finset.mul_sum, h2] at h1
  omega

theorem mo66493_rearr_lt {n : ℕ} (d : Fin n → ℕ) (hd : Function.Injective d)
    (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) :
    ∑ i, d i * d (σ i) < ∑ i, d i ^ 2 := by
  have hex : ∃ i, σ i ≠ i := by
    by_contra h
    push_neg at h
    exact hσ (Equiv.ext h)
  obtain ⟨i0, hi0⟩ := hex
  have h1 : ∑ i, 2 * (d i * d (σ i)) < ∑ i, (d i ^ 2 + d (σ i) ^ 2) := by
    apply Finset.sum_lt_sum
    · intro i _
      nlinarith [sq_nonneg ((d i : ℤ) - d (σ i))]
    · refine ⟨i0, Finset.mem_univ _, ?_⟩
      have hne : (d i0 : ℤ) ≠ d (σ i0) := by
        intro h
        exact hi0 (hd (by exact_mod_cast h.symm))
      have hpos : (0 : ℤ) < ((d i0 : ℤ) - d (σ i0)) ^ 2 := by
        have : (d i0 : ℤ) - d (σ i0) ≠ 0 := sub_ne_zero.mpr hne
        positivity
      have : ((2 * (d i0 * d (σ i0)) : ℕ) : ℤ) < ((d i0 ^ 2 + d (σ i0) ^ 2 : ℕ) : ℤ) := by
        push_cast
        nlinarith
      exact_mod_cast this
  have h2 : ∑ i, (d i ^ 2 + d (σ i) ^ 2) = 2 * ∑ i, d i ^ 2 := by
    rw [Finset.sum_add_distrib, Equiv.sum_comp σ (fun i => d i ^ 2)]
    ring
  rw [← Finset.mul_sum, h2] at h1
  omega

/-- The determinant polynomial. -/
noncomputable def mo66493_detPoly {F : Type} [Field F] {n : ℕ} (d : Fin n → ℕ)
    (R : Matrix (Fin n) (Fin n) F) : F[X] :=
  (Matrix.of fun i j => C (R i j) * X ^ (d j * d i)).det

theorem mo66493_detPoly_eq {F : Type} [Field F] {n : ℕ} (d : Fin n → ℕ)
    (R : Matrix (Fin n) (Fin n) F) :
    mo66493_detPoly d R = ∑ σ : Equiv.Perm (Fin n),
      C (((Equiv.Perm.sign σ : ℤ) : F) * ∏ i, R (σ i) i) * X ^ (∑ i, d i * d (σ i)) := by
  unfold mo66493_detPoly
  rw [Matrix.det_apply']
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  simp only [Matrix.of_apply]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_mul, ← map_prod]
  simp only [map_intCast]
  ring

theorem mo66493_detPoly_natDegree {F : Type} [Field F] {n : ℕ} (d : Fin n → ℕ)
    (R : Matrix (Fin n) (Fin n) F) :
    (mo66493_detPoly d R).natDegree ≤ ∑ i, d i ^ 2 := by
  rw [mo66493_detPoly_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  exact (natDegree_C_mul_X_pow_le _ _).trans (mo66493_rearr_le d σ)

theorem mo66493_detPoly_coeff {F : Type} [Field F] {n : ℕ} (d : Fin n → ℕ)
    (hd : Function.Injective d) (R : Matrix (Fin n) (Fin n) F) :
    (mo66493_detPoly d R).coeff (∑ i, d i ^ 2) = ∏ i, R i i := by
  rw [mo66493_detPoly_eq, Polynomial.finsetSum_coeff, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · rw [coeff_C_mul_X_pow]
    simp [sq]
  · intro σ _ hσ
    rw [coeff_C_mul_X_pow, if_neg]
    exact (ne_of_lt (mo66493_rearr_lt d hd σ hσ)).symm
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mo66493_detPoly_ne_zero {F : Type} [Field F] {n : ℕ} (d : Fin n → ℕ)
    (hd : Function.Injective d) (R : Matrix (Fin n) (Fin n) F) (hR : ∀ i j, R i j ≠ 0) :
    mo66493_detPoly d R ≠ 0 := by
  intro h
  have := mo66493_detPoly_coeff d hd R
  rw [h, coeff_zero] at this
  exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hR i i)) this.symm

theorem mo66493_twisted_det {F K : Type} [Field F] [Field K] [Algebra F K] {n : ℕ}
    (d : Fin n → ℕ) (R : Matrix (Fin n) (Fin n) F) (t : K) :
    (OMA.S_mo_66493.twisted d R (fun j => t ^ (d j))).det = aeval t (mo66493_detPoly d R) := by
  unfold mo66493_detPoly
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp [OMA.S_mo_66493.twisted, AlgHom.mapMatrix_apply, Matrix.map_apply, ← pow_mul]

theorem mo66493_exists_avoiding (F : Type) [Field F] [Fintype F] (D : ℕ) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : Algebra F K) (t : K),
      ∀ p : F[X], p ≠ 0 → p.natDegree ≤ D → aeval t p ≠ 0 := by
  classical
  set q := Fintype.card F with hq
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  set N := 2 * D + 1 with hN
  have hqN : 1 < q ^ N := Nat.one_lt_pow (by omega) (by omega)
  set f : F[X] := X ^ (q ^ N) - X with hf
  let _ : Fintype (SplittingField f) := Fintype.ofFinite _
  have hf_deg : f.natDegree = q ^ N := FiniteField.X_pow_card_sub_X_natDegree_eq F hqN
  have hsplit := SplittingField.splits f
  have hroots_card : (f.map (algebraMap F (SplittingField f))).roots.card = q ^ N := by
    rw [splits_iff_card_roots.mp hsplit, natDegree_map, hf_deg]
  have hsep : (f.map (algebraMap F (SplittingField f))).Separable := by
    have : CharP F (ringChar F) := ringChar.charP F
    have hdvd : ringChar F ∣ q ^ N :=
      dvd_pow ((CharP.cast_eq_zero_iff F (ringChar F) q).mp (FiniteField.cast_card_eq_zero F))
        (by omega)
    exact (galois_poly_separable (ringChar F) (q ^ N) hdvd).map
  have hnodup := nodup_roots hsep
  have hcardK : q ^ N ≤ Fintype.card (SplittingField f) := by
    rw [← hroots_card, ← Multiset.toFinset_card_of_nodup hnodup]
    exact Finset.card_le_univ _
  set Pset : Finset F[X] :=
    Finset.univ.image (fun c : Fin (D + 1) → F => ∑ i, C (c i) * X ^ (i : ℕ)) with hPset
  set Bad : Finset (SplittingField f) :=
    Pset.biUnion (fun g => (g.map (algebraMap F (SplittingField f))).roots.toFinset) with hBad
  have hPcard : Pset.card ≤ q ^ (D + 1) := by
    refine Finset.card_image_le.trans ?_
    simp [hq]
  have hDq : D < q ^ D := Nat.lt_pow_self (by omega)
  have hBadc : Bad.card < (Finset.univ : Finset (SplittingField f)).card := by
    calc Bad.card ≤ ∑ g ∈ Pset, ((g.map (algebraMap F (SplittingField f))).roots.toFinset).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ g ∈ Pset, D := by
          apply Finset.sum_le_sum
          intro g hg
          obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hg
          refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans
            (natDegree_map_le.trans ?_))
          exact natDegree_sum_le_of_forall_le _ _ (fun i _ =>
            (natDegree_C_mul_X_pow_le _ _).trans (by omega))
      _ = Pset.card * D := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ q ^ (D + 1) * D := Nat.mul_le_mul_right _ hPcard
      _ < q ^ (D + 1) * q ^ D := Nat.mul_lt_mul_of_pos_left hDq (by positivity)
      _ = q ^ N := by rw [← pow_add, hN]; ring_nf
      _ ≤ Fintype.card (SplittingField f) := hcardK
      _ = (Finset.univ : Finset (SplittingField f)).card := Finset.card_univ.symm
  obtain ⟨t, -, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hBadc
  refine ⟨SplittingField f, inferInstance, inferInstance, inferInstance, t, ?_⟩
  intro p hp0 hpD hroot
  apply ht
  have hpP : p ∈ Pset := by
    apply Finset.mem_image.mpr
    refine ⟨fun i => p.coeff i, Finset.mem_univ _, ?_⟩
    show ∑ i : Fin (D + 1), C (p.coeff i) * X ^ (i : ℕ) = p
    rw [Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i) (D + 1)]
    exact (p.as_sum_range_C_mul_X_pow' (by omega)).symm
  refine Finset.mem_biUnion.mpr ⟨p, hpP, ?_⟩
  rw [Multiset.mem_toFinset, mem_roots (Polynomial.map_ne_zero hp0), IsRoot, eval_map,
    ← aeval_def]
  exact hroot

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_mo_66493.main := by
  refine ⟨OMA.Helpers.mo66493_hadamard_example, ?_⟩
  intro F _ _ n d
  refine ⟨fun hd => ?_, fun hd K _ _ x => OMA.Helpers.mo66493_repeated n d hd K x⟩
  obtain ⟨K, hK, hKf, hA, t, ht⟩ := OMA.Helpers.mo66493_exists_avoiding F (∑ i, d i ^ 2)
  exact ⟨K, hK, hKf, hA, t, ht, fun R hR => by
    rw [OMA.Helpers.mo66493_twisted_det]
    exact ht _ (OMA.Helpers.mo66493_detPoly_ne_zero d hd R hR)
      (OMA.Helpers.mo66493_detPoly_natDegree d R)⟩
