import OMAStatements.S_mo_262336

/-!
Proof of the expansion of the permanent of M + a J (MathOverflow 262336).

Expanding each factor M i (s i) + a over the subsets S of rows gives
perm (M + a J) = Sum_S a^(n - |S|) Sum_s Prod_(i in S) M i (s i). The inner sum depends on s only
through its restriction to S, an embedding of S; every embedding is the restriction of some
permutation (extendSubtype), left multiplication shows that all fibres have the same size, and
counting permutations (n! = (n - |S|)! * descFactorial) gives the fibre size (n - |S|)!.
For the second part, the zero matrix and the matrix with a single entry 1 both have permanent 0,
while after the shift their permanents are 2a^2 and 2a^2 + a.
-/

namespace OMA.Helpers

open OMA.S_mo_262336

/-- The rows in `t` of a permutation, as an embedding of `t`. -/
def mo262336Res {n : ℕ} (t : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) : t ↪ Fin n :=
  ⟨fun i => σ i.1, fun _ _ h => Subtype.ext (σ.injective h)⟩

theorem mo262336_res_apply {n : ℕ} (t : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (i : t) :
    mo262336Res t σ i = σ i.1 := rfl

theorem mo262336_res_surj {n : ℕ} (t : Finset (Fin n)) (e : t ↪ Fin n) :
    ∃ π : Equiv.Perm (Fin n), mo262336Res t π = e := by
  classical
  refine ⟨Equiv.extendSubtype (p := fun x => x ∈ t) (q := fun y => y ∈ Set.range e)
    e.toEquivRange, ?_⟩
  ext i
  rw [mo262336_res_apply, Equiv.extendSubtype_apply_of_mem _ _ i.2,
    Function.Embedding.toEquivRange_apply]

theorem mo262336_fibre_card {n : ℕ} (t : Finset (Fin n)) [DecidableEq (t ↪ Fin n)]
    (e : t ↪ Fin n) :
    Fintype.card {σ // mo262336Res t σ = e} =
      Fintype.card {σ // mo262336Res t σ = mo262336Res t 1} := by
  obtain ⟨π, hπ⟩ := mo262336_res_surj t e
  have fwd : ∀ σ : Equiv.Perm (Fin n), mo262336Res t σ = e →
      mo262336Res t (π⁻¹ * σ) = mo262336Res t 1 := by
    intro σ h
    ext i
    have hi : σ i.1 = π i.1 := by
      rw [← mo262336_res_apply, ← mo262336_res_apply t π, h, hπ]
    rw [mo262336_res_apply, mo262336_res_apply, Equiv.Perm.mul_apply, hi]
    simp
  have bwd : ∀ τ : Equiv.Perm (Fin n), mo262336Res t τ = mo262336Res t 1 →
      mo262336Res t (π * τ) = e := by
    intro τ h
    ext i
    have hi : τ i.1 = i.1 := by
      rw [← mo262336_res_apply, h, mo262336_res_apply]
      rfl
    rw [← hπ, mo262336_res_apply, mo262336_res_apply, Equiv.Perm.mul_apply, hi]
  exact Fintype.card_congr
    { toFun := fun σ => ⟨π⁻¹ * σ.1, fwd σ.1 σ.2⟩
      invFun := fun τ => ⟨π * τ.1, bwd τ.1 τ.2⟩
      left_inv := fun σ => by
        apply Subtype.ext
        simp
      right_inv := fun τ => by
        apply Subtype.ext
        simp }

theorem mo262336_fibre_card' {n : ℕ} (t : Finset (Fin n)) [DecidableEq (t ↪ Fin n)]
    (e : t ↪ Fin n) :
    Fintype.card {σ // mo262336Res t σ = e} = (n - t.card).factorial := by
  rw [mo262336_fibre_card]
  set c := Fintype.card {σ // mo262336Res t σ = mo262336Res t 1}
  have hsum := Fintype.sum_fiberwise' (mo262336Res t) (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
  have hc : ∀ e' : t ↪ Fin n, Fintype.card {σ // mo262336Res t σ = e'} = c :=
    fun e' => mo262336_fibre_card t e'
  simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_perm,
    Fintype.card_fin] at hsum
  rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe] at hsum
  have hk : t.card ≤ n := by
    simpa using Finset.card_le_univ t
  have hfac := Nat.factorial_mul_descFactorial hk
  have hpos : n.descFactorial t.card ≠ 0 := by
    rw [Ne, Nat.descFactorial_eq_zero_iff_lt]
    omega
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos)
  rw [hsum, mul_comm, hfac]

theorem mo262336_inner {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (t : Finset (Fin n)) :
    ∑ σ : Equiv.Perm (Fin n), ∏ i ∈ t, M i (σ i) =
      ((n - t.card).factorial : R) * minors M t := by
  classical
  unfold minors
  have h1 : ∀ σ : Equiv.Perm (Fin n), ∏ i ∈ t, M i (σ i) =
      (fun e : t ↪ Fin n => ∏ i : t, M i (e i)) (mo262336Res t σ) := by
    intro σ
    simp only [mo262336_res_apply]
    exact (Finset.prod_coe_sort t (fun i => M i (σ i))).symm
  simp only [h1]
  rw [← Fintype.sum_fiberwise' (mo262336Res t) (fun e : t ↪ Fin n => ∏ i : t, M i (e i))]
  simp only [Finset.sum_const, Finset.card_univ, mo262336_fibre_card', nsmul_eq_mul,
    Finset.mul_sum]

theorem mo262336_part1 (R : Type) [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (a : ℤ) :
    perm (fun i j => M i j + (a : R)) = ∑ S : Finset (Fin n),
      ((n - S.card).factorial : R) * (a : R) ^ (n - S.card) * minors M S := by
  classical
  unfold perm
  have h1 : ∀ σ : Equiv.Perm (Fin n), ∏ i, (M i (σ i) + (a : R)) =
      ∑ S : Finset (Fin n), (∏ i ∈ S, M i (σ i)) * (a : R) ^ (n - S.card) := by
    intro σ
    rw [Finset.prod_add, Finset.powerset_univ]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [Finset.prod_const, ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [← Finset.sum_mul, mo262336_inner]
  ring

theorem mo262336_sum_perm2 (f : Equiv.Perm (Fin 2) → ℤ) :
    ∑ σ, f σ = f 1 + f (Equiv.swap 0 1) := by
  rw [show (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} by decide]
  rw [Finset.sum_pair (by decide)]

theorem mo262336_part2 (a : ℤ) (ha : a ≠ 0) : ∃ M N : Matrix (Fin 2) (Fin 2) ℤ,
    perm M = perm N ∧ perm (fun i j => M i j + a) ≠ perm (fun i j => N i j + a) := by
  refine ⟨fun _ _ => 0, fun i j => if i = 0 ∧ j = 0 then 1 else 0, ?_, ?_⟩
  · unfold perm
    rw [mo262336_sum_perm2, mo262336_sum_perm2]
    simp [Fin.prod_univ_two]
  · unfold perm
    rw [mo262336_sum_perm2, mo262336_sum_perm2]
    simp [Fin.prod_univ_two]
    intro h
    apply ha
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_mo_262336.main :=
  ⟨fun R _ n M a => OMA.Helpers.mo262336_part1 R n M a, OMA.Helpers.mo262336_part2⟩
