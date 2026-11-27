import OMAReductions.R_OeisA69191_conjecture_2_R1

/-!
# Step H2 of the reduction OeisA69191.conjecture_2.R1

Weak interlacing for a negative semidefinite rank one perturbation of a single diagonal
entry: if `A` is a real symmetric matrix, `c ≥ 0`, and `f`, `g` list the eigenvalues of `A`
and of `B = A - c E_kk` in decreasing order, then `g i ≤ f i` for every `i`, and
`f j ≤ g i` whenever `i < j`.

The proof is a Courant-Fischer style dimension count, done by hand:

* The decreasing lists `f` and `g` are identified with the sorted eigenvalues of the symmetric
  maps `toEuclideanLin A` and `toEuclideanLin B` (two antitone tuples with the same
  characteristic polynomial coincide, since their sorted root lists agree).
* Rayleigh bounds: expanding `x` in an orthonormal eigenbasis, `⟪x, T x⟫ = ∑ λ_j ⟪b_j, x⟫ ^ 2`.
  If `x` is orthogonal to the eigenvectors of index above `m` then `λ_m ⟪x, x⟫ ≤ ⟪x, T x⟫`;
  if it is orthogonal to those of index below `m` then `⟪x, T x⟫ ≤ λ_m ⟪x, x⟫`.
* In an `n` dimensional space there is a nonzero vector orthogonal to any `n - 1` given
  vectors (kernel of a linear map to an `n - 1` dimensional space).
* The quadratic forms satisfy `⟪x, B x⟫ = ⟪x, A x⟫ - c (x k) ^ 2`.

For `g i ≤ f i` take `x ≠ 0` orthogonal to the eigenvectors of `B` above `i` and of `A` below
`i`; then `g i ⟪x, x⟫ ≤ ⟪x, B x⟫ ≤ ⟪x, A x⟫ ≤ f i ⟪x, x⟫`. For `f (i + 1) ≤ g i` take `x ≠ 0`
orthogonal to the eigenvectors of `A` above `i + 1`, those of `B` below `i`, and to the basis
vector `e_k`; then `f (i + 1) ⟪x, x⟫ ≤ ⟪x, A x⟫ = ⟪x, B x⟫ ≤ g i ⟪x, x⟫`. Monotonicity of `f`
gives `f j ≤ g i` for all `j > i`.

Only Mathlib is used (spectral theorem for symmetric maps, Parseval identity for orthonormal
bases, rank nullity); no upstream theorem is used.
-/

open Matrix Polynomial

namespace OMA.Helpers

section Rayleigh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Parseval: the squared norm is the sum of the squared coordinates in an orthonormal basis. -/
theorem inner_self_eq_sum {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (x : E) :
    inner ℝ x x = ∑ i, (inner ℝ (b i) x) ^ 2 := by
  rw [← b.sum_inner_mul_inner x x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm x, sq]

variable [FiniteDimensional ℝ E]

/-- The quadratic form of a symmetric map in its sorted orthonormal eigenbasis. -/
theorem inner_apply_eq_sum {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (x : E) :
    inner ℝ x (T x) =
      ∑ i, hT.eigenvalues hn i * (inner ℝ (hT.eigenvectorBasis hn i) x) ^ 2 := by
  rw [← (hT.eigenvectorBasis hn).sum_inner_mul_inner x (T x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hT (hT.eigenvectorBasis hn i) x, hT.apply_eigenvectorBasis, real_inner_smul_left,
    real_inner_comm x]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  ring

/-- Lower Rayleigh bound on the span of the eigenvectors of index at most `m`. -/
theorem rayleigh_lower {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (x : E) (m : Fin n)
    (hx : ∀ j, m < j → inner ℝ (hT.eigenvectorBasis hn j) x = 0) :
    hT.eigenvalues hn m * inner ℝ x x ≤ inner ℝ x (T x) := by
  rw [inner_apply_eq_sum hT hn, inner_self_eq_sum (hT.eigenvectorBasis hn), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases le_or_gt j m with h | h
  · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn h) (sq_nonneg _)
  · rw [hx j h]; simp

/-- Upper Rayleigh bound on the span of the eigenvectors of index at least `m`. -/
theorem rayleigh_upper {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (x : E) (m : Fin n)
    (hx : ∀ j, j < m → inner ℝ (hT.eigenvectorBasis hn j) x = 0) :
    inner ℝ x (T x) ≤ hT.eigenvalues hn m * inner ℝ x x := by
  rw [inner_apply_eq_sum hT hn, inner_self_eq_sum (hT.eigenvectorBasis hn), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases le_or_gt m j with h | h
  · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn h) (sq_nonneg _)
  · rw [hx j h]; simp

/-- In an `n` dimensional space, some nonzero vector is orthogonal to `n - 1` given vectors
(all the `u j` with `j ≠ m`). -/
theorem exists_orth {n : ℕ} (hn : Module.finrank ℝ E = n) (u : Fin n → E) (m : Fin n) :
    ∃ x : E, x ≠ 0 ∧ ∀ j, j ≠ m → inner ℝ (u j) x = 0 := by
  let Φ : E →ₗ[ℝ] ({j : Fin n // j ≠ m} → ℝ) := LinearMap.pi (fun j => innerₛₗ ℝ (u j.1))
  have hlt : Module.finrank ℝ ({j : Fin n // j ≠ m} → ℝ) < Module.finrank ℝ E := by
    rw [Module.finrank_fintype_fun_eq_card, hn]
    have := Fintype.card_subtype_lt (p := fun j : Fin n => j ≠ m) (x := m) (by simp)
    simpa using this
  obtain ⟨x, hx, hx0⟩ :=
    (Submodule.ne_bot_iff _).mp (LinearMap.ker_ne_bot_of_finrank_lt (f := Φ) hlt)
  refine ⟨x, hx0, fun j hj => ?_⟩
  have := congrFun (LinearMap.mem_ker.mp hx) ⟨j, hj⟩
  simpa [Φ] using this

/-- The roots of `∏ (X - C (f i))` are the values of `f`, with multiplicity. -/
theorem roots_prod_fn {n : ℕ} (f : Fin n → ℝ) :
    (∏ i, (X - C (f i))).roots = Multiset.map f Finset.univ.val := by
  rw [Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

/-- Two antitone tuples giving the same product of linear factors are equal. -/
theorem antitone_eq_of_prod_eq {n : ℕ} (f g : Fin n → ℝ) (hf : Antitone f) (hg : Antitone g)
    (h : ∏ i, (X - C (f i)) = ∏ i, (X - C (g i))) : f = g := by
  have hr := congrArg Polynomial.roots h
  rw [roots_prod_fn, roots_prod_fn, Fin.univ_val_map, Fin.univ_val_map,
    Multiset.coe_eq_coe] at hr
  exact List.ofFn_injective (List.Perm.eq_of_sortedGE hf.sortedGE_ofFn hg.sortedGE_ofFn hr)

/-- An antitone tuple whose linear factors multiply to the characteristic polynomial of a
symmetric map is its sorted list of eigenvalues. -/
theorem eq_eigenvalues {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (f : Fin n → ℝ) (hf : Antitone f)
    (h : T.charpoly = ∏ i, (X - C (f i))) : f = hT.eigenvalues hn := by
  apply antitone_eq_of_prod_eq f _ hf (hT.eigenvalues_antitone hn)
  rw [← h, hT.charpoly_eq hn]
  simp

end Rayleigh

theorem charpoly_toEuclideanLin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (Matrix.toEuclideanLin A).charpoly = A.charpoly := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.charpoly_toLin]

/-- The quadratic form of `A - c E_kk`. -/
theorem inner_sub_single {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x (Matrix.toEuclideanLin (A - Matrix.single k k c) x) =
      inner ℝ x (Matrix.toEuclideanLin A x) - c * (x k) ^ 2 := by
  rw [map_sub, LinearMap.sub_apply, inner_sub_right]
  congr 1
  rw [Matrix.toLpLin_apply, Matrix.single_mulVec_eq, WithLp.toLp_smul, real_inner_smul_right,
    PiLp.toLp_single, EuclideanSpace.inner_single_right]
  simp
  ring

/-- Weak interlacing for `A - c E_kk` with `c ≥ 0`. -/
theorem interlace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (k : Fin n)
    (c : ℝ) (hc : 0 ≤ c) (f g : Fin n → ℝ) (hf : Antitone f) (hg : Antitone g)
    (hfA : A.charpoly = ∏ i, (X - C (f i)))
    (hgB : (A - Matrix.single k k c).charpoly = ∏ i, (X - C (g i))) :
    (∀ i, g i ≤ f i) ∧ (∀ i j, i < j → f j ≤ g i) := by
  have hB : (A - Matrix.single k k c).IsHermitian :=
    hA.sub (by simp [Matrix.IsHermitian])
  have hT : (Matrix.toEuclideanLin A).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hS : (Matrix.toEuclideanLin (A - Matrix.single k k c)).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hfe : f = hT.eigenvalues hn :=
    eq_eigenvalues hT hn f hf (by rw [charpoly_toEuclideanLin]; exact hfA)
  have hge : g = hS.eigenvalues hn :=
    eq_eigenvalues hS hn g hg (by rw [charpoly_toEuclideanLin]; exact hgB)
  have hq := inner_sub_single A k c
  constructor
  · intro i
    obtain ⟨x, hx0, hx⟩ := exists_orth hn
      (fun j => if j < i then hT.eigenvectorBasis hn j else hS.eigenvectorBasis hn j) i
    have h1 := rayleigh_lower hS hn x i (fun j hj => by
      have := hx j (ne_of_gt hj)
      simpa [not_lt.mpr hj.le] using this)
    have h2 := rayleigh_upper hT hn x i (fun j hj => by
      have := hx j (ne_of_lt hj)
      simpa [hj] using this)
    have hpos : 0 < inner ℝ x x := real_inner_self_pos.mpr hx0
    have h3 := hq x
    have h4 : 0 ≤ c * (x k) ^ 2 := mul_nonneg hc (sq_nonneg _)
    rw [hfe, hge]
    exact le_of_mul_le_mul_right (by linarith) hpos
  · intro i j hij
    have hi1 : i.val + 1 < n := by
      have := j.isLt
      have : i.val < j.val := hij
      omega
    let m : Fin n := ⟨i.val + 1, hi1⟩
    have hmj : m ≤ j := by
      change i.val + 1 ≤ j.val
      have : i.val < j.val := hij
      omega
    have him : i < m := by
      change i.val < i.val + 1
      omega
    obtain ⟨x, hx0, hx⟩ := exists_orth hn
      (fun l => if l < i then hS.eigenvectorBasis hn l else if l = i then
        EuclideanSpace.single k 1 else hT.eigenvectorBasis hn l) m
    have hxk : x k = 0 := by
      have := hx i (ne_of_lt him)
      simpa [EuclideanSpace.inner_single_left] using this
    have h1 := rayleigh_lower hT hn x m (fun l hl => by
      have := hx l (ne_of_gt hl)
      have hl1 : ¬ l < i := not_lt.mpr (him.trans hl).le
      have hl2 : l ≠ i := ne_of_gt (him.trans hl)
      simpa [hl1, hl2] using this)
    have h2 := rayleigh_upper hS hn x i (fun l hl => by
      have := hx l (ne_of_lt (hl.trans him))
      simpa [hl] using this)
    have hpos : 0 < inner ℝ x x := real_inner_self_pos.mpr hx0
    have h3 : inner ℝ x (Matrix.toEuclideanLin (A - Matrix.single k k c) x) =
        inner ℝ x (Matrix.toEuclideanLin A x) := by
      rw [hq x, hxk]
      ring
    have hfm : f m ≤ g i := by
      rw [hfe, hge]
      exact le_of_mul_le_mul_right (by linarith) hpos
    exact (hf hmj).trans hfm

end OMA.Helpers

theorem OMA.solution : OMA.R_OeisA69191_conjecture_2_R1.H2 := by
  intro n A hA k c hc f g hf hg hfA hgB
  exact OMA.Helpers.interlace A hA k c hc f g hf hg hfA hgB
