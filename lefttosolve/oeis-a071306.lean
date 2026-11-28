import OMAStatements.S_oeis_a071306
import Mathlib

/-!
Proof of the two conjectures of OEIS A071306 (orthogonal matrices over Z/7Z).

Orthogonal part (the argument works over any finite field K in which 2 is invertible). Write O(n)
for the set of n x n matrices M with M Mᵀ = 1 and S(n) for the unit vectors of Kⁿ.
* The first row of an orthogonal matrix is a unit vector.
* For every unit vector v there is an orthogonal R whose first row is v: the reflection along
  e - v when (e - v)·(e - v) is nonzero, and minus the reflection along e + v otherwise (the two
  norms add up to 4, which is nonzero). Right multiplication by R maps the orthogonal matrices with
  first row e bijectively onto those with first row v.
* The orthogonal matrices with first row e are exactly the block matrices diag(1, A) with A in
  O(n), since the first column is then forced to be e as well.
Hence |O(n+1)| = |S(n+1)| |O(n)|. Over Z/7Z, |S(1)| = 2, so |O(n)| is even for n >= 1, and
a(n+1) = |O(n+1)|/2 = (|O(n)|/2) b(n+1) = a(n) b(n+1).

Recurrence for b. Let c(n, t) be the number of x in (Z/7Z)ⁿ with x_1^2 + ... + x_n^2 = t.
Splitting off the first coordinate gives c(n+1, t) = sum over y of c(n, t - y^2). This step is
linear, so the defect c(m+3, t) - 7 c(m+2, t) + 7 c(m+1, t) - 49 c(m, t) satisfies the same
step, and it vanishes for m = 0 and every t (a finite computation). Hence it vanishes for all m,
and b(n) = c(n, 1) satisfies b(n) = 7 b(n-1) - 7 b(n-2) + 49 b(n-3) for n >= 3.
-/

namespace OMA.Helpers

open Matrix

open Matrix

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Orthogonal `n x n` matrices. -/
def oG (K : Type) [Field K] [Fintype K] [DecidableEq K] (n : ℕ) : Finset (Matrix (Fin n) (Fin n) K) :=
  Finset.univ.filter (fun M => M * Mᵀ = 1)

/-- Unit vectors. -/
def sph (K : Type) [Field K] [Fintype K] [DecidableEq K] (n : ℕ) : Finset (Fin n → K) :=
  Finset.univ.filter (fun x => x ⬝ᵥ x = 1)

/-- The reflection along `w`. -/
def o_refl {m : ℕ} (w : Fin m → K) : Matrix (Fin m) (Fin m) K :=
  1 - (2 / (w ⬝ᵥ w)) • vecMulVec w w

theorem o_refl_transpose {m : ℕ} (w : Fin m → K) : (o_refl w)ᵀ = o_refl w := by
  simp [o_refl, transpose_sub, transpose_smul]

theorem o_refl_orth {m : ℕ} (w : Fin m → K) (hw : w ⬝ᵥ w ≠ 0) : o_refl w * (o_refl w)ᵀ = 1 := by
  rw [o_refl_transpose]
  have hV : vecMulVec w w * vecMulVec w w = (w ⬝ᵥ w) • vecMulVec w w := by
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]
  set c : K := 2 / (w ⬝ᵥ w) with hc
  have hcc : c * c * (w ⬝ᵥ w) = 2 * c := by rw [hc]; field_simp
  unfold o_refl
  rw [← hc, sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, smul_mul_smul_comm, hV, smul_smul,
    hcc]
  rw [two_mul, add_smul]
  abel

theorem o_refl_row0 {n : ℕ} (h2 : (2 : K) ≠ 0) (v : Fin (n + 1) → K) (hv : v ⬝ᵥ v = 1)
    (hw : (Pi.single 0 1 - v) ⬝ᵥ (Pi.single 0 1 - v) ≠ 0) :
    o_refl (Pi.single 0 1 - v) 0 = v := by
  set e : Fin (n + 1) → K := Pi.single 0 1 with he
  have hee : e ⬝ᵥ e = 1 := by simp [he]
  have hev : e ⬝ᵥ v = v 0 := by simp [he]
  have hve : v ⬝ᵥ e = v 0 := by simp [he]
  have hww : (e - v) ⬝ᵥ (e - v) = 2 * (1 - v 0) := by
    simp only [sub_dotProduct, dotProduct_sub, hee, hev, hve, hv]; ring
  have h1 : (1 : K) - v 0 ≠ 0 := by
    intro h; apply hw; rw [hww, h, mul_zero]
  have hw0 : (e - v) 0 = 1 - v 0 := by simp [he]
  funext j
  simp only [o_refl, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, hww, hw0]
  have key : 2 / (2 * (1 - v 0)) * ((1 - v 0) * (e - v) j) = (e - v) j := by
    field_simp
  rw [key]
  by_cases hj : j = 0
  · subst hj; simp [he]
  · simp [he, hj, Ne.symm hj]

theorem o_refl_row0' {n : ℕ} (h2 : (2 : K) ≠ 0) (v : Fin (n + 1) → K) (hv : v ⬝ᵥ v = 1)
    (hw : (Pi.single 0 1 + v) ⬝ᵥ (Pi.single 0 1 + v) ≠ 0) :
    o_refl (Pi.single 0 1 + v) 0 = -v := by
  set e : Fin (n + 1) → K := Pi.single 0 1 with he
  have hee : e ⬝ᵥ e = 1 := by simp [he]
  have hev : e ⬝ᵥ v = v 0 := by simp [he]
  have hve : v ⬝ᵥ e = v 0 := by simp [he]
  have hww : (e + v) ⬝ᵥ (e + v) = 2 * (1 + v 0) := by
    simp only [add_dotProduct, dotProduct_add, hee, hev, hve, hv]; ring
  have h1 : (1 : K) + v 0 ≠ 0 := by
    intro h; apply hw; rw [hww, h, mul_zero]
  have hw0 : (e + v) 0 = 1 + v 0 := by simp [he]
  funext j
  simp only [o_refl, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, hww, hw0]
  have key : 2 / (2 * (1 + v 0)) * ((1 + v 0) * (e + v) j) = (e + v) j := by
    field_simp
  rw [key]
  by_cases hj : j = 0
  · subst hj; simp [he]
  · simp [he, hj, Ne.symm hj]

theorem o_row_mul {m : ℕ} (A B : Matrix (Fin m) (Fin m) K) (i : Fin m) : (A * B) i = A i ᵥ* B := by
  funext j; simp [Matrix.mul_apply, vecMul, dotProduct]

theorem o_one_row {m : ℕ} (i : Fin m) : (1 : Matrix (Fin m) (Fin m) K) i = Pi.single i 1 := by
  funext j; simp [Matrix.one_apply, Pi.single_apply, eq_comm]

theorem o_trans_exists {n : ℕ} (h2 : (2 : K) ≠ 0) (v : Fin (n + 1) → K) (hv : v ⬝ᵥ v = 1) :
    ∃ R : Matrix (Fin (n + 1)) (Fin (n + 1)) K, R * Rᵀ = 1 ∧ R 0 = v := by
  set e : Fin (n + 1) → K := Pi.single 0 1 with he
  have hee : e ⬝ᵥ e = 1 := by simp [he]
  have hev : e ⬝ᵥ v = v 0 := by simp [he]
  have hve : v ⬝ᵥ e = v 0 := by simp [he]
  have hsum : (e - v) ⬝ᵥ (e - v) + (e + v) ⬝ᵥ (e + v) = 4 := by
    simp only [sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add, hee, hev, hve, hv]
    ring
  by_cases hw : (e - v) ⬝ᵥ (e - v) = 0
  · have hu : (e + v) ⬝ᵥ (e + v) ≠ 0 := by
      rw [hw, zero_add] at hsum; rw [hsum]
      intro h4; apply h2
      have : (4 : K) = 2 * 2 := by norm_num
      rw [this] at h4
      exact (mul_self_eq_zero.1 h4)
    refine ⟨-o_refl (e + v), ?_, ?_⟩
    · rw [transpose_neg, neg_mul_neg]; exact o_refl_orth _ hu
    · rw [show (-o_refl (e + v)) 0 = -(o_refl (e + v) 0) from rfl, o_refl_row0' h2 v hv hu, neg_neg]
  · exact ⟨o_refl (e - v), o_refl_orth _ hw, o_refl_row0 h2 v hv hw⟩


theorem o_fiber_eq {n : ℕ} (h2 : (2 : K) ≠ 0) (v : Fin (n + 1) → K) (hv : v ⬝ᵥ v = 1) :
    ((oG K (n + 1)).filter (fun M => M 0 = v)).card =
      ((oG K (n + 1)).filter (fun M => M 0 = Pi.single 0 1)).card := by
  obtain ⟨R, hR, hR0⟩ := o_trans_exists h2 v hv
  have hR' : Rᵀ * R = 1 := mul_eq_one_comm.1 hR
  apply Finset.card_nbij' (fun M => M * Rᵀ) (fun M => M * R)
  · intro M hM
    simp only [Finset.mem_coe, oG, Finset.mem_filter, Finset.mem_univ, true_and] at hM ⊢
    obtain ⟨hM1, hM2⟩ := hM
    refine ⟨?_, ?_⟩
    · rw [transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Rᵀ, hR',
        Matrix.one_mul, hM1]
    · rw [o_row_mul, hM2, ← hR0, ← o_row_mul, hR, o_one_row]
  · intro M hM
    simp only [Finset.mem_coe, oG, Finset.mem_filter, Finset.mem_univ, true_and] at hM ⊢
    obtain ⟨hM1, hM2⟩ := hM
    refine ⟨?_, ?_⟩
    · rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc R, hR, Matrix.one_mul, hM1]
    · rw [o_row_mul, hM2, single_vecMul, one_smul, ← hR0]; rfl
  · intro M _
    simp only
    rw [Matrix.mul_assoc, hR', Matrix.mul_one]
  · intro M _
    simp only
    rw [Matrix.mul_assoc, hR, Matrix.mul_one]


/-- The block matrix `diag(1, A)`. -/
def bext {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  Matrix.of (Fin.cons (Fin.cons (1 : K) (0 : Fin n → K)) (fun i => Fin.cons (0 : K) (A i)))

omit [Fintype K] [DecidableEq K] in
theorem bext_00 {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : bext A 0 0 = 1 := by simp [bext]
omit [Fintype K] [DecidableEq K] in
theorem bext_0s {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (j : Fin n) : bext A 0 j.succ = 0 := by
  simp [bext]
omit [Fintype K] [DecidableEq K] in
theorem bext_s0 {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (i : Fin n) : bext A i.succ 0 = 0 := by
  simp [bext]
omit [Fintype K] [DecidableEq K] in
theorem bext_ss {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) : bext A i.succ j.succ = A i j := by
  simp [bext]

theorem o_block_card {n : ℕ} :
    ((oG K (n + 1)).filter (fun M => M 0 = Pi.single 0 1)).card = (oG K n).card := by
  have col0 : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) K, M * Mᵀ = 1 → M 0 = Pi.single 0 1 →
      ∀ i : Fin n, M i.succ 0 = 0 := by
    intro M h1 h2 i
    have := congrFun (congrFun h1 i.succ) 0
    rw [Matrix.mul_apply] at this
    simp only [transpose_apply, h2, Matrix.one_apply, Fin.succ_ne_zero, if_false] at this
    simpa [Pi.single_apply] using this
  apply Finset.card_nbij' (fun M => M.submatrix Fin.succ Fin.succ) bext
  · intro M hM
    simp only [Finset.mem_coe, oG, Finset.mem_filter, Finset.mem_univ, true_and] at hM ⊢
    obtain ⟨h1, h2⟩ := hM
    ext i j
    have := congrFun (congrFun h1 i.succ) j.succ
    rw [Matrix.mul_apply, Fin.sum_univ_succ] at this
    simp only [transpose_apply, col0 M h1 h2, zero_mul, zero_add, Matrix.one_apply,
      Fin.succ_inj] at this
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa using this
  · intro A hA
    simp only [Finset.mem_coe, oG, Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
    refine ⟨?_, ?_⟩
    · ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_succ]
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
      · simp [bext_00, bext_0s]
      · simp [bext_00, bext_0s, bext_s0, Matrix.one_apply, (Fin.succ_ne_zero j').symm]
      · simp [bext_00, bext_0s, bext_s0, Matrix.one_apply, Fin.succ_ne_zero i']
      · have := congrFun (congrFun hA i') j'
        rw [Matrix.mul_apply] at this
        simp only [transpose_apply] at this
        simp [bext_s0, bext_ss, this, Matrix.one_apply]
    · funext j
      refine Fin.cases ?_ (fun j' => ?_) j
      · simp [bext_00]
      · simp [bext_0s, Pi.single_apply, Fin.succ_ne_zero j']
  · intro M hM
    simp only [Finset.mem_coe, oG, Finset.mem_filter, Finset.mem_univ, true_and] at hM
    obtain ⟨h1, h2⟩ := hM
    ext i j
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
    · rw [bext_00, h2]; simp
    · rw [bext_0s, h2]; simp [Pi.single_apply, Fin.succ_ne_zero j']
    · rw [bext_s0, col0 M h1 h2 i']
    · rw [bext_ss]; rfl
  · intro A _
    ext i j
    simp [bext_ss]

theorem oG_succ {n : ℕ} (h2 : (2 : K) ≠ 0) :
    (oG K (n + 1)).card = (sph K (n + 1)).card * (oG K n).card := by
  have H : ∀ M ∈ oG K (n + 1), M 0 ∈ sph K (n + 1) := by
    intro M hM
    simp only [oG, sph, Finset.mem_filter, Finset.mem_univ, true_and] at hM ⊢
    have := congrFun (congrFun hM 0) 0
    rw [Matrix.mul_apply] at this
    simpa [dotProduct] using this
  rw [Finset.card_eq_sum_card_fiberwise H]
  have : ∀ v ∈ sph K (n + 1), ((oG K (n + 1)).filter (fun M => M 0 = v)).card = (oG K n).card := by
    intro v hv
    simp only [sph, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rw [o_fiber_eq h2 v hv, o_block_card]
  rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]


theorem oG_even (h2 : (2 : K) ≠ 0) (hs : 2 ∣ (sph K 1).card) :
    ∀ n : ℕ, 1 ≤ n → 2 ∣ (oG K n).card := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rw [oG_succ h2]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; exact Dvd.dvd.mul_right hs _
    · exact Dvd.dvd.mul_left (ih h) _

theorem p7_ncard_a (n : ℕ) : {M : Matrix (Fin n) (Fin n) (ZMod 7) | M * M.transpose = 1}.ncard =
    (@oG (ZMod 7) (@ZMod.instField 7 ⟨by norm_num⟩) _ _ n).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext M
  simp [oG]

theorem p7_ncard_b (n : ℕ) : {x : Fin n → ZMod 7 | (∑ i : Fin n, (x i) ^ 2) = 1}.ncard =
    (@sph (ZMod 7) (@ZMod.instField 7 ⟨by norm_num⟩) _ _ n).card := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  unfold sph
  congr 1
  apply Finset.filter_congr
  intro x _
  simp [dotProduct, sq]

theorem p7_sph1 : (@sph (ZMod 7) (@ZMod.instField 7 ⟨by norm_num⟩) _ _ 1).card = 2 := by
  decide +kernel


/-- Number of `x : Fin n → ZMod 7` with `Σ x_i^2 = t`. -/
def cnt (n : ℕ) (t : ZMod 7) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → ZMod 7 => (∑ i : Fin n, (x i) ^ 2) = t)).card

theorem cnt_succ (n : ℕ) (t : ZMod 7) : cnt (n + 1) t = ∑ y : ZMod 7, cnt n (t - y ^ 2) := by
  unfold cnt
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => x 0) (t := Finset.univ) (by simp)]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.card_nbij' (fun (x : Fin (n + 1) → ZMod 7) => (Fin.tail x : Fin n → ZMod 7))
    (fun (x : Fin n → ZMod 7) => (Fin.cons y x : Fin (n + 1) → ZMod 7))
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨h1, h2⟩ := hx
    rw [Fin.sum_univ_succ, h2] at h1
    rw [← h1]
    simp [Fin.tail]
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    refine ⟨?_, by simp⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hx]; ring
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [← hx.2]
    exact Fin.cons_self_tail x
  · intro x _
    funext i
    simp [Fin.tail]

theorem cnt_base : ∀ t : ZMod 7,
    (cnt 3 t : ℤ) - 7 * cnt 2 t + 7 * cnt 1 t - 49 * cnt 0 t = 0 := by
  decide +kernel

theorem cnt_rec : ∀ (m : ℕ) (t : ZMod 7),
    (cnt (m + 3) t : ℤ) - 7 * cnt (m + 2) t + 7 * cnt (m + 1) t - 49 * cnt m t = 0 := by
  intro m
  induction m with
  | zero => exact cnt_base
  | succ m ih =>
    intro t
    rw [show m + 1 + 3 = (m + 3) + 1 by ring, show m + 1 + 2 = (m + 2) + 1 by ring,
      cnt_succ (m + 3), cnt_succ (m + 2), cnt_succ (m + 1), cnt_succ m]
    push_cast
    have : ∀ y : ZMod 7, (cnt (m + 3) (t - y ^ 2) : ℤ) = 7 * cnt (m + 2) (t - y ^ 2)
        - 7 * cnt (m + 1) (t - y ^ 2) + 49 * cnt m (t - y ^ 2) := by
      intro y; have := ih (t - y ^ 2); linarith
    rw [Finset.sum_congr rfl (fun y _ => this y)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring

theorem p7_b_cnt (n : ℕ) : {x : Fin n → ZMod 7 | (∑ i : Fin n, (x i) ^ 2) = 1}.ncard = cnt n 1 := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  unfold cnt
  congr 1

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a071306.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    simp only [OMA.S_oeis_a071306.b, OMA.Helpers.p7_b_cnt]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
      show m + 3 - 3 = m by omega]
    have := OMA.Helpers.cnt_rec m 1
    linarith
  · intro n hn
    simp only [OMA.S_oeis_a071306.a, OMA.S_oeis_a071306.b, OMA.Helpers.p7_ncard_a,
      OMA.Helpers.p7_ncard_b]
    have h2 : (2 : ZMod 7) ≠ 0 := by decide
    rw [@OMA.Helpers.oG_succ (ZMod 7) (@ZMod.instField 7 ⟨by norm_num⟩) _ _ n h2, mul_comm]
    have hev := @OMA.Helpers.oG_even (ZMod 7) (@ZMod.instField 7 ⟨by norm_num⟩) _ _ h2
      (by rw [OMA.Helpers.p7_sph1]) n hn
    exact Nat.mul_div_right_comm hev _

