import OMAReductions.R_SnakeInBox_coil_upper_bound_R1
import Mathlib

/-!
# Step H1 of the reduction SnakeInBox.coil_upper_bound.R1

A set `C` of more than `2 ^ (n - 1)` vertices of the `n`-cube contains a vertex with at least
`sqrt n` neighbours in `C` (Huang's sensitivity argument); for `n ≥ 5` this exceeds two.

Here the argument is written out directly. The signed adjacency operator `hop` (sign of the
edge from `u` in direction `i` is `(-1)` to the number of elements of `u` below `i`) squares to
`n`. Functions supported on the half cube avoiding the top coordinate form a space of dimension
`2 ^ (n - 1)`, larger than the number of vertices outside `C`, so some nonzero `x` there makes
`h = hop x + sqrt n * x` vanish outside `C`; `h` is nonzero and satisfies `hop h = sqrt n * h`.
At a vertex where `|h|` is maximal, `sqrt n * |h u|` is at most the number of neighbours of
`u` in `C` times `|h u|`, which is at most `2 * |h u|`.
-/

namespace OMA.Helpers
open Finset

/-- The sign attached to the edge leaving `u` in direction `i`. -/
noncomputable def hsgn {n : ℕ} (u : Finset (Fin n)) (i : Fin n) : ℝ :=
  (-1) ^ (u.filter (fun j => j < i)).card

/-- Signed adjacency operator of the cube acting on real functions on its vertices. -/
noncomputable def hop {n : ℕ} (g : Finset (Fin n) → ℝ) (u : Finset (Fin n)) : ℝ :=
  ∑ i, hsgn u i * g (symmDiff u {i})

theorem neg_one_pow_card_symmDiff_singleton {n : ℕ} (X : Finset (Fin n)) (i : Fin n) :
    (-1 : ℝ) ^ (symmDiff X {i}).card = - (-1) ^ X.card := by
  by_cases hi : i ∈ X
  · have e : symmDiff X {i} = X.erase i := by
      ext x
      by_cases hx : x = i
      · subst hx; simp [Finset.mem_symmDiff, hi]
      · simp [Finset.mem_symmDiff, hx]
    rw [e, ← Finset.card_erase_add_one hi, pow_succ]
    ring
  · have e : symmDiff X {i} = insert i X := by
      ext x
      by_cases hx : x = i
      · subst hx; simp [Finset.mem_symmDiff, hi]
      · simp [Finset.mem_symmDiff, hx]
    rw [e, Finset.card_insert_of_notMem hi, pow_succ]
    ring

theorem hsgn_flip_self {n : ℕ} (u : Finset (Fin n)) (i : Fin n) :
    hsgn (symmDiff u {i}) i = hsgn u i := by
  unfold hsgn
  congr 2
  ext x
  by_cases hx : x = i
  · subst hx; simp
  · simp [Finset.mem_symmDiff, hx]

theorem hsgn_flip_lt {n : ℕ} (u : Finset (Fin n)) {i j : Fin n} (hij : i < j) :
    hsgn (symmDiff u {i}) j = - hsgn u j := by
  unfold hsgn
  have e : (symmDiff u {i}).filter (fun x => x < j) =
      symmDiff (u.filter (fun x => x < j)) {i} := by
    ext x
    by_cases hx : x = i
    · subst hx; simp [Finset.mem_symmDiff, hij]
    · simp [Finset.mem_symmDiff, hx]
  rw [e, neg_one_pow_card_symmDiff_singleton]

theorem hsgn_flip_gt {n : ℕ} (u : Finset (Fin n)) {i j : Fin n} (hij : j < i) :
    hsgn (symmDiff u {i}) j = hsgn u j := by
  unfold hsgn
  congr 2
  ext x
  by_cases hx : x = i
  · subst hx; simp [Finset.mem_symmDiff, not_lt.mpr hij.le]
  · simp [Finset.mem_symmDiff, hx]

theorem hsgn_mul_self {n : ℕ} (u : Finset (Fin n)) (i : Fin n) : hsgn u i * hsgn u i = 1 := by
  unfold hsgn
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

theorem abs_hsgn {n : ℕ} (u : Finset (Fin n)) (i : Fin n) : |hsgn u i| = 1 := by
  unfold hsgn
  simp

/-- A double sum with constant diagonal and antisymmetric off-diagonal part. -/
theorem double_sum_of_antisymm {n : ℕ} (F : Fin n → Fin n → ℝ) (c : ℝ)
    (hdiag : ∀ i, F i i = c) (hanti : ∀ i j, i ≠ j → F j i = - F i j) :
    ∑ i, ∑ j, F i j = n * c := by
  let O : Fin n → Fin n → ℝ := fun i j => if i = j then 0 else F i j
  have hsplit : ∀ i, ∑ j, F i j = c + ∑ j, O i j := by
    intro i
    have h1 : ∀ j, F i j = (if i = j then F i j else 0) + O i j := by
      intro j
      by_cases h : i = j <;> simp [O, h]
    rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp [hdiag]
  have hOanti : ∀ i j, O j i = - O i j := by
    intro i j
    by_cases h : i = j
    · subst h; simp [O]
    · simp only [O, if_neg (Ne.symm h), if_neg h, hanti i j h]
  have hc : ∑ i, ∑ j, O i j = ∑ i, ∑ j, O j i := Finset.sum_comm
  have hc2 : ∑ i, ∑ j, O j i = ∑ i, ∑ j, -(O i j) :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hOanti i j))
  simp only [Finset.sum_neg_distrib] at hc2
  have hz : ∑ i, ∑ j, O i j = 0 := by linarith
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib, hz, add_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The signed adjacency operator squares to `n` times the identity. -/
theorem hop_hop {n : ℕ} (g : Finset (Fin n) → ℝ) (u : Finset (Fin n)) :
    hop (hop g) u = n * g u := by
  unfold hop
  simp only [Finset.mul_sum]
  refine double_sum_of_antisymm
    (fun i j => hsgn u i * (hsgn (symmDiff u {i}) j * g (symmDiff (symmDiff u {i}) {j})))
    (g u) ?_ ?_
  · intro i
    beta_reduce
    rw [hsgn_flip_self, symmDiff_symmDiff_cancel_right, ← mul_assoc, hsgn_mul_self, one_mul]
  · intro i j hij
    beta_reduce
    rw [symmDiff_right_comm u {j} {i}]
    rcases lt_or_gt_of_ne hij with h | h
    · rw [hsgn_flip_lt u h, hsgn_flip_gt u h]; ring
    · rw [hsgn_flip_gt u h, hsgn_flip_lt u h]; ring

theorem hop_add_mul {n : ℕ} (a b : Finset (Fin n) → ℝ) (c : ℝ) (u : Finset (Fin n)) :
    hop (fun v => a v + c * b v) u = hop a u + c * hop b u := by
  unfold hop
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- Extension by zero from the half cube avoiding `t`. -/
noncomputable def hextL {n : ℕ} (t : Fin n) :
    ({u : Finset (Fin n) // t ∉ u} → ℝ) →ₗ[ℝ] (Finset (Fin n) → ℝ) where
  toFun x u := if h : t ∈ u then 0 else x ⟨u, h⟩
  map_add' x y := by
    ext u
    by_cases h : t ∈ u <;> simp [h]
  map_smul' c x := by
    ext u
    by_cases h : t ∈ u <;> simp [h]

/-- The operator `hop + lam` as a linear map. -/
noncomputable def hopL {n : ℕ} (lam : ℝ) : (Finset (Fin n) → ℝ) →ₗ[ℝ] (Finset (Fin n) → ℝ) where
  toFun g u := hop g u + lam * g u
  map_add' f g := by
    ext u
    simp only [Pi.add_apply, hop, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' c g := by
    ext u
    simp only [Pi.smul_apply, smul_eq_mul, hop, RingHom.id_apply]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl (fun i _ => by ring)
    · ring

theorem card_half {n : ℕ} (t : Fin n) :
    Fintype.card {u : Finset (Fin n) // t ∉ u} = 2 ^ (n - 1) := by
  rw [Fintype.card_subtype]
  have e : (Finset.univ.filter (fun u : Finset (Fin n) => t ∉ u)) = (Finset.univ.erase t).powerset := by
    ext u
    simp [Finset.subset_erase]
  rw [e, Finset.card_powerset, Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ,
    Fintype.card_fin]

theorem card_outside {n : ℕ} (C : Finset (Finset (Fin n))) :
    Fintype.card {w : Finset (Fin n) // w ∉ C} = 2 ^ n - C.card := by
  rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_finset, Fintype.card_fin]

theorem hypercube_adj_flip {n : ℕ} (u : Finset (Fin n)) (i : Fin n) :
    (SnakeInBox.Hypercube n).Adj u (symmDiff u {i}) := by
  unfold SnakeInBox.Hypercube
  rw [SimpleGraph.fromRel_adj]
  refine ⟨fun h => ?_, Or.inl ?_⟩
  · have h2 : symmDiff u (symmDiff u {i}) = (∅ : Finset (Fin n)) := by
      rw [← h, symmDiff_self]
      rfl
    rw [symmDiff_symmDiff_cancel_left] at h2
    exact Finset.singleton_ne_empty i h2
  · rw [symmDiff_symmDiff_cancel_left, Finset.card_singleton]

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_SnakeInBox_coil_upper_bound_R1.H1 := by
  intro n hn C hdeg
  classical
  by_contra hlt
  rw [not_le] at hlt
  let t : Fin n := ⟨n - 1, by omega⟩
  let lam : ℝ := Real.sqrt n
  have hlam2 : lam * lam = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hlam : 2 < lam := by
    have h4 : (4 : ℝ) < n := by exact_mod_cast (show 4 < n by omega)
    have h0 : 0 ≤ lam := Real.sqrt_nonneg _
    nlinarith
  let L := (LinearMap.funLeft ℝ ℝ (Subtype.val : {w : Finset (Fin n) // w ∉ C} → Finset (Fin n)))
    ∘ₗ (hopL lam) ∘ₗ (hextL t)
  have hdim : Module.finrank ℝ ({w : Finset (Fin n) // w ∉ C} → ℝ) <
      Module.finrank ℝ ({u : Finset (Fin n) // t ∉ u} → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, card_half,
      card_outside]
    have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h3 : 0 < 2 ^ (n - 1) := by positivity
    omega
  obtain ⟨x, hxker, hx0⟩ :=
    (Submodule.ne_bot_iff _).mp (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hdim)
  rw [LinearMap.mem_ker] at hxker
  set g : Finset (Fin n) → ℝ := hextL t x with hg
  set h : Finset (Fin n) → ℝ := hopL lam g with hh
  have hgval : ∀ u, g u = if hu : t ∈ u then 0 else x ⟨u, hu⟩ := fun u => rfl
  have hhval : ∀ u, h u = hop g u + lam * g u := fun u => rfl
  have hout : ∀ w, w ∉ C → h w = 0 := by
    intro w hw
    have h1 : L x ⟨w, hw⟩ = (0 : {w : Finset (Fin n) // w ∉ C} → ℝ) ⟨w, hw⟩ := by rw [hxker]
    exact h1
  -- h is nonzero
  have hne : ∃ w, h w ≠ 0 := by
    obtain ⟨u0, hu0⟩ := Function.ne_iff.mp hx0
    refine ⟨insert t u0.1, ?_⟩
    have htin : t ∈ insert t u0.1 := Finset.mem_insert_self t u0.1
    rw [hhval, hgval (insert t u0.1), dif_pos htin, mul_zero, add_zero]
    unfold hop
    rw [Finset.sum_eq_single t]
    · have e : symmDiff (insert t u0.1) {t} = u0.1 := by
        ext y
        by_cases hy : y = t
        · subst hy; simp [Finset.mem_symmDiff, u0.2]
        · simp [Finset.mem_symmDiff, hy]
      rw [e, hgval, dif_neg u0.2]
      intro hz
      rcases mul_eq_zero.mp hz with hz | hz
      · have := abs_hsgn (insert t u0.1) t
        rw [hz, abs_zero] at this
        exact zero_ne_one this
      · exact hu0 hz
    · intro i _ hi
      have : t ∈ symmDiff (insert t u0.1) {i} := by
        simp [Finset.mem_symmDiff, Ne.symm hi]
      rw [hgval, dif_pos this, mul_zero]
    · intro hc; exact absurd (Finset.mem_univ t) hc
  -- h is an eigenvector of hop with eigenvalue lam
  have heig : ∀ u, hop h u = lam * h u := by
    intro u
    have e1 : h = fun v => hop g v + lam * g v := funext hhval
    rw [e1, hop_add_mul, hop_hop]
    simp only
    rw [← hlam2]
    ring
  obtain ⟨u, -, hu⟩ := Finset.exists_max_image Finset.univ (fun v => |h v|) Finset.univ_nonempty
  have hupos : 0 < |h u| := by
    obtain ⟨w, hw⟩ := hne
    exact lt_of_lt_of_le (abs_pos.mpr hw) (hu w (Finset.mem_univ w))
  have huC : u ∈ C := by
    by_contra huC
    rw [hout u huC, abs_zero] at hupos
    exact lt_irrefl 0 hupos
  -- the degree bound
  have hcnt : (Finset.univ.filter (fun i : Fin n => symmDiff u {i} ∈ C)).card ≤ 2 := by
    refine le_trans (Finset.card_le_card_of_injOn (fun i => symmDiff u {i}) ?_ ?_) (hdeg u huC)
    · intro i hi
      rw [Finset.mem_coe, Finset.mem_filter] at hi
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨hi.2, hypercube_adj_flip u i⟩
    · intro i _ j _ hij
      have h1 : ({i} : Finset (Fin n)) = {j} := symmDiff_right_injective u hij
      exact Finset.singleton_injective h1
  have hbound : lam * |h u| ≤ 2 * |h u| := by
    calc lam * |h u| = |hop h u| := by
          rw [heig, abs_mul, abs_of_pos (by linarith : (0:ℝ) < lam)]
      _ ≤ ∑ i, |hsgn u i * h (symmDiff u {i})| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, (if symmDiff u {i} ∈ C then |h (symmDiff u {i})| else 0) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [abs_mul, abs_hsgn, one_mul]
          split_ifs with hc
          · rfl
          · rw [hout _ hc, abs_zero]
      _ = ∑ i ∈ Finset.univ.filter (fun i : Fin n => symmDiff u {i} ∈ C), |h (symmDiff u {i})| := by
          rw [Finset.sum_filter]
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => symmDiff u {i} ∈ C), |h u| :=
          Finset.sum_le_sum (fun i _ => hu _ (Finset.mem_univ _))
      _ = (Finset.univ.filter (fun i : Fin n => symmDiff u {i} ∈ C)).card * |h u| := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * |h u| := by
          apply mul_le_mul_of_nonneg_right _ hupos.le
          exact_mod_cast hcnt
  have : lam ≤ 2 := le_of_mul_le_mul_right hbound hupos
  linarith
