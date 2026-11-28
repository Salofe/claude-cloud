import OMAStatements.S_mo_342993
import Mathlib

namespace OMA.Helpers

open Polynomial Matrix OMA.S_mo_342993

variable {K : Type} [Field K]

theorem mo342993_taylor_X_sub_C (a : K) : taylor a (X - C a) = X := by
  rw [map_sub, taylor_X, taylor_C]
  ring

/-- If `(X - a) ^ s` divides `f`, the Taylor coefficients of `f` at `a` below `s` vanish. -/
theorem mo342993_coeff_vanish {a : K} {s t : ℕ} {f : K[X]} (hf : (X - C a) ^ s ∣ f)
    (ht : t < s) : (taylor a f).coeff t = 0 := by
  obtain ⟨g, rfl⟩ := hf
  rw [taylor_mul, taylor_pow, mo342993_taylor_X_sub_C, coeff_X_pow_mul']
  simp [show ¬ s ≤ t by omega]

theorem mo342993_coeff_modByMonic {a : K} {s t : ℕ} {f q : K[X]} (_hq : q.Monic)
    (hdvd : (X - C a) ^ s ∣ q) (ht : t < s) :
    (taylor a (f %ₘ q)).coeff t = (taylor a f).coeff t := by
  rw [modByMonic_eq_sub_mul_div f q, map_sub, coeff_sub,
    mo342993_coeff_vanish (dvd_mul_of_dvd_left hdvd _) ht, sub_zero]

/-- A row of the confluent matrix applied to the coefficients of `P` is a Taylor coefficient. -/
theorem mo342993_eval_sum {N t : ℕ} (a : K) (P : K[X]) (hP : P.natDegree < N) :
    (∑ r : Fin N, P.coeff r.val * ((r.val.choose t : K) * a ^ (r.val - t))) =
      (taylor a P).coeff t := by
  rw [taylor_coeff, hasseDeriv_apply, eval_sum]
  simp only [eval_monomial]
  rw [sum_over_range' _ (fun n => by simp) N hP, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun r _ => by ring

theorem mo342993_nodal_monic {k : ℕ} (x : Fin k → K) (s : ℕ) : (nodal x s).Monic :=
  monic_prod_of_monic _ _ (fun i _ => (monic_X_sub_C (x i)).pow s)

theorem mo342993_nodal_natDegree {k : ℕ} (x : Fin k → K) (s : ℕ) :
    (nodal x s).natDegree = k * s := by
  unfold nodal
  rw [natDegree_prod_of_monic _ _ (fun i _ => (monic_X_sub_C (x i)).pow s)]
  simp [natDegree_pow]

theorem mo342993_dvd_nodal {k : ℕ} (x : Fin k → K) (s : ℕ) (i : Fin k) :
    (X - C (x i)) ^ s ∣ nodal x s :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

theorem mo342993_card_natDegree {k s : ℕ} (hk : 0 < k) (hs : 0 < s) (x : Fin k → K)
    (i : Fin k) (t : ℕ) : (cardinalPoly x s i t).natDegree < k * s := by
  unfold cardinalPoly
  rw [← mo342993_nodal_natDegree x s]
  apply natDegree_modByMonic_lt _ (mo342993_nodal_monic x s)
  intro h
  have h1 := mo342993_nodal_natDegree x s
  rw [h, natDegree_one] at h1
  have : 0 < k * s := Nat.mul_pos hk hs
  omega

theorem mo342993_g_eval_ne {k : ℕ} (s : ℕ) (x : Fin k → K) (hx : Function.Injective x)
    (i : Fin k) : (∏ j ∈ Finset.univ.erase i, (X - C (x j)) ^ s).eval (x i) ≠ 0 := by
  rw [eval_prod, Finset.prod_ne_zero_iff]
  intro j hj
  rw [eval_pow, eval_sub, eval_X, eval_C]
  apply pow_ne_zero
  rw [sub_ne_zero]
  intro h
  exact (Finset.ne_of_mem_erase hj) (hx h).symm

theorem mo342993_local_eval {k : ℕ} (s : ℕ) (x : Fin k → K) (hx : Function.Injective x)
    (i : Fin k) : (localFactor x s i).eval (x i) = 1 := by
  unfold localFactor
  simp only [eval_mul, eval_C]
  exact inv_mul_cancel₀ (mo342993_g_eval_ne s x hx i)

theorem mo342993_local_dvd {k : ℕ} (s : ℕ) (x : Fin k → K) {i j : Fin k} (hij : j ≠ i) :
    (X - C (x j)) ^ s ∣ localFactor x s i := by
  unfold localFactor
  dsimp only
  exact Dvd.dvd.mul_left
    (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩)) _

/-- The Taylor coefficients of the cardinal polynomials at the nodes. -/
theorem mo342993_key {k s : ℕ} (x : Fin k → K) (hx : Function.Injective x) (i i' : Fin k)
    {t t' : ℕ} (ht' : t' < s) :
    (taylor (x i') (cardinalPoly x s i t)).coeff t' = if t = t' ∧ i = i' then 1 else 0 := by
  unfold cardinalPoly
  rw [mo342993_coeff_modByMonic (mo342993_nodal_monic x s) (mo342993_dvd_nodal x s i') ht']
  by_cases hii : i = i'
  · subst hii
    have hroot : X - C (x i) ∣ 1 - localFactor x s i := by
      rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_one, mo342993_local_eval s x hx i, sub_self]
    have hsplit : (X - C (x i)) ^ t * (1 - (1 - localFactor x s i) ^ s) =
        (X - C (x i)) ^ t - (X - C (x i)) ^ t * (1 - localFactor x s i) ^ s := by ring
    rw [hsplit, map_sub, coeff_sub,
      mo342993_coeff_vanish (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hroot s) _) ht',
      sub_zero, taylor_pow, mo342993_taylor_X_sub_C, coeff_X_pow]
    by_cases h : t = t'
    · subst h
      simp
    · simp [h, Ne.symm h]
  · rw [if_neg (fun h => hii h.2)]
    apply mo342993_coeff_vanish _ ht'
    apply dvd_mul_of_dvd_right
    have h1 : localFactor x s i ∣ 1 - (1 - localFactor x s i) ^ s := by
      have := sub_dvd_pow_sub_pow (1 : K[X]) (1 - localFactor x s i) s
      simpa using this
    exact dvd_trans (mo342993_local_dvd s x (Ne.symm hii)) h1

theorem mo342993_left {k s : ℕ} (hk : 0 < k) (hs : 0 < s) (x : Fin k → K)
    (hx : Function.Injective x) : inverseFormula x s * confluent x s = 1 := by
  ext ⟨t, i⟩ ⟨t', i'⟩
  rw [Matrix.mul_apply]
  simp only [inverseFormula, confluent, Matrix.of_apply]
  rw [mo342993_eval_sum (x i') _ (mo342993_card_natDegree hk hs x i t.val),
    mo342993_key x hx i i' t'.isLt, Matrix.one_apply]
  simp [Prod.ext_iff, Fin.val_inj]

theorem mo342993_right {k s : ℕ} (hk : 0 < k) (hs : 0 < s) (x : Fin k → K)
    (hx : Function.Injective x) : confluent x s * inverseFormula x s = 1 := by
  have h := mo342993_left hk hs x hx
  have hc : Fintype.card (Fin s × Fin k) = Fintype.card (Fin (k * s)) := by
    simp [Nat.mul_comm]
  exact (Matrix.mul_eq_one_comm_of_card_eq (Fin s × Fin k) (Fin (k * s)) K
    (A := inverseFormula x s) (B := confluent x s) hc).mp h

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_mo_342993.main := by
  intro K _ k s hk hs x hx
  have hl := mo342993_left hk hs x hx
  have hr := mo342993_right hk hs x hx
  refine ⟨hl, hr, fun b v => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [← h, Matrix.mulVec_mulVec, hl, Matrix.one_mulVec]
  · rw [h, Matrix.mulVec_mulVec, hr, Matrix.one_mulVec]
