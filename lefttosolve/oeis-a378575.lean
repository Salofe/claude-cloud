import OMAStatements.S_oeis_a378575
import Mathlib

namespace OMA.Helpers
open OMA.S_oeis_a378575 PowerSeries

theorem map_powSeq378 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (g : ℕ → R) :
    ∀ k n, φ (powSeq g k n) = powSeq (fun i => φ (g i)) k n := by
  intro k
  induction k with
  | zero => intro n; simp only [powSeq]; split_ifs <;> simp
  | succ k ih => intro n; simp only [powSeq, map_sum, map_mul, ih]

theorem map_comp378 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f g : ℕ → R) (n : ℕ) :
    φ (comp f g n) = comp (fun i => φ (f i)) (fun i => φ (g i)) n := by
  simp only [comp, map_sum, map_mul, map_powSeq378]

theorem map_iterComp378 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : ℕ → R) :
    ∀ r n, φ (iterComp f r n) = iterComp (fun i => φ (f i)) r n := by
  intro r
  induction r with
  | zero => intro n; simp only [iterComp]; split_ifs <;> simp
  | succ r ih =>
    intro n
    simp only [iterComp, map_comp378]
    congr 1
    funext i
    exact ih i

theorem powSeq_congr378 {R : Type*} [CommRing R] (g g' : ℕ → R) (n : ℕ)
    (h : ∀ i ≤ n, g i = g' i) : ∀ k m, m ≤ n → powSeq g k m = powSeq g' k m := by
  intro k
  induction k with
  | zero => intro m _; rfl
  | succ k ih =>
    intro m hm
    simp only [powSeq]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i < m + 1 := Finset.mem_range.mp hi
    rw [h i (by omega), ih (m - i) (by omega)]

theorem comp_congr378 {R : Type*} [CommRing R] (f f' g g' : ℕ → R) (n : ℕ)
    (hf : ∀ i ≤ n, f i = f' i) (hg : ∀ i ≤ n, g i = g' i) :
    ∀ m, m ≤ n → comp f g m = comp f' g' m := by
  intro m hm
  simp only [comp]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k < m + 1 := Finset.mem_range.mp hk
  rw [hf k (by omega), powSeq_congr378 g g' n hg k m hm]

theorem iterComp_congr378 {R : Type*} [CommRing R] (f f' : ℕ → R) (n : ℕ)
    (hf : ∀ i ≤ n, f i = f' i) : ∀ r m, m ≤ n → iterComp f r m = iterComp f' r m := by
  intro r
  induction r with
  | zero => intro m _; rfl
  | succ r ih =>
    intro m hm
    simp only [iterComp]
    exact comp_congr378 f f' _ _ n hf (fun i hi => ih i hi) m hm

theorem powSeq_coeff378 {R : Type*} [CommRing R] (g : ℕ → R) :
    ∀ k n, powSeq g k n = coeff n ((mk g) ^ k) := by
  intro k
  induction k with
  | zero => intro n; simp [powSeq, coeff_one]
  | succ k ih =>
    intro n
    rw [pow_succ', coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [powSeq, coeff_mk, ih]

theorem comp_coeff378 {R : Type*} [CommRing R] (f g : ℕ → R) (n : ℕ) :
    comp f g n = coeff n (∑ k ∈ Finset.range (n + 1), C (f k) * (mk g) ^ k) := by
  simp only [comp, map_sum, coeff_C_mul, powSeq_coeff378]

/-- The sequence `0, 1, c, c^2, ...`, the coefficients of `x / (1 - c x)`. -/
def gfun378 {R : Type*} [CommRing R] (c : R) (n : ℕ) : R := if n = 0 then 0 else c ^ (n - 1)

/-- The geometric series `1 / (1 - c x)`. -/
def U378 {R : Type*} [CommRing R] (c : R) : R⟦X⟧ := mk fun n => c ^ n

theorem U378_mul {R : Type*} [CommRing R] (c : R) : (1 - C c * X) * U378 c = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, coeff_one, mul_assoc, coeff_C_mul]
  rcases n with _ | n
  · simp [U378]
  · rw [coeff_succ_X_mul]
    simp [U378, pow_succ]
    ring

theorem gfun378_eq {R : Type*} [CommRing R] (c : R) : mk (gfun378 c) = X * U378 c := by
  ext n
  rcases n with _ | n
  · simp [gfun378]
  · rw [coeff_succ_X_mul]
    simp [gfun378, U378]

theorem tsum378 {R : Type*} [CommRing R] (G : R⟦X⟧) (N : ℕ) :
    (1 - G) * ∑ k ∈ Finset.range N, G ^ (k + 1) = G - G ^ (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

theorem key378 {R : Type*} [CommRing R] (c : R) (n : ℕ) :
    comp (gfun378 (1 : R)) (gfun378 c) n = gfun378 (c + 1) n := by
  rw [comp_coeff378]
  have hb : ∑ k ∈ Finset.range (n + 1), C (gfun378 (1 : R) k) * (mk (gfun378 c)) ^ k =
      ∑ k ∈ Finset.range n, (mk (gfun378 c)) ^ (k + 1) := by
    rw [Finset.sum_range_succ']
    simp [gfun378]
  rw [hb]
  set G := mk (gfun378 c) with hG
  set T := ∑ k ∈ Finset.range n, G ^ (k + 1) with hT
  have hA := U378_mul c
  have hB := U378_mul (c + 1)
  have hGe : G = X * U378 c := gfun378_eq c
  have hH : mk (gfun378 (c + 1)) = X * U378 (c + 1) := gfun378_eq (c + 1)
  have h1 := tsum378 G n
  rw [← hT] at h1
  -- W * (1 - G) = 1
  have hW : ((1 - C c * X) * U378 (c + 1)) * (1 - G) = 1 := by
    rw [hGe]
    rw [map_add, map_one] at hB
    linear_combination hB - X * U378 (c + 1) * hA
  have hHG : (1 - G) * (X * U378 (c + 1)) = G := by
    rw [hGe]
    rw [map_add, map_one] at hB
    linear_combination (-(X * U378 (c + 1))) * hA + (X * U378 c) * hB
  have hdiff : T - X * U378 (c + 1) =
      X ^ (n + 1) * (-((1 - C c * X) * U378 (c + 1) * U378 c ^ (n + 1))) := by
    have e : T - X * U378 (c + 1) =
        ((1 - C c * X) * U378 (c + 1)) * (1 - G) * (T - X * U378 (c + 1)) := by
      rw [hW, one_mul]
    rw [e, mul_assoc, mul_sub, h1, hHG]
    rw [hGe]
    ring
  have hc : coeff n T = coeff n (X * U378 (c + 1)) := by
    have := congrArg (coeff n) hdiff
    rw [map_sub, coeff_X_pow_mul', if_neg (by omega)] at this
    exact sub_eq_zero.mp this
  rw [hc, ← hH, coeff_mk]

theorem iter378 {R : Type*} [CommRing R] :
    ∀ r n, iterComp (gfun378 (1 : R)) r n = gfun378 (r : R) n := by
  intro r
  induction r with
  | zero =>
    intro n
    rcases n with _ | _ | n <;> simp [iterComp, gfun378]
  | succ r ih =>
    intro n
    simp only [iterComp]
    rw [show iterComp (gfun378 (1 : R)) r = gfun378 (r : R) from funext ih, key378]
    push_cast
    rfl

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a378575.main := by
  intro a h0 hrec
  set c : ℕ → ZMod 4 := fun n => ((a n : ℤ) : ZMod 4) with hcdef
  have hc : ∀ n, c (n + 1) = (if n = 0 then 1 else 0) + OMA.S_oeis_a378575.iterComp c 5 n := by
    intro n
    have h := congrArg (Int.castRingHom (ZMod 4)) (hrec n)
    rw [map_add, OMA.Helpers.map_iterComp378] at h
    simp only [hcdef]
    rw [show ((a (n + 1) : ℤ) : ZMod 4) = Int.castRingHom (ZMod 4) (a (n + 1)) from rfl, h]
    congr 1
    split_ifs <;> simp
  have hall : ∀ n, c n = OMA.Helpers.gfun378 (1 : ZMod 4) n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | m
      · simp [hcdef, h0, OMA.Helpers.gfun378]
      · rw [hc m]
        rw [OMA.Helpers.iterComp_congr378 c (OMA.Helpers.gfun378 (1 : ZMod 4)) m
          (fun i hi => ih i (by omega)) 5 m le_rfl]
        rw [OMA.Helpers.iter378]
        have h5 : ((5 : ℕ) : ZMod 4) = 1 := by decide
        rw [h5]
        rcases m with _ | m <;> simp [OMA.Helpers.gfun378]
  intro n hn
  have h := hall n
  have h1 : OMA.Helpers.gfun378 (1 : ZMod 4) n = 1 := by
    simp [OMA.Helpers.gfun378]
    omega
  rw [h1] at h
  have h2 : ((a n : ℤ) : ZMod 4) = ((1 : ℤ) : ZMod 4) := by
    rw [Int.cast_one]
    exact h
  exact (ZMod.intCast_eq_intCast_iff (a n) 1 4).mp h2
