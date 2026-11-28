import OMAStatements.S_oeis_a228254
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a228254 Finset PowerSeries

/-- The entries of an array, read as integers on `ℕ` (zero outside the array). -/
def toZ {n : ℕ} (x : Fin (n + 3) → Fin 3) (i : ℕ) : ℤ :=
  if h : i < n + 3 then ((x ⟨i, h⟩).val : ℤ) else 0

theorem D_apply {n : ℕ} (x : Fin (n + 3) → Fin 3) (i : Fin n) :
    D x i = toZ x (i.val + 3) - 3 * toZ x (i.val + 2) + 3 * toZ x (i.val + 1) - toZ x i.val := by
  have hi := i.isLt
  unfold D toZ
  rw [dif_pos (by omega), dif_pos (by omega), dif_pos (by omega), dif_pos (by omega)]

theorem toZ_bounds {n : ℕ} (x : Fin (n + 3) → Fin 3) (i : ℕ) (hi : i < n + 3) :
    0 ≤ toZ x i ∧ toZ x i ≤ 2 := by
  unfold toZ
  rw [dif_pos hi]
  have := (x ⟨i, hi⟩).isLt
  omega

/-- A sequence with vanishing third differences and values in `[-2, 2]` on at least seven
consecutive indices is constant there. -/
theorem const_of_third_diff (N : ℕ) (hN : 4 ≤ N) (E : ℕ → ℤ)
    (hb : ∀ i, i < N + 3 → -2 ≤ E i ∧ E i ≤ 2)
    (hr : ∀ i, i < N → E (i + 3) - 3 * E (i + 2) + 3 * E (i + 1) - E i = 0) :
    ∀ i, i < N + 3 → E i = E 0 := by
  have h12 : E 1 = E 0 ∧ E 2 = E 0 := by
    have r0 : E 3 - 3 * E 2 + 3 * E 1 - E 0 = 0 := hr 0 (by omega)
    have r1 : E 4 - 3 * E 3 + 3 * E 2 - E 1 = 0 := hr 1 (by omega)
    have r2 : E 5 - 3 * E 4 + 3 * E 3 - E 2 = 0 := hr 2 (by omega)
    have r3 : E 6 - 3 * E 5 + 3 * E 4 - E 3 = 0 := hr 3 (by omega)
    have b0 := hb 0 (by omega)
    have b1 := hb 1 (by omega)
    have b2 := hb 2 (by omega)
    have b3 := hb 3 (by omega)
    have b4 := hb 4 (by omega)
    have b5 := hb 5 (by omega)
    have b6 := hb 6 (by omega)
    obtain ⟨l0, u0⟩ := b0
    obtain ⟨l1, u1⟩ := b1
    obtain ⟨l2, u2⟩ := b2
    generalize E 0 = p0 at *
    generalize E 1 = p1 at *
    generalize E 2 = p2 at *
    interval_cases p0 <;> interval_cases p1 <;> interval_cases p2 <;> omega
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    match i, ih, hi with
    | 0, _, _ => rfl
    | 1, _, _ => exact h12.1
    | 2, _, _ => exact h12.2
    | j + 3, ih, hi =>
      have r := hr j (by omega)
      have e2 := ih (j + 2) (by omega) (by omega)
      have e1 := ih (j + 1) (by omega) (by omega)
      have e0 := ih j (by omega) (by omega)
      linarith

theorem D_injOn (n : ℕ) (hn : 4 ≤ n) :
    Set.InjOn (D (n := n)) {x : Fin (n + 3) → Fin 3 | ∃ i, x i = 0} := by
  rintro x ⟨i0, hi0⟩ y ⟨j0, hj0⟩ hxy
  have hr : ∀ i, i < n → (fun k => toZ x k - toZ y k) (i + 3) -
      3 * (fun k => toZ x k - toZ y k) (i + 2) + 3 * (fun k => toZ x k - toZ y k) (i + 1) -
      (fun k => toZ x k - toZ y k) i = 0 := by
    intro i hi
    have h := congrFun hxy ⟨i, hi⟩
    rw [D_apply, D_apply] at h
    show toZ x (i + 3) - toZ y (i + 3) - 3 * (toZ x (i + 2) - toZ y (i + 2)) +
      3 * (toZ x (i + 1) - toZ y (i + 1)) - (toZ x i - toZ y i) = 0
    linarith
  have hb : ∀ i, i < n + 3 → -2 ≤ (fun k => toZ x k - toZ y k) i ∧
      (fun k => toZ x k - toZ y k) i ≤ 2 := by
    intro i hi
    have := toZ_bounds x i hi
    have := toZ_bounds y i hi
    show -2 ≤ toZ x i - toZ y i ∧ toZ x i - toZ y i ≤ 2
    omega
  have hc : ∀ i, i < n + 3 → toZ x i - toZ y i = toZ x 0 - toZ y 0 :=
    const_of_third_diff n hn _ hb hr
  have hx0 : toZ x i0.val = 0 := by
    unfold toZ
    rw [dif_pos i0.isLt]
    simp [hi0]
  have hy0 : toZ y j0.val = 0 := by
    unfold toZ
    rw [dif_pos j0.isLt]
    simp [hj0]
  have c1 := hc i0.val i0.isLt
  have c2 := hc j0.val j0.isLt
  have by0 := toZ_bounds y i0.val i0.isLt
  have bx0 := toZ_bounds x j0.val j0.isLt
  have hzero : toZ x 0 - toZ y 0 = 0 := by omega
  funext k
  have hk : toZ x k.val - toZ y k.val = 0 := by rw [hc k.val k.isLt]; exact hzero
  unfold toZ at hk
  rw [dif_pos k.isLt, dif_pos k.isLt] at hk
  apply Fin.ext
  have : ((x k).val : ℤ) = ((y k).val : ℤ) := by
    simp only [Fin.eta] at hk
    omega
  exact_mod_cast this

theorem image_eq (n : ℕ) :
    (univ : Finset (Fin (n + 3) → Fin 3)).image D =
      (univ.filter (fun x : Fin (n + 3) → Fin 3 => ∃ i, x i = 0)).image D := by
  apply Subset.antisymm
  · intro d hd
    rw [mem_image] at hd ⊢
    obtain ⟨x, -, rfl⟩ := hd
    obtain ⟨i0, -, hmin⟩ := exists_min_image (univ : Finset (Fin (n + 3)))
      (fun i => (x i).val) univ_nonempty
    have hmin' : ∀ j, (x i0).val ≤ (x j).val := fun j => hmin j (mem_univ j)
    refine ⟨fun j => ⟨(x j).val - (x i0).val, by have := (x j).isLt; omega⟩, ?_, ?_⟩
    · rw [mem_filter]
      refine ⟨mem_univ _, i0, ?_⟩
      apply Fin.ext
      simp
    · have hc : ∀ j, (((x j).val - (x i0).val : ℕ) : ℤ) = ((x j).val : ℤ) - ((x i0).val : ℤ) :=
        fun j => Nat.cast_sub (hmin' j)
      funext i
      simp only [D, hc]
      ring
  · exact image_subset_image (filter_subset _ _)

theorem card_filter_zero (n : ℕ) :
    (univ.filter (fun x : Fin (n + 3) → Fin 3 => ∃ i, x i = 0)).card = 3 ^ (n + 3) - 2 ^ (n + 3) := by
  have htot := card_filter_add_card_filter_not (s := (univ : Finset (Fin (n + 3) → Fin 3)))
    (fun x => ∃ i, x i = 0)
  have hneg : univ.filter (fun x : Fin (n + 3) → Fin 3 => ¬ ∃ i, x i = 0) =
      Fintype.piFinset (fun _ => ({1, 2} : Finset (Fin 3))) := by
    ext x
    have key : ∀ v : Fin 3, v ∈ ({1, 2} : Finset (Fin 3)) ↔ v ≠ 0 := by decide
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, key, not_exists, ne_eq]
  rw [hneg, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, card_univ,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at htot
  have h2 : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
  rw [h2] at htot
  omega

theorem a_closed (n : ℕ) (hn : 4 ≤ n) : a n = 3 ^ (n + 3) - 2 ^ (n + 3) := by
  unfold a
  rw [image_eq, card_image_of_injOn, card_filter_zero]
  intro x hx y hy hxy
  rw [coe_filter] at hx hy
  exact D_injOn n hn (by simpa using hx) (by simpa using hy) hxy

/-- Encoding of a third difference sequence of length 3 by a natural number. -/
def enc (d : Fin 3 → ℤ) : ℕ := (d 0 + 8).toNat + 17 * (d 1 + 8).toNat + 289 * (d 2 + 8).toNat

/-- Base-3 decoding of an array of length 6. -/
def dec6 (i : Fin 729) : Fin (3 + 3) → Fin 3 :=
  fun j => ⟨i.val / 3 ^ j.val % 3, Nat.mod_lt _ (by norm_num)⟩

set_option maxHeartbeats 0 in
theorem card3 : ((univ : Finset (Fin 729)).image (fun i => enc (D (dec6 i)))).card = 621 := by
  decide +kernel

theorem D_bound {n : ℕ} (x : Fin (n + 3) → Fin 3) (i : Fin n) : -8 ≤ D x i ∧ D x i ≤ 8 := by
  have hi := i.isLt
  rw [D_apply]
  have := toZ_bounds x (i.val + 3) (by omega)
  have := toZ_bounds x (i.val + 2) (by omega)
  have := toZ_bounds x (i.val + 1) (by omega)
  have := toZ_bounds x i.val (by omega)
  constructor <;> linarith

theorem enc_injOn : Set.InjOn enc {d : Fin 3 → ℤ | ∀ i, -8 ≤ d i ∧ d i ≤ 8} := by
  intro d hd e he h
  have t : ∀ z : ℤ, -8 ≤ z → ((z + 8).toNat : ℤ) = z + 8 := fun z hz => Int.toNat_of_nonneg (by omega)
  have h' : ((enc d : ℕ) : ℤ) = ((enc e : ℕ) : ℤ) := by rw [h]
  unfold enc at h'
  push_cast at h'
  rw [t _ (hd 0).1, t _ (hd 1).1, t _ (hd 2).1, t _ (he 0).1, t _ (he 1).1, t _ (he 2).1] at h'
  have d0 := hd 0
  have d1 := hd 1
  have d2 := hd 2
  have e0 := he 0
  have e1 := he 1
  have e2 := he 2
  funext i
  fin_cases i <;> simp <;> omega

theorem img3 : (univ : Finset (Fin (3 + 3) → Fin 3)).image (enc ∘ D) =
    (univ : Finset (Fin 729)).image (fun i => enc (D (dec6 i))) := by
  ext c
  simp only [mem_image, mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨x, rfl⟩
    have hlt : (finFunctionFinEquiv x : ℕ) < 729 := (finFunctionFinEquiv x).isLt
    refine ⟨⟨(finFunctionFinEquiv x : ℕ), hlt⟩, ?_⟩
    have hx : dec6 ⟨(finFunctionFinEquiv x : ℕ), hlt⟩ = x := by
      funext j
      apply Fin.ext
      show (finFunctionFinEquiv x : ℕ) / 3 ^ j.val % 3 = (x j).val
      have := congrFun (finFunctionFinEquiv.symm_apply_apply x) j
      rw [← this]
      rfl
    rw [hx]
  · rintro ⟨i, rfl⟩
    exact ⟨_, rfl⟩

theorem a3 : a 3 = 621 := by
  have hinj : Set.InjOn enc ((univ : Finset (Fin (3 + 3) → Fin 3)).image D : Set (Fin 3 → ℤ)) := by
    intro d hd e he h
    rw [coe_image] at hd he
    obtain ⟨x, -, rfl⟩ := hd
    obtain ⟨y, -, rfl⟩ := he
    exact enc_injOn (fun i => D_bound x i) (fun i => D_bound y i) h
  unfold a
  rw [← card_image_of_injOn hinj, image_image, img3, card3]

set_option maxHeartbeats 0 in
theorem a1 : a 1 = 17 := by decide +kernel

set_option maxHeartbeats 0 in
theorem a2 : a 2 = 143 := by decide +kernel

theorem a_closedQ (n : ℕ) (hn : 4 ≤ n) : (a n : ℚ) = 27 * 3 ^ n - 8 * 2 ^ n := by
  rw [a_closed n hn, Nat.cast_sub (Nat.pow_le_pow_left (by norm_num) _)]
  push_cast
  ring

theorem gf_of (f : ℕ → ℚ) (h1 : f 1 = 17) (h2 : f 2 = 143) (h3 : f 3 = 621)
    (hc : ∀ n, 4 ≤ n → f n = 27 * 3 ^ n - 8 * 2 ^ n) :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else f n) *
      ((1 - 2 * X) * (1 - 3 * X)) = X * (17 + 58 * X + 8 * X ^ 2 - 188 * X ^ 3 - 264 * X ^ 4) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else f n) with hA
  have hden : A * (((1 : ℚ⟦X⟧) - 2 * X) * (1 - 3 * X)) =
      A - C (5 : ℚ) * (A * X ^ 1) + C (6 : ℚ) * (A * X ^ 2) := by
    simp only [map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (17 + 58 * X + 8 * X ^ 2 - 188 * X ^ 3 - 264 * X ^ 4) =
      C (17 : ℚ) * X ^ 1 + C (58 : ℚ) * X ^ 2 + C (8 : ℚ) * X ^ 3 - C (188 : ℚ) * X ^ 4 -
        C (264 : ℚ) * X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [hden, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk, coeff_C]
  match k with
  | 0 => simp
  | 1 => simp [h1]
  | 2 => norm_num [h1, h2]
  | 3 => norm_num [h1, h2, h3]
  | 4 => norm_num [h2, h3, hc 4 le_rfl]
  | 5 => norm_num [h3, hc 4 le_rfl, hc 5 (by norm_num)]
  | j + 6 =>
    simp [hc (j + 6) (by omega), hc (j + 5) (by omega), hc (j + 4) (by omega)]
    ring

theorem gen_fun : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - 2 * X) * (1 - 3 * X)) = X * (17 + 58 * X + 8 * X ^ 2 - 188 * X ^ 3 - 264 * X ^ 4) :=
  gf_of (fun n => (a n : ℚ)) (by rw [a1]; norm_num) (by rw [a2]; norm_num) (by rw [a3]; norm_num)
    a_closedQ

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a228254.main :=
  ⟨OMA.Helpers.gen_fun, fun n hn => by
    rw [OMA.Helpers.a_closed n (by omega), add_comm 3 n]⟩
