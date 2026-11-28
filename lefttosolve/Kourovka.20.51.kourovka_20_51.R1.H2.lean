import OMAReductions.R_Kourovka_20_51_kourovka_20_51_R1
import Mathlib

/-!
# Step H2 of the reduction Kourovka.20.51.kourovka_20_51.R1

For odd primes p and q with p dividing q - 1, the Frobenius group of order p * q has
exactly p + (q - 1) / p conjugacy classes.

Construction: an element g of order p in the unit group of ZMod q (Cauchy), the cyclic
subgroup H it generates, and the semidirect product of the additive group of ZMod q by H
acting through multiplication. Two elements (n, h) and (m, k) commute exactly when
(h - 1) * m = (k - 1) * n. For fixed (h, k) the solutions (n, m) form a line in the plane
over ZMod q unless h = k = 1, so there are q ^ 2 + (p ^ 2 - 1) * q commuting pairs. The
Mathlib identity relating commuting pairs to the number of conjugacy classes then gives
the class count. Only Mathlib is used.
-/

namespace OMA.Helpers

open Multiplicative

noncomputable def actHom (q : ℕ) (H : Subgroup (ZMod q)ˣ) : H →* MulAut (Multiplicative (ZMod q)) :=
  (MulAutMultiplicative (ZMod q)).symm.toMonoidHom.comp
    ((DistribMulAction.toAddAut (ZMod q)ˣ (ZMod q)).comp H.subtype)

theorem actHom_apply (q : ℕ) (H : Subgroup (ZMod q)ˣ) (h : H) (n : Multiplicative (ZMod q)) :
    actHom q H h n = ofAdd (((h : (ZMod q)ˣ) : ZMod q) * toAdd n) := rfl

theorem commute_iff (q : ℕ) (H : Subgroup (ZMod q)ˣ)
    (a b : SemidirectProduct (Multiplicative (ZMod q)) H (actHom q H)) :
    Commute a b ↔ (((a.right : (ZMod q)ˣ) : ZMod q) - 1) * toAdd b.left =
      (((b.right : (ZMod q)ˣ) : ZMod q) - 1) * toAdd a.left := by
  constructor
  · intro h
    have h1 := congrArg SemidirectProduct.left h.eq
    simp only [SemidirectProduct.mul_left, actHom_apply] at h1
    have h2 := congrArg toAdd h1
    simp only [toAdd_mul, toAdd_ofAdd] at h2
    linear_combination h2
  · intro h
    apply SemidirectProduct.ext
    · simp only [SemidirectProduct.mul_left, actHom_apply]
      apply toAdd.injective
      simp only [toAdd_mul, toAdd_ofAdd]
      linear_combination h
    · simp only [SemidirectProduct.mul_right]
      exact mul_comm _ _

theorem card_line (q : ℕ) [Fact q.Prime] (a b : ZMod q) :
    Fintype.card {nn : ZMod q × ZMod q // a * nn.2 = b * nn.1} =
      if a = 0 ∧ b = 0 then q ^ 2 else q := by
  split_ifs with hab
  · obtain ⟨rfl, rfl⟩ := hab
    simp only [zero_mul]
    rw [Fintype.card_subtype_true, Fintype.card_prod, ZMod.card, sq]
  · by_cases ha : a = 0
    · subst ha
      have hb : b ≠ 0 := fun h => hab ⟨rfl, h⟩
      let e : ZMod q ≃ {nn : ZMod q × ZMod q // 0 * nn.2 = b * nn.1} :=
        { toFun := fun y => ⟨(0, y), by simp⟩
          invFun := fun nn => nn.1.2
          left_inv := fun y => rfl
          right_inv := fun nn => by
            obtain ⟨⟨x, y⟩, hxy⟩ := nn
            simp only [zero_mul] at hxy
            have hx : x = 0 := (mul_eq_zero.mp hxy.symm).resolve_left hb
            subst hx
            rfl }
      rw [← Fintype.card_congr e, ZMod.card]
    · let e : ZMod q ≃ {nn : ZMod q × ZMod q // a * nn.2 = b * nn.1} :=
        { toFun := fun x => ⟨(x, a⁻¹ * (b * x)), by field_simp⟩
          invFun := fun nn => nn.1.1
          left_inv := fun x => rfl
          right_inv := fun nn => by
            obtain ⟨⟨x, y⟩, hxy⟩ := nn
            simp only at hxy
            have hy : y = a⁻¹ * (b * x) := by
              rw [← hxy]; field_simp
            subst hy
            rfl }
      rw [← Fintype.card_congr e, ZMod.card]


theorem card_commuting (q : ℕ) [Fact q.Prime] (H : Subgroup (ZMod q)ˣ) :
    Nat.card {x : SemidirectProduct (Multiplicative (ZMod q)) H (actHom q H) ×
      SemidirectProduct (Multiplicative (ZMod q)) H (actHom q H) // Commute x.1 x.2} =
      q ^ 2 + (Nat.card H * Nat.card H - 1) * q := by
  classical
  let G := SemidirectProduct (Multiplicative (ZMod q)) H (actHom q H)
  let E : {x : G × G // Commute x.1 x.2} ≃ Σ h : H × H, {nn : ZMod q × ZMod q //
      (((h.1 : (ZMod q)ˣ) : ZMod q) - 1) * nn.2 = (((h.2 : (ZMod q)ˣ) : ZMod q) - 1) * nn.1} :=
    { toFun := fun x => ⟨(x.1.1.right, x.1.2.right),
        ⟨(toAdd x.1.1.left, toAdd x.1.2.left), (commute_iff q H x.1.1 x.1.2).mp x.2⟩⟩
      invFun := fun s => ⟨(⟨ofAdd s.2.1.1, s.1.1⟩, ⟨ofAdd s.2.1.2, s.1.2⟩),
        (commute_iff q H _ _).mpr s.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun s => rfl }
  rw [Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [card_line]
  have key : ∀ h : H × H, ((((h.1 : (ZMod q)ˣ) : ZMod q) - 1 = 0 ∧
      ((h.2 : (ZMod q)ˣ) : ZMod q) - 1 = 0) ↔ h = 1) := by
    intro h
    rw [sub_eq_zero, sub_eq_zero, Units.val_eq_one, Units.val_eq_one,
      OneMemClass.coe_eq_one, OneMemClass.coe_eq_one, Prod.ext_iff]
    rfl
  simp only [key]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, Finset.filter_eq', Finset.filter_ne']
  simp only [Finset.mem_univ, if_true, Finset.card_singleton, smul_eq_mul]
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_prod,
    Fintype.card_eq_nat_card, one_mul]

theorem frobenius_classes (p q : ℕ) (hp : p.Prime) (hpo : Odd p) (hq : q.Prime) (hqo : Odd q)
    (hdvd : p ∣ q - 1) :
    ∃ (G : Type) (_ : Group G), Finite G ∧ (∃ a b : G, a*b ≠ b*a) ∧
      Odd (Nat.card G) ∧ Nat.card (ConjClasses G) = p + (q-1)/p := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Fintype.card (ZMod q)ˣ = q - 1 := ZMod.card_units q
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card p (hcard ▸ hdvd)
  let H : Subgroup (ZMod q)ˣ := Subgroup.zpowers g
  have hH : Nat.card H = p := (Nat.card_zpowers g).trans hg
  let G := SemidirectProduct (Multiplicative (ZMod q)) H (actHom q H)
  have hG : Nat.card G = q * p := by
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, hH]
    simp [Nat.card_eq_fintype_card]
  have : Finite G := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  have hq1 : 1 < q := hq.one_lt
  have hp1 : 1 < p := hp.one_lt
  refine ⟨G, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · refine ⟨⟨ofAdd (1 : ZMod q), 1⟩, ⟨1, ⟨g, Subgroup.mem_zpowers g⟩⟩, fun h => ?_⟩
    have hc := (commute_iff q H _ _).mp h
    simp only [OneMemClass.coe_one, Units.val_one, sub_self, zero_mul, toAdd_ofAdd, mul_one] at hc
    have hg1 : g = 1 := by
      apply Units.ext
      rw [Units.val_one]
      exact (sub_eq_zero.mp hc.symm)
    rw [hg1, orderOf_one] at hg
    omega
  · rw [hG]
    exact hqo.mul hpo
  · have hc := card_comm_eq_card_conjClasses_mul_card G
    rw [card_commuting q H, hG, hH] at hc
    obtain ⟨m, hm⟩ := hdvd
    have hqm : q = p * m + 1 := by omega
    rw [hm, Nat.mul_div_cancel_left m hp.pos]
    set k := Nat.card (ConjClasses G)
    subst hqm
    have h2 : (p * m + 1) * ((p * m + 1) + (p * p - 1)) = (p * m + 1) * (k * p) := by
      rw [mul_add]
      have : (p * m + 1) ^ 2 = (p * m + 1) * (p * m + 1) := sq _
      nlinarith [hc]
    have h3 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < p * m + 1) h2
    have h4 : (m + p) * p = k * p := by
      have : p * p - 1 + 1 = p * p := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by positivity))
      nlinarith [h3]
    have h5 := Nat.eq_of_mul_eq_mul_right hp.pos h4
    omega

end OMA.Helpers

theorem OMA.solution : OMA.R_Kourovka_20_51_kourovka_20_51_R1.H2 :=
  fun p q hp hpo hq hqo hdvd => OMA.Helpers.frobenius_classes p q hp hpo hq hqo hdvd
