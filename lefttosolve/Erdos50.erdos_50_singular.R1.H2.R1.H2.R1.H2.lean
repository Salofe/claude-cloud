import OMAReductions.R_Erdos50_erdos_50_singular_R1_H2_R1_H2_R1
import Mathlib

open Finset
open scoped Classical

namespace OMA.Helpers

theorem crt_count {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (F : ℕ × ℕ → Prop) :
    ((range (a*b)).filter (fun n => F (n % a, n % b))).card =
      ((range a ×ˢ range b).filter F).card := by
  let f : ℕ → ℕ × ℕ := fun n => (n % a, n % b)
  have hinj : Set.InjOn f (range (a*b) : Set ℕ) := by
    intro u hu v hv h
    have e := (Nat.modEq_and_modEq_iff_modEq_mul hab).1
      ⟨show u ≡ v [MOD a] from congrArg Prod.fst h, show u ≡ v [MOD b] from congrArg Prod.snd h⟩
    exact e.eq_of_lt_of_lt (mem_range.mp hu) (mem_range.mp hv)
  have himg : (range (a*b)).image f = range a ×ˢ range b := by
    apply eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨n, -, rfl⟩ := mem_image.mp hx
      exact mem_product.mpr ⟨mem_range.mpr (Nat.mod_lt _ ha), mem_range.mpr (Nat.mod_lt _ hb)⟩
    · rw [card_image_of_injOn hinj, card_product, card_range, card_range, card_range]
  rw [← himg, filter_image, card_image_of_injOn (hinj.mono (coe_subset.mpr (filter_subset _ _)))]

theorem card_filter_product (s t : Finset ℕ) (F : ℕ × ℕ → Prop) :
    ((s ×ˢ t).filter F).card = ∑ a ∈ s, (t.filter (fun b => F (a, b))).card := by
  rw [card_filter, sum_product]
  apply sum_congr rfl
  intro a _
  rw [card_filter]

theorem count_eq (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (R : Finset ℕ → Prop) :
    ((range (∏ p ∈ Q, p)).filter (fun n => R (Q.filter (· ∣ n)))).card =
      ∑ T ∈ Q.powerset.filter R, ∏ p ∈ Q \ T, (p - 1) := by
  induction Q using Finset.induction_on generalizing R with
  | empty =>
    by_cases h : R ∅ <;> simp [h, filter_singleton]
  | @insert p Q hpQ ih =>
    have hQ' : ∀ x ∈ Q, x.Prime := fun x hx => hQ x (mem_insert_of_mem hx)
    have hp : p.Prime := hQ p (mem_insert_self p Q)
    have hq : 0 < ∏ x ∈ Q, x := prod_pos fun x hx => (hQ' x hx).pos
    have hcop : p.Coprime (∏ x ∈ Q, x) := Nat.Coprime.prod_right fun x hx =>
      (Nat.coprime_primes hp (hQ' x hx)).mpr (fun h => hpQ (h ▸ hx))
    have key : ∀ n, (insert p Q).filter (· ∣ n) =
        if n % p = 0 then insert p (Q.filter (· ∣ n % ∏ x ∈ Q, x))
        else Q.filter (· ∣ n % ∏ x ∈ Q, x) := by
      intro n
      have e : Q.filter (· ∣ n % ∏ x ∈ Q, x) = Q.filter (· ∣ n) :=
        filter_congr (fun x hx => Nat.dvd_mod_iff (dvd_prod_of_mem _ hx))
      rw [filter_insert, e]
      simp only [Nat.dvd_iff_mod_eq_zero]
    obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hp.pos; omega⟩
    let F : ℕ × ℕ → Prop := fun x =>
      R (if x.1 = 0 then insert p (Q.filter (· ∣ x.2)) else Q.filter (· ∣ x.2))
    have h1 : ((range (∏ x ∈ insert p Q, x)).filter
        (fun n => R ((insert p Q).filter (· ∣ n)))).card =
        ((range (p * ∏ x ∈ Q, x)).filter (fun n => F (n % p, n % ∏ x ∈ Q, x))).card := by
      rw [prod_insert hpQ]
      congr 1
      apply filter_congr
      intro n _
      rw [key n]
    rw [h1, crt_count hp.pos hq hcop, card_filter_product,
      show range p = range (k + 1) by rw [hk], sum_range_succ']
    simp only [F, Nat.add_one_ne_zero, if_false, if_true, sum_const, card_range, smul_eq_mul]
    rw [ih hQ' R, ih hQ' (fun T => R (insert p T))]
    -- right-hand side
    rw [powerset_insert, filter_union, sum_union]
    · have hA : ∑ T ∈ Q.powerset.filter R, ∏ x ∈ insert p Q \ T, (x - 1) =
          (p - 1) * ∑ T ∈ Q.powerset.filter R, ∏ x ∈ Q \ T, (x - 1) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro T hT
        have hTQ : T ⊆ Q := mem_powerset.mp (mem_filter.mp hT).1
        have hpT : p ∉ T := fun h => hpQ (hTQ h)
        rw [insert_sdiff_of_notMem _ hpT, prod_insert (fun h => hpQ (mem_sdiff.mp h).1)]
      have hB : ∑ T ∈ (Q.powerset.image (insert p)).filter R, ∏ x ∈ insert p Q \ T, (x - 1) =
          ∑ T ∈ Q.powerset.filter (fun T => R (insert p T)), ∏ x ∈ Q \ T, (x - 1) := by
        rw [filter_image, sum_image]
        · apply sum_congr rfl
          intro T hT
          have hTQ : T ⊆ Q := mem_powerset.mp (mem_filter.mp hT).1
          congr 1
          ext x
          simp only [mem_sdiff, mem_insert]
          constructor
          · rintro ⟨h1, h2⟩
            refine ⟨?_, fun h => h2 (Or.inr h)⟩
            rcases h1 with h1 | h1
            · exact absurd h1 (fun h => h2 (Or.inl h))
            · exact h1
          · rintro ⟨h1, h2⟩
            refine ⟨Or.inr h1, ?_⟩
            rintro (h | h)
            · exact hpQ (h ▸ h1)
            · exact h2 h
        · intro T1 hT1 T2 hT2 h
          have h1 : p ∉ T1 := fun h' => hpQ (mem_powerset.mp (mem_filter.mp hT1).1 h')
          have h2 : p ∉ T2 := fun h' => hpQ (mem_powerset.mp (mem_filter.mp hT2).1 h')
          rw [← erase_insert h1, ← erase_insert h2]
          exact congrArg (fun S => S.erase p) h
      rw [hA, hB, show p - 1 = k by omega]
    · rw [disjoint_left]
      intro T h1 h2
      have hTQ : T ⊆ Q := mem_powerset.mp (mem_filter.mp h1).1
      obtain ⟨U, -, rfl⟩ := mem_image.mp (mem_filter.mp h2).1
      exact hpQ (hTQ (mem_insert_self p U))

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos50_erdos_50_singular_R1_H2_R1_H2_R1.H2 := by
  intro Q hQ R
  dsimp only
  rw [OMA.Helpers.count_eq Q hQ R, Nat.cast_sum, sum_div]
  apply sum_congr rfl
  intro T hT
  have hTQ : T ⊆ Q := mem_powerset.mp (mem_filter.mp hT).1
  have hpos : ∀ x ∈ Q, (x:ℝ) ≠ 0 := fun x hx => by exact_mod_cast (hQ x hx).ne_zero
  rw [Nat.cast_prod, Nat.cast_prod, ← prod_sdiff hTQ]
  rw [prod_congr rfl (fun x hx => Nat.cast_pred (hQ x (mem_sdiff.mp hx).1).pos)]
  have e : ∀ x ∈ Q \ T, (1 - 1/(x:ℝ)) = ((x:ℝ) - 1) / x := fun x hx => by
    field_simp [hpos x (mem_sdiff.mp hx).1]
  rw [prod_congr rfl e]
  rw [prod_div_distrib, prod_div_distrib, prod_const_one]
  ring
