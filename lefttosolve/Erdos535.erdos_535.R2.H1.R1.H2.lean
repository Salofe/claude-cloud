import OMAReductions.R_Erdos535_erdos_535_R2_H1_R1
import Mathlib

/-!
# Step H2 of the reduction Erdos535.erdos_535.R2.H1.R1

Colour the ground set with k colours. Averaging over all colourings, some colouring makes at
least a k!/k^k fraction of the sets rainbow, and k^k is at most 3^k k!. A rainbow set is
encoded by the word whose j-th letter is its element of colour j. Distinct words give distinct
sets, and a word sunflower gives a set sunflower with kernel the common letters.
-/

namespace OMA.Helpers

open Finset

theorem count_inj {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → Prop) [DecidablePred p]
    (k : ℕ) (hp : Fintype.card {i // p i} = k) :
    (univ.filter (fun c : ι → Fin k => ∀ x y, p x → p y → c x = c y → x = y)).card
      = k.factorial * k ^ (Fintype.card ι - k) := by
  classical
  rw [← Fintype.card_subtype]
  have e : {c : ι → Fin k // ∀ x y, p x → p y → c x = c y → x = y} ≃
      ({i // p i} ↪ Fin k) × ({i // ¬ p i} → Fin k) :=
    ((Equiv.piEquivPiSubtypeProd p (fun _ => Fin k)).subtypeEquiv
      (p := fun c => ∀ x y, p x → p y → c x = c y → x = y)
      (q := fun z => Function.Injective z.1) (by
        intro c
        simp only [Equiv.piEquivPiSubtypeProd_apply]
        constructor
        · intro h a b hab
          exact Subtype.ext (h a b a.2 b.2 hab)
        · intro h x y hx hy hxy
          exact congrArg Subtype.val (@h ⟨x, hx⟩ ⟨y, hy⟩ hxy))).trans
    (Equiv.prodSubtypeFstEquivSubtypeProd.trans
      (Equiv.prodCongr (Equiv.subtypeInjectiveEquivEmbedding _ _) (Equiv.refl _)))
  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_embedding_eq, Fintype.card_fun,
    Fintype.card_subtype_compl, hp, Fintype.card_fin, Nat.descFactorial_self]

theorem pow_le_three_pow_mul_factorial (k : ℕ) : k ^ k ≤ 3 ^ k * k.factorial := by
  have h1 : ((k : ℝ) ^ k / k.factorial) ≤ Real.exp k :=
    Real.pow_div_factorial_le_exp (k : ℝ) (by positivity) k
  have h2 : Real.exp (k : ℝ) ≤ 3 ^ k := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le
      (Real.exp_one_lt_d9.le.trans (by norm_num)) k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have h3 : (k : ℝ) ^ k ≤ 3 ^ k * k.factorial := by
    rw [div_le_iff₀ hf] at h1
    nlinarith
  exact_mod_cast h3

theorem exists_coloring (k : ℕ) (hk : 0 < k) (F : Finset (Finset ℕ))
    (hF : ∀ A ∈ F, A.card = k) :
    ∃ g : ℕ → Fin k, F.card ≤ 3 ^ k *
      (F.filter (fun A => ∀ x ∈ A, ∀ y ∈ A, g x = g y → x = y)).card := by
  set U : Finset ℕ := F.biUnion id with hU
  have hsub : ∀ A ∈ F, A ⊆ U := fun A hA x hx => mem_biUnion.mpr ⟨A, hA, hx⟩
  let ext : ({x // x ∈ U} → Fin k) → ℕ → Fin k :=
    fun c x => if h : x ∈ U then c ⟨x, h⟩ else ⟨0, hk⟩
  have hcount : ∀ A ∈ F, (univ.filter (fun c : {x // x ∈ U} → Fin k =>
      ∀ x ∈ A, ∀ y ∈ A, ext c x = ext c y → x = y)).card
        = k.factorial * k ^ (U.card - k) := by
    intro A hA
    have hp : Fintype.card {i : {x // x ∈ U} // i.1 ∈ A} = k := by
      rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtype (fun {x} hx => hsub A hA hx)),
        Fintype.card_coe, hF A hA]
    have := count_inj (fun i : {x // x ∈ U} => i.1 ∈ A) k hp
    rw [Fintype.card_coe] at this
    rw [← this]
    congr 1
    apply Finset.filter_congr
    intro c _
    constructor
    · intro h x y hx hy hxy
      apply Subtype.ext
      apply h x.1 hx y.1 hy
      simp only [ext, dif_pos x.2, dif_pos y.2]
      exact hxy
    · intro h x hx y hy hxy
      have hxU := hsub A hA hx
      have hyU := hsub A hA hy
      simp only [ext, dif_pos hxU, dif_pos hyU] at hxy
      exact congrArg Subtype.val (h ⟨x, hxU⟩ ⟨y, hyU⟩ hx hy hxy)
  have hdc : ∑ c : {x // x ∈ U} → Fin k,
      (F.filter (fun A => ∀ x ∈ A, ∀ y ∈ A, ext c x = ext c y → x = y)).card
        = F.card * (k.factorial * k ^ (U.card - k)) := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm, Finset.card_eq_sum_ones F, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro A hA
    rw [← Finset.card_filter, hcount A hA, one_mul]
  by_contra hcon
  push Not at hcon
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hlt : ∑ c : {x // x ∈ U} → Fin k, 3 ^ k *
      (F.filter (fun A => ∀ x ∈ A, ∀ y ∈ A, ext c x = ext c y → x = y)).card
        < ∑ c : {x // x ∈ U} → Fin k, F.card := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact Finset.univ_nonempty
    · intro c _
      exact hcon (ext c)
  rw [← Finset.mul_sum, hdc, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_coe, Fintype.card_fin, smul_eq_mul] at hlt
  rcases F.eq_empty_or_nonempty with hE | ⟨A, hA⟩
  · subst hE
    simp at hlt
  have hkU : k ≤ U.card := (hF A hA) ▸ card_le_card (hsub A hA)
  obtain ⟨d, hd⟩ : ∃ d, U.card = k + d := ⟨U.card - k, by omega⟩
  rw [hd, Nat.add_sub_cancel_left, pow_add] at hlt
  have hle := pow_le_three_pow_mul_factorial k
  have key : k ^ k * k ^ d * F.card ≤ 3 ^ k * (F.card * (k.factorial * k ^ d)) := by
    calc k ^ k * k ^ d * F.card ≤ 3 ^ k * k.factorial * k ^ d * F.card := by gcongr
      _ = 3 ^ k * (F.card * (k.factorial * k ^ d)) := by ring
  exact absurd hlt (not_lt.mpr key)

end OMA.Helpers

open Finset in
theorem OMA.solution : OMA.R_Erdos535_erdos_535_R2_H1_R1.H2 := by
  unfold OMA.R_Erdos535_erdos_535_R2_H1_R1.H2
  intro r k hk F hF hfree
  obtain ⟨g, hg⟩ := OMA.Helpers.exists_coloring k hk F hF
  set S := F.filter (fun A => ∀ x ∈ A, ∀ y ∈ A, g x = g y → x = y) with hS
  set M := (F.biUnion id).sup id + 1 with hM
  have hMpos : 0 < M := Nat.succ_pos _
  have hlt : ∀ A ∈ F, ∀ x ∈ A, x < M := by
    intro A hA x hx
    have hx' : x ∈ F.biUnion id := mem_biUnion.mpr ⟨A, hA, hx⟩
    have := Finset.le_sup (f := id) hx'
    simp only [id] at this
    omega
  let enc : Finset ℕ → Fin k → Fin M := fun A j =>
    ⟨((A.filter (fun x => g x = j)).sum id) % M, Nat.mod_lt _ hMpos⟩
  have hF1 : ∀ A ∈ S, ∀ x ∈ A, (enc A (g x)).val = x := by
    intro A hA x hx
    rw [mem_filter] at hA
    have hfil : A.filter (fun y => g y = g x) = {x} := by
      ext y
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨hy, hgy⟩
        exact hA.2 y hy x hx hgy
      · rintro rfl
        exact ⟨hx, rfl⟩
    show ((A.filter (fun y => g y = g x)).sum id) % M = x
    rw [hfil, sum_singleton, id, Nat.mod_eq_of_lt (hlt A hA.1 x hx)]
  have hF2 : ∀ A ∈ S, ∀ j : Fin k, ∃ x ∈ A, g x = j := by
    intro A hA j
    rw [mem_filter] at hA
    have hcard : (A.image g).card = k := by
      rw [card_image_of_injOn (fun x hx y hy h => hA.2 x hx y hy h), hF A hA.1]
    have huniv : A.image g = univ := eq_univ_of_card _ (by rw [hcard, Fintype.card_fin])
    have hj : j ∈ A.image g := by
      rw [huniv]
      exact mem_univ j
    exact mem_image.mp hj
  have hF3 : ∀ A ∈ S, ∀ j : Fin k, (enc A j).val ∈ A := by
    intro A hA j
    obtain ⟨x, hx, rfl⟩ := hF2 A hA j
    rw [hF1 A hA x hx]
    exact hx
  have hinj : Set.InjOn enc S := by
    intro A hA B hB hAB
    have hA' : A ∈ S := hA
    have hB' : B ∈ S := hB
    ext x
    constructor
    · intro hx
      have := hF3 B hB' (g x)
      rwa [← hAB, hF1 A hA' x hx] at this
    · intro hx
      have := hF3 A hA' (g x)
      rwa [hAB, hF1 B hB' x hx] at this
  refine ⟨M, S.image enc, ?_, ?_⟩
  · rw [card_image_of_injOn hinj]
    exact hg
  · intro w hw hcoord a b
    by_contra hab
    choose A hAS hAw using fun i => mem_image.mp (hw i)
    obtain ⟨j0, hj0⟩ : ∃ j, w a j ≠ w b j := by
      by_contra h
      push Not at h
      exact hab (funext h)
    have hinjj0 : Function.Injective (fun i => w i j0) := by
      rcases hcoord j0 with h | h
      · exact absurd (h a b) hj0
      · exact h
    have hAinj : Function.Injective A := by
      intro i i' h
      apply hinjj0
      show w i j0 = w i' j0
      rw [← hAw i, ← hAw i', h]
    have hkey : ∀ i i', i ≠ i' → ∀ x, x ∈ A i → x ∈ A i' → ∀ c, x ∈ A c := by
      intro i i' hii' x hxi hxi' c
      have e1 : (w i (g x)).val = x := by
        rw [← hAw i]
        exact hF1 _ (hAS i) x hxi
      have e2 : (w i' (g x)).val = x := by
        rw [← hAw i']
        exact hF1 _ (hAS i') x hxi'
      have heq : w i (g x) = w i' (g x) := Fin.ext (e1.trans e2.symm)
      rcases hcoord (g x) with h | h
      · have e3 : (w c (g x)).val = x := by
          rw [h c i]
          exact e1
        rw [← e3, ← hAw c]
        exact hF3 _ (hAS c) (g x)
      · exact absurd (h heq) hii'
    have hab' : a ≠ b := fun h => hab (congrArg w h)
    apply hfree
    refine ⟨univ.image A, ?_, ?_, A a ∩ A b, ?_⟩
    · intro X hX
      obtain ⟨i, _, rfl⟩ := mem_image.mp hX
      exact (mem_filter.mp (hAS i)).1
    · rw [card_image_of_injective _ hAinj, card_univ, Fintype.card_fin]
    · intro X hX Y hY hXY
      obtain ⟨i, _, rfl⟩ := mem_image.mp hX
      obtain ⟨i', _, rfl⟩ := mem_image.mp hY
      have hii' : i ≠ i' := fun h => hXY (congrArg A h)
      ext x
      simp only [mem_inter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨hkey i i' hii' x h1 h2 a, hkey i i' hii' x h1 h2 b⟩
      · rintro ⟨h1, h2⟩
        exact ⟨hkey a b hab' x h1 h2 i, hkey a b hab' x h1 h2 i'⟩
