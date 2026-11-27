import FormalConjectures.Arxiv.«2605.02731».DeanCycles
import Mathlib

open SimpleGraph

namespace OMA.Helpers

variable {V : Type*}

/-- `ZC G`: `G` has a cycle (a duplicate-free cyclic list of vertices) of length divisible by three. -/
def ZC (G : SimpleGraph V) : Prop :=
  ∃ (c : V) (l : List V), (c :: l).Nodup ∧ List.IsChain G.Adj (c :: (l ++ [c])) ∧ 3 ∣ l.length + 1

theorem exists_walk_of_chain {G : SimpleGraph V} {c : V} {l : List V}
    (hch : List.IsChain G.Adj (c :: (l ++ [c]))) :
    ∃ w : G.Walk c c, w.support = c :: (l ++ [c]) := by
  have hne : (c :: (l ++ [c])) ≠ [] := by simp
  have h2 : (c :: (l ++ [c])).getLast hne = c := by simp
  have h1 : (c :: (l ++ [c])).head hne = c := by simp
  exact ⟨(SimpleGraph.Walk.ofSupport (c :: (l ++ [c])) hne hch).copy h1 h2, by
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_ofSupport]⟩

theorem ZC.exists_cycle {G : SimpleGraph V} (h : ZC G) : ∃ m ∈ G.cycleLengths, 3 ∣ m := by
  obtain ⟨c, l, hnd, hch, hdiv⟩ := h
  obtain ⟨w, hw⟩ := exists_walk_of_chain hch
  have hlen : w.length = l.length + 1 := by
    have := w.length_support
    rw [hw] at this
    simp at this
    omega
  have h3 : 3 ≤ l.length + 1 := Nat.le_of_dvd (by omega) hdiv
  refine ⟨l.length + 1, ⟨c, w, ?_, hlen⟩, hdiv⟩
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  refine ⟨?_, by omega⟩
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_tail_of_not_nil]
  · rw [hw, List.tail_cons]
    have : (l ++ [c]).Perm (c :: l) := List.perm_append_singleton c l
    exact this.nodup_iff.mpr hnd
  · rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega

theorem ZC.mono {G H : SimpleGraph V} (hle : H ≤ G) (h : ZC H) : ZC G := by
  obtain ⟨c, l, hnd, hch, hdiv⟩ := h
  exact ⟨c, l, hnd, hch.imp (fun _ _ hab => hle hab), hdiv⟩

/-- rotation of a cyclic chain so that it starts at a given vertex -/
theorem rot {R : V → V → Prop} {c x : V} {l : List V} (hnd : (c :: l).Nodup)
    (hch : List.IsChain R (c :: (l ++ [c]))) (hx : x ∈ l) :
    ∃ l', (x :: l').Nodup ∧ List.IsChain R (x :: (l' ++ [x])) ∧ l'.length = l.length := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hx
  refine ⟨l₂ ++ c :: l₁, ?_, ?_, ?_⟩
  · have : (x :: (l₂ ++ c :: l₁)).Perm (c :: (l₁ ++ x :: l₂)) := by
      have h1 : (x :: (l₂ ++ c :: l₁)).Perm ((c :: l₁) ++ (x :: l₂)) := by
        rw [← List.cons_append]
        exact List.perm_append_comm
      simpa using h1
    exact this.nodup_iff.mpr hnd
  · have h1 : List.IsChain R ((c :: l₁) ++ x :: (l₂ ++ [c])) := by simpa using hch
    rw [List.isChain_split] at h1
    have h2 : List.IsChain R ((x :: l₂) ++ c :: (l₁ ++ [x])) := by
      rw [List.isChain_split]
      exact ⟨by simpa using h1.2, by simpa using h1.1⟩
    simpa using h2
  · simp
    omega


/-- delete all edges at the vertices of `D`, and add the edges `c–w` for `w ∈ W` -/
def surg (G : SimpleGraph V) (D : Set V) (c : V) (W : Set V) : SimpleGraph V where
  Adj u v := (G.Adj u v ∧ u ∉ D ∧ v ∉ D) ∨ (u = c ∧ v ∈ W ∧ u ≠ v) ∨ (v = c ∧ u ∈ W ∧ u ≠ v)
  symm := ⟨by
    rintro u v (⟨h, hu, hv⟩ | ⟨h, hw, hne⟩ | ⟨h, hw, hne⟩)
    · exact Or.inl ⟨h.symm, hv, hu⟩
    · exact Or.inr (Or.inr ⟨h, hw, hne.symm⟩)
    · exact Or.inr (Or.inl ⟨h, hw, hne.symm⟩)⟩
  loopless := ⟨by
    rintro u (⟨h, -, -⟩ | ⟨-, -, hne⟩ | ⟨-, -, hne⟩)
    · exact G.irrefl h
    · exact hne rfl
    · exact hne rfl⟩

theorem surg_adj {G : SimpleGraph V} {D W : Set V} {c u v : V} :
    (surg G D c W).Adj u v ↔
      (G.Adj u v ∧ u ∉ D ∧ v ∉ D) ∨ (u = c ∧ v ∈ W ∧ u ≠ v) ∨ (v = c ∧ u ∈ W ∧ u ≠ v) := Iff.rfl

theorem chain_pred {R : V → V → Prop} : ∀ {a : V} {L : List V}, List.IsChain R (a :: L) →
    ∀ v ∈ L, ∃ u, R u v
  | a, [], _, v, hv => by simp at hv
  | a, b :: L, h, v, hv => by
    rw [List.isChain_cons_cons] at h
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact ⟨a, h.1⟩
    · exact chain_pred h.2 v hv'

theorem cyc_chain_iff {R : V → V → Prop} {c w₁ wk : V} {m : List V} :
    List.IsChain R (c :: ((w₁ :: (m ++ [wk])) ++ [c])) ↔
      R c w₁ ∧ List.IsChain R (w₁ :: (m ++ [wk])) ∧ R wk c := by
  have : c :: ((w₁ :: (m ++ [wk])) ++ [c]) = c :: w₁ :: (m ++ wk :: c :: []) := by simp
  rw [this, List.isChain_cons_cons, ← List.cons_append, List.isChain_append_cons_cons]
  simp

/-- lifting lemma: a cycle of the surgered graph gives a cycle of `G` of the same length mod 3 -/
theorem ZC_of_surg {G : SimpleGraph V} {D W : Set V} {c d : V} {S : List V}
    (hS : List.IsChain G.Adj (c :: (S ++ [d]))) (hnd : (c :: (S ++ [d])).Nodup)
    (hlen : 3 ∣ S.length + 1) (hSD : ∀ v ∈ S ++ [d], v ∈ D)
    (hW : ∀ w ∈ W, G.Adj d w ∧ w ∉ D)
    (h : ZC (surg G D c W)) : ZC G := by
  obtain ⟨c₀, l, hnd', hch, hdiv⟩ := h
  have hcS : c ∉ S ++ [d] := (List.nodup_cons.mp hnd).1
  have hiso : ∀ v ∈ S ++ [d], ∀ u, ¬ (surg G D c W).Adj u v := by
    intro v hv u huv
    have hvD := hSD v hv
    have hvc : v ≠ c := by rintro rfl; exact hcS hv
    rcases huv with ⟨-, -, hv'⟩ | ⟨-, hvW, -⟩ | ⟨hvc', -, -⟩
    · exact hv' hvD
    · exact (hW v hvW).2 hvD
    · exact hvc hvc'
  have hGadj : ∀ u v, (surg G D c W).Adj u v → u ≠ c → v ≠ c → G.Adj u v := by
    rintro u v (⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩) hu hv
    · exact h
    · exact absurd h hu
    · exact absurd h hv
  have hcadj : ∀ v, (surg G D c W).Adj c v → G.Adj c v ∨ G.Adj d v := by
    rintro v (⟨h, -, -⟩ | ⟨-, hw, -⟩ | ⟨h, -, hne⟩)
    · exact Or.inl h
    · exact Or.inr (hW v hw).1
    · exact absurd h.symm hne
  by_cases hc : c ∈ c₀ :: l
  · obtain ⟨l', hnd'', hch', hlen'⟩ : ∃ l', (c :: l').Nodup ∧
        List.IsChain (surg G D c W).Adj (c :: (l' ++ [c])) ∧ l'.length = l.length := by
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact ⟨l, hnd', hch, rfl⟩
      · exact rot hnd' hch hc'
    rw [← hlen'] at hdiv
    -- decompose l'
    obtain ⟨w₁, l'', rfl⟩ : ∃ w₁ l'', l' = w₁ :: l'' := by
      cases l' with
      | nil => simp at hdiv
      | cons w₁ l'' => exact ⟨w₁, l'', rfl⟩
    obtain ⟨m, wk, rfl⟩ : ∃ m wk, l'' = m ++ [wk] := by
      rcases List.eq_nil_or_concat' l'' with rfl | ⟨m, wk, rfl⟩
      · simp at hdiv
      · exact ⟨m, wk, rfl⟩
    rw [cyc_chain_iff] at hch'
    obtain ⟨h1, hM, hk⟩ := hch'
    have hcM : c ∉ w₁ :: (m ++ [wk]) := (List.nodup_cons.mp hnd'').1
    have hMnd : (w₁ :: (m ++ [wk])).Nodup := (List.nodup_cons.mp hnd'').2
    have hMG : List.IsChain G.Adj (w₁ :: (m ++ [wk])) := by
      refine hM.imp_of_mem_imp ?_
      intro a b ha hb hab
      exact hGadj a b hab (by rintro rfl; exact hcM ha) (by rintro rfl; exact hcM hb)
    have hdisj : ∀ v ∈ w₁ :: (m ++ [wk]), v ∉ S ++ [d] := by
      intro v hv hvS
      obtain ⟨u, hu⟩ := chain_pred (List.IsChain.cons_cons h1 hM) v hv
      exact hiso v hvS u hu
    have hwkmem : wk ∈ w₁ :: (m ++ [wk]) := by simp
    have hw1mem : w₁ ∈ w₁ :: (m ++ [wk]) := by simp
    have hd_mem : d ∈ S ++ [d] := by simp
    have hk' : G.Adj wk c ∨ G.Adj wk d := by
      rcases hcadj wk hk.symm with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    rcases hcadj w₁ h1 with h1G | h1d <;> rcases hk' with hkG | hkd
    · -- both old
      exact ⟨c, w₁ :: (m ++ [wk]), hnd'', cyc_chain_iff.mpr ⟨h1G, hMG, hkG⟩, hdiv⟩
    · -- last edge new
      refine ⟨c, (w₁ :: (m ++ [wk])) ++ (S ++ [d]).reverse, ?_, ?_, ?_⟩
      · rw [List.nodup_cons] at hnd ⊢
        refine ⟨?_, ?_⟩
        · intro hmem
          rcases List.mem_append.mp hmem with h | h
          · exact hcM h
          · exact hnd.1 (List.mem_reverse.mp h)
        · rw [List.nodup_append]
          refine ⟨hMnd, List.nodup_reverse.mpr hnd.2, ?_⟩
          intro a ha b hb hab
          subst hab
          exact hdisj a ha (List.mem_reverse.mp hb)
      · have hrev : List.IsChain G.Adj ((c :: (S ++ [d])).reverse) := by
          rw [List.isChain_reverse]
          exact hS.imp (fun _ _ hab => hab.symm)
        have e1 : c :: ((w₁ :: (m ++ [wk])) ++ (S ++ [d]).reverse ++ [c])
            = (c :: w₁ :: m) ++ wk :: ((c :: (S ++ [d])).reverse) := by simp
        rw [e1, List.isChain_split]
        refine ⟨?_, ?_⟩
        · have : (c :: w₁ :: m) ++ [wk] = c :: w₁ :: (m ++ [wk]) := by simp
          rw [this]
          exact List.IsChain.cons_cons h1G hMG
        · have e2 : (c :: (S ++ [d])).reverse = d :: (S.reverse ++ [c]) := by simp
          rw [e2] at hrev ⊢
          exact List.IsChain.cons_cons hkd hrev
      · simp only [List.length_append, List.length_cons, List.length_reverse, List.length_nil] at hdiv ⊢
        omega
    · -- first edge new
      refine ⟨c, (S ++ [d]) ++ (w₁ :: (m ++ [wk])), ?_, ?_, ?_⟩
      · rw [List.nodup_cons] at hnd ⊢
        refine ⟨?_, ?_⟩
        · simp only [List.mem_append, not_or] at hcS ⊢
          exact ⟨hcS, by simpa using hcM⟩
        · rw [List.nodup_append]
          refine ⟨hnd.2, hMnd, ?_⟩
          intro a ha b hb hab
          subst hab
          exact hdisj a hb ha
      · have e1 : c :: ((S ++ [d]) ++ (w₁ :: (m ++ [wk])) ++ [c])
            = (c :: S) ++ d :: w₁ :: (m ++ wk :: c :: []) := by simp
        rw [e1, List.isChain_append_cons_cons]
        refine ⟨by simpa using hS, h1d.symm.symm, ?_⟩
        have e2 : w₁ :: (m ++ wk :: c :: []) = (w₁ :: m) ++ wk :: c :: [] := by simp
        rw [e2, List.isChain_append_cons_cons]
        exact ⟨by simpa using hMG, hkG, List.isChain_singleton c⟩
      · simp only [List.length_append, List.length_cons, List.length_nil] at hdiv ⊢
        omega
    · -- both new
      refine ⟨d, w₁ :: (m ++ [wk]), ?_, cyc_chain_iff.mpr ⟨h1d, hMG, hkd⟩, hdiv⟩
      rw [List.nodup_cons]
      exact ⟨fun hd' => hdisj d hd' hd_mem, hMnd⟩
  · refine ⟨c₀, l, hnd', ?_, hdiv⟩
    refine hch.imp_of_mem_imp ?_
    intro a b ha hb hab
    have hmem : ∀ x, x ∈ c₀ :: (l ++ [c₀]) → x ∈ c₀ :: l := by
      intro x hx
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx ⊢
      tauto
    exact hGadj a b hab (by rintro rfl; exact hc (hmem _ ha)) (by rintro rfl; exact hc (hmem _ hb))


/-- at least three neighbours -/
def Big (G : SimpleGraph V) (v : V) : Prop :=
  ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ G.Adj v a ∧ G.Adj v b ∧ G.Adj v c

/-- one or two neighbours -/
def Low (G : SimpleGraph V) (v : V) : Prop := (∃ w, G.Adj v w) ∧ ¬ Big G v

/-- the statement proved by induction -/
def Good (G : SimpleGraph V) : Prop :=
  ZC G ∨ (∀ v a b, G.Adj v a → G.Adj v b → a = b) ∨ ∀ y₁ y₂ : V, ∃ v, Low G v ∧ v ≠ y₁ ∧ v ≠ y₂

theorem Big.map {G H : SimpleGraph V} {v : V} (f : V → V)
    (hinj : ∀ u₁ u₂, G.Adj v u₁ → G.Adj v u₂ → f u₁ = f u₂ → u₁ = u₂)
    (hadj : ∀ u, G.Adj v u → H.Adj v (f u)) (h : Big G v) : Big H v := by
  obtain ⟨n₁, n₂, n₃, h12, h13, h23, a1, a2, a3⟩ := h
  exact ⟨f n₁, f n₂, f n₃, fun h => h12 (hinj _ _ a1 a2 h), fun h => h13 (hinj _ _ a1 a3 h),
    fun h => h23 (hinj _ _ a2 a3 h), hadj _ a1, hadj _ a2, hadj _ a3⟩

theorem Big.mono {G H : SimpleGraph V} {v : V} (hadj : ∀ u, G.Adj v u → H.Adj v u) (h : Big G v) :
    Big H v :=
  h.map id (fun _ _ _ _ h => h) hadj

theorem no_tri {G : SimpleGraph V} (hZ : ¬ ZC G) {u v w : V} (h1 : G.Adj u v) (h2 : G.Adj v w)
    (h3 : G.Adj w u) : False :=
  hZ ⟨u, [v, w], by simp [h1.ne, h2.ne, h3.ne.symm], by simp [h1, h2, h3], by norm_num⟩

theorem no_hex {G : SimpleGraph V} (hZ : ¬ ZC G) {v₁ v₂ v₃ v₄ v₅ v₆ : V}
    (hnd : [v₁, v₂, v₃, v₄, v₅, v₆].Nodup)
    (h1 : G.Adj v₁ v₂) (h2 : G.Adj v₂ v₃) (h3 : G.Adj v₃ v₄) (h4 : G.Adj v₄ v₅)
    (h5 : G.Adj v₅ v₆) (h6 : G.Adj v₆ v₁) : False :=
  hZ ⟨v₁, [v₂, v₃, v₄, v₅, v₆], hnd, by simp [h1, h2, h3, h4, h5, h6], by norm_num⟩

/-- delete one edge -/
def delE (G : SimpleGraph V) (u v : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ ¬ (a = u ∧ b = v) ∧ ¬ (a = v ∧ b = u)
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun h' => h.2.2 ⟨h'.2, h'.1⟩, fun h' => h.2.1 ⟨h'.2, h'.1⟩⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

theorem delE_adj {G : SimpleGraph V} {u v a b : V} :
    (delE G u v).Adj a b ↔ G.Adj a b ∧ ¬ (a = u ∧ b = v) ∧ ¬ (a = v ∧ b = u) := Iff.rfl

theorem delE_lt {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : delE G u v < G := by
  refine lt_of_le_of_ne (fun a b hab => hab.1) ?_
  intro heq
  have h' : (delE G u v).Adj u v := by
    rw [heq]
    exact h
  exact h'.2.1 ⟨rfl, rfl⟩

theorem delE_adj_of_ne {G : SimpleGraph V} {u v w t : V} (hu : w ≠ u) (hv : w ≠ v) :
    (delE G u v).Adj w t ↔ G.Adj w t := by
  rw [delE_adj]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, fun h' => hu h'.1, fun h' => hv h'.1⟩

theorem low_delE_of_ne {G : SimpleGraph V} {u v w : V} (hu : w ≠ u) (hv : w ≠ v) :
    Low (delE G u v) w ↔ Low G w := by
  unfold Low Big
  simp only [delE_adj_of_ne hu hv]

/-- the hypotheses of the inductive step -/
structure Ctx (G : SimpleGraph V) : Prop where
  hZ : ¬ ZC G
  IHs : ∀ H : SimpleGraph V, H < G → Good H
  IHc : ∀ H : SimpleGraph V, H.support ⊂ G.support → Good H

theorem Ctx.sub {G : SimpleGraph V} (C : Ctx G) {H : SimpleGraph V} (hlt : H < G) {v a b : V}
    (ha : H.Adj v a) (hb : H.Adj v b) (hab : a ≠ b) (z₁ z₂ : V) :
    ∃ u, Low H u ∧ u ≠ z₁ ∧ u ≠ z₂ := by
  rcases C.IHs H hlt with h | h | h
  · exact absurd (h.mono hlt.le) C.hZ
  · exact absurd (h v a b ha hb) hab
  · exact h z₁ z₂

theorem Ctx.cut {G : SimpleGraph V} (C : Ctx G) {H : SimpleGraph V} (hs : H.support ⊂ G.support)
    (hZH : ¬ ZC H) {v a b : V}
    (ha : H.Adj v a) (hb : H.Adj v b) (hab : a ≠ b) (z₁ z₂ : V) :
    ∃ u, Low H u ∧ u ≠ z₁ ∧ u ≠ z₂ := by
  rcases C.IHc H hs with h | h | h
  · exact absurd h hZH
  · exact absurd (h v a b ha hb) hab
  · exact h z₁ z₂

theorem big_of_not_low {G : SimpleGraph V} {v u : V} (h : G.Adj v u) (hl : ¬ Low G v) : Big G v := by
  by_contra hB
  exact hl ⟨⟨u, h⟩, hB⟩

/-- Step 1: deleting an edge leaves a Low vertex outside any two given vertices -/
theorem Ctx.del {G : SimpleGraph V} (C : Ctx G) {β : V} (hβ : Big G β) {u v : V} (huv : G.Adj u v)
    (z₁ z₂ : V) : ∃ w, Low (delE G u v) w ∧ w ≠ z₁ ∧ w ≠ z₂ := by
  obtain ⟨n₁, n₂, n₃, h12, h13, h23, a1, a2, a3⟩ := hβ
  have huv' : u ≠ v := huv.ne
  have key : ∀ n, G.Adj β n → ¬ (delE G u v).Adj β n → (β = u ∧ n = v) ∨ (β = v ∧ n = u) := by
    intro n hn hnot
    by_contra hcon
    exact hnot ⟨hn, fun h => hcon (Or.inl h), fun h => hcon (Or.inr h)⟩
  by_cases e1 : (delE G u v).Adj β n₁
  · by_cases e2 : (delE G u v).Adj β n₂
    · exact C.sub (delE_lt huv) e1 e2 h12 z₁ z₂
    · have e3 : (delE G u v).Adj β n₃ := by
        by_contra e3
        rcases key n₂ a2 e2 with ⟨hb, hn⟩ | ⟨hb, hn⟩ <;> rcases key n₃ a3 e3 with ⟨hb', hn'⟩ | ⟨hb', hn'⟩
        · exact h23 (hn.trans hn'.symm)
        · exact huv' (hb.symm.trans hb')
        · exact huv' (hb'.symm.trans hb)
        · exact h23 (hn.trans hn'.symm)
      exact C.sub (delE_lt huv) e1 e3 h13 z₁ z₂
  · have e2 : (delE G u v).Adj β n₂ := by
      by_contra e2
      rcases key n₁ a1 e1 with ⟨hb, hn⟩ | ⟨hb, hn⟩ <;> rcases key n₂ a2 e2 with ⟨hb', hn'⟩ | ⟨hb', hn'⟩
      · exact h12 (hn.trans hn'.symm)
      · exact huv' (hb.symm.trans hb')
      · exact huv' (hb'.symm.trans hb)
      · exact h12 (hn.trans hn'.symm)
    have e3 : (delE G u v).Adj β n₃ := by
      by_contra e3
      rcases key n₁ a1 e1 with ⟨hb, hn⟩ | ⟨hb, hn⟩ <;> rcases key n₃ a3 e3 with ⟨hb', hn'⟩ | ⟨hb', hn'⟩
      · exact h13 (hn.trans hn'.symm)
      · exact huv' (hb.symm.trans hb')
      · exact huv' (hb'.symm.trans hb)
      · exact h13 (hn.trans hn'.symm)
    exact C.sub (delE_lt huv) e2 e3 h23 z₁ z₂


theorem delE_adj_snd {G : SimpleGraph V} {x a t : V} (hxa : G.Adj x a) :
    (delE G x a).Adj a t ↔ G.Adj a t ∧ t ≠ x := by
  rw [delE_adj]
  constructor
  · exact fun h => ⟨h.1, fun ht => h.2.2 ⟨rfl, ht⟩⟩
  · exact fun h => ⟨h.1, fun h' => hxa.ne h'.1.symm, fun h' => h.2 h'.2⟩

/-- Step 2: structure at a Low vertex `x` and a neighbour `a` of it -/
theorem Ctx.low_struct {G : SimpleGraph V} (C : Ctx G) {y₁ y₂ : V}
    (hlow : ∀ v, Low G v → v = y₁ ∨ v = y₂) {β : V} (hβ : Big G β) {x a : V} (hx : Low G x)
    (hxa : G.Adj x a) :
    (∃ b, G.Adj x b ∧ b ≠ a) ∧
      ∃ a₁ a₂, a₁ ≠ a₂ ∧ a₁ ≠ x ∧ a₂ ≠ x ∧ ∀ u, G.Adj a u ↔ u = x ∨ u = a₁ ∨ u = a₂ := by
  have hgen : ∀ w, Low (delE G x a) w → w ≠ x → w ≠ a → w = y₁ ∨ w = y₂ :=
    fun w hw h1 h2 => hlow w ((low_delE_of_ne h1 h2).mp hw)
  have hxy : x = y₁ ∨ x = y₂ := hlow x hx
  refine ⟨?_, ?_⟩
  · by_contra hno
    push Not at hno
    have hxiso : ¬ Low (delE G x a) x := by
      rintro ⟨⟨w, hw⟩, -⟩
      have := hno w hw.1
      subst this
      exact hw.2.1 ⟨rfl, rfl⟩
    rcases hxy with rfl | rfl
    · obtain ⟨w, hw, hwa, hwy⟩ := C.del hβ hxa a y₂
      by_cases hwx : w = x
      · subst hwx; exact hxiso hw
      · rcases hgen w hw hwx hwa with h | h
        · exact hwx h
        · exact hwy h
    · obtain ⟨w, hw, hwa, hwy⟩ := C.del hβ hxa a y₁
      by_cases hwx : w = x
      · subst hwx; exact hxiso hw
      · rcases hgen w hw hwx hwa with h | h
        · exact hwy h
        · exact hwx h
  · have haL : ¬ Low G a := by
      intro haL
      have hay := hlow a haL
      obtain ⟨w, hw, hw1, hw2⟩ := C.del hβ hxa y₁ y₂
      by_cases hwx : w = x
      · subst hwx
        rcases hxy with h | h
        · exact hw1 h
        · exact hw2 h
      · by_cases hwa : w = a
        · subst hwa
          rcases hay with h | h
          · exact hw1 h
          · exact hw2 h
        · rcases hgen w hw hwx hwa with h | h
          · exact hw1 h
          · exact hw2 h
    obtain ⟨n₁, n₂, n₃, h12, h13, h23, e1, e2, e3⟩ := big_of_not_low hxa.symm haL
    obtain ⟨a₁, a₂, h12', ha1x, ha2x, ea1, ea2⟩ :
        ∃ a₁ a₂, a₁ ≠ a₂ ∧ a₁ ≠ x ∧ a₂ ≠ x ∧ G.Adj a a₁ ∧ G.Adj a a₂ := by
      by_cases h1 : n₁ = x
      · exact ⟨n₂, n₃, h23, fun h => h12 (h1.trans h.symm), fun h => h13 (h1.trans h.symm), e2, e3⟩
      · by_cases h2 : n₂ = x
        · exact ⟨n₁, n₃, h13, h1, fun h => h23 (h2.trans h.symm), e1, e3⟩
        · exact ⟨n₁, n₂, h12, h1, h2, e1, e2⟩
    refine ⟨a₁, a₂, h12', ha1x, ha2x, fun u => ⟨fun hu => ?_, ?_⟩⟩
    · by_contra hcon
      push Not at hcon
      obtain ⟨hux, hu1, hu2⟩ := hcon
      have haB : Big (delE G x a) a :=
        ⟨a₁, a₂, u, h12', fun h => hu1 h.symm, fun h => hu2 h.symm,
          (delE_adj_snd hxa).mpr ⟨ea1, ha1x⟩, (delE_adj_snd hxa).mpr ⟨ea2, ha2x⟩,
          (delE_adj_snd hxa).mpr ⟨hu, hux⟩⟩
      obtain ⟨w, hw, hw1, hw2⟩ := C.del hβ hxa y₁ y₂
      by_cases hwx : w = x
      · subst hwx
        rcases hxy with h | h
        · exact hw1 h
        · exact hw2 h
      · by_cases hwa : w = a
        · subst hwa
          exact hw.2 haB
        · rcases hgen w hw hwx hwa with h | h
          · exact hw1 h
          · exact hw2 h
    · rintro (rfl | rfl | rfl)
      · exact hxa.symm
      · exact ea1
      · exact ea2


theorem Big.exists_ne {G : SimpleGraph V} {v : V} (h : Big G v) (p q : V) :
    ∃ u, G.Adj v u ∧ u ≠ p ∧ u ≠ q := by
  obtain ⟨n₁, n₂, n₃, h12, h13, h23, e1, e2, e3⟩ := h
  by_cases h1 : n₁ = p ∨ n₁ = q
  · by_cases h2 : n₂ = p ∨ n₂ = q
    · refine ⟨n₃, e3, ?_, ?_⟩ <;> grind
    · exact ⟨n₂, e2, fun h => h2 (Or.inl h), fun h => h2 (Or.inr h)⟩
  · exact ⟨n₁, e1, fun h => h1 (Or.inl h), fun h => h1 (Or.inr h)⟩

/-- Lemma C: contraction along the path `c – a – x – b` -/
theorem Ctx.lemC {G : SimpleGraph V} (C : Ctx G) {x y a b c c' b₁ b₂ : V}
    (hlow : ∀ v, Low G v → v = x ∨ v = y)
    (h2c : ∀ v u, G.Adj v u → ∃ u', G.Adj v u' ∧ u' ≠ u)
    (Nx : ∀ u, G.Adj x u ↔ u = a ∨ u = b)
    (Na : ∀ u, G.Adj a u ↔ u = x ∨ u = c ∨ u = c')
    (Nb : ∀ u, G.Adj b u ↔ u = x ∨ u = b₁ ∨ u = b₂)
    (hab : a ≠ b) (hb12 : b₁ ≠ b₂)
    (hcx : c ≠ x) (hc'x : c' ≠ x) (hb1x : b₁ ≠ x) (hb2x : b₂ ≠ x)
    (hc : ∀ w, (w = b₁ ∨ w = b₂) → w ≠ c → ¬ G.Adj c w) :
    (c = b₁ ∨ c = b₂) ∧ c ≠ y ∧ c' ≠ y ∧
      (∀ u₁ u₂, G.Adj c u₁ → G.Adj c u₂ → u₁ ≠ a → u₁ ≠ b → u₂ ≠ a → u₂ ≠ b → u₁ = u₂) ∧
      ((c' = b₁ ∨ c' = b₂) → ∀ u₁ u₂, G.Adj c' u₁ → G.Adj c' u₂ →
        u₁ ≠ a → u₁ ≠ b → u₂ ≠ a → u₂ ≠ b → u₁ = u₂) := by
  have hxa : G.Adj x a := (Nx a).mpr (Or.inl rfl)
  have hxb : G.Adj x b := (Nx b).mpr (Or.inr rfl)
  have hac : G.Adj a c := (Na c).mpr (Or.inr (Or.inl rfl))
  have hac' : G.Adj a c' := (Na c').mpr (Or.inr (Or.inr rfl))
  have hbb1 : G.Adj b b₁ := (Nb b₁).mpr (Or.inr (Or.inl rfl))
  have hbb2 : G.Adj b b₂ := (Nb b₂).mpr (Or.inr (Or.inr rfl))
  have hnab : ¬ G.Adj a b := fun h => no_tri C.hZ hxa h hxb.symm
  have hca : c ≠ a := hac.ne.symm
  have hcb : c ≠ b := by rintro rfl; exact hnab hac
  have hc'a : c' ≠ a := hac'.ne.symm
  have hc'b : c' ≠ b := by rintro rfl; exact hnab hac'
  have hb1a : b₁ ≠ a := by rintro rfl; exact hnab hbb1.symm
  have hb2a : b₂ ≠ a := by rintro rfl; exact hnab hbb2.symm
  have hb1b : b₁ ≠ b := hbb1.ne.symm
  have hb2b : b₂ ≠ b := hbb2.ne.symm
  have hxa' : x ≠ a := hxa.ne
  have hxb' : x ≠ b := hxb.ne
  have hncx : ∀ t, G.Adj t x → t = a ∨ t = b := fun t ht => (Nx t).mp ht.symm
  have hnca : ∀ t, G.Adj t a → t = x ∨ t = c ∨ t = c' := fun t ht => (Na t).mp ht.symm
  have hncb : ∀ t, G.Adj t b → t = x ∨ t = b₁ ∨ t = b₂ := fun t ht => (Nb t).mp ht.symm
  -- the surgered graph
  let D : Set V := {x, a, b}
  let W : Set V := {w | (w = b₁ ∨ w = b₂) ∧ w ≠ c}
  have hDmem : ∀ t, t ∈ D ↔ t = x ∨ t = a ∨ t = b := by
    intro t; simp [D]
  have hcut : ∀ u v, G.Adj u v → u ≠ x → u ≠ a → u ≠ b → v ≠ x → v ≠ a → v ≠ b →
      (surg G D c W).Adj u v := by
    intro u v huv h1 h2 h3 h4 h5 h6
    refine Or.inl ⟨huv, ?_, ?_⟩
    · rw [hDmem]; tauto
    · rw [hDmem]; tauto
  have hnew : ∀ w, (w = b₁ ∨ w = b₂) → w ≠ c → (surg G D c W).Adj c w := by
    intro w hw hwc
    exact Or.inr (Or.inl ⟨rfl, ⟨hw, hwc⟩, hwc.symm⟩)
  have hHel : ∀ u v, (surg G D c W).Adj u v →
      (G.Adj u v ∧ u ≠ x ∧ u ≠ a ∧ u ≠ b ∧ v ≠ x ∧ v ≠ a ∧ v ≠ b) ∨
      (u = c ∧ (v = b₁ ∨ v = b₂) ∧ v ≠ c) ∨ (v = c ∧ (u = b₁ ∨ u = b₂) ∧ u ≠ c) := by
    rintro u v (⟨h, hu, hv⟩ | ⟨h, hw, -⟩ | ⟨h, hw, -⟩)
    · rw [hDmem] at hu hv
      left
      refine ⟨h, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> tauto
    · exact Or.inr (Or.inl ⟨h, hw.1, hw.2⟩)
    · exact Or.inr (Or.inr ⟨h, hw.1, hw.2⟩)
  have hZH : ¬ ZC (surg G D c W) := by
    intro h
    refine C.hZ (ZC_of_surg (S := [a, x]) (d := b) ?_ ?_ (by norm_num) ?_ ?_ h)
    · simp [hac.symm, hxa.symm, hxb]
    · simp [hca, hcx, hcb, hxa'.symm, hab, hxb']
    · intro v hv
      rw [hDmem]
      simp at hv
      tauto
    · rintro w ⟨hw, hwc⟩
      refine ⟨by rcases hw with rfl | rfl <;> assumption, ?_⟩
      rw [hDmem]
      rcases hw with rfl | rfl <;> tauto
  have hsupp : (surg G D c W).support ⊂ G.support := by
    refine ⟨?_, fun h => ?_⟩
    · rintro v ⟨u, hu⟩
      rcases hHel v u hu with h | h | h
      · exact ⟨u, h.1⟩
      · exact ⟨a, h.1 ▸ hac.symm⟩
      · rcases h.2.1 with rfl | rfl
        · exact ⟨b, hbb1.symm⟩
        · exact ⟨b, hbb2.symm⟩
    · obtain ⟨u, hu⟩ := h (⟨a, hxa⟩ : x ∈ G.support)
      rcases hHel x u hu with h | h | h
      · exact h.2.1 rfl
      · exact hcx h.1.symm
      · rcases h.2.1 with h' | h'
        · exact hb1x h'.symm
        · exact hb2x h'.symm
  -- lows of the surgered graph
  have hLows : ∀ v, Low (surg G D c W) v → v = y ∨ v = c' ∨ (v = c ∧ (c = b₁ ∨ c = b₂)) := by
    rintro v ⟨⟨u, hu⟩, hnB⟩
    by_cases hvc : v = c
    · subst hvc
      right; right
      refine ⟨rfl, ?_⟩
      by_contra hcB
      push Not at hcB
      obtain ⟨u₀, hu₀, hu₀a⟩ := h2c v a hac.symm
      have h1 : u₀ ≠ x := by
        rintro rfl
        rcases hncx v hu₀ with h | h
        · exact hca h
        · exact hcb h
      have h2 : u₀ ≠ b := by
        rintro rfl
        rcases hncb v hu₀ with h | h | h
        · exact hcx h
        · exact hcB.1 h
        · exact hcB.2 h
      have h3 : u₀ ≠ b₁ := by
        rintro rfl
        exact hc u₀ (Or.inl rfl) (Ne.symm hcB.1) hu₀
      have h4 : u₀ ≠ b₂ := by
        rintro rfl
        exact hc u₀ (Or.inr rfl) (Ne.symm hcB.2) hu₀
      exact hnB ⟨b₁, b₂, u₀, hb12, h3.symm, h4.symm, hnew b₁ (Or.inl rfl) (Ne.symm hcB.1),
        hnew b₂ (Or.inr rfl) (Ne.symm hcB.2), hcut v u₀ hu₀ hcx hca hcb h1 hu₀a h2⟩
    · by_cases hvc' : v = c'
      · exact Or.inr (Or.inl hvc')
      · left
        -- v is not in D
        have hvD : v ≠ x ∧ v ≠ a ∧ v ≠ b := by
          rcases hHel v u hu with h | h | h
          · exact ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩
          · exact absurd h.1 hvc
          · rcases h.2.1 with rfl | rfl
            · exact ⟨hb1x, hb1a, hb1b⟩
            · exact ⟨hb2x, hb2a, hb2b⟩
        have hvG : ∃ t, G.Adj v t := by
          rcases hHel v u hu with h | h | h
          · exact ⟨u, h.1⟩
          · exact absurd h.1 hvc
          · rcases h.2.1 with rfl | rfl
            · exact ⟨b, hbb1.symm⟩
            · exact ⟨b, hbb2.symm⟩
        have hvLow : Low G v := by
          refine ⟨hvG, fun hB => hnB ?_⟩
          classical
          refine hB.map (fun t => if t = b then c else t) ?_ ?_
          · intro t₁ t₂ ht₁ ht₂ heq
            by_cases e1 : t₁ = b <;> by_cases e2 : t₂ = b
            · exact e1.trans e2.symm
            · simp only [e1, e2, if_true, if_false] at heq
              exfalso
              have hvB : v = b₁ ∨ v = b₂ := by
                rcases hncb v (e1 ▸ ht₁) with h | h | h
                · exact absurd h hvD.1
                · exact Or.inl h
                · exact Or.inr h
              exact hc v hvB hvc (heq ▸ ht₂).symm
            · simp only [e1, e2, if_true, if_false] at heq
              exfalso
              have hvB : v = b₁ ∨ v = b₂ := by
                rcases hncb v (e2 ▸ ht₂) with h | h | h
                · exact absurd h hvD.1
                · exact Or.inl h
                · exact Or.inr h
              exact hc v hvB hvc (heq ▸ ht₁).symm
            · simpa only [e1, e2, if_false] using heq
          · intro t ht
            by_cases e : t = b
            · simp only [e, if_true]
              have hvB : v = b₁ ∨ v = b₂ := by
                rcases hncb v (e ▸ ht) with h | h | h
                · exact absurd h hvD.1
                · exact Or.inl h
                · exact Or.inr h
              exact (hnew v hvB hvc).symm
            · simp only [e, if_false]
              refine hcut v t ht hvD.1 hvD.2.1 hvD.2.2 ?_ ?_ e
              · rintro rfl
                rcases hncx v ht with h | h
                · exact hvD.2.1 h
                · exact hvD.2.2 h
              · rintro rfl
                rcases hnca v ht with h | h | h
                · exact hvD.1 h
                · exact hvc h
                · exact hvc' h
        rcases hlow v hvLow with h | h
        · exact absurd h hvD.1
        · exact h
  -- a vertex with two neighbours in the surgered graph
  have hwit : ∃ v p q, (surg G D c W).Adj v p ∧ (surg G D c W).Adj v q ∧ p ≠ q := by
    by_cases hcB : c = b₁ ∨ c = b₂
    · obtain ⟨w, hwB, hwc⟩ : ∃ w, (w = b₁ ∨ w = b₂) ∧ w ≠ c := by
        rcases hcB with h | h
        · exact ⟨b₂, Or.inr rfl, fun h' => hb12 (h.symm.trans h'.symm)⟩
        · exact ⟨b₁, Or.inl rfl, fun h' => hb12 (h'.trans h)⟩
      have hcw : (surg G D c W).Adj c w := hnew w hwB hwc
      have hwx : w ≠ x := by rcases hwB with rfl | rfl <;> assumption
      have hwa : w ≠ a := by rcases hwB with rfl | rfl <;> assumption
      have hwb : w ≠ b := by rcases hwB with rfl | rfl <;> assumption
      have hbw : G.Adj b w := by rcases hwB with rfl | rfl <;> assumption
      by_cases hcN : ∃ u, G.Adj c u ∧ u ≠ a ∧ u ≠ b
      · obtain ⟨u, hu, hua, hub⟩ := hcN
        have hux : u ≠ x := by
          rintro rfl
          rcases hncx c hu with h | h
          · exact hca h
          · exact hcb h
        refine ⟨c, w, u, hcw, hcut c u hu hcx hca hcb hux hua hub, ?_⟩
        rintro rfl
        exact hc w hwB hwc hu
      · push Not at hcN
        have hcLow : Low G c := by
          refine ⟨⟨a, hac.symm⟩, fun hB => ?_⟩
          obtain ⟨u, hu, hua, hub⟩ := hB.exists_ne a b
          exact hub (hcN u hu hua)
        have hcy : c = y := (hlow c hcLow).resolve_left hcx
        have hwL : ¬ Low G w := by
          intro h
          rcases hlow w h with h' | h'
          · exact hwx h'
          · exact hwc (h'.trans hcy.symm)
        obtain ⟨u, hu, hua, hub⟩ := (big_of_not_low hbw.symm hwL).exists_ne a b
        have hux : u ≠ x := by
          rintro rfl
          rcases hncx w hu with h | h
          · exact hwa h
          · exact hwb h
        refine ⟨w, c, u, hcw.symm, hcut w u hu hwx hwa hwb hux hua hub, ?_⟩
        rintro rfl
        exact hc w hwB hwc hu.symm
    · push Not at hcB
      exact ⟨c, b₁, b₂, hnew b₁ (Or.inl rfl) (Ne.symm hcB.1), hnew b₂ (Or.inr rfl) (Ne.symm hcB.2),
        hb12⟩
  obtain ⟨v₀, p₀, q₀, hp₀, hq₀, hpq₀⟩ := hwit
  -- conclusions
  obtain ⟨v, hvL, hvy, hvc'⟩ := C.cut hsupp hZH hp₀ hq₀ hpq₀ y c'
  obtain ⟨hvc, hcB⟩ : v = c ∧ (c = b₁ ∨ c = b₂) := by
    rcases hLows v hvL with h | h | h
    · exact absurd h hvy
    · exact absurd h hvc'
    · exact h
  subst hvc
  obtain ⟨v', hv'L, hv'y, hv'c⟩ := C.cut hsupp hZH hp₀ hq₀ hpq₀ y v
  have hv'c' : v' = c' := by
    rcases hLows v' hv'L with h | h | h
    · exact absurd h hv'y
    · exact h
    · exact absurd h.1 hv'c
  subst hv'c'
  obtain ⟨w, hwB, hwc⟩ : ∃ w, (w = b₁ ∨ w = b₂) ∧ w ≠ v := by
    rcases hcB with h | h
    · exact ⟨b₂, Or.inr rfl, fun h' => hb12 (h.symm.trans h'.symm)⟩
    · exact ⟨b₁, Or.inl rfl, fun h' => hb12 (h'.trans h)⟩
  refine ⟨hcB, hvy, hv'y, ?_, ?_⟩
  · intro u₁ u₂ h1 h2 h1a h1b h2a h2b
    by_contra hne
    have hx1 : u₁ ≠ x := by
      rintro rfl
      rcases hncx v h1 with h | h
      · exact hca h
      · exact hcb h
    have hx2 : u₂ ≠ x := by
      rintro rfl
      rcases hncx v h2 with h | h
      · exact hca h
      · exact hcb h
    refine hvL.2 ⟨u₁, u₂, w, hne, ?_, ?_, hcut v u₁ h1 hcx hca hcb hx1 h1a h1b,
      hcut v u₂ h2 hcx hca hcb hx2 h2a h2b, hnew w hwB hwc⟩
    · rintro rfl
      exact hc u₁ hwB hwc h1
    · rintro rfl
      exact hc u₂ hwB hwc h2
  · intro hc'B u₁ u₂ h1 h2 h1a h1b h2a h2b
    by_contra hne
    have hc'v : v' ≠ v := hv'c
    have hx1 : u₁ ≠ x := by
      rintro rfl
      rcases hncx v' h1 with h | h
      · exact hc'a h
      · exact hc'b h
    have hx2 : u₂ ≠ x := by
      rintro rfl
      rcases hncx v' h2 with h | h
      · exact hc'a h
      · exact hc'b h
    refine hv'L.2 ⟨u₁, u₂, v, hne, ?_, ?_, hcut v' u₁ h1 hc'x hc'a hc'b hx1 h1a h1b,
      hcut v' u₂ h2 hc'x hc'a hc'b hx2 h2a h2b, (hnew v' hc'B hc'v).symm⟩
    · rintro rfl
      exact hc v' hc'B hc'v h1.symm
    · rintro rfl
      exact hc v' hc'B hc'v h2.symm


/-- keep only the edges between vertices satisfying `P` -/
def restr (G : SimpleGraph V) (P : V → Prop) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ P u ∧ P v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

theorem restr_le {G : SimpleGraph V} {P : V → Prop} : restr G P ≤ G := fun _ _ h => h.1

/-- a path between two distinct reachable vertices, as a list -/
theorem path_list {H : SimpleGraph V} {u w : V} (h : H.Reachable u w) (hne : u ≠ w) :
    ∃ m : List V, (u :: (m ++ [w])).Nodup ∧ List.IsChain H.Adj (u :: (m ++ [w])) := by
  obtain ⟨q, hq⟩ := h.exists_isPath
  have hnd := hq.support_nodup
  have hch := q.isChain_adj_support
  have hlast := q.getLast_support
  have hsupp := q.cons_tail_support.symm
  generalize q.support.tail = t at hsupp
  rcases List.eq_nil_or_concat' t with rfl | ⟨m, z, rfl⟩
  · exfalso
    apply hne
    have : q.support.getLast q.support_ne_nil = u := by simp [hsupp]
    exact this.symm.trans hlast
  · have hz : z = w := by
      have : q.support.getLast q.support_ne_nil = z := by simp [hsupp]
      exact this.symm.trans hlast
    subst hz
    refine ⟨m, ?_, ?_⟩
    · rw [← hsupp]; exact hnd
    · rw [← hsupp]; exact hch

/-- closing a path `p … w` by an extra path `w, ext…, p` -/
theorem close_path {G : SimpleGraph V} {p w : V} {m ext : List V}
    (hnd : (p :: (m ++ [w])).Nodup) (hch : List.IsChain G.Adj (p :: (m ++ [w])))
    (hext : List.IsChain G.Adj (w :: (ext ++ [p]))) (hextnd : ext.Nodup)
    (hdisj : ∀ v ∈ ext, v ∉ p :: (m ++ [w])) (hdiv : 3 ∣ m.length + 1 + ext.length + 1) :
    ZC G := by
  refine ⟨p, (m ++ [w]) ++ ext, ?_, ?_, ?_⟩
  · have e : p :: ((m ++ [w]) ++ ext) = (p :: (m ++ [w])) ++ ext := by simp
    rw [e, List.nodup_append]
    refine ⟨hnd, hextnd, ?_⟩
    intro a ha b hb hab
    subst hab
    exact hdisj a hb ha
  · have e : p :: ((m ++ [w]) ++ ext ++ [p]) = (p :: m) ++ w :: (ext ++ [p]) := by simp
    rw [e, List.isChain_split]
    exact ⟨by simpa using hch, hext⟩
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- the three closing paths of Case II -/
theorem caseII_path {G : SimpleGraph V} (hZ : ¬ ZC G) {x a b p a' b' w : V} {m : List V}
    (hnd : (p :: (m ++ [w])).Nodup) (hch : List.IsChain G.Adj (p :: (m ++ [w])))
    (havoid : ∀ v ∈ p :: (m ++ [w]), v ≠ x ∧ v ≠ a ∧ v ≠ b ∧ v ≠ a' ∧ v ≠ b')
    (hwa' : G.Adj w a') (ha'a : G.Adj a' a) (hap : G.Adj a p) (ha'b' : G.Adj a' b')
    (hb'b : G.Adj b' b) (hbp : G.Adj b p) (hax : G.Adj a x) (hxb : G.Adj x b)
    (hab : a ≠ b) (ha'b : a' ≠ b) (ha'x : a' ≠ x) (hb'x : b' ≠ x) : False := by
  have h3 : 3 ∣ m.length + 1 + 2 + 1 ∨ 3 ∣ m.length + 1 + 3 + 1 ∨ 3 ∣ m.length + 1 + 4 + 1 := by
    omega
  rcases h3 with h | h | h
  · refine hZ (close_path (ext := [a', a]) hnd hch ?_ ?_ ?_ h)
    · simp [hwa', ha'a, hap]
    · simp [ha'a.ne]
    · intro v hv hv'
      have := havoid v hv'
      simp at hv
      rcases hv with rfl | rfl
      · exact this.2.2.2.1 rfl
      · exact this.2.1 rfl
  · refine hZ (close_path (ext := [a', b', b]) hnd hch ?_ ?_ ?_ h)
    · simp [hwa', ha'b', hb'b, hbp]
    · simp [ha'b'.ne, ha'b, hb'b.ne]
    · intro v hv hv'
      have := havoid v hv'
      simp at hv
      rcases hv with rfl | rfl | rfl
      · exact this.2.2.2.1 rfl
      · exact this.2.2.2.2 rfl
      · exact this.2.2.1 rfl
  · refine hZ (close_path (ext := [a', a, x, b]) hnd hch ?_ ?_ ?_ h)
    · simp [hwa', ha'a, hax, hxb, hbp]
    · simp [ha'a.ne, ha'x, ha'b, hax.ne, hab, hxb.ne]
    · intro v hv hv'
      have := havoid v hv'
      simp at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact this.2.2.2.1 rfl
      · exact this.2.1 rfl
      · exact this.1 rfl
      · exact this.2.2.1 rfl

/-- Case II: `a` and `b` have exactly one common neighbour `p` besides `x` -/
theorem Ctx.caseII {G : SimpleGraph V} (C : Ctx G) {x y a b p a' b' : V}
    (hlow : ∀ v, Low G v → v = x ∨ v = y)
    (h2c : ∀ v u, G.Adj v u → ∃ u', G.Adj v u' ∧ u' ≠ u)
    (Nx : ∀ u, G.Adj x u ↔ u = a ∨ u = b)
    (Na : ∀ u, G.Adj a u ↔ u = x ∨ u = p ∨ u = a')
    (Nb : ∀ u, G.Adj b u ↔ u = x ∨ u = p ∨ u = b')
    (hab : a ≠ b) (hpx : p ≠ x) (ha'x : a' ≠ x) (hb'x : b' ≠ x)
    (hadj : G.Adj a' b') (hpBig : Big G p) : False := by
  have hxa : G.Adj x a := (Nx a).mpr (Or.inl rfl)
  have hxb : G.Adj x b := (Nx b).mpr (Or.inr rfl)
  have hap : G.Adj a p := (Na p).mpr (Or.inr (Or.inl rfl))
  have haa' : G.Adj a a' := (Na a').mpr (Or.inr (Or.inr rfl))
  have hbp : G.Adj b p := (Nb p).mpr (Or.inr (Or.inl rfl))
  have hbb' : G.Adj b b' := (Nb b').mpr (Or.inr (Or.inr rfl))
  have hnab : ¬ G.Adj a b := fun h => no_tri C.hZ hxa h hxb.symm
  have hnpa' : ¬ G.Adj p a' := fun h => no_tri C.hZ hap h haa'.symm
  have hnpb' : ¬ G.Adj p b' := fun h => no_tri C.hZ hbp h hbb'.symm
  have hpa : p ≠ a := hap.ne.symm
  have hpb : p ≠ b := hbp.ne.symm
  have ha'a : a' ≠ a := haa'.ne.symm
  have ha'b : a' ≠ b := by rintro rfl; exact hnab haa'
  have hb'b : b' ≠ b := hbb'.ne.symm
  have hb'a : b' ≠ a := by rintro rfl; exact hnab hbb'.symm
  have hpa' : p ≠ a' := by rintro rfl; exact hnpb' hadj
  have hpb' : p ≠ b' := by rintro rfl; exact hnpa' hadj.symm
  have hncx : ∀ t, G.Adj t x → t = a ∨ t = b := fun t ht => (Nx t).mp ht.symm
  have hnca : ∀ t, G.Adj t a → t = x ∨ t = p ∨ t = a' := fun t ht => (Na t).mp ht.symm
  have hncb : ∀ t, G.Adj t b → t = x ∨ t = p ∨ t = b' := fun t ht => (Nb t).mp ht.symm
  let P : V → Prop := fun v => v ≠ x ∧ v ≠ a ∧ v ≠ b ∧ v ≠ a' ∧ v ≠ b'
  have hPp : P p := ⟨hpx, hpa, hpb, hpa', hpb'⟩
  -- reachable vertices satisfy P
  have hreachP : ∀ v, (restr G P).Reachable p v → P v := by
    intro v hv
    by_cases hpv : p = v
    · exact hpv ▸ hPp
    · obtain ⟨m, -, hch⟩ := path_list hv hpv
      obtain ⟨u, hu⟩ := chain_pred hch v (by simp)
      exact hu.2.2
  -- no reachable vertex is adjacent to a' or b' (other than through a, b)
  have hno : ∀ w, (restr G P).Reachable p w →
      ¬ ((G.Adj w a' ∧ w ≠ a ∧ w ≠ b') ∨ (G.Adj w b' ∧ w ≠ b ∧ w ≠ a')) := by
    intro w hw hcon
    have hpw : p ≠ w := by
      rintro rfl
      rcases hcon with h | h
      · exact hnpa' h.1
      · exact hnpb' h.1
    obtain ⟨m, hnd, hch⟩ := path_list hw hpw
    have hchG : List.IsChain G.Adj (p :: (m ++ [w])) := hch.imp (fun _ _ h => h.1)
    have havoid : ∀ v ∈ p :: (m ++ [w]), P v := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact hPp
      · obtain ⟨u, hu⟩ := chain_pred hch v hv'
        exact hu.2.2
    rcases hcon with h | h
    · exact caseII_path C.hZ hnd hchG havoid h.1 haa'.symm hap hadj hbb'.symm hbp hxa.symm hxb
        hab ha'b ha'x hb'x
    · refine caseII_path C.hZ (x := x) (a := b) (b := a) (a' := b') (b' := a') hnd hchG ?_ h.1
        hbb'.symm hbp hadj.symm haa'.symm hap hxb.symm hxa hab.symm hb'a hb'x ha'x
      intro v hv
      have := havoid v hv
      exact ⟨this.1, this.2.2.1, this.2.1, this.2.2.2.2, this.2.2.2.1⟩
  -- the component of p
  let K : V → Prop := fun v => (restr G P).Reachable p v
  have hlt : restr G K < G := by
    refine lt_of_le_of_ne restr_le ?_
    intro heq
    have h' : (restr G K).Adj x a := by
      rw [heq]
      exact hxa
    exact (hreachP x h'.2.1).1 rfl
  -- neighbours of a reachable vertex other than p are reachable
  have hnb : ∀ v, K v → v ≠ p → ∀ t, G.Adj v t → (restr G K).Adj v t := by
    intro v hv hvp t ht
    have hPv := hreachP v hv
    have hPt : P t := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rintro rfl
        rcases hncx v ht with h | h
        · exact hPv.2.1 h
        · exact hPv.2.2.1 h
      · rintro rfl
        rcases hnca v ht with h | h | h
        · exact hPv.1 h
        · exact hvp h
        · exact hPv.2.2.2.1 h
      · rintro rfl
        rcases hncb v ht with h | h | h
        · exact hPv.1 h
        · exact hvp h
        · exact hPv.2.2.2.2 h
      · rintro rfl
        exact hno v hv (Or.inl ⟨ht, hPv.2.1, hPv.2.2.2.2⟩)
      · rintro rfl
        exact hno v hv (Or.inr ⟨ht, hPv.2.2.1, hPv.2.2.2.1⟩)
    have hvt : (restr G P).Adj v t := ⟨ht, hPv, hPt⟩
    exact ⟨ht, hv, SimpleGraph.Reachable.trans hv hvt.reachable⟩
  have hLows : ∀ v, Low (restr G K) v → v = y ∨ v = p := by
    rintro v ⟨⟨u, hu⟩, hnB⟩
    by_cases hvp : v = p
    · exact Or.inr hvp
    · left
      have hvLow : Low G v := ⟨⟨u, hu.1⟩, fun hB => hnB (hB.mono (hnb v hu.2.1 hvp))⟩
      rcases hlow v hvLow with h | h
      · exact absurd h (hreachP v hu.2.1).1
      · exact h
  obtain ⟨p', hpp', hp'a, hp'b⟩ := hpBig.exists_ne a b
  have hPp' : P p' := by
    refine ⟨?_, hp'a, hp'b, ?_, ?_⟩
    · rintro rfl
      rcases hncx p hpp' with h | h
      · exact hpa h
      · exact hpb h
    · rintro rfl
      exact hnpa' hpp'
    · rintro rfl
      exact hnpb' hpp'
  have hKp : K p := SimpleGraph.Reachable.refl p
  have hpp'r : (restr G P).Adj p p' := ⟨hpp', hPp, hPp'⟩
  have hKp' : K p' := hpp'r.reachable
  obtain ⟨z, hz, hzp⟩ := h2c p' p hpp'.symm
  have e1 : (restr G K).Adj p' p := ⟨hpp'.symm, hKp', hKp⟩
  have e2 : (restr G K).Adj p' z := hnb p' hKp' hpp'.ne.symm z hz
  obtain ⟨v, hvL, hvy, hvp⟩ := C.sub hlt e1 e2 (Ne.symm hzp) y p
  rcases hLows v hvL with h | h
  · exact hvy h
  · exact hvp h


/-- Case I: `a` and `b` have the same neighbourhood `{x, p, q}` -/
theorem Ctx.caseI {G : SimpleGraph V} (C : Ctx G) {x y a b p q p' q' : V}
    (hlow : ∀ v, Low G v → v = x ∨ v = y)
    (h2c : ∀ v u, G.Adj v u → ∃ u', G.Adj v u' ∧ u' ≠ u)
    (Nx : ∀ u, G.Adj x u ↔ u = a ∨ u = b)
    (Na : ∀ u, G.Adj a u ↔ u = x ∨ u = p ∨ u = q)
    (Nb : ∀ u, G.Adj b u ↔ u = x ∨ u = p ∨ u = q)
    (Np : ∀ u, G.Adj p u ↔ u = a ∨ u = b ∨ u = p')
    (Nq : ∀ u, G.Adj q u ↔ u = a ∨ u = b ∨ u = q')
    (hab : a ≠ b) (hpq : p ≠ q) (hpx : p ≠ x) (hqx : q ≠ x)
    (hp'a : p' ≠ a) (hp'b : p' ≠ b) (hq'a : q' ≠ a) (hq'b : q' ≠ b) : False := by
  have hxa : G.Adj x a := (Nx a).mpr (Or.inl rfl)
  have hxb : G.Adj x b := (Nx b).mpr (Or.inr rfl)
  have hap : G.Adj a p := (Na p).mpr (Or.inr (Or.inl rfl))
  have haq : G.Adj a q := (Na q).mpr (Or.inr (Or.inr rfl))
  have hbp : G.Adj b p := (Nb p).mpr (Or.inr (Or.inl rfl))
  have hbq : G.Adj b q := (Nb q).mpr (Or.inr (Or.inr rfl))
  have hpp' : G.Adj p p' := (Np p').mpr (Or.inr (Or.inr rfl))
  have hqq' : G.Adj q q' := (Nq q').mpr (Or.inr (Or.inr rfl))
  have hnpq : ¬ G.Adj p q := fun h => no_tri C.hZ hap h haq.symm
  have hncx : ∀ t, G.Adj t x → t = a ∨ t = b := fun t ht => (Nx t).mp ht.symm
  have hnca : ∀ t, G.Adj t a → t = x ∨ t = p ∨ t = q := fun t ht => (Na t).mp ht.symm
  have hncb : ∀ t, G.Adj t b → t = x ∨ t = p ∨ t = q := fun t ht => (Nb t).mp ht.symm
  have hncp : ∀ t, G.Adj t p → t = a ∨ t = b ∨ t = p' := fun t ht => (Np t).mp ht.symm
  have hncq : ∀ t, G.Adj t q → t = a ∨ t = b ∨ t = q' := fun t ht => (Nq t).mp ht.symm
  have hxa' : x ≠ a := hxa.ne
  have hxb' : x ≠ b := hxb.ne
  have hpa : p ≠ a := hap.ne.symm
  have hpb : p ≠ b := hbp.ne.symm
  have hqa : q ≠ a := haq.ne.symm
  have hqb : q ≠ b := hbq.ne.symm
  have hp'p : p' ≠ p := hpp'.ne.symm
  have hq'q : q' ≠ q := hqq'.ne.symm
  have hp'x : p' ≠ x := by
    rintro rfl
    rcases hncx p hpp' with h | h
    · exact hpa h
    · exact hpb h
  have hq'x : q' ≠ x := by
    rintro rfl
    rcases hncx q hqq' with h | h
    · exact hqa h
    · exact hqb h
  have hp'q : p' ≠ q := by rintro rfl; exact hnpq hpp'
  have hq'p : q' ≠ p := by rintro rfl; exact hnpq hqq'.symm
  have hp'q' : p' ≠ q' := by
    rintro rfl
    refine no_hex C.hZ (v₁ := x) (v₂ := a) (v₃ := p) (v₄ := p') (v₅ := q) (v₆ := b) ?_ hxa hap hpp'
      hqq'.symm hbq.symm hxb.symm
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
      and_true]
    refine ⟨⟨hxa', hpx.symm, hp'x.symm, hqx.symm, hxb'⟩, ⟨hpa.symm, hp'a.symm, hqa.symm, hab⟩,
      ⟨hp'p.symm, hpq, hpb⟩, ⟨hp'q, hp'b⟩, hqb, not_false⟩
  -- no common neighbour of p' and q' (hexagon)
  have hq'N : ∀ w, G.Adj q' w → w ≠ q → w ≠ x ∧ w ≠ a ∧ w ≠ b ∧ w ≠ p ∧ w ≠ q' := by
    intro w hw hwq
    refine ⟨?_, ?_, ?_, ?_, hw.ne.symm⟩
    · rintro rfl
      rcases hncx q' hw with h | h
      · exact hq'a h
      · exact hq'b h
    · rintro rfl
      rcases hnca q' hw with h | h | h
      · exact hq'x h
      · exact hq'p h
      · exact hq'q h
    · rintro rfl
      rcases hncb q' hw with h | h | h
      · exact hq'x h
      · exact hq'p h
      · exact hq'q h
    · rintro rfl
      rcases hncp q' hw with h | h | h
      · exact hq'a h
      · exact hq'b h
      · exact hp'q' h.symm
  have hhex : ∀ w, G.Adj q' w → w ≠ q → w ≠ p' → ¬ G.Adj p' w := by
    intro w hw hwq hwp' hcon
    obtain ⟨h1, h2, h3, h4, h5⟩ := hq'N w hw hwq
    refine no_hex C.hZ (v₁ := w) (v₂ := q') (v₃ := q) (v₄ := a) (v₅ := p) (v₆ := p') ?_ hw.symm
      hqq'.symm haq.symm hap hpp' hcon
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
      and_true]
    exact ⟨⟨h5, hwq, h2, h4, hwp'⟩, ⟨hq'q, hq'a, hq'p, hp'q'.symm⟩, ⟨hqa, hpq.symm, hp'q.symm⟩,
      ⟨hpa.symm, hp'a.symm⟩, hp'p.symm, not_false⟩
  let D : Set V := {x, a, b, p, q, q'}
  let W : Set V := {w | G.Adj q' w ∧ w ≠ q ∧ w ≠ p'}
  have hDmem : ∀ t, t ∈ D ↔ t = x ∨ t = a ∨ t = b ∨ t = p ∨ t = q ∨ t = q' := by
    intro t; simp [D]
  have hp'D : p' ∉ D := by
    rw [hDmem]
    intro h
    rcases h with h | h | h | h | h | h
    · exact hp'x h
    · exact hp'a h
    · exact hp'b h
    · exact hp'p h
    · exact hp'q h
    · exact hp'q' h
  have hcut : ∀ u v, G.Adj u v → u ∉ D → v ∉ D → (surg G D p' W).Adj u v :=
    fun u v huv hu hv => Or.inl ⟨huv, hu, hv⟩
  have hnew : ∀ w, G.Adj q' w → w ≠ q → w ≠ p' → (surg G D p' W).Adj p' w :=
    fun w hw hwq hwp' => Or.inr (Or.inl ⟨rfl, ⟨hw, hwq, hwp'⟩, hwp'.symm⟩)
  have hWD : ∀ w, G.Adj q' w → w ≠ q → w ∉ D := by
    intro w hw hwq
    obtain ⟨h1, h2, h3, h4, h5⟩ := hq'N w hw hwq
    rw [hDmem]
    intro h
    rcases h with h | h | h | h | h | h
    · exact h1 h
    · exact h2 h
    · exact h3 h
    · exact h4 h
    · exact hwq h
    · exact h5 h
  have hZH : ¬ ZC (surg G D p' W) := by
    intro h
    refine C.hZ (ZC_of_surg (S := [p, a, x, b, q]) (d := q') ?_ ?_ (by norm_num) ?_ ?_ h)
    · simp [hpp'.symm, hap.symm, hxa.symm, hxb, hbq, hqq']
    · simp only [List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
      exact ⟨⟨hp'p, hp'a, hp'x, hp'b, hp'q, hp'q'⟩, ⟨hpa, hpx, hpb, hpq, hq'p.symm⟩,
        ⟨hxa'.symm, hab, hqa.symm, hq'a.symm⟩, ⟨hxb', hqx.symm, hq'x.symm⟩, ⟨hqb.symm, hq'b.symm⟩,
        hq'q.symm, not_false⟩
    · intro v hv
      rw [hDmem]
      simp at hv
      tauto
    · rintro w ⟨hw, hwq, -⟩
      exact ⟨hw, hWD w hw hwq⟩
  have hsupp : (surg G D p' W).support ⊂ G.support := by
    refine ⟨?_, fun h => ?_⟩
    · rintro v ⟨u, hu⟩
      rcases hu with h | h | h
      · exact ⟨u, h.1⟩
      · exact ⟨p, h.1 ▸ hpp'.symm⟩
      · exact ⟨q', h.2.1.1.symm⟩
    · obtain ⟨u, hu⟩ := h (⟨a, hxa⟩ : x ∈ G.support)
      rcases hu with h | h | h
      · exact h.2.1 ((hDmem x).mpr (Or.inl rfl))
      · exact hp'x h.1.symm
      · exact hWD x h.2.1.1 h.2.1.2.1 ((hDmem x).mpr (Or.inl rfl))
  -- adjacency at a vertex outside D and different from p'
  have hgen : ∀ v t, v ∉ D → v ≠ p' → G.Adj v t → t ≠ q' → (surg G D p' W).Adj v t := by
    intro v t hvD hvp' hvt htq'
    rw [hDmem] at hvD
    push Not at hvD
    obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hvD
    refine hcut v t hvt ((hDmem v).not.mpr (by tauto)) ?_
    rw [hDmem]
    intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · rcases hncx v hvt with h | h
      · exact v2 h
      · exact v3 h
    · rcases hnca v hvt with h | h | h
      · exact v1 h
      · exact v4 h
      · exact v5 h
    · rcases hncb v hvt with h | h | h
      · exact v1 h
      · exact v4 h
      · exact v5 h
    · rcases hncp v hvt with h | h | h
      · exact v2 h
      · exact v3 h
      · exact hvp' h
    · rcases hncq v hvt with h | h | h
      · exact v2 h
      · exact v3 h
      · exact v6 h
    · exact htq' rfl
  have hLows : ∀ v, Low (surg G D p' W) v → v = y ∨ v = p' := by
    rintro v ⟨⟨u, hu⟩, hnB⟩
    by_cases hvp' : v = p'
    · exact Or.inr hvp'
    · left
      have hvD : v ∉ D := by
        rcases hu with h | h | h
        · exact h.2.1
        · exact absurd h.1 hvp'
        · exact hWD v h.2.1.1 h.2.1.2.1
      have hvq : v ≠ q := fun h => hvD ((hDmem v).mpr (by tauto))
      have hvG : ∃ t, G.Adj v t := by
        rcases hu with h | h | h
        · exact ⟨u, h.1⟩
        · exact absurd h.1 hvp'
        · exact ⟨q', h.2.1.1.symm⟩
      have hvLow : Low G v := by
        refine ⟨hvG, fun hB => hnB ?_⟩
        classical
        refine hB.map (fun t => if t = q' then p' else t) ?_ ?_
        · intro t₁ t₂ ht₁ ht₂ heq
          by_cases e1 : t₁ = q' <;> by_cases e2 : t₂ = q'
          · exact e1.trans e2.symm
          · simp only [e1, e2, if_true, if_false] at heq
            exfalso
            exact hhex v (e1 ▸ ht₁).symm hvq hvp' (heq ▸ ht₂).symm
          · simp only [e1, e2, if_true, if_false] at heq
            exfalso
            exact hhex v (e2 ▸ ht₂).symm hvq hvp' (heq ▸ ht₁).symm
          · simpa only [e1, e2, if_false] using heq
        · intro t ht
          by_cases e : t = q'
          · simp only [e, if_true]
            exact (hnew v (e ▸ ht).symm hvq hvp').symm
          · simp only [e, if_false]
            exact hgen v t hvD hvp' ht e
      rcases hlow v hvLow with h | h
      · exact absurd ((hDmem v).mpr (Or.inl h)) hvD
      · exact h
  -- a vertex with two neighbours
  have hwit : ∃ v s t, (surg G D p' W).Adj v s ∧ (surg G D p' W).Adj v t ∧ s ≠ t := by
    by_cases hN : ∃ u, G.Adj p' u ∧ u ≠ p ∧ u ≠ q'
    · obtain ⟨u₀, hu₀, hu₀p, hu₀q'⟩ := hN
      have hu₀D : u₀ ∉ D := by
        rw [hDmem]
        intro h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl
        · rcases hncx p' hu₀ with h | h
          · exact hp'a h
          · exact hp'b h
        · rcases hnca p' hu₀ with h | h | h
          · exact hp'x h
          · exact hp'p h
          · exact hp'q h
        · rcases hncb p' hu₀ with h | h | h
          · exact hp'x h
          · exact hp'p h
          · exact hp'q h
        · exact hu₀p rfl
        · rcases hncq p' hu₀ with h | h | h
          · exact hp'a h
          · exact hp'b h
          · exact hp'q' h
        · exact hu₀q' rfl
      obtain ⟨z, hz, hzp'⟩ := h2c u₀ p' hu₀.symm
      have hzq' : z ≠ q' := by
        rintro rfl
        exact hhex u₀ hz.symm (fun h => hu₀D ((hDmem u₀).mpr (by tauto))) hu₀.ne.symm hu₀
      exact ⟨u₀, p', z, (hcut p' u₀ hu₀ hp'D hu₀D).symm, hgen u₀ z hu₀D hu₀.ne.symm hz hzq',
        Ne.symm hzp'⟩
    · push Not at hN
      have hp'Low : Low G p' := by
        refine ⟨⟨p, hpp'.symm⟩, fun hB => ?_⟩
        obtain ⟨u, hu, hup, huq'⟩ := hB.exists_ne p q'
        exact huq' (hN u hu hup)
      have hp'y : p' = y := (hlow p' hp'Low).resolve_left hp'x
      have hq'L : ¬ Low G q' := by
        intro h
        rcases hlow q' h with h' | h'
        · exact hq'x h'
        · exact hp'q' (hp'y.trans h'.symm)
      obtain ⟨u₀, hu₀, hu₀q, hu₀p'⟩ := (big_of_not_low hqq'.symm hq'L).exists_ne q p'
      have hu₀D : u₀ ∉ D := hWD u₀ hu₀ hu₀q
      obtain ⟨z, hz, hzq'⟩ := h2c u₀ q' hu₀.symm
      have hzp' : z ≠ p' := by
        rintro rfl
        exact hhex u₀ hu₀ hu₀q hu₀p' hz.symm
      exact ⟨u₀, p', z, (hnew u₀ hu₀ hu₀q hu₀p').symm, hgen u₀ z hu₀D hu₀p' hz hzq', Ne.symm hzp'⟩
  obtain ⟨v₀, s₀, t₀, hs₀, ht₀, hst₀⟩ := hwit
  obtain ⟨v, hvL, hvy, hvp'⟩ := C.cut hsupp hZH hs₀ ht₀ hst₀ y p'
  rcases hLows v hvL with h | h
  · exact hvy h
  · exact hvp' h


/-- Case I in terms of the neighbourhoods of `a` and `b` only -/
theorem Ctx.caseI' {G : SimpleGraph V} (C : Ctx G) {x y a b p q : V}
    (hlow : ∀ v, Low G v → v = x ∨ v = y)
    (h2c : ∀ v u, G.Adj v u → ∃ u', G.Adj v u' ∧ u' ≠ u)
    (Nx : ∀ u, G.Adj x u ↔ u = a ∨ u = b)
    (Na : ∀ u, G.Adj a u ↔ u = x ∨ u = p ∨ u = q)
    (Nb : ∀ u, G.Adj b u ↔ u = x ∨ u = p ∨ u = q)
    (hab : a ≠ b) (hpq : p ≠ q) (hpx : p ≠ x) (hqx : q ≠ x) : False := by
  have hap : G.Adj a p := (Na p).mpr (Or.inr (Or.inl rfl))
  have haq : G.Adj a q := (Na q).mpr (Or.inr (Or.inr rfl))
  have hbp : G.Adj b p := (Nb p).mpr (Or.inr (Or.inl rfl))
  have hbq : G.Adj b q := (Nb q).mpr (Or.inr (Or.inr rfl))
  have hnpq : ¬ G.Adj p q := fun h => no_tri C.hZ hap h haq.symm
  obtain ⟨-, hpy, hqy, hpu, hqu⟩ := C.lemC (c := p) (c' := q) (b₁ := p) (b₂ := q) hlow h2c Nx Na Nb
    hab hpq hpx hqx hpx hqx (by
      rintro w (rfl | rfl) hw
      · exact absurd rfl hw
      · exact hnpq)
  have hqu' := hqu (Or.inr rfl)
  have hpBig : Big G p := big_of_not_low hap.symm (fun h => (hlow p h).elim hpx hpy)
  have hqBig : Big G q := big_of_not_low haq.symm (fun h => (hlow q h).elim hqx hqy)
  obtain ⟨p', hpp', hp'a, hp'b⟩ := hpBig.exists_ne a b
  obtain ⟨q', hqq', hq'a, hq'b⟩ := hqBig.exists_ne a b
  have Np : ∀ u, G.Adj p u ↔ u = a ∨ u = b ∨ u = p' := by
    intro u
    constructor
    · intro hu
      by_cases h1 : u = a
      · exact Or.inl h1
      · by_cases h2 : u = b
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (hpu u p' hu hpp' h1 h2 hp'a hp'b))
    · rintro (rfl | rfl | rfl)
      · exact hap.symm
      · exact hbp.symm
      · exact hpp'
  have Nq : ∀ u, G.Adj q u ↔ u = a ∨ u = b ∨ u = q' := by
    intro u
    constructor
    · intro hu
      by_cases h1 : u = a
      · exact Or.inl h1
      · by_cases h2 : u = b
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (hqu' u q' hu hqq' h1 h2 hq'a hq'b))
    · rintro (rfl | rfl | rfl)
      · exact haq.symm
      · exact hbq.symm
      · exact hqq'
  exact C.caseI hlow h2c Nx Na Nb Np Nq hab hpq hpx hqx hp'a hp'b hq'a hq'b

/-- Case II in terms of the neighbourhoods of `a` and `b` only -/
theorem Ctx.caseII' {G : SimpleGraph V} (C : Ctx G) {x y a b p a' b' : V}
    (hlow : ∀ v, Low G v → v = x ∨ v = y)
    (h2c : ∀ v u, G.Adj v u → ∃ u', G.Adj v u' ∧ u' ≠ u)
    (Nx : ∀ u, G.Adj x u ↔ u = a ∨ u = b)
    (Na : ∀ u, G.Adj a u ↔ u = x ∨ u = p ∨ u = a')
    (Nb : ∀ u, G.Adj b u ↔ u = x ∨ u = p ∨ u = b')
    (hab : a ≠ b) (hpx : p ≠ x) (ha'x : a' ≠ x) (hb'x : b' ≠ x)
    (hpa' : p ≠ a') (hpb' : p ≠ b') (ha'b' : a' ≠ b') : False := by
  have hap : G.Adj a p := (Na p).mpr (Or.inr (Or.inl rfl))
  have haa' : G.Adj a a' := (Na a').mpr (Or.inr (Or.inr rfl))
  have hbp : G.Adj b p := (Nb p).mpr (Or.inr (Or.inl rfl))
  have hbb' : G.Adj b b' := (Nb b').mpr (Or.inr (Or.inr rfl))
  have Na' : ∀ u, G.Adj a u ↔ u = x ∨ u = a' ∨ u = p := fun u => (Na u).trans (by tauto)
  have hadj : G.Adj a' b' := by
    by_contra hnadj
    have L := C.lemC (c := a') (c' := p) (b₁ := p) (b₂ := b') hlow h2c Nx Na' Nb hab hpb' ha'x hpx
      hpx hb'x (by
        rintro w (rfl | rfl) hw
        · exact fun h => no_tri C.hZ hap h.symm haa'.symm
        · exact hnadj)
    rcases L.1 with h | h
    · exact hpa' h.symm
    · exact ha'b' h
  have L := C.lemC (c := p) (c' := a') (b₁ := p) (b₂ := b') hlow h2c Nx Na Nb hab hpb' hpx ha'x
    hpx hb'x (by
      rintro w (rfl | rfl) hw
      · exact absurd rfl hw
      · exact fun h => no_tri C.hZ hbp h hbb'.symm)
  have hpy := L.2.1
  have hpBig : Big G p := big_of_not_low hap.symm (fun h => (hlow p h).elim hpx hpy)
  exact C.caseII hlow h2c Nx Na Nb hab hpx ha'x hb'x hadj hpBig

/-- the final case analysis -/
theorem Ctx.finish {G : SimpleGraph V} (C : Ctx G) {x y a b a₁ a₂ b₁ b₂ : V}
    (hlow : ∀ v, Low G v → v = x ∨ v = y)
    (h2c : ∀ v u, G.Adj v u → ∃ u', G.Adj v u' ∧ u' ≠ u)
    (Nx : ∀ u, G.Adj x u ↔ u = a ∨ u = b)
    (Na : ∀ u, G.Adj a u ↔ u = x ∨ u = a₁ ∨ u = a₂)
    (Nb : ∀ u, G.Adj b u ↔ u = x ∨ u = b₁ ∨ u = b₂)
    (hab : a ≠ b) (ha12 : a₁ ≠ a₂) (hb12 : b₁ ≠ b₂)
    (ha1x : a₁ ≠ x) (ha2x : a₂ ≠ x) (hb1x : b₁ ≠ x) (hb2x : b₂ ≠ x) : False := by
  have Na' : ∀ u, G.Adj a u ↔ u = x ∨ u = a₂ ∨ u = a₁ := fun u => (Na u).trans (by tauto)
  have Nb' : ∀ u, G.Adj b u ↔ u = x ∨ u = b₂ ∨ u = b₁ := fun u => (Nb u).trans (by tauto)
  have Nx' : ∀ u, G.Adj x u ↔ u = b ∨ u = a := fun u => (Nx u).trans or_comm
  by_cases h11 : a₁ = b₁
  · subst h11
    by_cases h22 : a₂ = b₂
    · subst h22
      exact C.caseI' hlow h2c Nx Na Nb hab ha12 ha1x ha2x
    · exact C.caseII' hlow h2c Nx Na Nb hab ha1x ha2x hb2x ha12 hb12 h22
  · by_cases h12 : a₁ = b₂
    · subst h12
      by_cases h21 : a₂ = b₁
      · subst h21
        exact C.caseI' hlow h2c Nx Na Nb' hab ha12 ha1x ha2x
      · exact C.caseII' hlow h2c Nx Na Nb' hab ha1x ha2x hb1x ha12 (Ne.symm hb12) h21
    · by_cases h21 : a₂ = b₁
      · subst h21
        exact C.caseII' hlow h2c Nx Na' Nb hab ha2x ha1x hb2x (Ne.symm ha12) hb12 h12
      · by_cases h22 : a₂ = b₂
        · subst h22
          exact C.caseII' hlow h2c Nx Na' Nb' hab ha2x ha1x hb1x (Ne.symm ha12) (Ne.symm hb12) h11
        · -- Case III: no common neighbour
          have hxa : G.Adj x a := (Nx a).mpr (Or.inl rfl)
          have hxb : G.Adj x b := (Nx b).mpr (Or.inr rfl)
          have haa1 : G.Adj a a₁ := (Na a₁).mpr (Or.inr (Or.inl rfl))
          have haa2 : G.Adj a a₂ := (Na a₂).mpr (Or.inr (Or.inr rfl))
          have hbb1 : G.Adj b b₁ := (Nb b₁).mpr (Or.inr (Or.inl rfl))
          have hbb2 : G.Adj b b₂ := (Nb b₂).mpr (Or.inr (Or.inr rfl))
          have hnab : ¬ G.Adj a b := fun h => no_tri C.hZ hxa h hxb.symm
          have A1 : G.Adj a₁ b₁ ∨ G.Adj a₁ b₂ := by
            by_contra hcon
            push Not at hcon
            have L := C.lemC (c := a₁) (c' := a₂) hlow h2c Nx Na Nb hab hb12 ha1x ha2x hb1x hb2x (by
              rintro w (rfl | rfl) -
              · exact hcon.1
              · exact hcon.2)
            rcases L.1 with h | h
            · exact h11 h
            · exact h12 h
          have A2 : G.Adj a₂ b₁ ∨ G.Adj a₂ b₂ := by
            by_contra hcon
            push Not at hcon
            have L := C.lemC (c := a₂) (c' := a₁) hlow h2c Nx Na' Nb hab hb12 ha2x ha1x hb1x hb2x (by
              rintro w (rfl | rfl) -
              · exact hcon.1
              · exact hcon.2)
            rcases L.1 with h | h
            · exact h21 h
            · exact h22 h
          have B1 : G.Adj a₁ b₁ ∨ G.Adj a₂ b₁ := by
            by_contra hcon
            push Not at hcon
            have L := C.lemC (a := b) (b := a) (c := b₁) (c' := b₂) (b₁ := a₁) (b₂ := a₂) hlow h2c Nx'
              Nb Na hab.symm ha12 hb1x hb2x ha1x ha2x (by
              rintro w (rfl | rfl) -
              · exact fun h => hcon.1 h.symm
              · exact fun h => hcon.2 h.symm)
            rcases L.1 with h | h
            · exact h11 h.symm
            · exact h21 h.symm
          have B2 : G.Adj a₁ b₂ ∨ G.Adj a₂ b₂ := by
            by_contra hcon
            push Not at hcon
            have L := C.lemC (a := b) (b := a) (c := b₂) (c' := b₁) (b₁ := a₁) (b₂ := a₂) hlow h2c Nx'
              Nb' Na hab.symm ha12 hb2x hb1x ha1x ha2x (by
              rintro w (rfl | rfl) -
              · exact fun h => hcon.1 h.symm
              · exact fun h => hcon.2 h.symm)
            rcases L.1 with h | h
            · exact h12 h.symm
            · exact h22 h.symm
          have M : (G.Adj a₁ b₁ ∧ G.Adj a₂ b₂) ∨ (G.Adj a₁ b₂ ∧ G.Adj a₂ b₁) := by tauto
          have ha1a : a₁ ≠ a := haa1.ne.symm
          have ha2a : a₂ ≠ a := haa2.ne.symm
          have hb1b : b₁ ≠ b := hbb1.ne.symm
          have hb2b : b₂ ≠ b := hbb2.ne.symm
          have ha1b : a₁ ≠ b := by rintro rfl; exact hnab haa1
          have ha2b : a₂ ≠ b := by rintro rfl; exact hnab haa2
          have hb1a : b₁ ≠ a := by rintro rfl; exact hnab hbb1.symm
          have hb2a : b₂ ≠ a := by rintro rfl; exact hnab hbb2.symm
          rcases M with ⟨m1, m2⟩ | ⟨m1, m2⟩
          · refine no_hex C.hZ (v₁ := a) (v₂ := a₁) (v₃ := b₁) (v₄ := b) (v₅ := b₂) (v₆ := a₂) ?_
              haa1 m1 hbb1.symm hbb2 m2.symm haa2.symm
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
              List.nodup_nil, and_true]
            exact ⟨⟨ha1a.symm, hb1a.symm, hab, hb2a.symm, ha2a.symm⟩, ⟨h11, ha1b, h12, ha12⟩,
              ⟨hb1b, hb12, Ne.symm h21⟩, ⟨hb2b.symm, ha2b.symm⟩, Ne.symm h22, not_false⟩
          · refine no_hex C.hZ (v₁ := a) (v₂ := a₁) (v₃ := b₂) (v₄ := b) (v₅ := b₁) (v₆ := a₂) ?_
              haa1 m1 hbb2.symm hbb1 m2.symm haa2.symm
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
              List.nodup_nil, and_true]
            exact ⟨⟨ha1a.symm, hb2a.symm, hab, hb1a.symm, ha2a.symm⟩, ⟨h12, ha1b, h11, ha12⟩,
              ⟨hb2b, hb12.symm, Ne.symm h22⟩, ⟨hb1b.symm, ha2b.symm⟩, Ne.symm h21, not_false⟩

/-- the inductive step -/
theorem step {G : SimpleGraph V} (IHs : ∀ H : SimpleGraph V, H < G → Good H)
    (IHc : ∀ H : SimpleGraph V, H.support ⊂ G.support → Good H) : Good G := by
  by_contra hG
  have hZ : ¬ ZC G := fun h => hG (Or.inl h)
  have hdeg : ¬ ∀ v a b, G.Adj v a → G.Adj v b → a = b := fun h => hG (Or.inr (Or.inl h))
  have hcov : ¬ ∀ y₁ y₂ : V, ∃ v, Low G v ∧ v ≠ y₁ ∧ v ≠ y₂ := fun h => hG (Or.inr (Or.inr h))
  have C : Ctx G := ⟨hZ, IHs, IHc⟩
  obtain ⟨v₀, a₀, b₀, h1, h2, h3⟩ : ∃ v₀ a₀ b₀, G.Adj v₀ a₀ ∧ G.Adj v₀ b₀ ∧ a₀ ≠ b₀ := by
    by_contra hcon
    exact hdeg (fun v a b ha hb => by
      by_contra hne
      exact hcon ⟨v, a, b, ha, hb, hne⟩)
  obtain ⟨y₁, y₂, hlow12⟩ : ∃ y₁ y₂, ∀ v, Low G v → v = y₁ ∨ v = y₂ := by
    by_contra hcon
    refine hcov (fun y₁ y₂ => ?_)
    by_contra hno
    refine hcon ⟨y₁, y₂, fun v hv => ?_⟩
    by_contra hv'
    push Not at hv'
    exact hno ⟨v, hv, hv'.1, hv'.2⟩
  -- Step 0: a Big vertex
  obtain ⟨β, hβ⟩ : ∃ β, Big G β := by
    by_contra hno
    push Not at hno
    have l1 := hlow12 v₀ ⟨⟨a₀, h1⟩, hno v₀⟩
    have l2 := hlow12 a₀ ⟨⟨v₀, h1.symm⟩, hno a₀⟩
    have l3 := hlow12 b₀ ⟨⟨v₀, h2.symm⟩, hno b₀⟩
    have n1 := h1.ne
    have n2 := h2.ne
    grind
  -- a Low vertex
  obtain ⟨x, hx⟩ : ∃ x, Low G x := by
    obtain ⟨w, hw, hw1, hw2⟩ := C.del hβ h1 v₀ a₀
    exact ⟨w, (low_delE_of_ne hw1 hw2).mp hw⟩
  obtain ⟨y, hlow⟩ : ∃ y, ∀ v, Low G v → v = x ∨ v = y := by
    rcases hlow12 x hx with rfl | rfl
    · exact ⟨y₂, hlow12⟩
    · exact ⟨y₁, fun v hv => (hlow12 v hv).symm⟩
  have h2c : ∀ v u, G.Adj v u → ∃ u', G.Adj v u' ∧ u' ≠ u := by
    intro v u hvu
    by_cases hB : Big G v
    · obtain ⟨u', hu', h, -⟩ := hB.exists_ne u u
      exact ⟨u', hu', h⟩
    · exact (C.low_struct hlow12 hβ ⟨⟨u, hvu⟩, hB⟩ hvu).1
  obtain ⟨a, hxa⟩ := hx.1
  obtain ⟨⟨b, hxb, hba⟩, a₁, a₂, ha12, ha1x, ha2x, Na⟩ := C.low_struct hlow12 hβ hx hxa
  obtain ⟨-, b₁, b₂, hb12, hb1x, hb2x, Nb⟩ := C.low_struct hlow12 hβ hx hxb
  have Nx : ∀ u, G.Adj x u ↔ u = a ∨ u = b := by
    intro u
    constructor
    · intro hu
      by_contra hcon
      push Not at hcon
      exact hx.2 ⟨a, b, u, hba.symm, fun h => hcon.1 h.symm, fun h => hcon.2 h.symm, hxa, hxb, hu⟩
    · rintro (rfl | rfl) <;> assumption
  exact C.finish hlow h2c Nx Na Nb hba.symm ha12 hb12 ha1x ha2x hb1x hb2x

theorem good_all [Finite V] : ∀ (n m : ℕ) (G : SimpleGraph V),
    G.support.ncard = n → G.edgeSet.ncard = m → Good G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
      intro G hn hm
      refine step ?_ ?_
      · intro H hlt
        have hsub : H.support ⊆ G.support := SimpleGraph.support_mono hlt.le
        have hed : H.edgeSet.ncard < G.edgeSet.ncard :=
          Set.ncard_lt_ncard (SimpleGraph.edgeSet_ssubset_edgeSet.mpr hlt) (Set.toFinite _)
        rcases (Set.ncard_le_ncard hsub (Set.toFinite _)).lt_or_eq with h | h
        · exact ihn _ (hn ▸ h) _ H rfl rfl
        · exact ihm _ (hm ▸ hed) H (h.trans hn) rfl
      · intro H hss
        exact ihn _ (hn ▸ Set.ncard_lt_ncard hss (Set.toFinite _)) _ H rfl rfl

end OMA.Helpers

theorem OMA.solution : type_of% @Arxiv.«2605.02731».dean_conjecture.variants.three := by
  intro V _ _ G _ hG
  have hbig : ∀ v, OMA.Helpers.Big G v := by
    intro v
    have h3 : 3 ≤ G.degree v := hG.trans (G.minDegree_le_degree v)
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at h3
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp h3
    exact ⟨a, b, c, hab, hac, hbc, by simpa using ha, by simpa using hb, by simpa using hc⟩
  cases isEmpty_or_nonempty V with
  | inl hemp => simp at hG
  | inr hne =>
    obtain ⟨v⟩ := hne
    rcases OMA.Helpers.good_all _ _ G rfl rfl with h | h | h
    · exact h.exists_cycle
    · obtain ⟨a, b, c, hab, -, -, ha, hb, -⟩ := hbig v
      exact absurd (h v a b ha hb) hab
    · obtain ⟨u, hu, -, -⟩ := h v v
      exact absurd (hbig u) hu.2
