import OMAStatements.S_opg_a_gold_grabbing_game
import Mathlib

open OMA.S_opg_a_gold_grabbing_game Finset

namespace OMA.Helpers

theorem mem_support_of_dist_le {V : Type} {G : SimpleGraph V} (hG : G.IsAcyclic) {u v w : V}
    {p : G.Walk u v} (hp : p.IsPath) (hpl : p.length = G.dist u v) (hadj : G.Adj v w)
    (hd : G.dist u w ≤ G.dist u v) (hr : G.Reachable u v) : w ∈ p.support := by
  by_contra hw
  obtain ⟨q, hq, hql⟩ := (hr.trans hadj.reachable).exists_path_of_dist
  have hv : v ∈ q.support :=
    hG.mem_support_of_ne_mem_support_of_adj_of_isPath hq hp hadj.symm hw
  have := hG.path_concat hp hq hadj hv
  have h2 : q.length = p.length + 1 := by rw [this, SimpleGraph.Walk.length_concat]
  omega

theorem leaf_exists {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.IsTree)
    (s : Finset (Fin n)) (hs : s.Nonempty) : (leafMoves G s).Nonempty := by
  obtain ⟨u, hu⟩ := hs
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image s (fun x => G.dist u x) ⟨u, hu⟩
  refine ⟨v, ?_⟩
  unfold leafMoves
  rw [mem_filter]
  refine ⟨hv, ?_⟩
  by_contra hc
  rw [not_le] at hc
  obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.mp hc
  rw [mem_filter] at hw1 hw2
  have hr : G.Reachable u v := hG.connected u v
  obtain ⟨p, hp, hpl⟩ := hr.exists_path_of_dist
  have m1 := mem_support_of_dist_le hG.isAcyclic hp hpl hw1.2 (hmax w1 hw1.1) hr
  have m2 := mem_support_of_dist_le hG.isAcyclic hp hpl hw2.2 (hmax w2 hw2.1) hr
  have e1 := hG.isAcyclic.eq_penultimate_of_adj_end hp hw1.2 m1
  have e2 := hG.isAcyclic.eq_penultimate_of_adj_end hp hw2.2 m2
  exact hne (e1.trans e2.symm)

section game

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (gold : Fin n → ℕ)

/-- The value of a position for the player to move (backward induction). -/
noncomputable def val (s : Finset (Fin n)) : ℤ :=
  if h : (leafMoves G s).Nonempty then
    (leafMoves G s).attach.sup' (Finset.attach_nonempty_iff.mpr h)
      (fun v => (gold v.1 : ℤ) - val (s.erase v.1))
  else 0
termination_by s.card
decreasing_by exact card_erase_lt_of_mem (mem_filter.mp v.2).1

theorem val_pos (s : Finset (Fin n)) (h : (leafMoves G s).Nonempty) :
    val G gold s = (leafMoves G s).attach.sup' (Finset.attach_nonempty_iff.mpr h)
      (fun v => (gold v.1 : ℤ) - val G gold (s.erase v.1)) := by
  rw [val, dif_pos h]

theorem val_neg (s : Finset (Fin n)) (h : ¬ (leafMoves G s).Nonempty) : val G gold s = 0 := by
  rw [val, dif_neg h]

theorem le_val (s : Finset (Fin n)) (h : (leafMoves G s).Nonempty) (w : Fin n)
    (hw : w ∈ leafMoves G s) : (gold w : ℤ) - val G gold (s.erase w) ≤ val G gold s := by
  rw [val_pos G gold s h]
  exact Finset.le_sup' (fun v : {x // x ∈ leafMoves G s} => (gold v.1 : ℤ) - val G gold (s.erase v.1))
    (Finset.mem_attach _ ⟨w, hw⟩)

/-- An optimal move: one maximizing the gold taken minus the value left to the opponent. -/
noncomputable def best : Policy G := fun s h =>
  ⟨Classical.choose (Finset.exists_max_image (leafMoves G s)
      (fun v => (gold v : ℤ) - val G gold (s.erase v)) h),
    (Classical.choose_spec (Finset.exists_max_image (leafMoves G s)
      (fun v => (gold v : ℤ) - val G gold (s.erase v)) h)).1⟩

theorem best_spec (s : Finset (Fin n)) (h : (leafMoves G s).Nonempty) :
    val G gold s = (gold (best G gold s h).1 : ℤ) - val G gold (s.erase (best G gold s h).1) := by
  apply le_antisymm
  · rw [val_pos G gold s h]
    apply Finset.sup'_le
    intro v _
    exact (Classical.choose_spec (Finset.exists_max_image (leafMoves G s)
      (fun v => (gold v : ℤ) - val G gold (s.erase v)) h)).2 v.1 v.2
  · exact le_val G gold s h _ (best G gold s h).2

theorem main_ind (q : Policy G) : ∀ k, ∀ s : Finset (Fin n), s.card = k →
    playScore G gold s (best G gold) (best G gold) = val G gold s ∧
    playScore G gold s q (best G gold) ≤ val G gold s ∧
    val G gold s ≤ playScore G gold s (best G gold) q := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s hs
    by_cases h : (leafMoves G s).Nonempty
    · have hlt : ∀ v ∈ leafMoves G s, (s.erase v).card < k := fun v hv =>
        hs ▸ card_erase_lt_of_mem (mem_filter.mp hv).1
      have IH := fun v hv => ih _ (hlt v hv) (s.erase v) rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [playScore, dif_pos h]
        simp only
        rw [(IH _ (best G gold s h).2).1, ← best_spec]
      · rw [playScore, dif_pos h]
        simp only
        have := (IH _ (q s h).2).2.2
        have := le_val G gold s h _ (q s h).2
        linarith
      · rw [playScore, dif_pos h]
        simp only
        have := (IH _ (best G gold s h).2).2.1
        have := best_spec G gold s h
        linarith
    · rw [playScore, dif_neg h, playScore, dif_neg h, playScore, dif_neg h, val_neg G gold s h]
      simp

end game

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_opg_a_gold_grabbing_game.main := by
  intro n G _ hG gold
  refine ⟨OMA.Helpers.best G gold, fun q s => ⟨OMA.Helpers.leaf_exists G hG s, ?_, ?_⟩⟩
  · have := OMA.Helpers.main_ind G gold q s.card s rfl
    rw [this.1]
    exact this.2.1
  · have := OMA.Helpers.main_ind G gold q s.card s rfl
    rw [this.1]
    exact this.2.2
