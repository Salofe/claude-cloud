import OMAReductions.R_MonochromaticQuantumGraph_eqSystem6_no_solution_ge3_R1

/-!
# Step H1 of the reduction MonochromaticQuantumGraph.eqSystem6_no_solution_ge3.R1

Six vertices, three colours, complex weights, and every bichromatic edge has weight zero.
We show that the monochromatic quantum graph equations have no solution.

Write x_c(uv) for the weight of the monochromatic edge uv in colour c and Q_c(T) for the
perfect matching sum of colour c on the four vertices outside the pair T. The equations give

* (A) for each colour c, the sum over k of x_c(0k) Q_c(0k) equals 1 (constant colouring);
* (B) x_b(T) Q_a(T) = 0 for distinct colours a, b and every pair T (a 4+2 colouring);
* (C) x_a(T0) x_b(T1) x_c(T2) = 0 for a perfect matching T0 T1 T2 and distinct a, b, c.

By (A) each colour c has a partner p_c of vertex 0 with x_c(0 p_c) and Q_c(0 p_c) nonzero, and
(B) forces the three partners to be distinct. Relabelling the vertices 1, ..., 5 (the equations
are invariant, see `relab`) we may assume that the partners are 1, 2, 3. Each Q_c(0 p_c) is a
sum of three products, one of which is nonzero; in each of the 27 resulting cases a short
zero/nonzero propagation through (B) and (C) gives a contradiction.

Only the upstream definitions are used.
-/

open MonochromaticQuantumGraph

namespace OMA.Helpers

/-- Weight of the monochromatic edge `u v` in colour `c`. -/
def X (W : WeightsN 6 3 ℂ) (c : Fin 3) (u v : Fin 6) : ℂ := W ⟨u, v, c, c⟩

/-- Perfect matching sum of colour `c` on the four vertices `a b d e`. -/
def P4 (W : WeightsN 6 3 ℂ) (c : Fin 3) (a b d e : Fin 6) : ℂ :=
  X W c a b * X W c d e + X W c a d * X W c b e + X W c a e * X W c b d

/-- Bichromatic edges have weight zero. -/
def Mono (W : WeightsN 6 3 ℂ) : Prop := ∀ e : EdgeN 6 3, e.u < e.v → e.i ≠ e.j → W e = 0

/-- The perfect matching sum on six vertices, written out. -/
def F (W : WeightsN 6 3 ℂ) (ι : Fin 6 → Fin 3) : ℂ :=
  W ⟨0, 1, ι 0, ι 1⟩ *
    (W ⟨2, 3, ι 2, ι 3⟩ * W ⟨4, 5, ι 4, ι 5⟩ +
      W ⟨2, 4, ι 2, ι 4⟩ * W ⟨3, 5, ι 3, ι 5⟩ +
      W ⟨2, 5, ι 2, ι 5⟩ * W ⟨3, 4, ι 3, ι 4⟩) +
  W ⟨0, 2, ι 0, ι 2⟩ *
    (W ⟨1, 3, ι 1, ι 3⟩ * W ⟨4, 5, ι 4, ι 5⟩ +
      W ⟨1, 4, ι 1, ι 4⟩ * W ⟨3, 5, ι 3, ι 5⟩ +
      W ⟨1, 5, ι 1, ι 5⟩ * W ⟨3, 4, ι 3, ι 4⟩) +
  W ⟨0, 3, ι 0, ι 3⟩ *
    (W ⟨1, 2, ι 1, ι 2⟩ * W ⟨4, 5, ι 4, ι 5⟩ +
      W ⟨1, 4, ι 1, ι 4⟩ * W ⟨2, 5, ι 2, ι 5⟩ +
      W ⟨1, 5, ι 1, ι 5⟩ * W ⟨2, 4, ι 2, ι 4⟩) +
  W ⟨0, 4, ι 0, ι 4⟩ *
    (W ⟨1, 2, ι 1, ι 2⟩ * W ⟨3, 5, ι 3, ι 5⟩ +
      W ⟨1, 3, ι 1, ι 3⟩ * W ⟨2, 5, ι 2, ι 5⟩ +
      W ⟨1, 5, ι 1, ι 5⟩ * W ⟨2, 3, ι 2, ι 3⟩) +
  W ⟨0, 5, ι 0, ι 5⟩ *
    (W ⟨1, 2, ι 1, ι 2⟩ * W ⟨3, 4, ι 3, ι 4⟩ +
      W ⟨1, 3, ι 1, ι 3⟩ * W ⟨2, 4, ι 2, ι 4⟩ +
      W ⟨1, 4, ι 1, ι 4⟩ * W ⟨2, 3, ι 2, ι 3⟩)

theorem pm_formula (W : WeightsN 6 3 ℂ) (ι : Fin 6 → Fin 3) : pmSumN 6 3 W ι = F W ι := by
  simp only [F]
  simp [pmSumN, pmSumList, pmSumListAux, vertices, mkEdge]
  ring

theorem allEqual_iff (ι : Fin 6 → Fin 3) :
    allEqual ι ↔ (ι 0 = ι 1 ∧ ι 1 = ι 2 ∧ ι 2 = ι 3 ∧ ι 3 = ι 4 ∧ ι 4 = ι 5) := by
  simp [allEqual, allEqualList, vertices]

theorem eqsys_zero (W : WeightsN 6 3 ℂ) (hE : EqSystemN 6 3 W) (ι : Fin 6 → Fin 3)
    (h : ¬ (ι 0 = ι 1 ∧ ι 1 = ι 2 ∧ ι 2 = ι 3 ∧ ι 3 = ι 4 ∧ ι 4 = ι 5)) : F W ι = 0 := by
  have h2 := hE ι
  rw [pm_formula] at h2
  rw [h2, if_neg]
  rwa [allEqual_iff]

theorem eqsys_one (W : WeightsN 6 3 ℂ) (hE : EqSystemN 6 3 W) (c : Fin 3) :
    F W (fun _ => c) = 1 := by
  have h2 := hE (fun _ => c)
  rw [pm_formula] at h2
  rw [h2, if_pos]
  rw [allEqual_iff]
  simp

theorem mono_zero {W : WeightsN 6 3 ℂ} (hm : Mono W) {u v : Fin 6} {i j : Fin 3} (huv : u < v)
    (hij : i ≠ j) : W ⟨u, v, i, j⟩ = 0 := hm ⟨u, v, i, j⟩ huv hij

/- ### The 4+2 equations (B) -/

theorem fB_0_1 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W) (a b : Fin 3)
    (hab : a ≠ b) : X W b 0 1 * P4 W a 2 3 4 5 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have h := eqsys_zero W hE ![b, b, a, a, a, a] (by simp [hba])
  simp [F, mono_zero hm, hba, -mul_eq_zero] at h
  unfold P4 X
  linear_combination h

theorem fB_0_2 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W) (a b : Fin 3)
    (hab : a ≠ b) : X W b 0 2 * P4 W a 1 3 4 5 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have h := eqsys_zero W hE ![b, a, b, a, a, a] (by simp [hab, hba])
  simp [F, mono_zero hm, hab, hba, -mul_eq_zero] at h
  unfold P4 X
  linear_combination h

theorem fB_0_3 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W) (a b : Fin 3)
    (hab : a ≠ b) : X W b 0 3 * P4 W a 1 2 4 5 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have h := eqsys_zero W hE ![b, a, a, b, a, a] (by simp [hab, hba])
  simp [F, mono_zero hm, hab, hba, -mul_eq_zero] at h
  unfold P4 X
  linear_combination h

theorem fB_0_4 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W) (a b : Fin 3)
    (hab : a ≠ b) : X W b 0 4 * P4 W a 1 2 3 5 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have h := eqsys_zero W hE ![b, a, a, a, b, a] (by simp [hab, hba])
  simp [F, mono_zero hm, hab, hba, -mul_eq_zero] at h
  unfold P4 X
  linear_combination h

theorem fB_0_5 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W) (a b : Fin 3)
    (hab : a ≠ b) : X W b 0 5 * P4 W a 1 2 3 4 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have h := eqsys_zero W hE ![b, a, a, a, a, b] (by simp [hab, hba])
  simp [F, mono_zero hm, hab, hba, -mul_eq_zero] at h
  unfold P4 X
  linear_combination h

theorem fB_1_2 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W) (a b : Fin 3)
    (hab : a ≠ b) : X W b 1 2 * P4 W a 0 3 4 5 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have h := eqsys_zero W hE ![a, b, b, a, a, a] (by simp [hab, hba])
  simp [F, mono_zero hm, hab, hba, -mul_eq_zero] at h
  unfold P4 X
  linear_combination h

theorem fB_1_3 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W) (a b : Fin 3)
    (hab : a ≠ b) : X W b 1 3 * P4 W a 0 2 4 5 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have h := eqsys_zero W hE ![a, b, a, b, a, a] (by simp [hab, hba])
  simp [F, mono_zero hm, hab, hba, -mul_eq_zero] at h
  unfold P4 X
  linear_combination h

theorem fB_1_4 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W) (a b : Fin 3)
    (hab : a ≠ b) : X W b 1 4 * P4 W a 0 2 3 5 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have h := eqsys_zero W hE ![a, b, a, a, b, a] (by simp [hab, hba])
  simp [F, mono_zero hm, hab, hba, -mul_eq_zero] at h
  unfold P4 X
  linear_combination h

theorem fB_1_5 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W) (a b : Fin 3)
    (hab : a ≠ b) : X W b 1 5 * P4 W a 0 2 3 4 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have h := eqsys_zero W hE ![a, b, a, a, a, b] (by simp [hab, hba])
  simp [F, mono_zero hm, hab, hba, -mul_eq_zero] at h
  unfold P4 X
  linear_combination h

theorem fB_2_3 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W) (a b : Fin 3)
    (hab : a ≠ b) : X W b 2 3 * P4 W a 0 1 4 5 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have h := eqsys_zero W hE ![a, a, b, b, a, a] (by simp [hab, hba])
  simp [F, mono_zero hm, hab, hba, -mul_eq_zero] at h
  unfold P4 X
  linear_combination h

theorem fB_2_4 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W) (a b : Fin 3)
    (hab : a ≠ b) : X W b 2 4 * P4 W a 0 1 3 5 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have h := eqsys_zero W hE ![a, a, b, a, b, a] (by simp [hab, hba])
  simp [F, mono_zero hm, hab, hba, -mul_eq_zero] at h
  unfold P4 X
  linear_combination h

theorem fB_2_5 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W) (a b : Fin 3)
    (hab : a ≠ b) : X W b 2 5 * P4 W a 0 1 3 4 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have h := eqsys_zero W hE ![a, a, b, a, a, b] (by simp [hab, hba])
  simp [F, mono_zero hm, hab, hba, -mul_eq_zero] at h
  unfold P4 X
  linear_combination h

theorem fB_3_4 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W) (a b : Fin 3)
    (hab : a ≠ b) : X W b 3 4 * P4 W a 0 1 2 5 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have h := eqsys_zero W hE ![a, a, a, b, b, a] (by simp [hab, hba])
  simp [F, mono_zero hm, hab, hba, -mul_eq_zero] at h
  unfold P4 X
  linear_combination h

theorem fB_3_5 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W) (a b : Fin 3)
    (hab : a ≠ b) : X W b 3 5 * P4 W a 0 1 2 4 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have h := eqsys_zero W hE ![a, a, a, b, a, b] (by simp [hab, hba])
  simp [F, mono_zero hm, hab, hba, -mul_eq_zero] at h
  unfold P4 X
  linear_combination h

theorem fB_4_5 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W) (a b : Fin 3)
    (hab : a ≠ b) : X W b 4 5 * P4 W a 0 1 2 3 = 0 := by
  have h := eqsys_zero W hE ![a, a, a, a, b, b] (by simp [hab])
  simp [F, mono_zero hm, hab, -mul_eq_zero] at h
  unfold P4 X
  linear_combination h

/- ### The 2+2+2 equations (C) -/

theorem fC_01_23_45 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    X W a 0 1 * X W b 2 3 * X W c 4 5 = 0 := by
  have h := eqsys_zero W hE ![a, a, b, b, c, c] (by simp [hab, hbc])
  simp [F, mono_zero hm, hab, hac, hbc, -mul_eq_zero] at h
  unfold X
  linear_combination h

theorem fC_01_24_35 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    X W a 0 1 * X W b 2 4 * X W c 3 5 = 0 := by
  have hcb : c ≠ b := fun h => hbc h.symm
  have h := eqsys_zero W hE ![a, a, b, c, b, c] (by simp [hab, hbc, hcb])
  simp [F, mono_zero hm, hab, hac, hbc, hcb, -mul_eq_zero] at h
  unfold X
  linear_combination h

theorem fC_01_25_34 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    X W a 0 1 * X W b 2 5 * X W c 3 4 = 0 := by
  have hcb : c ≠ b := fun h => hbc h.symm
  have h := eqsys_zero W hE ![a, a, b, c, c, b] (by simp [hab, hbc, hcb])
  simp [F, mono_zero hm, hab, hac, hbc, hcb, -mul_eq_zero] at h
  unfold X
  linear_combination h

theorem fC_02_13_45 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    X W a 0 2 * X W b 1 3 * X W c 4 5 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have h := eqsys_zero W hE ![a, b, a, b, c, c] (by simp [hab, hba, hbc])
  simp [F, mono_zero hm, hab, hac, hba, hbc, -mul_eq_zero] at h
  unfold X
  linear_combination h

theorem fC_02_14_35 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    X W a 0 2 * X W b 1 4 * X W c 3 5 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have hcb : c ≠ b := fun h => hbc h.symm
  have h := eqsys_zero W hE ![a, b, a, c, b, c] (by simp [hab, hac, hba, hbc, hcb])
  simp [F, mono_zero hm, hab, hac, hba, hbc, hcb, -mul_eq_zero] at h
  unfold X
  linear_combination h

theorem fC_02_15_34 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    X W a 0 2 * X W b 1 5 * X W c 3 4 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have hcb : c ≠ b := fun h => hbc h.symm
  have h := eqsys_zero W hE ![a, b, a, c, c, b] (by simp [hab, hac, hba, hcb])
  simp [F, mono_zero hm, hab, hac, hba, hbc, hcb, -mul_eq_zero] at h
  unfold X
  linear_combination h

theorem fC_03_12_45 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    X W a 0 3 * X W b 1 2 * X W c 4 5 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have h := eqsys_zero W hE ![a, b, b, a, c, c] (by simp [hab, hac, hba])
  simp [F, mono_zero hm, hab, hac, hba, hbc, -mul_eq_zero] at h
  unfold X
  linear_combination h

theorem fC_03_14_25 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    X W a 0 3 * X W b 1 4 * X W c 2 5 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have hca : c ≠ a := fun h => hac h.symm
  have hcb : c ≠ b := fun h => hbc h.symm
  have h := eqsys_zero W hE ![a, b, c, a, b, c] (by simp [hab, hbc, hca])
  simp [F, mono_zero hm, hab, hac, hba, hbc, hca, hcb, -mul_eq_zero] at h
  unfold X
  linear_combination h

theorem fC_03_15_24 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    X W a 0 3 * X W b 1 5 * X W c 2 4 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have hca : c ≠ a := fun h => hac h.symm
  have hcb : c ≠ b := fun h => hbc h.symm
  have h := eqsys_zero W hE ![a, b, c, a, c, b] (by simp [hab, hac, hbc, hca, hcb])
  simp [F, mono_zero hm, hab, hac, hba, hbc, hca, hcb, -mul_eq_zero] at h
  unfold X
  linear_combination h

theorem fC_04_12_35 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    X W a 0 4 * X W b 1 2 * X W c 3 5 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have hca : c ≠ a := fun h => hac h.symm
  have h := eqsys_zero W hE ![a, b, b, c, a, c] (by simp [hab, hac, hbc, hca])
  simp [F, mono_zero hm, hab, hac, hba, hbc, hca, -mul_eq_zero] at h
  unfold X
  linear_combination h

theorem fC_04_13_25 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    X W a 0 4 * X W b 1 3 * X W c 2 5 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have hca : c ≠ a := fun h => hac h.symm
  have hcb : c ≠ b := fun h => hbc h.symm
  have h := eqsys_zero W hE ![a, b, c, b, a, c] (by simp [hab, hac, hba, hbc, hcb])
  simp [F, mono_zero hm, hab, hac, hba, hbc, hca, hcb, -mul_eq_zero] at h
  unfold X
  linear_combination h

theorem fC_04_15_23 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    X W a 0 4 * X W b 1 5 * X W c 2 3 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have hca : c ≠ a := fun h => hac h.symm
  have hcb : c ≠ b := fun h => hbc h.symm
  have h := eqsys_zero W hE ![a, b, c, c, a, b] (by simp [hab, hbc, hca])
  simp [F, mono_zero hm, hab, hac, hba, hbc, hca, hcb, -mul_eq_zero] at h
  unfold X
  linear_combination h

theorem fC_05_12_34 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    X W a 0 5 * X W b 1 2 * X W c 3 4 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have hca : c ≠ a := fun h => hac h.symm
  have h := eqsys_zero W hE ![a, b, b, c, c, a] (by simp [hab, hbc, hca])
  simp [F, mono_zero hm, hab, hac, hba, hbc, hca, -mul_eq_zero] at h
  unfold X
  linear_combination h

theorem fC_05_13_24 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    X W a 0 5 * X W b 1 3 * X W c 2 4 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have hca : c ≠ a := fun h => hac h.symm
  have hcb : c ≠ b := fun h => hbc h.symm
  have h := eqsys_zero W hE ![a, b, c, b, c, a] (by simp [hab, hbc, hca, hcb])
  simp [F, mono_zero hm, hab, hac, hba, hbc, hca, hcb, -mul_eq_zero] at h
  unfold X
  linear_combination h

theorem fC_05_14_23 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    X W a 0 5 * X W b 1 4 * X W c 2 3 = 0 := by
  have hba : b ≠ a := fun h => hab h.symm
  have hca : c ≠ a := fun h => hac h.symm
  have hcb : c ≠ b := fun h => hbc h.symm
  have h := eqsys_zero W hE ![a, b, c, c, b, a] (by simp [hab, hba, hbc, hcb])
  simp [F, mono_zero hm, hab, hac, hba, hbc, hca, hcb, -mul_eq_zero] at h
  unfold X
  linear_combination h

/- ### Zero/nonzero bookkeeping -/

theorem mz_l {x y : ℂ} (h : x * y = 0) (hy : y ≠ 0) : x = 0 :=
  (mul_eq_zero.mp h).resolve_right hy

theorem mz_r {x y : ℂ} (h : x * y = 0) (hx : x ≠ 0) : y = 0 :=
  (mul_eq_zero.mp h).resolve_left hx

theorem mz_ff {x y : ℂ} (h : x * y = 0) (hx : x ≠ 0) (hy : y ≠ 0) : False :=
  mul_ne_zero hx hy h

theorem t3_ff {x y z : ℂ} (h : x * y * z = 0) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) : False :=
  mul_ne_zero (mul_ne_zero hx hy) hz h

theorem t3_1 {x y z : ℂ} (h : x * y * z = 0) (hy : y ≠ 0) (hz : z ≠ 0) : x = 0 := by
  by_contra hx
  exact t3_ff h hx hy hz

theorem t3_2 {x y z : ℂ} (h : x * y * z = 0) (hx : x ≠ 0) (hz : z ≠ 0) : y = 0 := by
  by_contra hy
  exact t3_ff h hx hy hz

theorem t3_3 {x y z : ℂ} (h : x * y * z = 0) (hx : x ≠ 0) (hy : y ≠ 0) : z = 0 := by
  by_contra hz
  exact t3_ff h hx hy hz

theorem P4_ff_1 {W : WeightsN 6 3 ℂ} {c : Fin 3} {a b d e : Fin 6} (h : P4 W c a b d e = 0)
    (n1 : X W c a b ≠ 0) (n2 : X W c d e ≠ 0) (z2 : X W c a d * X W c b e = 0)
    (z3 : X W c a e * X W c b d = 0) : False := by
  unfold P4 at h
  rw [z2, z3, add_zero, add_zero] at h
  exact mul_ne_zero n1 n2 h

theorem P4_ff_2 {W : WeightsN 6 3 ℂ} {c : Fin 3} {a b d e : Fin 6} (h : P4 W c a b d e = 0)
    (n1 : X W c a d ≠ 0) (n2 : X W c b e ≠ 0) (z1 : X W c a b * X W c d e = 0)
    (z3 : X W c a e * X W c b d = 0) : False := by
  unfold P4 at h
  rw [z1, z3, zero_add, add_zero] at h
  exact mul_ne_zero n1 n2 h

theorem P4_ff_3 {W : WeightsN 6 3 ℂ} {c : Fin 3} {a b d e : Fin 6} (h : P4 W c a b d e = 0)
    (n1 : X W c a e ≠ 0) (n2 : X W c b d ≠ 0) (z1 : X W c a b * X W c d e = 0)
    (z2 : X W c a d * X W c b e = 0) : False := by
  unfold P4 at h
  rw [z1, z2, zero_add, zero_add] at h
  exact mul_ne_zero n1 n2 h

theorem P4_cases {W : WeightsN 6 3 ℂ} {c : Fin 3} {a b d e : Fin 6} (h : P4 W c a b d e ≠ 0) :
    (X W c a b ≠ 0 ∧ X W c d e ≠ 0) ∨ (X W c a d ≠ 0 ∧ X W c b e ≠ 0) ∨
      (X W c a e ≠ 0 ∧ X W c b d ≠ 0) := by
  unfold P4 at h
  by_cases h1 : X W c a b * X W c d e = 0
  · by_cases h2 : X W c a d * X W c b e = 0
    · rw [h1, h2, zero_add, zero_add] at h
      exact Or.inr (Or.inr ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩)
    · exact Or.inr (Or.inl ⟨left_ne_zero_of_mul h2, right_ne_zero_of_mul h2⟩)
  · exact Or.inl ⟨left_ne_zero_of_mul h1, right_ne_zero_of_mul h1⟩

/- ### The 27 cases with partners 1, 2, 3 -/

theorem leaf_000 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (_o1 : X W 1 0 2 ≠ 0)
    (q1 : P4 W 1 1 3 4 5 ≠ 0) (_o2 : X W 2 0 3 ≠ 0) (q2 : P4 W 2 1 2 4 5 ≠ 0)
    (a0 : X W 0 2 3 ≠ 0) (_b0 : X W 0 4 5 ≠ 0)
    (_a1 : X W 1 1 3 ≠ 0) (b1 : X W 1 4 5 ≠ 0)
    (_a2 : X W 2 1 2 ≠ 0) (_b2 : X W 2 4 5 ≠ 0) : False := by
  have d1 : X W 0 0 2 = 0 :=
    mz_l (fB_0_2 W hm hE 1 0 (by decide)) q1
  have d2 : X W 0 0 3 = 0 :=
    mz_l (fB_0_3 W hm hE 2 0 (by decide)) q2
  have d3 : P4 W 0 0 1 2 3 = 0 :=
    mz_r (fB_4_5 W hm hE 0 1 (by decide)) b1
  exact P4_ff_1 d3 o0 a0
    (mul_eq_zero_of_left d1 _) (mul_eq_zero_of_left d2 _)

theorem leaf_001 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (_o1 : X W 1 0 2 ≠ 0)
    (q1 : P4 W 1 1 3 4 5 ≠ 0) (_o2 : X W 2 0 3 ≠ 0) (q2 : P4 W 2 1 2 4 5 ≠ 0)
    (a0 : X W 0 2 3 ≠ 0) (_b0 : X W 0 4 5 ≠ 0)
    (_a1 : X W 1 1 3 ≠ 0) (b1 : X W 1 4 5 ≠ 0)
    (_a2 : X W 2 1 4 ≠ 0) (_b2 : X W 2 2 5 ≠ 0) : False := by
  have d1 : X W 0 0 2 = 0 :=
    mz_l (fB_0_2 W hm hE 1 0 (by decide)) q1
  have d2 : X W 0 0 3 = 0 :=
    mz_l (fB_0_3 W hm hE 2 0 (by decide)) q2
  have d3 : P4 W 0 0 1 2 3 = 0 :=
    mz_r (fB_4_5 W hm hE 0 1 (by decide)) b1
  exact P4_ff_1 d3 o0 a0
    (mul_eq_zero_of_left d1 _) (mul_eq_zero_of_left d2 _)

theorem leaf_002 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (_o1 : X W 1 0 2 ≠ 0)
    (q1 : P4 W 1 1 3 4 5 ≠ 0) (_o2 : X W 2 0 3 ≠ 0) (q2 : P4 W 2 1 2 4 5 ≠ 0)
    (a0 : X W 0 2 3 ≠ 0) (_b0 : X W 0 4 5 ≠ 0)
    (_a1 : X W 1 1 3 ≠ 0) (b1 : X W 1 4 5 ≠ 0)
    (_a2 : X W 2 1 5 ≠ 0) (_b2 : X W 2 2 4 ≠ 0) : False := by
  have d1 : X W 0 0 2 = 0 :=
    mz_l (fB_0_2 W hm hE 1 0 (by decide)) q1
  have d2 : X W 0 0 3 = 0 :=
    mz_l (fB_0_3 W hm hE 2 0 (by decide)) q2
  have d3 : P4 W 0 0 1 2 3 = 0 :=
    mz_r (fB_4_5 W hm hE 0 1 (by decide)) b1
  exact P4_ff_1 d3 o0 a0
    (mul_eq_zero_of_left d1 _) (mul_eq_zero_of_left d2 _)

theorem leaf_010 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (_o1 : X W 1 0 2 ≠ 0)
    (q1 : P4 W 1 1 3 4 5 ≠ 0) (_o2 : X W 2 0 3 ≠ 0) (q2 : P4 W 2 1 2 4 5 ≠ 0)
    (a0 : X W 0 2 3 ≠ 0) (_b0 : X W 0 4 5 ≠ 0)
    (_a1 : X W 1 1 4 ≠ 0) (_b1 : X W 1 3 5 ≠ 0)
    (_a2 : X W 2 1 2 ≠ 0) (b2 : X W 2 4 5 ≠ 0) : False := by
  have d1 : X W 0 0 2 = 0 :=
    mz_l (fB_0_2 W hm hE 1 0 (by decide)) q1
  have d2 : X W 0 0 3 = 0 :=
    mz_l (fB_0_3 W hm hE 2 0 (by decide)) q2
  have d3 : P4 W 0 0 1 2 3 = 0 :=
    mz_r (fB_4_5 W hm hE 0 2 (by decide)) b2
  exact P4_ff_1 d3 o0 a0
    (mul_eq_zero_of_left d1 _) (mul_eq_zero_of_left d2 _)

theorem leaf_011 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (_o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (o1 : X W 1 0 2 ≠ 0)
    (_q1 : P4 W 1 1 3 4 5 ≠ 0) (_o2 : X W 2 0 3 ≠ 0) (q2 : P4 W 2 1 2 4 5 ≠ 0)
    (a0 : X W 0 2 3 ≠ 0) (_b0 : X W 0 4 5 ≠ 0)
    (_a1 : X W 1 1 4 ≠ 0) (b1 : X W 1 3 5 ≠ 0)
    (a2 : X W 2 1 4 ≠ 0) (_b2 : X W 2 2 5 ≠ 0) : False := by
  have d1 : X W 1 0 3 = 0 :=
    mz_l (fB_0_3 W hm hE 2 1 (by decide)) q2
  have d2 : P4 W 1 0 2 3 5 = 0 :=
    mz_r (fB_1_4 W hm hE 1 2 (by decide)) a2
  have d3 : X W 1 0 5 = 0 :=
    (t3_1 (fC_05_14_23 W hm hE 1 2 0 (by decide) (by decide) (by decide)) a2 a0)
  exact P4_ff_1 d2 o1 b1
    (mul_eq_zero_of_left d1 _) (mul_eq_zero_of_left d3 _)

theorem leaf_012 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (_o1 : X W 1 0 2 ≠ 0)
    (_q1 : P4 W 1 1 3 4 5 ≠ 0) (_o2 : X W 2 0 3 ≠ 0) (_q2 : P4 W 2 1 2 4 5 ≠ 0)
    (_a0 : X W 0 2 3 ≠ 0) (_b0 : X W 0 4 5 ≠ 0)
    (_a1 : X W 1 1 4 ≠ 0) (b1 : X W 1 3 5 ≠ 0)
    (_a2 : X W 2 1 5 ≠ 0) (b2 : X W 2 2 4 ≠ 0) : False := by
  exact t3_ff (fC_01_24_35 W hm hE 0 2 1 (by decide) (by decide) (by decide))
    o0 b2 b1

theorem leaf_020 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (_o1 : X W 1 0 2 ≠ 0)
    (q1 : P4 W 1 1 3 4 5 ≠ 0) (_o2 : X W 2 0 3 ≠ 0) (q2 : P4 W 2 1 2 4 5 ≠ 0)
    (a0 : X W 0 2 3 ≠ 0) (_b0 : X W 0 4 5 ≠ 0)
    (_a1 : X W 1 1 5 ≠ 0) (_b1 : X W 1 3 4 ≠ 0)
    (_a2 : X W 2 1 2 ≠ 0) (b2 : X W 2 4 5 ≠ 0) : False := by
  have d1 : X W 0 0 2 = 0 :=
    mz_l (fB_0_2 W hm hE 1 0 (by decide)) q1
  have d2 : X W 0 0 3 = 0 :=
    mz_l (fB_0_3 W hm hE 2 0 (by decide)) q2
  have d3 : P4 W 0 0 1 2 3 = 0 :=
    mz_r (fB_4_5 W hm hE 0 2 (by decide)) b2
  exact P4_ff_1 d3 o0 a0
    (mul_eq_zero_of_left d1 _) (mul_eq_zero_of_left d2 _)

theorem leaf_021 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (_o1 : X W 1 0 2 ≠ 0)
    (_q1 : P4 W 1 1 3 4 5 ≠ 0) (_o2 : X W 2 0 3 ≠ 0) (_q2 : P4 W 2 1 2 4 5 ≠ 0)
    (_a0 : X W 0 2 3 ≠ 0) (_b0 : X W 0 4 5 ≠ 0)
    (_a1 : X W 1 1 5 ≠ 0) (b1 : X W 1 3 4 ≠ 0)
    (_a2 : X W 2 1 4 ≠ 0) (b2 : X W 2 2 5 ≠ 0) : False := by
  exact t3_ff (fC_01_25_34 W hm hE 0 2 1 (by decide) (by decide) (by decide))
    o0 b2 b1

theorem leaf_022 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (_o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (o1 : X W 1 0 2 ≠ 0)
    (_q1 : P4 W 1 1 3 4 5 ≠ 0) (_o2 : X W 2 0 3 ≠ 0) (q2 : P4 W 2 1 2 4 5 ≠ 0)
    (a0 : X W 0 2 3 ≠ 0) (_b0 : X W 0 4 5 ≠ 0)
    (_a1 : X W 1 1 5 ≠ 0) (b1 : X W 1 3 4 ≠ 0)
    (a2 : X W 2 1 5 ≠ 0) (_b2 : X W 2 2 4 ≠ 0) : False := by
  have d1 : X W 1 0 3 = 0 :=
    mz_l (fB_0_3 W hm hE 2 1 (by decide)) q2
  have d2 : P4 W 1 0 2 3 4 = 0 :=
    mz_r (fB_1_5 W hm hE 1 2 (by decide)) a2
  have d3 : X W 1 0 4 = 0 :=
    (t3_1 (fC_04_15_23 W hm hE 1 2 0 (by decide) (by decide) (by decide)) a2 a0)
  exact P4_ff_1 d2 o1 b1
    (mul_eq_zero_of_left d1 _) (mul_eq_zero_of_left d3 _)

theorem leaf_100 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (_o0 : X W 0 0 1 ≠ 0) (q0 : P4 W 0 2 3 4 5 ≠ 0) (o1 : X W 1 0 2 ≠ 0)
    (_q1 : P4 W 1 1 3 4 5 ≠ 0) (_o2 : X W 2 0 3 ≠ 0) (q2 : P4 W 2 1 2 4 5 ≠ 0)
    (_a0 : X W 0 2 4 ≠ 0) (_b0 : X W 0 3 5 ≠ 0)
    (a1 : X W 1 1 3 ≠ 0) (_b1 : X W 1 4 5 ≠ 0)
    (_a2 : X W 2 1 2 ≠ 0) (b2 : X W 2 4 5 ≠ 0) : False := by
  have d1 : X W 1 0 1 = 0 :=
    mz_l (fB_0_1 W hm hE 0 1 (by decide)) q0
  have d2 : X W 1 0 3 = 0 :=
    mz_l (fB_0_3 W hm hE 2 1 (by decide)) q2
  have d3 : P4 W 1 0 1 2 3 = 0 :=
    mz_r (fB_4_5 W hm hE 1 2 (by decide)) b2
  exact P4_ff_2 d3 o1 a1
    (mul_eq_zero_of_left d1 _) (mul_eq_zero_of_left d2 _)

theorem leaf_101 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (_o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (o1 : X W 1 0 2 ≠ 0)
    (_q1 : P4 W 1 1 3 4 5 ≠ 0) (_o2 : X W 2 0 3 ≠ 0) (_q2 : P4 W 2 1 2 4 5 ≠ 0)
    (_a0 : X W 0 2 4 ≠ 0) (b0 : X W 0 3 5 ≠ 0)
    (_a1 : X W 1 1 3 ≠ 0) (_b1 : X W 1 4 5 ≠ 0)
    (a2 : X W 2 1 4 ≠ 0) (_b2 : X W 2 2 5 ≠ 0) : False := by
  exact t3_ff (fC_02_14_35 W hm hE 1 2 0 (by decide) (by decide) (by decide))
    o1 a2 b0

theorem leaf_102 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (_o1 : X W 1 0 2 ≠ 0)
    (_q1 : P4 W 1 1 3 4 5 ≠ 0) (_o2 : X W 2 0 3 ≠ 0) (q2 : P4 W 2 1 2 4 5 ≠ 0)
    (_a0 : X W 0 2 4 ≠ 0) (b0 : X W 0 3 5 ≠ 0)
    (a1 : X W 1 1 3 ≠ 0) (_b1 : X W 1 4 5 ≠ 0)
    (_a2 : X W 2 1 5 ≠ 0) (b2 : X W 2 2 4 ≠ 0) : False := by
  have d1 : X W 0 0 3 = 0 :=
    mz_l (fB_0_3 W hm hE 2 0 (by decide)) q2
  have d2 : P4 W 0 0 1 3 5 = 0 :=
    mz_r (fB_2_4 W hm hE 0 2 (by decide)) b2
  have d3 : X W 0 0 5 = 0 :=
    (t3_1 (fC_05_13_24 W hm hE 0 1 2 (by decide) (by decide) (by decide)) a1 b2)
  exact P4_ff_1 d2 o0 b0
    (mul_eq_zero_of_left d1 _) (mul_eq_zero_of_left d3 _)

theorem leaf_110 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (_o1 : X W 1 0 2 ≠ 0)
    (q1 : P4 W 1 1 3 4 5 ≠ 0) (_o2 : X W 2 0 3 ≠ 0) (_q2 : P4 W 2 1 2 4 5 ≠ 0)
    (a0 : X W 0 2 4 ≠ 0) (_b0 : X W 0 3 5 ≠ 0)
    (_a1 : X W 1 1 4 ≠ 0) (b1 : X W 1 3 5 ≠ 0)
    (a2 : X W 2 1 2 ≠ 0) (_b2 : X W 2 4 5 ≠ 0) : False := by
  have d1 : X W 0 0 2 = 0 :=
    mz_l (fB_0_2 W hm hE 1 0 (by decide)) q1
  have d2 : P4 W 0 0 1 2 4 = 0 :=
    mz_r (fB_3_5 W hm hE 0 1 (by decide)) b1
  have d3 : X W 0 0 4 = 0 :=
    (t3_1 (fC_04_12_35 W hm hE 0 2 1 (by decide) (by decide) (by decide)) a2 b1)
  exact P4_ff_1 d2 o0 a0
    (mul_eq_zero_of_left d1 _) (mul_eq_zero_of_left d3 _)

theorem leaf_111 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (_o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (o1 : X W 1 0 2 ≠ 0)
    (_q1 : P4 W 1 1 3 4 5 ≠ 0) (_o2 : X W 2 0 3 ≠ 0) (_q2 : P4 W 2 1 2 4 5 ≠ 0)
    (_a0 : X W 0 2 4 ≠ 0) (b0 : X W 0 3 5 ≠ 0)
    (_a1 : X W 1 1 4 ≠ 0) (_b1 : X W 1 3 5 ≠ 0)
    (a2 : X W 2 1 4 ≠ 0) (_b2 : X W 2 2 5 ≠ 0) : False := by
  exact t3_ff (fC_02_14_35 W hm hE 1 2 0 (by decide) (by decide) (by decide))
    o1 a2 b0

theorem leaf_112 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (_o1 : X W 1 0 2 ≠ 0)
    (_q1 : P4 W 1 1 3 4 5 ≠ 0) (_o2 : X W 2 0 3 ≠ 0) (_q2 : P4 W 2 1 2 4 5 ≠ 0)
    (_a0 : X W 0 2 4 ≠ 0) (_b0 : X W 0 3 5 ≠ 0)
    (_a1 : X W 1 1 4 ≠ 0) (b1 : X W 1 3 5 ≠ 0)
    (_a2 : X W 2 1 5 ≠ 0) (b2 : X W 2 2 4 ≠ 0) : False := by
  exact t3_ff (fC_01_24_35 W hm hE 0 2 1 (by decide) (by decide) (by decide))
    o0 b2 b1

theorem leaf_120 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (_o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (_o1 : X W 1 0 2 ≠ 0)
    (_q1 : P4 W 1 1 3 4 5 ≠ 0) (o2 : X W 2 0 3 ≠ 0) (_q2 : P4 W 2 1 2 4 5 ≠ 0)
    (a0 : X W 0 2 4 ≠ 0) (_b0 : X W 0 3 5 ≠ 0)
    (a1 : X W 1 1 5 ≠ 0) (_b1 : X W 1 3 4 ≠ 0)
    (_a2 : X W 2 1 2 ≠ 0) (_b2 : X W 2 4 5 ≠ 0) : False := by
  exact t3_ff (fC_03_15_24 W hm hE 2 1 0 (by decide) (by decide) (by decide))
    o2 a1 a0

theorem leaf_121 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (_o1 : X W 1 0 2 ≠ 0)
    (_q1 : P4 W 1 1 3 4 5 ≠ 0) (_o2 : X W 2 0 3 ≠ 0) (_q2 : P4 W 2 1 2 4 5 ≠ 0)
    (_a0 : X W 0 2 4 ≠ 0) (_b0 : X W 0 3 5 ≠ 0)
    (_a1 : X W 1 1 5 ≠ 0) (b1 : X W 1 3 4 ≠ 0)
    (_a2 : X W 2 1 4 ≠ 0) (b2 : X W 2 2 5 ≠ 0) : False := by
  exact t3_ff (fC_01_25_34 W hm hE 0 2 1 (by decide) (by decide) (by decide))
    o0 b2 b1

theorem leaf_122 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (_o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (_o1 : X W 1 0 2 ≠ 0)
    (_q1 : P4 W 1 1 3 4 5 ≠ 0) (o2 : X W 2 0 3 ≠ 0) (_q2 : P4 W 2 1 2 4 5 ≠ 0)
    (a0 : X W 0 2 4 ≠ 0) (_b0 : X W 0 3 5 ≠ 0)
    (a1 : X W 1 1 5 ≠ 0) (_b1 : X W 1 3 4 ≠ 0)
    (_a2 : X W 2 1 5 ≠ 0) (_b2 : X W 2 2 4 ≠ 0) : False := by
  exact t3_ff (fC_03_15_24 W hm hE 2 1 0 (by decide) (by decide) (by decide))
    o2 a1 a0

theorem leaf_200 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (_o0 : X W 0 0 1 ≠ 0) (q0 : P4 W 0 2 3 4 5 ≠ 0) (o1 : X W 1 0 2 ≠ 0)
    (_q1 : P4 W 1 1 3 4 5 ≠ 0) (_o2 : X W 2 0 3 ≠ 0) (q2 : P4 W 2 1 2 4 5 ≠ 0)
    (_a0 : X W 0 2 5 ≠ 0) (_b0 : X W 0 3 4 ≠ 0)
    (a1 : X W 1 1 3 ≠ 0) (_b1 : X W 1 4 5 ≠ 0)
    (_a2 : X W 2 1 2 ≠ 0) (b2 : X W 2 4 5 ≠ 0) : False := by
  have d1 : X W 1 0 1 = 0 :=
    mz_l (fB_0_1 W hm hE 0 1 (by decide)) q0
  have d2 : X W 1 0 3 = 0 :=
    mz_l (fB_0_3 W hm hE 2 1 (by decide)) q2
  have d3 : P4 W 1 0 1 2 3 = 0 :=
    mz_r (fB_4_5 W hm hE 1 2 (by decide)) b2
  exact P4_ff_2 d3 o1 a1
    (mul_eq_zero_of_left d1 _) (mul_eq_zero_of_left d2 _)

theorem leaf_201 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (_o1 : X W 1 0 2 ≠ 0)
    (_q1 : P4 W 1 1 3 4 5 ≠ 0) (_o2 : X W 2 0 3 ≠ 0) (q2 : P4 W 2 1 2 4 5 ≠ 0)
    (_a0 : X W 0 2 5 ≠ 0) (b0 : X W 0 3 4 ≠ 0)
    (a1 : X W 1 1 3 ≠ 0) (_b1 : X W 1 4 5 ≠ 0)
    (_a2 : X W 2 1 4 ≠ 0) (b2 : X W 2 2 5 ≠ 0) : False := by
  have d1 : X W 0 0 3 = 0 :=
    mz_l (fB_0_3 W hm hE 2 0 (by decide)) q2
  have d2 : P4 W 0 0 1 3 4 = 0 :=
    mz_r (fB_2_5 W hm hE 0 2 (by decide)) b2
  have d3 : X W 0 0 4 = 0 :=
    (t3_1 (fC_04_13_25 W hm hE 0 1 2 (by decide) (by decide) (by decide)) a1 b2)
  exact P4_ff_1 d2 o0 b0
    (mul_eq_zero_of_left d1 _) (mul_eq_zero_of_left d3 _)

theorem leaf_202 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (_o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (o1 : X W 1 0 2 ≠ 0)
    (_q1 : P4 W 1 1 3 4 5 ≠ 0) (_o2 : X W 2 0 3 ≠ 0) (_q2 : P4 W 2 1 2 4 5 ≠ 0)
    (_a0 : X W 0 2 5 ≠ 0) (b0 : X W 0 3 4 ≠ 0)
    (_a1 : X W 1 1 3 ≠ 0) (_b1 : X W 1 4 5 ≠ 0)
    (a2 : X W 2 1 5 ≠ 0) (_b2 : X W 2 2 4 ≠ 0) : False := by
  exact t3_ff (fC_02_15_34 W hm hE 1 2 0 (by decide) (by decide) (by decide))
    o1 a2 b0

theorem leaf_210 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (_o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (_o1 : X W 1 0 2 ≠ 0)
    (_q1 : P4 W 1 1 3 4 5 ≠ 0) (o2 : X W 2 0 3 ≠ 0) (_q2 : P4 W 2 1 2 4 5 ≠ 0)
    (a0 : X W 0 2 5 ≠ 0) (_b0 : X W 0 3 4 ≠ 0)
    (a1 : X W 1 1 4 ≠ 0) (_b1 : X W 1 3 5 ≠ 0)
    (_a2 : X W 2 1 2 ≠ 0) (_b2 : X W 2 4 5 ≠ 0) : False := by
  exact t3_ff (fC_03_14_25 W hm hE 2 1 0 (by decide) (by decide) (by decide))
    o2 a1 a0

theorem leaf_211 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (_o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (_o1 : X W 1 0 2 ≠ 0)
    (_q1 : P4 W 1 1 3 4 5 ≠ 0) (o2 : X W 2 0 3 ≠ 0) (_q2 : P4 W 2 1 2 4 5 ≠ 0)
    (a0 : X W 0 2 5 ≠ 0) (_b0 : X W 0 3 4 ≠ 0)
    (a1 : X W 1 1 4 ≠ 0) (_b1 : X W 1 3 5 ≠ 0)
    (_a2 : X W 2 1 4 ≠ 0) (_b2 : X W 2 2 5 ≠ 0) : False := by
  exact t3_ff (fC_03_14_25 W hm hE 2 1 0 (by decide) (by decide) (by decide))
    o2 a1 a0

theorem leaf_212 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (_o1 : X W 1 0 2 ≠ 0)
    (_q1 : P4 W 1 1 3 4 5 ≠ 0) (_o2 : X W 2 0 3 ≠ 0) (_q2 : P4 W 2 1 2 4 5 ≠ 0)
    (_a0 : X W 0 2 5 ≠ 0) (_b0 : X W 0 3 4 ≠ 0)
    (_a1 : X W 1 1 4 ≠ 0) (b1 : X W 1 3 5 ≠ 0)
    (_a2 : X W 2 1 5 ≠ 0) (b2 : X W 2 2 4 ≠ 0) : False := by
  exact t3_ff (fC_01_24_35 W hm hE 0 2 1 (by decide) (by decide) (by decide))
    o0 b2 b1

theorem leaf_220 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (_o1 : X W 1 0 2 ≠ 0)
    (q1 : P4 W 1 1 3 4 5 ≠ 0) (_o2 : X W 2 0 3 ≠ 0) (_q2 : P4 W 2 1 2 4 5 ≠ 0)
    (a0 : X W 0 2 5 ≠ 0) (_b0 : X W 0 3 4 ≠ 0)
    (_a1 : X W 1 1 5 ≠ 0) (b1 : X W 1 3 4 ≠ 0)
    (a2 : X W 2 1 2 ≠ 0) (_b2 : X W 2 4 5 ≠ 0) : False := by
  have d1 : X W 0 0 2 = 0 :=
    mz_l (fB_0_2 W hm hE 1 0 (by decide)) q1
  have d2 : P4 W 0 0 1 2 5 = 0 :=
    mz_r (fB_3_4 W hm hE 0 1 (by decide)) b1
  have d3 : X W 0 0 5 = 0 :=
    (t3_1 (fC_05_12_34 W hm hE 0 2 1 (by decide) (by decide) (by decide)) a2 b1)
  exact P4_ff_1 d2 o0 a0
    (mul_eq_zero_of_left d1 _) (mul_eq_zero_of_left d3 _)

theorem leaf_221 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (_o1 : X W 1 0 2 ≠ 0)
    (_q1 : P4 W 1 1 3 4 5 ≠ 0) (_o2 : X W 2 0 3 ≠ 0) (_q2 : P4 W 2 1 2 4 5 ≠ 0)
    (_a0 : X W 0 2 5 ≠ 0) (_b0 : X W 0 3 4 ≠ 0)
    (_a1 : X W 1 1 5 ≠ 0) (b1 : X W 1 3 4 ≠ 0)
    (_a2 : X W 2 1 4 ≠ 0) (b2 : X W 2 2 5 ≠ 0) : False := by
  exact t3_ff (fC_01_25_34 W hm hE 0 2 1 (by decide) (by decide) (by decide))
    o0 b2 b1

theorem leaf_222 (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (_o0 : X W 0 0 1 ≠ 0) (_q0 : P4 W 0 2 3 4 5 ≠ 0) (o1 : X W 1 0 2 ≠ 0)
    (_q1 : P4 W 1 1 3 4 5 ≠ 0) (_o2 : X W 2 0 3 ≠ 0) (_q2 : P4 W 2 1 2 4 5 ≠ 0)
    (_a0 : X W 0 2 5 ≠ 0) (b0 : X W 0 3 4 ≠ 0)
    (_a1 : X W 1 1 5 ≠ 0) (_b1 : X W 1 3 4 ≠ 0)
    (a2 : X W 2 1 5 ≠ 0) (_b2 : X W 2 2 4 ≠ 0) : False := by
  exact t3_ff (fC_02_15_34 W hm hE 1 2 0 (by decide) (by decide) (by decide))
    o1 a2 b0

theorem core (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W)
    (o0 : X W 0 0 1 ≠ 0) (q0 : P4 W 0 2 3 4 5 ≠ 0) (o1 : X W 1 0 2 ≠ 0) (q1 : P4 W 1 1 3 4 5 ≠ 0)
    (o2 : X W 2 0 3 ≠ 0) (q2 : P4 W 2 1 2 4 5 ≠ 0) : False := by
  rcases P4_cases q0 with ⟨a0, b0⟩ | ⟨a0, b0⟩ | ⟨a0, b0⟩ <;>
  rcases P4_cases q1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ | ⟨a1, b1⟩ <;>
  rcases P4_cases q2 with ⟨a2, b2⟩ | ⟨a2, b2⟩ | ⟨a2, b2⟩
  · exact leaf_000 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_001 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_002 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_010 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_011 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_012 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_020 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_021 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_022 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_100 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_101 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_102 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_110 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_111 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_112 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_120 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_121 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_122 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_200 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_201 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_202 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_210 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_211 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_212 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_220 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_221 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2
  · exact leaf_222 W hm hE o0 q0 o1 q1 o2 q2 a0 b0 a1 b1 a2 b2

/- ### Relabelling the vertices -/

/-- The weights obtained by renaming the vertices with `s`. -/
def relab (s : Fin 6 → Fin 6) (W : WeightsN 6 3 ℂ) : WeightsN 6 3 ℂ :=
  fun e => if s e.u < s e.v then W ⟨s e.u, s e.v, e.i, e.j⟩ else W ⟨s e.v, s e.u, e.j, e.i⟩

theorem relab_mono (s : Fin 6 → Fin 6) (hs : Function.Injective s) (W : WeightsN 6 3 ℂ)
    (hm : Mono W) : Mono (relab s W) := by
  intro e huv hij
  unfold relab
  split_ifs with h
  · exact hm _ h hij
  · have hne : s e.v ≠ s e.u := fun h2 => (ne_of_lt huv) (hs h2).symm
    exact hm ⟨s e.v, s e.u, e.j, e.i⟩ (lt_of_le_of_ne (not_lt.mp h) hne) (Ne.symm hij)

theorem allEqual_iff2 (ι : Fin 6 → Fin 3) : allEqual ι ↔ ∀ i, ι i = ι 0 := by
  rw [allEqual_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩ i
    fin_cases i <;> simp_all
  · intro h
    rw [h 1, h 2, h 3, h 4, h 5]
    simp

theorem allEqual_comp (ι : Fin 6 → Fin 3) (s : Fin 6 → Fin 6) (hs : Function.Surjective s) :
    allEqual (fun v => ι (s v)) ↔ allEqual ι := by
  rw [allEqual_iff2, allEqual_iff2]
  constructor
  · intro h i
    obtain ⟨j, rfl⟩ := hs i
    obtain ⟨k, hk⟩ := hs 0
    rw [h j, ← h k, hk]
  · intro h i
    rw [h (s i), h (s 0)]

/-- Perfect matching sum of colour `c` outside the pair `0 k`. -/
def Qk (W : WeightsN 6 3 ℂ) (c : Fin 3) : Fin 6 → ℂ :=
  ![0, P4 W c 2 3 4 5, P4 W c 1 3 4 5, P4 W c 1 2 4 5, P4 W c 1 2 3 5, P4 W c 1 2 3 4]

/-- `k` is a partner of vertex `0` in colour `c`. -/
def Own (W : WeightsN 6 3 ℂ) (c : Fin 3) (k : Fin 6) : Prop := X W c 0 k ≠ 0 ∧ Qk W c k ≠ 0

/-- No solution has the partners `a b c` for the colours `0 1 2`. -/
def Good (a b c : Fin 6) : Prop :=
  ∀ W : WeightsN 6 3 ℂ, Mono W → EqSystemN 6 3 W → Own W 0 a → Own W 1 b → Own W 2 c → False

theorem good_1_2_3 : Good 1 2 3 := by
  intro W hm hE h0 h1 h2
  exact core W hm hE h0.1 (by simpa [Qk] using h0.2) h1.1 (by simpa [Qk] using h1.2) h2.1
    (by simpa [Qk] using h2.2)

theorem relab_eqsys_1 (W : WeightsN 6 3 ℂ) (hE : EqSystemN 6 3 W) :
    EqSystemN 6 3 (relab ![0, 2, 1, 3, 4, 5] W) := by
  intro ι
  have h := hE (fun v => ι (![0, 2, 1, 3, 4, 5] v))
  rw [pm_formula] at h ⊢
  have e1 : F (relab ![0, 2, 1, 3, 4, 5] W) ι =
      F W (fun v => ι (![0, 2, 1, 3, 4, 5] v)) := by
    simp [F, relab]
    ring
  rw [e1, h]
  have hs : Function.Surjective (![0, 2, 1, 3, 4, 5] : Fin 6 → Fin 6) := by decide
  simp only [allEqual_comp ι _ hs]

theorem relab_X0_1 (W : WeightsN 6 3 ℂ) (c : Fin 3) (j : Fin 6) :
    X (relab ![0, 2, 1, 3, 4, 5] W) c 0 (![0, 2, 1, 3, 4, 5] j) = X W c 0 j := by
  fin_cases j <;> simp [X, relab]

theorem relab_Qk_1 (W : WeightsN 6 3 ℂ) (c : Fin 3) (j : Fin 6) :
    Qk (relab ![0, 2, 1, 3, 4, 5] W) c (![0, 2, 1, 3, 4, 5] j) = Qk W c j := by
  fin_cases j <;> simp [Qk, P4, X, relab] <;> ring

theorem stage_1 {a b c a2 b2 c2 : Fin 6} (ha : ![0, 2, 1, 3, 4, 5] a2 = a)
    (hb : ![0, 2, 1, 3, 4, 5] b2 = b) (hc : ![0, 2, 1, 3, 4, 5] c2 = c) (h : Good a b c) :
    Good a2 b2 c2 := by
  intro W hm hE h0 h1 h2
  subst ha hb hc
  refine h (relab ![0, 2, 1, 3, 4, 5] W) (relab_mono _ (by decide) W hm) (relab_eqsys_1 W hE)
    ?_ ?_ ?_
  · exact ⟨by rw [relab_X0_1]; exact h0.1, by rw [relab_Qk_1]; exact h0.2⟩
  · exact ⟨by rw [relab_X0_1]; exact h1.1, by rw [relab_Qk_1]; exact h1.2⟩
  · exact ⟨by rw [relab_X0_1]; exact h2.1, by rw [relab_Qk_1]; exact h2.2⟩

theorem relab_eqsys_2 (W : WeightsN 6 3 ℂ) (hE : EqSystemN 6 3 W) :
    EqSystemN 6 3 (relab ![0, 1, 3, 2, 4, 5] W) := by
  intro ι
  have h := hE (fun v => ι (![0, 1, 3, 2, 4, 5] v))
  rw [pm_formula] at h ⊢
  have e1 : F (relab ![0, 1, 3, 2, 4, 5] W) ι =
      F W (fun v => ι (![0, 1, 3, 2, 4, 5] v)) := by
    simp [F, relab]
    ring
  rw [e1, h]
  have hs : Function.Surjective (![0, 1, 3, 2, 4, 5] : Fin 6 → Fin 6) := by decide
  simp only [allEqual_comp ι _ hs]

theorem relab_X0_2 (W : WeightsN 6 3 ℂ) (c : Fin 3) (j : Fin 6) :
    X (relab ![0, 1, 3, 2, 4, 5] W) c 0 (![0, 1, 3, 2, 4, 5] j) = X W c 0 j := by
  fin_cases j <;> simp [X, relab]

theorem relab_Qk_2 (W : WeightsN 6 3 ℂ) (c : Fin 3) (j : Fin 6) :
    Qk (relab ![0, 1, 3, 2, 4, 5] W) c (![0, 1, 3, 2, 4, 5] j) = Qk W c j := by
  fin_cases j <;> simp [Qk, P4, X, relab] <;> ring

theorem stage_2 {a b c a2 b2 c2 : Fin 6} (ha : ![0, 1, 3, 2, 4, 5] a2 = a)
    (hb : ![0, 1, 3, 2, 4, 5] b2 = b) (hc : ![0, 1, 3, 2, 4, 5] c2 = c) (h : Good a b c) :
    Good a2 b2 c2 := by
  intro W hm hE h0 h1 h2
  subst ha hb hc
  refine h (relab ![0, 1, 3, 2, 4, 5] W) (relab_mono _ (by decide) W hm) (relab_eqsys_2 W hE)
    ?_ ?_ ?_
  · exact ⟨by rw [relab_X0_2]; exact h0.1, by rw [relab_Qk_2]; exact h0.2⟩
  · exact ⟨by rw [relab_X0_2]; exact h1.1, by rw [relab_Qk_2]; exact h1.2⟩
  · exact ⟨by rw [relab_X0_2]; exact h2.1, by rw [relab_Qk_2]; exact h2.2⟩

theorem relab_eqsys_3 (W : WeightsN 6 3 ℂ) (hE : EqSystemN 6 3 W) :
    EqSystemN 6 3 (relab ![0, 1, 2, 4, 3, 5] W) := by
  intro ι
  have h := hE (fun v => ι (![0, 1, 2, 4, 3, 5] v))
  rw [pm_formula] at h ⊢
  have e1 : F (relab ![0, 1, 2, 4, 3, 5] W) ι =
      F W (fun v => ι (![0, 1, 2, 4, 3, 5] v)) := by
    simp [F, relab]
    ring
  rw [e1, h]
  have hs : Function.Surjective (![0, 1, 2, 4, 3, 5] : Fin 6 → Fin 6) := by decide
  simp only [allEqual_comp ι _ hs]

theorem relab_X0_3 (W : WeightsN 6 3 ℂ) (c : Fin 3) (j : Fin 6) :
    X (relab ![0, 1, 2, 4, 3, 5] W) c 0 (![0, 1, 2, 4, 3, 5] j) = X W c 0 j := by
  fin_cases j <;> simp [X, relab]

theorem relab_Qk_3 (W : WeightsN 6 3 ℂ) (c : Fin 3) (j : Fin 6) :
    Qk (relab ![0, 1, 2, 4, 3, 5] W) c (![0, 1, 2, 4, 3, 5] j) = Qk W c j := by
  fin_cases j <;> simp [Qk, P4, X, relab] <;> ring

theorem stage_3 {a b c a2 b2 c2 : Fin 6} (ha : ![0, 1, 2, 4, 3, 5] a2 = a)
    (hb : ![0, 1, 2, 4, 3, 5] b2 = b) (hc : ![0, 1, 2, 4, 3, 5] c2 = c) (h : Good a b c) :
    Good a2 b2 c2 := by
  intro W hm hE h0 h1 h2
  subst ha hb hc
  refine h (relab ![0, 1, 2, 4, 3, 5] W) (relab_mono _ (by decide) W hm) (relab_eqsys_3 W hE)
    ?_ ?_ ?_
  · exact ⟨by rw [relab_X0_3]; exact h0.1, by rw [relab_Qk_3]; exact h0.2⟩
  · exact ⟨by rw [relab_X0_3]; exact h1.1, by rw [relab_Qk_3]; exact h1.2⟩
  · exact ⟨by rw [relab_X0_3]; exact h2.1, by rw [relab_Qk_3]; exact h2.2⟩

theorem relab_eqsys_4 (W : WeightsN 6 3 ℂ) (hE : EqSystemN 6 3 W) :
    EqSystemN 6 3 (relab ![0, 1, 2, 3, 5, 4] W) := by
  intro ι
  have h := hE (fun v => ι (![0, 1, 2, 3, 5, 4] v))
  rw [pm_formula] at h ⊢
  have e1 : F (relab ![0, 1, 2, 3, 5, 4] W) ι =
      F W (fun v => ι (![0, 1, 2, 3, 5, 4] v)) := by
    simp [F, relab]
    ring
  rw [e1, h]
  have hs : Function.Surjective (![0, 1, 2, 3, 5, 4] : Fin 6 → Fin 6) := by decide
  simp only [allEqual_comp ι _ hs]

theorem relab_X0_4 (W : WeightsN 6 3 ℂ) (c : Fin 3) (j : Fin 6) :
    X (relab ![0, 1, 2, 3, 5, 4] W) c 0 (![0, 1, 2, 3, 5, 4] j) = X W c 0 j := by
  fin_cases j <;> simp [X, relab]

theorem relab_Qk_4 (W : WeightsN 6 3 ℂ) (c : Fin 3) (j : Fin 6) :
    Qk (relab ![0, 1, 2, 3, 5, 4] W) c (![0, 1, 2, 3, 5, 4] j) = Qk W c j := by
  fin_cases j <;> simp [Qk, P4, X, relab] <;> ring

theorem stage_4 {a b c a2 b2 c2 : Fin 6} (ha : ![0, 1, 2, 3, 5, 4] a2 = a)
    (hb : ![0, 1, 2, 3, 5, 4] b2 = b) (hc : ![0, 1, 2, 3, 5, 4] c2 = c) (h : Good a b c) :
    Good a2 b2 c2 := by
  intro W hm hE h0 h1 h2
  subst ha hb hc
  refine h (relab ![0, 1, 2, 3, 5, 4] W) (relab_mono _ (by decide) W hm) (relab_eqsys_4 W hE)
    ?_ ?_ ?_
  · exact ⟨by rw [relab_X0_4]; exact h0.1, by rw [relab_Qk_4]; exact h0.2⟩
  · exact ⟨by rw [relab_X0_4]; exact h1.1, by rw [relab_Qk_4]; exact h1.2⟩
  · exact ⟨by rw [relab_X0_4]; exact h2.1, by rw [relab_Qk_4]; exact h2.2⟩

theorem all_good (a b c : Fin 6) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) : Good a b c := by
  have g_1_2_3 : Good 1 2 3 := good_1_2_3
  have g_2_1_3 : Good 2 1 3 :=
    stage_1 (by decide) (by decide) (by decide) g_1_2_3
  have g_1_3_2 : Good 1 3 2 :=
    stage_2 (by decide) (by decide) (by decide) g_1_2_3
  have g_1_2_4 : Good 1 2 4 :=
    stage_3 (by decide) (by decide) (by decide) g_1_2_3
  have g_3_1_2 : Good 3 1 2 :=
    stage_2 (by decide) (by decide) (by decide) g_2_1_3
  have g_2_1_4 : Good 2 1 4 :=
    stage_3 (by decide) (by decide) (by decide) g_2_1_3
  have g_2_3_1 : Good 2 3 1 :=
    stage_1 (by decide) (by decide) (by decide) g_1_3_2
  have g_1_4_2 : Good 1 4 2 :=
    stage_3 (by decide) (by decide) (by decide) g_1_3_2
  have g_1_3_4 : Good 1 3 4 :=
    stage_2 (by decide) (by decide) (by decide) g_1_2_4
  have g_1_2_5 : Good 1 2 5 :=
    stage_4 (by decide) (by decide) (by decide) g_1_2_4
  have g_3_2_1 : Good 3 2 1 :=
    stage_1 (by decide) (by decide) (by decide) g_3_1_2
  have g_4_1_2 : Good 4 1 2 :=
    stage_3 (by decide) (by decide) (by decide) g_3_1_2
  have g_3_1_4 : Good 3 1 4 :=
    stage_2 (by decide) (by decide) (by decide) g_2_1_4
  have g_2_1_5 : Good 2 1 5 :=
    stage_4 (by decide) (by decide) (by decide) g_2_1_4
  have g_2_4_1 : Good 2 4 1 :=
    stage_3 (by decide) (by decide) (by decide) g_2_3_1
  have g_1_4_3 : Good 1 4 3 :=
    stage_2 (by decide) (by decide) (by decide) g_1_4_2
  have g_1_5_2 : Good 1 5 2 :=
    stage_4 (by decide) (by decide) (by decide) g_1_4_2
  have g_2_3_4 : Good 2 3 4 :=
    stage_1 (by decide) (by decide) (by decide) g_1_3_4
  have g_1_3_5 : Good 1 3 5 :=
    stage_4 (by decide) (by decide) (by decide) g_1_3_4
  have g_4_2_1 : Good 4 2 1 :=
    stage_3 (by decide) (by decide) (by decide) g_3_2_1
  have g_4_1_3 : Good 4 1 3 :=
    stage_2 (by decide) (by decide) (by decide) g_4_1_2
  have g_5_1_2 : Good 5 1 2 :=
    stage_4 (by decide) (by decide) (by decide) g_4_1_2
  have g_3_2_4 : Good 3 2 4 :=
    stage_1 (by decide) (by decide) (by decide) g_3_1_4
  have g_3_1_5 : Good 3 1 5 :=
    stage_4 (by decide) (by decide) (by decide) g_3_1_4
  have g_3_4_1 : Good 3 4 1 :=
    stage_2 (by decide) (by decide) (by decide) g_2_4_1
  have g_2_5_1 : Good 2 5 1 :=
    stage_4 (by decide) (by decide) (by decide) g_2_4_1
  have g_2_4_3 : Good 2 4 3 :=
    stage_1 (by decide) (by decide) (by decide) g_1_4_3
  have g_1_5_3 : Good 1 5 3 :=
    stage_4 (by decide) (by decide) (by decide) g_1_4_3
  have g_2_3_5 : Good 2 3 5 :=
    stage_4 (by decide) (by decide) (by decide) g_2_3_4
  have g_1_4_5 : Good 1 4 5 :=
    stage_3 (by decide) (by decide) (by decide) g_1_3_5
  have g_4_3_1 : Good 4 3 1 :=
    stage_2 (by decide) (by decide) (by decide) g_4_2_1
  have g_5_2_1 : Good 5 2 1 :=
    stage_4 (by decide) (by decide) (by decide) g_4_2_1
  have g_4_2_3 : Good 4 2 3 :=
    stage_1 (by decide) (by decide) (by decide) g_4_1_3
  have g_5_1_3 : Good 5 1 3 :=
    stage_4 (by decide) (by decide) (by decide) g_4_1_3
  have g_3_2_5 : Good 3 2 5 :=
    stage_4 (by decide) (by decide) (by decide) g_3_2_4
  have g_4_1_5 : Good 4 1 5 :=
    stage_3 (by decide) (by decide) (by decide) g_3_1_5
  have g_3_4_2 : Good 3 4 2 :=
    stage_1 (by decide) (by decide) (by decide) g_3_4_1
  have g_3_5_1 : Good 3 5 1 :=
    stage_4 (by decide) (by decide) (by decide) g_3_4_1
  have g_2_5_3 : Good 2 5 3 :=
    stage_4 (by decide) (by decide) (by decide) g_2_4_3
  have g_1_5_4 : Good 1 5 4 :=
    stage_3 (by decide) (by decide) (by decide) g_1_5_3
  have g_2_4_5 : Good 2 4 5 :=
    stage_3 (by decide) (by decide) (by decide) g_2_3_5
  have g_4_3_2 : Good 4 3 2 :=
    stage_1 (by decide) (by decide) (by decide) g_4_3_1
  have g_5_3_1 : Good 5 3 1 :=
    stage_4 (by decide) (by decide) (by decide) g_4_3_1
  have g_5_2_3 : Good 5 2 3 :=
    stage_4 (by decide) (by decide) (by decide) g_4_2_3
  have g_5_1_4 : Good 5 1 4 :=
    stage_3 (by decide) (by decide) (by decide) g_5_1_3
  have g_4_2_5 : Good 4 2 5 :=
    stage_3 (by decide) (by decide) (by decide) g_3_2_5
  have g_3_5_2 : Good 3 5 2 :=
    stage_4 (by decide) (by decide) (by decide) g_3_4_2
  have g_4_5_1 : Good 4 5 1 :=
    stage_3 (by decide) (by decide) (by decide) g_3_5_1
  have g_2_5_4 : Good 2 5 4 :=
    stage_3 (by decide) (by decide) (by decide) g_2_5_3
  have g_3_4_5 : Good 3 4 5 :=
    stage_2 (by decide) (by decide) (by decide) g_2_4_5
  have g_5_3_2 : Good 5 3 2 :=
    stage_4 (by decide) (by decide) (by decide) g_4_3_2
  have g_5_4_1 : Good 5 4 1 :=
    stage_3 (by decide) (by decide) (by decide) g_5_3_1
  have g_5_2_4 : Good 5 2 4 :=
    stage_3 (by decide) (by decide) (by decide) g_5_2_3
  have g_4_3_5 : Good 4 3 5 :=
    stage_2 (by decide) (by decide) (by decide) g_4_2_5
  have g_4_5_2 : Good 4 5 2 :=
    stage_3 (by decide) (by decide) (by decide) g_3_5_2
  have g_3_5_4 : Good 3 5 4 :=
    stage_2 (by decide) (by decide) (by decide) g_2_5_4
  have g_5_4_2 : Good 5 4 2 :=
    stage_3 (by decide) (by decide) (by decide) g_5_3_2
  have g_5_3_4 : Good 5 3 4 :=
    stage_2 (by decide) (by decide) (by decide) g_5_2_4
  have g_4_5_3 : Good 4 5 3 :=
    stage_2 (by decide) (by decide) (by decide) g_4_5_2
  have g_5_4_3 : Good 5 4 3 :=
    stage_2 (by decide) (by decide) (by decide) g_5_4_2
  fin_cases a <;> fin_cases b <;> fin_cases c
  all_goals first
    | assumption
    | (exfalso; revert ha hb hc hab hac hbc; decide)

/- ### Partners of vertex 0 -/

theorem F_const (W : WeightsN 6 3 ℂ) (c : Fin 3) :
    F W (fun _ => c) = X W c 0 1 * Qk W c 1 + X W c 0 2 * Qk W c 2 + X W c 0 3 * Qk W c 3 +
      X W c 0 4 * Qk W c 4 + X W c 0 5 * Qk W c 5 := by
  simp [F, X, Qk, P4]

theorem partner (W : WeightsN 6 3 ℂ) (hE : EqSystemN 6 3 W) (c : Fin 3) :
    ∃ k : Fin 6, k ≠ 0 ∧ Own W c k := by
  have h := eqsys_one W hE c
  rw [F_const] at h
  by_contra hne
  have z : ∀ k : Fin 6, k ≠ 0 → X W c 0 k * Qk W c k = 0 := by
    intro k hk
    by_cases hx : X W c 0 k = 0
    · rw [hx, zero_mul]
    · by_cases hq : Qk W c k = 0
      · rw [hq, mul_zero]
      · exact absurd ⟨k, hk, hx, hq⟩ hne
  rw [z 1 (by decide), z 2 (by decide), z 3 (by decide), z 4 (by decide),
    z 5 (by decide)] at h
  norm_num at h

theorem own_ne (W : WeightsN 6 3 ℂ) (hm : Mono W) (hE : EqSystemN 6 3 W) (a b : Fin 3)
    (hab : a ≠ b) (k : Fin 6) (ha : Own W a k) (hb : Own W b k) : False := by
  obtain ⟨-, hq⟩ := ha
  obtain ⟨hx, -⟩ := hb
  fin_cases k
  · exact hq (by simp [Qk])
  · exact mz_ff (fB_0_1 W hm hE a b hab) hx (by simpa [Qk] using hq)
  · exact mz_ff (fB_0_2 W hm hE a b hab) hx (by simpa [Qk] using hq)
  · exact mz_ff (fB_0_3 W hm hE a b hab) hx (by simpa [Qk] using hq)
  · exact mz_ff (fB_0_4 W hm hE a b hab) hx (by simpa [Qk] using hq)
  · exact mz_ff (fB_0_5 W hm hE a b hab) hx (by simpa [Qk] using hq)

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_MonochromaticQuantumGraph_eqSystem6_no_solution_ge3_R1.H1 := by
  intro W hm hE
  obtain ⟨p0, hp0, o0⟩ := partner W hE 0
  obtain ⟨p1, hp1, o1⟩ := partner W hE 1
  obtain ⟨p2, hp2, o2⟩ := partner W hE 2
  have h01 : p0 ≠ p1 := fun h => own_ne W hm hE 1 0 (by decide) p0 (h ▸ o1) o0
  have h02 : p0 ≠ p2 := fun h => own_ne W hm hE 2 0 (by decide) p0 (h ▸ o2) o0
  have h12 : p1 ≠ p2 := fun h => own_ne W hm hE 2 1 (by decide) p1 (h ▸ o2) o1
  exact all_good p0 p1 p2 hp0 hp1 hp2 h01 h02 h12 W hm hE o0 o1 o2
