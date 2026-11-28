import OMAReductions.R_Erdos20_erdos_20_R1_H2_R2
import Mathlib

/-!
# Step H2 of the reduction Erdos20.erdos_20.R1.H2.R2

Given a sunflower-free family `W` of words of length `n` over `Fin m`, concatenate `t` words of
`W` into the first `t * n` coordinates of a word of length `N` over `Fin N`, embedding the alphabet
by `Fin.castLE` and padding the remaining coordinates with `0`. The packing map is injective, so
the packed family has `W.card ^ t` elements. A sunflower of packed words restricts, block by block,
to sunflowers of `W`, which are trivial; hence the packed family is sunflower-free.
-/

namespace OMA.Helpers

/-- Read a coordinate of `Fin N` as a block index and a position inside that block. -/
def erdos20Decode {t n N : ℕ} (j : Fin N) : Option (Fin t × Fin n) :=
  if h : j.val < t * n then some (finProdFinEquiv.symm ⟨j.val, h⟩) else none

/-- The coordinate of position `i` in block `s`. -/
def erdos20Pos {t n N : ℕ} (htn : t * n ≤ N) (s : Fin t) (i : Fin n) : Fin N :=
  Fin.castLE htn (finProdFinEquiv (s, i))

theorem erdos20_decode_pos {t n N : ℕ} (htn : t * n ≤ N) (s : Fin t) (i : Fin n) :
    erdos20Decode (t := t) (n := n) (erdos20Pos htn s i) = some (s, i) := by
  have h : (erdos20Pos htn s i).val < t * n := (finProdFinEquiv (s, i)).isLt
  unfold erdos20Decode
  rw [dif_pos h]
  congr 1
  apply finProdFinEquiv.symm_apply_eq.mpr
  exact Fin.ext rfl

/-- Concatenate the words `f 0, ..., f (t - 1)` and pad with `0`. -/
def erdos20Word {t n m N : ℕ} (hN : 0 < N) (hm : m ≤ N) (f : Fin t → Fin n → Fin m)
    (j : Fin N) : Fin N :=
  match erdos20Decode (t := t) (n := n) j with
  | some si => Fin.castLE hm (f si.1 si.2)
  | none => ⟨0, hN⟩

theorem erdos20_word_pos {t n m N : ℕ} (hN : 0 < N) (hm : m ≤ N) (htn : t * n ≤ N)
    (f : Fin t → Fin n → Fin m) (s : Fin t) (i : Fin n) :
    erdos20Word hN hm f (erdos20Pos htn s i) = Fin.castLE hm (f s i) := by
  unfold erdos20Word
  rw [erdos20_decode_pos]

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos20_erdos_20_R1_H2_R2.H2 := by
  classical
  intro r n m t N hN hm htn W hW
  let word := fun f : Fin t → Fin n → Fin m => OMA.Helpers.erdos20Word hN hm f
  have hpos : ∀ f s i, word f (OMA.Helpers.erdos20Pos htn s i) = Fin.castLE hm (f s i) :=
    fun f s i => OMA.Helpers.erdos20_word_pos hN hm htn f s i
  have hinj : Function.Injective word := by
    intro f g h
    funext s i
    have e := congrFun h (OMA.Helpers.erdos20Pos htn s i)
    rw [hpos, hpos] at e
    exact Fin.castLE_injective hm e
  refine ⟨(Fintype.piFinset fun _ : Fin t => W).image word, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Fintype.card_piFinset]
    simp
  · intro v hv hcond a b
    choose f hf hfv using fun i => Finset.mem_image.mp (hv i)
    have hval : ∀ i s j, v i (OMA.Helpers.erdos20Pos htn s j) = Fin.castLE hm (f i s j) := by
      intro i s j
      rw [← hfv i]
      exact hpos (f i) s j
    have key : ∀ s, ∀ a b, f a s = f b s := by
      intro s
      apply hW (fun i => f i s) (fun i => Fintype.mem_piFinset.mp (hf i) s)
      intro j
      rcases hcond (OMA.Helpers.erdos20Pos htn s j) with h | h
      · left
        intro a b
        have e := h a b
        rw [hval a s j, hval b s j] at e
        exact Fin.castLE_injective hm e
      · right
        intro a b hab
        apply h
        change v a (OMA.Helpers.erdos20Pos htn s j) = v b (OMA.Helpers.erdos20Pos htn s j)
        rw [hval a s j, hval b s j]
        exact congrArg (Fin.castLE hm) hab
    rw [← hfv a, ← hfv b]
    congr 1
    funext s
    exact key s a b
