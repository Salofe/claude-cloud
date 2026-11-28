import OMAReductions.R_Erdos40_erdos_40_variants_weaker_R1_H2_R1

/-!
# Step H1 of the reduction Erdos40.erdos_40.variants.weaker.R1.H2.R1

If every ordered representation count `sumRep A n` is at most `2 h + 1`, we find `B ⊆ A` with
every count at most `2 h` that keeps at least half of `A` in every prefix `[1, n]`.

* Parity. The swap `(a, b) ↦ (b, a)` is an involution of the ordered fibre of `n`, whose only
  possible fixed point is `(c, c)` with `n = c + c`. Hence an odd count forces `n = c + c` with
  `c ∈ A`. In particular every saturated sum (count exactly `2 h + 1`) is `c + c` with `c ∈ A`.
* Top element. A saturated `c` has a representation other than `(c, c)`, so there is `t` with
  `c < t ≤ c + c`, `t ∈ A` and `c + c - t ∈ A`. We fix such a `top c`.
* Greedy removal. By well-founded recursion, `v` is removed iff `v = top c` for some saturated
  `c < v` that is not removed. Every saturated `c` loses `c` or `top c`, which destroys the
  representation `(c, c)` or `(c + c - top c, top c)`, so all counts of `B` drop to `2 h`.
* Counting. Each removed `v` has a kept saturated parent `c < v` with `top c = v`; this parent map
  is injective and lands in `B ∩ [1, n]`, so the removed part of a prefix is at most the kept part.

Only the upstream definitions `sumRep`, `sumConv` and `indicatorOne` are unfolded; no upstream
theorem is used.
-/

namespace OMA.Helpers

open Finset

open scoped Classical in
/-- The ordered representation fibre of `n` by elements of `A`. -/
noncomputable def e40Fib (A : Set ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (antidiagonal n).filter (fun p => p.1 ∈ A ∧ p.2 ∈ A)

/-- Membership in the ordered fibre. -/
theorem mem_e40Fib {A : Set ℕ} {n : ℕ} {p : ℕ × ℕ} :
    p ∈ e40Fib A n ↔ p.1 + p.2 = n ∧ p.1 ∈ A ∧ p.2 ∈ A := by
  unfold e40Fib
  simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal]

/-- The representation count is the size of the ordered fibre (own unfolding of the upstream
definitions). -/
theorem sumRep_eq_card (A : Set ℕ) (n : ℕ) :
    AdditiveCombinatorics.sumRep A n = (e40Fib A n).card := by
  classical
  unfold AdditiveCombinatorics.sumRep AdditiveCombinatorics.sumConv e40Fib
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.2 ∈ A
  · rw [if_pos ⟨h1, h2⟩]
    simp only [Set.indicatorOne, Set.indicator_of_mem h1, Set.indicator_of_mem h2, mul_one]
  · rw [if_neg (fun h => h2 h.2)]
    simp only [Set.indicatorOne, Set.indicator_of_notMem h2, mul_zero]
  · rw [if_neg (fun h => h1 h.1)]
    simp only [Set.indicatorOne, Set.indicator_of_notMem h1, zero_mul]
  · rw [if_neg (fun h => h1 h.1)]
    simp only [Set.indicatorOne, Set.indicator_of_notMem h1, zero_mul]

/-- Swap parity: an ordered fibre of odd size contains a diagonal pair, so `n = c + c` with
`c ∈ A`. -/
theorem exists_half_of_odd {A : Set ℕ} {n : ℕ} (hodd : Odd (e40Fib A n).card) :
    ∃ c ∈ A, n = c + c := by
  classical
  by_contra hno
  have hswap : ((e40Fib A n).filter (fun p => ¬ p.1 < p.2)).card =
      ((e40Fib A n).filter (fun p => p.1 < p.2)).card := by
    refine Finset.card_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter, mem_e40Fib] at hp
      rw [Finset.mem_coe, Finset.mem_filter, mem_e40Fib]
      obtain ⟨⟨hs, h1, h2⟩, hlt⟩ := hp
      refine ⟨⟨by simp only [Prod.fst_swap, Prod.snd_swap]; omega, h2, h1⟩, ?_⟩
      simp only [Prod.fst_swap, Prod.snd_swap]
      by_contra hc
      exact hno ⟨p.1, h1, by omega⟩
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter, mem_e40Fib] at hp
      rw [Finset.mem_coe, Finset.mem_filter, mem_e40Fib]
      obtain ⟨⟨hs, h1, h2⟩, hlt⟩ := hp
      refine ⟨⟨by simp only [Prod.fst_swap, Prod.snd_swap]; omega, h2, h1⟩, ?_⟩
      simp only [Prod.fst_swap, Prod.snd_swap]
      omega
    · intro p _
      exact Prod.swap_swap p
    · intro p _
      exact Prod.swap_swap p
  have htot := Finset.card_filter_add_card_filter_not (s := e40Fib A n)
    (fun p : ℕ × ℕ => p.1 < p.2)
  rw [hswap] at htot
  obtain ⟨k, hk⟩ := hodd
  omega

/-- A fibre of `c + c` with at least two pairs has a pair `(c + c - t, t)` with `c < t`. -/
theorem exists_top {A : Set ℕ} {c : ℕ} (hc : 1 < (e40Fib A (c + c)).card) :
    ∃ t, c < t ∧ t ≤ c + c ∧ t ∈ A ∧ c + c - t ∈ A := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc
  have key : ∀ p ∈ e40Fib A (c + c), p ≠ (c, c) →
      ∃ t, c < t ∧ t ≤ c + c ∧ t ∈ A ∧ c + c - t ∈ A := by
    rintro ⟨x, y⟩ hp hne
    rw [mem_e40Fib] at hp
    obtain ⟨hs, h1, h2⟩ := hp
    simp only at hs h1 h2
    rcases lt_trichotomy x y with h | h | h
    · refine ⟨y, by omega, by omega, h2, ?_⟩
      have hxy : c + c - y = x := by omega
      rw [hxy]
      exact h1
    · exfalso
      apply hne
      simp only [Prod.mk.injEq]
      omega
    · refine ⟨x, by omega, by omega, h1, ?_⟩
      have hxy : c + c - x = y := by omega
      rw [hxy]
      exact h2
  by_cases hac : a = (c, c)
  · exact key b hb (fun hbc => hab (hac.trans hbc.symm))
  · exact key a ha hac

/-- Greedy removal: `v` is removed when it is the chosen top element of a saturated
`c < v` that was itself kept. -/
noncomputable def remP (S : ℕ → Prop) (top : ℕ → ℕ) (v : ℕ) : Prop :=
  ∃ c, ∃ _ : c < v, S c ∧ top c = v ∧ ¬ remP S top c
termination_by v

/-- Unfolding equation of the greedy removal predicate. -/
theorem remP_iff (S : ℕ → Prop) (top : ℕ → ℕ) (v : ℕ) :
    remP S top v ↔ ∃ c, ∃ _ : c < v, S c ∧ top c = v ∧ ¬ remP S top c := by
  rw [remP]

/-- A predicate satisfying the greedy removal equation exists. -/
theorem exists_greedy (S : ℕ → Prop) (top : ℕ → ℕ) :
    ∃ rem : ℕ → Prop, ∀ v, rem v ↔ ∃ c, ∃ _ : c < v, S c ∧ top c = v ∧ ¬ rem c :=
  ⟨remP S top, remP_iff S top⟩

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos40_erdos_40_variants_weaker_R1_H2_R1.H1 := by
  classical
  intro h hh A hcap
  obtain ⟨S, hS⟩ : ∃ S : ℕ → Prop, ∀ c, S c ↔
      (c ∈ A ∧ (OMA.Helpers.e40Fib A (c + c)).card = 2 * h + 1) :=
    ⟨_, fun c => Iff.rfl⟩
  have htopex : ∀ c, ∃ t, ¬ S c ∨ (c < t ∧ t ≤ c + c ∧ t ∈ A ∧ c + c - t ∈ A) := by
    intro c
    by_cases hc : S c
    · obtain ⟨t, ht⟩ := OMA.Helpers.exists_top (A := A) (c := c)
        (by rw [((hS c).mp hc).2]; omega)
      exact ⟨t, Or.inr ht⟩
    · exact ⟨0, Or.inl hc⟩
  choose top htop' using htopex
  have htop : ∀ c, S c → (c < top c ∧ top c ≤ c + c ∧ top c ∈ A ∧ c + c - top c ∈ A) :=
    fun c hc => (htop' c).resolve_left (not_not_intro hc)
  obtain ⟨rem, hrem⟩ := OMA.Helpers.exists_greedy S top
  refine ⟨{x | x ∈ A ∧ ¬ rem x}, fun x hx => hx.1, ?_, ?_⟩
  · intro n
    have hBA : OMA.Helpers.e40Fib {x | x ∈ A ∧ ¬ rem x} n ⊆ OMA.Helpers.e40Fib A n := by
      intro p hp
      rw [OMA.Helpers.mem_e40Fib] at hp ⊢
      exact ⟨hp.1, hp.2.1.1, hp.2.2.1⟩
    rw [OMA.Helpers.sumRep_eq_card]
    have hA := hcap n
    rw [OMA.Helpers.sumRep_eq_card] at hA
    by_cases hsat : (OMA.Helpers.e40Fib A n).card = 2 * h + 1
    · obtain ⟨c, hcA, rfl⟩ := OMA.Helpers.exists_half_of_odd (A := A) (n := n)
        (by rw [hsat]; exact ⟨h, rfl⟩)
      have hSc : S c := (hS c).mpr ⟨hcA, hsat⟩
      have hlt : (OMA.Helpers.e40Fib {x | x ∈ A ∧ ¬ rem x} (c + c)).card <
          (OMA.Helpers.e40Fib A (c + c)).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset hBA]
        by_cases hrc : rem c
        · refine ⟨(c, c), ?_, ?_⟩
          · rw [OMA.Helpers.mem_e40Fib]
            exact ⟨rfl, hcA, hcA⟩
          · rw [OMA.Helpers.mem_e40Fib]
            rintro ⟨_, ⟨_, hn⟩, _⟩
            exact hn hrc
        · have hrt : rem (top c) := (hrem (top c)).mpr ⟨c, (htop c hSc).1, hSc, rfl, hrc⟩
          obtain ⟨h1, h2, h3, h4⟩ := htop c hSc
          refine ⟨(c + c - top c, top c), ?_, ?_⟩
          · rw [OMA.Helpers.mem_e40Fib]
            exact ⟨by simp only; omega, h4, h3⟩
          · rw [OMA.Helpers.mem_e40Fib]
            rintro ⟨_, _, _, hn⟩
            exact hn hrt
      omega
    · have := Finset.card_le_card hBA
      omega
  · intro n
    have hparex : ∀ v, ∃ c, ¬ rem v ∨ (c < v ∧ S c ∧ top c = v ∧ ¬ rem c) := by
      intro v
      by_cases hv : rem v
      · obtain ⟨c, hcv, hSc, htc, hrc⟩ := (hrem v).mp hv
        exact ⟨c, Or.inr ⟨hcv, hSc, htc, hrc⟩⟩
      · exact ⟨0, Or.inl hv⟩
    choose par hpar' using hparex
    have hpar : ∀ v, rem v → (par v < v ∧ S (par v) ∧ top (par v) = v ∧ ¬ rem (par v)) :=
      fun v hv => (hpar' v).resolve_left (not_not_intro hv)
    have hfinB : ({x | x ∈ A ∧ ¬ rem x} ∩ Set.Icc 1 n).Finite :=
      (Set.finite_Icc 1 n).inter_of_right _
    have hfinR : ({x | x ∈ A ∧ rem x} ∩ Set.Icc 1 n).Finite :=
      (Set.finite_Icc 1 n).inter_of_right _
    have hsplit : A ∩ Set.Icc 1 n ⊆
        ({x | x ∈ A ∧ ¬ rem x} ∩ Set.Icc 1 n) ∪ ({x | x ∈ A ∧ rem x} ∩ Set.Icc 1 n) := by
      rintro x ⟨hxA, hx⟩
      by_cases hr : rem x
      · exact Or.inr ⟨⟨hxA, hr⟩, hx⟩
      · exact Or.inl ⟨⟨hxA, hr⟩, hx⟩
    have hR : ({x | x ∈ A ∧ rem x} ∩ Set.Icc 1 n).ncard ≤
        ({x | x ∈ A ∧ ¬ rem x} ∩ Set.Icc 1 n).ncard := by
      apply Set.ncard_le_ncard_of_injOn par
      · rintro v ⟨⟨_, hvr⟩, hv1, hvn⟩
        obtain ⟨hcv, hSc, _, hrc⟩ := hpar v hvr
        obtain ⟨hlo, hhi, _, _⟩ := htop (par v) hSc
        exact ⟨⟨((hS (par v)).mp hSc).1, hrc⟩, by omega, by omega⟩
      · rintro v ⟨⟨_, hvr⟩, _⟩ w ⟨⟨_, hwr⟩, _⟩ hvw
        have e1 := (hpar v hvr).2.2.1
        have e2 := (hpar w hwr).2.2.1
        rw [← e1, ← e2, hvw]
    calc (A ∩ Set.Icc 1 n).ncard
        ≤ (({x | x ∈ A ∧ ¬ rem x} ∩ Set.Icc 1 n) ∪
            ({x | x ∈ A ∧ rem x} ∩ Set.Icc 1 n)).ncard :=
          Set.ncard_le_ncard hsplit (hfinB.union hfinR)
      _ ≤ ({x | x ∈ A ∧ ¬ rem x} ∩ Set.Icc 1 n).ncard +
            ({x | x ∈ A ∧ rem x} ∩ Set.Icc 1 n).ncard := Set.ncard_union_le _ _
      _ ≤ 2 * ({x | x ∈ A ∧ ¬ rem x} ∩ Set.Icc 1 n).ncard := by omega
