import OMAReductions.R_Erdos261_erdos_261_parts_iii_R1

/-!
# Step H2 of the reduction Erdos261.erdos_261.parts.iii.R1

Track the signed defect `c = ρ - ℓ - 1` of the scaled residual `ρ` at level `ℓ`. Taking `ℓ`
sends `c` to `2c - ℓ`, skipping it sends `c` to `2c + ℓ`; we take exactly when `c > 0`, and at
`c = 0` a choice function decides. In every case `|c|` follows `a ↦ |2a - ℓ|`, so `|c|` does not
depend on the choices, stays at most `ℓ - 1`, and vanishes exactly at the zeros of the canonical
orbit of the statement (the canonical orbit is the path that always skips at `c = 0`).

For a binary sequence `b`, the choice at the `k`-th zero is `b k` (the index of a zero is read off
with `Nat.count`). The partial sums of `a / 2^a` over the taken levels below `ℓ + 1` equal
`1 - ρ / 2^ℓ` with `0 < ρ ≤ 2ℓ`, so the series has sum `1` and the set is infinite. The `k`-th
zero plus one lies in the set exactly when `b k` is true, which gives injectivity.
-/

namespace OMA.Helpers

/-- One step of the signed defect `c = ρ - ℓ - 1` at level `l`. -/
def e261Step (ch : ℕ → Bool) (l : ℕ) (c : ℤ) : ℤ :=
  if 0 < c ∨ (c = 0 ∧ ch l = true) then 2 * c - l else 2 * c + l

/-- The signed defect at level `j + 1`. -/
def e261Path (ch : ℕ → Bool) : ℕ → ℤ
  | 0 => 0
  | n + 1 => e261Step ch (n + 1) (e261Path ch n)

theorem e261Path_succ (ch : ℕ → Bool) (n : ℕ) :
    e261Path ch (n + 1) = e261Step ch (n + 1) (e261Path ch n) := rfl

theorem e261_abs_step (ch : ℕ → Bool) (l : ℕ) (c : ℤ) :
    |e261Step ch l c| = |2 * |c| - l| := by
  unfold e261Step
  rcases lt_trichotomy c 0 with h | h | h
  · have h1 : ¬ (0 < c ∨ (c = 0 ∧ ch l = true)) := by omega
    rw [if_neg h1, abs_of_neg h]
    rw [show 2 * -c - (l : ℤ) = -(2 * c + l) by ring, abs_neg]
  · subst h
    split_ifs <;> simp
  · rw [if_pos (Or.inl h), abs_of_pos h]

theorem e261_abs_path (ch ch' : ℕ → Bool) (j : ℕ) :
    |e261Path ch j| = |e261Path ch' j| := by
  induction j with
  | zero => rfl
  | succ n ih => rw [e261Path_succ, e261Path_succ, e261_abs_step, e261_abs_step, ih]

theorem e261_abs_le (ch : ℕ → Bool) (j : ℕ) : |e261Path ch j| ≤ j := by
  induction j with
  | zero => simp [e261Path]
  | succ n ih =>
    rw [e261Path_succ, e261_abs_step]
    have h0 := abs_nonneg (e261Path ch n)
    rw [abs_le]
    push_cast
    constructor <;> linarith

theorem e261_orbit (j : ℕ) :
    ((fun p : ℕ × ℕ => (p.1 + 1, if p.1 + 1 < p.2 then 2 * (p.2 - p.1) else 2 * p.2))^[j]
      (1, 2)).1 = j + 1 ∧
    ((((fun p : ℕ × ℕ => (p.1 + 1, if p.1 + 1 < p.2 then 2 * (p.2 - p.1) else 2 * p.2))^[j]
      (1, 2)).2 : ℕ) : ℤ) = e261Path (fun _ => false) j + j + 2 := by
  induction j with
  | zero => simp [e261Path]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h1, h2⟩ := ih
    set p := (fun p : ℕ × ℕ => (p.1 + 1, if p.1 + 1 < p.2 then 2 * (p.2 - p.1) else 2 * p.2))^[n]
      (1, 2) with hp
    rw [e261Path_succ]
    unfold e261Step
    simp only [Bool.false_eq_true, and_false, or_false]
    refine ⟨by simp [h1], ?_⟩
    rw [h1]
    split_ifs with ha hb hb <;> push_cast <;> omega

/-- The set of levels taken along the path with choices `ch`. -/
def e261Set (ch : ℕ → Bool) : Set ℕ :=
  {l | 1 ≤ l ∧ (0 < e261Path ch (l - 1) ∨ (e261Path ch (l - 1) = 0 ∧ ch l = true))}

theorem e261_psum (ch : ℕ → Bool) (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), (e261Set ch).indicator (fun a : ℕ => (a : ℝ) / 2 ^ a) i =
      1 - ((e261Path ch j + j + 2 : ℤ) : ℝ) / 2 ^ (j + 1) := by
  induction j with
  | zero => simp [e261Set, e261Path]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, e261Path_succ]
    unfold e261Step
    by_cases h : 0 < e261Path ch n ∨ (e261Path ch n = 0 ∧ ch (n + 1) = true)
    · have hm : n + 1 ∈ e261Set ch := ⟨by omega, by simpa using h⟩
      rw [Set.indicator_of_mem hm, if_pos h]
      push_cast
      field_simp
      ring
    · have hm : n + 1 ∉ e261Set ch := fun hm => h (by simpa [e261Set] using hm.2)
      rw [Set.indicator_of_notMem hm, if_neg h]
      push_cast
      field_simp
      ring

theorem e261_resid_pos (ch : ℕ → Bool) (j : ℕ) : 0 < ((e261Path ch j + j + 2 : ℤ) : ℝ) := by
  have := e261_abs_le ch j
  have h2 : (0 : ℤ) < e261Path ch j + j + 2 := by
    rw [abs_le] at this; omega
  exact_mod_cast h2

theorem e261_resid_le (ch : ℕ → Bool) (j : ℕ) :
    ((e261Path ch j + j + 2 : ℤ) : ℝ) ≤ 2 * ((j + 1 : ℕ) : ℝ) := by
  have := e261_abs_le ch j
  have h2 : e261Path ch j + j + 2 ≤ 2 * ((j + 1 : ℕ) : ℤ) := by
    rw [abs_le] at this; push_cast; omega
  exact_mod_cast h2

theorem e261_hasSum (ch : ℕ → Bool) :
    HasSum ((e261Set ch).indicator (fun a : ℕ => (a : ℝ) / 2 ^ a)) 1 := by
  have hnn : ∀ i, 0 ≤ (e261Set ch).indicator (fun a : ℕ => (a : ℝ) / 2 ^ a) i :=
    fun i => Set.indicator_nonneg (fun a _ => by positivity) i
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn, ← Filter.tendsto_add_atTop_iff_nat 1]
  simp_rw [e261_psum]
  have hu : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 1 / 2 ^ (n + 1)) Filter.atTop
      (nhds 0) := by
    have h := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)
    exact (Filter.tendsto_add_atTop_iff_nat 1).2 h
  have hx : Filter.Tendsto (fun n : ℕ => ((e261Path ch n + n + 2 : ℤ) : ℝ) / 2 ^ (n + 1))
      Filter.atTop (nhds 0) := by
    have h2 := hu.const_mul 2
    rw [mul_zero] at h2
    refine squeeze_zero (fun n => (div_pos (e261_resid_pos ch n) (by positivity)).le) ?_ h2
    intro n
    rw [pow_one, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (e261_resid_le ch n) (by positivity)
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub hx
  simpa using this

theorem e261_infinite (ch : ℕ → Bool) : (e261Set ch).Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ := hfin.bddAbove
  have hzero : ∀ i ∉ Finset.range (M + 1),
      (e261Set ch).indicator (fun a : ℕ => (a : ℝ) / 2 ^ a) i = 0 := by
    intro i hi
    apply Set.indicator_of_notMem
    intro hmem
    have := hM hmem
    simp at hi
    omega
  have h1 : HasSum ((e261Set ch).indicator (fun a : ℕ => (a : ℝ) / 2 ^ a))
      (∑ i ∈ Finset.range (M + 1), (e261Set ch).indicator (fun a : ℕ => (a : ℝ) / 2 ^ a) i) :=
    hasSum_sum_of_ne_finset_zero hzero
  have h2 := (e261_hasSum ch).unique h1
  rw [e261_psum] at h2
  have := div_pos (e261_resid_pos ch M) (by positivity : (0 : ℝ) < 2 ^ (M + 1))
  linarith

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos261_erdos_261_parts_iii_R1.H2 := by
  intro hZ
  classical
  set Z := {j : ℕ | ((fun p : ℕ × ℕ => (p.1 + 1, if p.1 + 1 < p.2 then 2 * (p.2 - p.1)
    else 2 * p.2))^[j] (1, 2)).2 = j + 2} with hZdef
  have hZmem : ∀ j ∈ Z, e261Path (fun _ => false) j = 0 := by
    intro j hj
    have h := (e261_orbit j).2
    have hj' : ((fun p : ℕ × ℕ => (p.1 + 1, if p.1 + 1 < p.2 then 2 * (p.2 - p.1)
      else 2 * p.2))^[j] (1, 2)).2 = j + 2 := hj
    rw [hj'] at h
    push_cast at h
    omega
  have hZinf : (Set.ofPred (· ∈ Z)).Infinite := hZ
  let ch : (ℕ → Bool) → ℕ → Bool := fun b l => b (Nat.count (· ∈ Z) (l - 1))
  have key : ∀ b k, (Nat.nth (· ∈ Z) k + 1 ∈ e261Set (ch b) ↔ b k = true) := by
    intro b k
    have hmem : Nat.nth (· ∈ Z) k ∈ Z := Nat.nth_mem_of_infinite hZinf k
    have h0 : e261Path (ch b) (Nat.nth (· ∈ Z) k) = 0 := by
      have h1 := e261_abs_path (ch b) (fun _ => false) (Nat.nth (· ∈ Z) k)
      rw [hZmem _ hmem, abs_zero] at h1
      exact abs_eq_zero.mp h1
    have hc : Nat.count (· ∈ Z) (Nat.nth (· ∈ Z) k) = k := Nat.count_nth_of_infinite hZinf k
    simp only [e261Set, Set.mem_ofPred_eq, Nat.add_sub_cancel, h0, lt_irrefl, false_or, true_and,
      ch, hc]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨by omega, h⟩
  refine ⟨fun b => e261Set (ch b), ?_, fun b => ⟨e261_infinite (ch b), fun a ha => ha.1,
    e261_hasSum (ch b)⟩⟩
  intro b c hbc
  funext k
  have h1 := key b k
  have h2 := key c k
  simp only at hbc
  rw [hbc] at h1
  exact Bool.eq_iff_iff.mpr (h1.symm.trans h2)
