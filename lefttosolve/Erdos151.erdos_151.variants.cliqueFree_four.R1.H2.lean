import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R1

/-! Step H2 of reduction Erdos151.erdos_151.variants.cliqueFree_four.R1.

Every triangle-free graph on at most six vertices has a colouring of its vertices with two
colours in which at most one edge is monochromatic (it becomes bipartite after deleting at
most one edge). The kernel checks this over all graphs on six labelled vertices, written as
15-bit masks of their edges: either the mask contains one of the 20 triangle masks, or for
one of the 32 colourings (vertex 0 coloured false) the monochromatic edges of the mask form
zero or a power of two. Both tests are unrolled into plain Bool expressions on Nat.land and
Nat.beq, which the kernel evaluates quickly; the run is split into 8 chunks.

Given an edge colouring c, keep this vertex colouring if no edge with equal end colours has
the colour of its ends, and swap the two colours otherwise: in that case the only such edge
is the special monochromatic edge, and swapping fixes it while every other edge keeps
different end colours. -/

namespace OMA.Helpers

/-- Bit position of the pair of distinct vertices `i`, `j` below six (colex order). -/
def ix (i j : ℕ) : ℕ := if i < j then j * (j - 1) / 2 + i else i * (i - 1) / 2 + j

/-- For each triple of vertices below six, the bit mask of its three pairs. -/
def trisM : List ℕ :=
  [7, 25, 193, 3073, 42, 322, 5122, 584, 9224, 17472, 52, 388, 6148, 656, 10256, 18560, 800,
    12320, 20736, 25088]

/-- For each colouring of the vertices below six with vertex `0` coloured `false`, the bit
mask of its monochromatic pairs. -/
def monos : List ℕ :=
  [32767, 30570, 28377, 26188, 24007, 21842, 19681, 17524, 15423, 13482, 11545, 9612, 7687,
    5778, 3873, 1972, 1023, 2922, 4825, 6732, 8647, 10578, 12513, 14452, 16447, 18602,
    20761, 22924, 25095, 27282, 29473, 31668]

/-- The edge mask `m` contains a triangle (unrolled form of `trisM.any`). -/
def hasTri (m : ℕ) : Bool :=
  Nat.beq (Nat.land m 7) 7 ||
  (Nat.beq (Nat.land m 25) 25 ||
  (Nat.beq (Nat.land m 193) 193 ||
  (Nat.beq (Nat.land m 3073) 3073 ||
  (Nat.beq (Nat.land m 42) 42 ||
  (Nat.beq (Nat.land m 322) 322 ||
  (Nat.beq (Nat.land m 5122) 5122 ||
  (Nat.beq (Nat.land m 584) 584 ||
  (Nat.beq (Nat.land m 9224) 9224 ||
  (Nat.beq (Nat.land m 17472) 17472 ||
  (Nat.beq (Nat.land m 52) 52 ||
  (Nat.beq (Nat.land m 388) 388 ||
  (Nat.beq (Nat.land m 6148) 6148 ||
  (Nat.beq (Nat.land m 656) 656 ||
  (Nat.beq (Nat.land m 10256) 10256 ||
  (Nat.beq (Nat.land m 18560) 18560 ||
  (Nat.beq (Nat.land m 800) 800 ||
  (Nat.beq (Nat.land m 12320) 12320 ||
  (Nat.beq (Nat.land m 20736) 20736 ||
  (Nat.beq (Nat.land m 25088) 25088 ||
  false)))))))))))))))))))

/-- `x` is zero or a power of two. -/
def oneBit (x : ℕ) : Bool := Nat.beq (Nat.land x (x - 1)) 0

/-- Some colouring leaves at most one monochromatic edge of `m` (unrolled `monos.any`). -/
def fine (m : ℕ) : Bool :=
  oneBit (Nat.land m 32767) ||
  (oneBit (Nat.land m 30570) ||
  (oneBit (Nat.land m 28377) ||
  (oneBit (Nat.land m 26188) ||
  (oneBit (Nat.land m 24007) ||
  (oneBit (Nat.land m 21842) ||
  (oneBit (Nat.land m 19681) ||
  (oneBit (Nat.land m 17524) ||
  (oneBit (Nat.land m 15423) ||
  (oneBit (Nat.land m 13482) ||
  (oneBit (Nat.land m 11545) ||
  (oneBit (Nat.land m 9612) ||
  (oneBit (Nat.land m 7687) ||
  (oneBit (Nat.land m 5778) ||
  (oneBit (Nat.land m 3873) ||
  (oneBit (Nat.land m 1972) ||
  (oneBit (Nat.land m 1023) ||
  (oneBit (Nat.land m 2922) ||
  (oneBit (Nat.land m 4825) ||
  (oneBit (Nat.land m 6732) ||
  (oneBit (Nat.land m 8647) ||
  (oneBit (Nat.land m 10578) ||
  (oneBit (Nat.land m 12513) ||
  (oneBit (Nat.land m 14452) ||
  (oneBit (Nat.land m 16447) ||
  (oneBit (Nat.land m 18602) ||
  (oneBit (Nat.land m 20761) ||
  (oneBit (Nat.land m 22924) ||
  (oneBit (Nat.land m 25095) ||
  (oneBit (Nat.land m 27282) ||
  (oneBit (Nat.land m 29473) ||
  (oneBit (Nat.land m 31668) ||
  false)))))))))))))))))))))))))))))))

/-- The test run on every edge mask. -/
def chk (m : ℕ) : Bool := hasTri m || fine m

/-- `okTree s d` runs `chk` on `s, s + 1, ..., s + 2 ^ d - 1`. -/
def okTree (s : ℕ) : ℕ → Bool
  | 0 => chk s
  | d + 1 => okTree s d && okTree (s + 2 ^ d) d

theorem chunk0 : okTree (4096 * 0) 12 = true := by decide +kernel

theorem chunk1 : okTree (4096 * 1) 12 = true := by decide +kernel

theorem chunk2 : okTree (4096 * 2) 12 = true := by decide +kernel

theorem chunk3 : okTree (4096 * 3) 12 = true := by decide +kernel

theorem chunk4 : okTree (4096 * 4) 12 = true := by decide +kernel

theorem chunk5 : okTree (4096 * 5) 12 = true := by decide +kernel

theorem chunk6 : okTree (4096 * 6) 12 = true := by decide +kernel

theorem chunk7 : okTree (4096 * 7) 12 = true := by decide +kernel

theorem okTree_spec : ∀ d s, okTree s d = true → ∀ x < 2 ^ d, chk (s + x) = true
  | 0, s, h, x, hx => by
    obtain rfl : x = 0 := by simpa using hx
    simpa [okTree] using h
  | d + 1, s, h, x, hx => by
    rw [okTree, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge x (2 ^ d) with hx' | hx'
    · exact okTree_spec d s h.1 x hx'
    · have hx2 : x - 2 ^ d < 2 ^ d := by rw [Nat.pow_succ] at hx; omega
      have := okTree_spec d (s + 2 ^ d) h.2 (x - 2 ^ d) hx2
      rwa [Nat.add_assoc, Nat.add_sub_cancel' hx'] at this

theorem chk_all (m : ℕ) (hm : m < 2 ^ 15) : chk m = true := by
  have hm' : m < 32768 := by simpa using hm
  have hc : ∀ i < 8, okTree (4096 * i) 12 = true := by
    intro i hi
    interval_cases i
    exacts [chunk0, chunk1, chunk2, chunk3, chunk4, chunk5, chunk6, chunk7]
  have hx : m % 4096 < 2 ^ 12 := by
    rw [show (2 : ℕ) ^ 12 = 4096 by norm_num]
    exact Nat.mod_lt _ (by norm_num)
  have := okTree_spec 12 (4096 * (m / 4096)) (hc _ (by omega)) (m % 4096) hx
  rwa [Nat.div_add_mod] at this

theorem hasTri_eq (m : ℕ) : hasTri m = trisM.any fun T => Nat.beq (Nat.land m T) T := rfl

theorem fine_eq (m : ℕ) : fine m = monos.any fun M => oneBit (Nat.land m M) := rfl

theorem ix_lt : ∀ i < 6, ∀ j < 6, i ≠ j → ix i j < 15 := by decide +kernel

theorem ix_inj_fin : ∀ i j u v : Fin 6, i ≠ j → u ≠ v → ix i j = ix u v →
    (i = u ∧ j = v) ∨ (i = v ∧ j = u) := by decide +kernel

theorem ix_inj {i j u v : ℕ} (hi : i < 6) (hj : j < 6) (hu : u < 6) (hv : v < 6) (hij : i ≠ j)
    (huv : u ≠ v) (h : ix i j = ix u v) : (i = u ∧ j = v) ∨ (i = v ∧ j = u) := by
  have := ix_inj_fin ⟨i, hi⟩ ⟨j, hj⟩ ⟨u, hu⟩ ⟨v, hv⟩ (fun e => hij (congrArg Fin.val e))
    (fun e => huv (congrArg Fin.val e)) h
  simpa only [Fin.mk.injEq] using this

theorem trisM_spec : ∀ T ∈ trisM, ∃ a < 6, ∃ b < 6, ∃ c < 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    T.testBit (ix a b) = true ∧ T.testBit (ix a c) = true ∧ T.testBit (ix b c) = true := by
  decide +kernel

theorem monos_spec : ∀ M ∈ monos, ∃ d < 64, ∀ i < 6, ∀ j < 6, i ≠ j →
    M.testBit (ix i j) = (d.testBit i == d.testBit j) := by
  decide +kernel

/-- The number whose bits `0, 1, ..., n - 1` are `f 0, f 1, ..., f (n - 1)`. -/
def maskOf : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | n + 1, f => Nat.bit (f 0) (maskOf n fun q => f (q + 1))

theorem testBit_maskOf : ∀ n (f : ℕ → Bool) q, q < n → (maskOf n f).testBit q = f q
  | 0, _, q, h => absurd h (Nat.not_lt_zero q)
  | _ + 1, _, 0, _ => Nat.testBit_bit_zero _ _
  | n + 1, _, q + 1, h =>
    (Nat.testBit_bit_succ q _ _).trans (testBit_maskOf n _ q (Nat.lt_of_succ_lt_succ h))

theorem maskOf_lt : ∀ n (f : ℕ → Bool), maskOf n f < 2 ^ n
  | 0, _ => Nat.one_pos
  | n + 1, _ => Nat.bit_lt_two_pow_succ_iff.mpr (maskOf_lt n _)

/-- A triangle-free graph on at most six vertices has a vertex colouring with at most one
monochromatic edge: any two monochromatic edges are the same edge. -/
theorem colouring {k : ℕ} (L : SimpleGraph (Fin k)) (hk : k ≤ 6) (hL : L.CliqueFree 3) :
    ∃ col : Fin k → Bool, ∀ x y u v : Fin k, L.Adj x y → L.Adj u v → col x = col y →
      col u = col v → (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  classical
  let A : ℕ → ℕ → Prop := fun i j => ∃ (hi : i < k) (hj : j < k), L.Adj ⟨i, hi⟩ ⟨j, hj⟩
  have hAs : ∀ i j, A i j → A j i := fun i j ⟨hi, hj, h⟩ => ⟨hj, hi, h.symm⟩
  have hAne : ∀ i j, A i j → i ≠ j := by
    rintro i j ⟨hi, hj, h⟩ rfl
    exact L.irrefl h
  let f : ℕ → Bool := fun q => decide (∃ i < 6, ∃ j < 6, ix i j = q ∧ A i j)
  let m := maskOf 15 f
  have hm : ∀ i < 6, ∀ j < 6, i ≠ j → (m.testBit (ix i j) = true ↔ A i j) := by
    intro i hi j hj hij
    rw [testBit_maskOf 15 f _ (ix_lt i hi j hj hij)]
    simp only [f, decide_eq_true_eq]
    constructor
    · rintro ⟨u, hu, v, hv, he, hA⟩
      rcases ix_inj hu hv hi hj (hAne u v hA) hij he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hA
      · exact hAs _ _ hA
    · intro hA
      exact ⟨i, hi, j, hj, rfl, hA⟩
  have hnt : hasTri m = false := by
    rw [Bool.eq_false_iff]
    intro h
    rw [hasTri_eq, List.any_eq_true] at h
    obtain ⟨T, hT, hmT⟩ := h
    have hmT' : m &&& T = T := Nat.eq_of_beq_eq_true hmT
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, h1, h2, h3⟩ := trisM_spec T hT
    have bit : ∀ q, T.testBit q = true → m.testBit q = true := by
      intro q hq
      have := congrArg (fun z => z.testBit q) hmT'
      simp only [Nat.testBit_and, hq, Bool.and_true] at this
      exact this
    obtain ⟨ha', hb', e1⟩ := (hm a ha b hb hab).mp (bit _ h1)
    obtain ⟨_, hc', e2⟩ := (hm a ha c hc hac).mp (bit _ h2)
    obtain ⟨_, _, e3⟩ := (hm b hb c hc hbc).mp (bit _ h3)
    exact hL {⟨a, ha'⟩, ⟨b, hb'⟩, ⟨c, hc'⟩} (SimpleGraph.is3Clique_triple_iff.mpr ⟨e1, e2, e3⟩)
  have hfine : fine m = true := by
    have := chk_all m (maskOf_lt 15 f)
    rwa [chk, hnt, Bool.false_or] at this
  rw [fine_eq, List.any_eq_true] at hfine
  obtain ⟨M, hM, hone⟩ := hfine
  obtain ⟨d, -, hd⟩ := monos_spec M hM
  refine ⟨fun x => d.testBit x.val, ?_⟩
  intro x y u v hxy huv hcxy hcuv
  have h6 : ∀ z : Fin k, z.val < 6 := fun z => lt_of_lt_of_le z.isLt hk
  have hne : ∀ z w : Fin k, L.Adj z w → z.val ≠ w.val := fun z w h he => h.ne (Fin.ext he)
  have key : ∀ z w : Fin k, L.Adj z w → d.testBit z.val = d.testBit w.val →
      (m &&& M).testBit (ix z.val w.val) = true := by
    intro z w hzw hc
    rw [Nat.testBit_and, Bool.and_eq_true]
    refine ⟨(hm _ (h6 z) _ (h6 w) (hne z w hzw)).mpr ⟨z.isLt, w.isLt, hzw⟩, ?_⟩
    rw [hd _ (h6 z) _ (h6 w) (hne z w hzw), hc, beq_self_eq_true]
  have k1 := key x y hxy hcxy
  have k2 := key u v huv hcuv
  have hpow : (m &&& M) &&& ((m &&& M) - 1) = 0 := Nat.eq_of_beq_eq_true hone
  have hnz : m &&& M ≠ 0 := by
    intro h0
    rw [h0, Nat.zero_testBit] at k1
    exact Bool.false_ne_true k1
  obtain ⟨e, he⟩ := (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo hnz).mp hpow
  rw [he, Nat.testBit_two_pow, decide_eq_true_eq] at k1 k2
  rcases ix_inj (h6 x) (h6 y) (h6 u) (h6 v) (hne x y hxy) (hne u v huv) (k1.symm.trans k2) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨Fin.ext h1, Fin.ext h2⟩
  · exact Or.inr ⟨Fin.ext h1, Fin.ext h2⟩

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1.H2 := by
  intro k L hk hL c hc
  obtain ⟨col, hcol⟩ := colouring L hk hL
  by_cases hW : ∃ u v : Fin k, L.Adj u v ∧ col u = col v ∧ col u = c u v
  · obtain ⟨u, v, huv, hcuv, hcu⟩ := hW
    refine ⟨fun z => !col z, ?_⟩
    rintro x y hxy ⟨h1, h2⟩
    have hxy' : col x = col y := Bool.not_inj (h1.trans h2.symm)
    rcases hcol x y u v hxy huv hxy' hcuv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [← hcu] at h1
      exact (Bool.not_eq_self _).mp h1
    · rw [hc, ← hcu, hcuv] at h1
      exact (Bool.not_eq_self _).mp h1
  · refine ⟨col, ?_⟩
    rintro x y hxy ⟨h1, h2⟩
    exact hW ⟨x, y, hxy, h1.trans h2.symm, h1⟩
