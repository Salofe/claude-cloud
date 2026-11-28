import OMAStatements.S_oeis_a250084

/-!
Proof of the g.f. and the recurrence for A250084 (arrays of length 8 with entries in 0..n in
which every 6 consecutive entries have the maximum of some two of them equal to the minimum of
the other four).

* Window condition. For six values `y`, the condition holds iff no threshold `v` has exactly two
  of the values `≤ v` (`window_iff`), i.e. the second and third smallest values coincide.
* Threshold sets. `x` is good iff every threshold set `Tv x v` (`v < n`) meets each of the three
  windows in a number of positions other than 2 (`good_iff`).
* Chains. Counting arrays by their top threshold set gives a linear recursion `G` on 8-bit codes
  (`M_succ`, `M_eq_G`); `(1-x)^8` annihilates it entrywise at `m = 0` by a finite computation,
  hence for every `m`. The recurrence and the generating function follow.
-/

namespace OMA.Helpers

open OMA.S_oeis_a250084 Finset

/-! ### The window condition -/

/-- The condition of the statement on six values (without the bound on `v`). -/
def Cy (y : Fin 6 → ℕ) : Prop :=
  ∃ S ∈ (univ : Finset (Fin 6)).powersetCard 2, ∃ v, (∀ t ∈ S, y t ≤ v) ∧ (∃ t ∈ S, y t = v) ∧
    (∀ t ∉ S, v ≤ y t) ∧ (∃ t ∉ S, y t = v)

theorem cy_to (y : Fin 6 → ℕ) (h : Cy y) (w : ℕ) : (univ.filter (fun t => y t ≤ w)).card ≠ 2 := by
  obtain ⟨S, hS, v, h1, ⟨s, hs, hsv⟩, h3, ⟨t0, ht0, ht0v⟩⟩ := h
  have hc : S.card = 2 := (Finset.mem_powersetCard.1 hS).2
  by_cases hw : w < v
  · have hsub : univ.filter (fun t => y t ≤ w) ⊆ S.erase s := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      have htS : t ∈ S := by
        by_contra hn
        have := h3 t hn
        omega
      refine Finset.mem_erase.2 ⟨?_, htS⟩
      rintro rfl
      omega
    have h1' := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hs, hc] at h1'
    omega
  · have hsub : insert t0 S ⊆ univ.filter (fun t => y t ≤ w) := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Finset.mem_insert.1 ht with rfl | ht'
      · omega
      · have := h1 t ht'
        omega
    have h1' := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem ht0, hc] at h1'
    omega

theorem cy_of (y : Fin 6 → ℕ) (h : ∀ w : ℕ, (univ.filter (fun t => y t ≤ w)).card ≠ 2) :
    Cy y := by
  set U := univ.filter (fun s => 2 ≤ (univ.filter (fun t => y t ≤ y s)).card) with hU
  have hUne : U.Nonempty := by
    obtain ⟨m, _, hm⟩ := Finset.exists_max_image (univ : Finset (Fin 6)) y Finset.univ_nonempty
    refine ⟨m, ?_⟩
    rw [hU, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have : univ.filter (fun t => y t ≤ y m) = univ := by
      apply Finset.filter_true_of_mem
      intro t _
      exact hm t (Finset.mem_univ t)
    rw [this]
    simp
  obtain ⟨s, hsU, hmin⟩ := Finset.exists_min_image U y hUne
  have hs2 : 2 ≤ (univ.filter (fun t => y t ≤ y s)).card := by
    rw [hU, Finset.mem_filter] at hsU
    exact hsU.2
  have hs3 : 3 ≤ (univ.filter (fun t => y t ≤ y s)).card := by
    have := h (y s)
    omega
  set L := univ.filter (fun t => y t < y s) with hL
  set E := univ.filter (fun t => y t = y s) with hE
  have hLc : L.card ≤ 1 := by
    by_cases hLne : L.Nonempty
    · obtain ⟨l, hl, hlmax⟩ := Finset.exists_max_image L y hLne
      have hyl : y l < y s := by
        rw [hL, Finset.mem_filter] at hl
        exact hl.2
      have hlU : l ∉ U := by
        intro hlU
        have := hmin l hlU
        omega
      have hcl : (univ.filter (fun t => y t ≤ y l)).card ≤ 1 := by
        rw [hU, Finset.mem_filter] at hlU
        have : ¬ 2 ≤ (univ.filter (fun t => y t ≤ y l)).card :=
          fun h2 => hlU ⟨Finset.mem_univ _, h2⟩
        omega
      have hsub : L ⊆ univ.filter (fun t => y t ≤ y l) := by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hlmax t ht
      exact le_trans (Finset.card_le_card hsub) hcl
    · rw [Finset.not_nonempty_iff_eq_empty.mp hLne]
      simp
  have hsplit : (univ.filter (fun t => y t ≤ y s)) ⊆ L ∪ E := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [Finset.mem_union, hL, hE, Finset.mem_filter, Finset.mem_filter]
    rcases Nat.lt_or_ge (y t) (y s) with h' | h'
    · exact Or.inl ⟨Finset.mem_univ _, h'⟩
    · exact Or.inr ⟨Finset.mem_univ _, by omega⟩
  have hcard := le_trans (Finset.card_le_card hsplit) (Finset.card_union_le L E)
  have hsE : s ∈ E := by
    rw [hE, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hnotL : ∀ t, ¬ y t < y s → t ∉ L := by
    intro t ht htL
    rw [hL, Finset.mem_filter] at htL
    exact ht htL.2
  rcases Nat.lt_or_ge 0 L.card with hpos | hzero
  · -- one value below `y s`
    obtain ⟨l, hLl⟩ := Finset.card_eq_one.1 (by omega : L.card = 1)
    have hlL : l ∈ L := by rw [hLl]; exact Finset.mem_singleton_self l
    have hyl : y l < y s := by
      rw [hL, Finset.mem_filter] at hlL
      exact hlL.2
    have hE1 : 1 ≤ (E.erase s).card := by
      rw [Finset.card_erase_of_mem hsE]
      omega
    obtain ⟨e, he⟩ := Finset.card_pos.1 (by omega : 0 < (E.erase s).card)
    have hes : e ≠ s := (Finset.mem_erase.1 he).1
    have hye : y e = y s := by
      have := (Finset.mem_erase.1 he).2
      rw [hE, Finset.mem_filter] at this
      exact this.2
    have hls : l ≠ s := by
      rintro rfl
      omega
    refine ⟨{l, s}, ?_, y s, ?_, ⟨s, by simp, rfl⟩, ?_, ⟨e, ?_, hye⟩⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, Finset.card_pair hls⟩
    · intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht'
      · omega
      · rw [Finset.mem_singleton.1 ht']
    · intro t ht
      by_contra hlt
      rw [not_le] at hlt
      have htL : t ∈ L := by
        rw [hL, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hlt⟩
      rw [hLl, Finset.mem_singleton] at htL
      apply ht
      rw [htL]
      exact Finset.mem_insert_self l {s}
    · intro he'
      rcases Finset.mem_insert.1 he' with rfl | he''
      · omega
      · exact hes (Finset.mem_singleton.1 he'')
  · -- no value below `y s`
    have hL0 : L.card = 0 := by omega
    have hE3 : 3 ≤ E.card := by omega
    have hE2 : 1 < (E.erase s).card := by
      rw [Finset.card_erase_of_mem hsE]
      omega
    obtain ⟨e1, he1, e2, he2, he12⟩ := Finset.one_lt_card.1 hE2
    have he1s : e1 ≠ s := (Finset.mem_erase.1 he1).1
    have he2s : e2 ≠ s := (Finset.mem_erase.1 he2).1
    have hye1 : y e1 = y s := by
      have := (Finset.mem_erase.1 he1).2
      rw [hE, Finset.mem_filter] at this
      exact this.2
    have hye2 : y e2 = y s := by
      have := (Finset.mem_erase.1 he2).2
      rw [hE, Finset.mem_filter] at this
      exact this.2
    have hLempty : L = ∅ := Finset.card_eq_zero.1 hL0
    refine ⟨{s, e1}, ?_, y s, ?_, ⟨s, by simp, rfl⟩, ?_, ⟨e2, ?_, hye2⟩⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, Finset.card_pair he1s.symm⟩
    · intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht'
      · exact le_rfl
      · rw [Finset.mem_singleton.1 ht', hye1]
    · intro t _
      by_contra hlt
      rw [not_le] at hlt
      have htL : t ∈ L := by
        rw [hL, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hlt⟩
      rw [hLempty] at htL
      exact Finset.notMem_empty t htL
    · intro he'
      rcases Finset.mem_insert.1 he' with h' | h'
      · exact he2s h'
      · exact he12 (Finset.mem_singleton.1 h').symm

theorem window_iff (y : Fin 6 → ℕ) :
    Cy y ↔ ∀ v : ℕ, (univ.filter (fun t => y t ≤ v)).card ≠ 2 :=
  ⟨cy_to y, cy_of y⟩

/-! ### Threshold sets -/

/-- Entry `k` of a set of positions (`false` past the end). -/
def fget (f : Fin 8 → Bool) (k : ℕ) : Bool := if h : k < 8 then f ⟨k, h⟩ else false

/-- Every window meets the set `f` in a number of positions other than 2. -/
def GoodF (f : Fin 8 → Bool) : Prop :=
  ∀ i < (3 : ℕ), (univ.filter (fun t : Fin 6 => fget f (i + t) = true)).card ≠ 2

instance decGoodF (f : Fin 8 → Bool) : Decidable (GoodF f) := by
  unfold GoodF
  infer_instance

/-- The positions where `x` is at most `v`. -/
def Tv {n : ℕ} (x : Fin 8 → Fin (n + 1)) (v : ℕ) : Fin 8 → Bool := fun p => decide ((x p : ℕ) ≤ v)

theorem get_le {n : ℕ} (x : Fin 8 → Fin (n + 1)) (k : ℕ) : OMA.S_oeis_a250084.get x k ≤ n := by
  unfold OMA.S_oeis_a250084.get
  split_ifs
  · have := (x ⟨k, by assumption⟩).isLt
    omega
  · omega

theorem goodF_univ : GoodF (fun _ => true) := by
  decide

theorem good_iff {n : ℕ} (x : Fin 8 → Fin (n + 1)) :
    good x = true ↔ ∀ v < n, GoodF (Tv x v) := by
  have step1 : good x = true ↔ ∀ i < (3 : ℕ), Cy (fun t : Fin 6 => OMA.S_oeis_a250084.get x (i + t)) := by
    unfold good
    rw [decide_eq_true_iff]
    refine forall_congr' fun i => imp_congr_right fun _ => ?_
    constructor
    · rintro ⟨S, hS, v, _, h1, h2, h3, h4⟩
      exact ⟨S, hS, v, h1, h2, h3, h4⟩
    · rintro ⟨S, hS, v, h1, ⟨t, ht, htv⟩, h3, h4⟩
      refine ⟨S, hS, v, ?_, h1, ⟨t, ht, htv⟩, h3, h4⟩
      rw [← htv]
      exact Nat.lt_succ_of_le (get_le x _)
  have step2 : ∀ i < (3 : ℕ), ∀ v : ℕ,
      (univ.filter (fun t : Fin 6 => OMA.S_oeis_a250084.get x (i + t) ≤ v)) =
        univ.filter (fun t : Fin 6 => fget (Tv x v) (i + t) = true) := by
    intro i hi v
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have ht : i + (t : ℕ) < 8 := by have := t.isLt; omega
    unfold OMA.S_oeis_a250084.get fget Tv
    rw [dif_pos ht, dif_pos ht, decide_eq_true_iff]
  rw [step1]
  constructor
  · intro h v _ i hi
    rw [← step2 i hi v]
    exact (window_iff _).1 (h i hi) v
  · intro h i hi
    rw [window_iff]
    intro v
    rw [step2 i hi v]
    by_cases hv : v < n
    · exact h v hv i hi
    · have e : Tv x v = fun _ => true := by
        funext p
        unfold Tv
        have := (x p).isLt
        simp only [decide_eq_true_iff]
        omega
      rw [e]
      exact goodF_univ i hi

/-! ### Chains of threshold sets -/

/-- Arrays with entries in `0..n`, all threshold sets below `n` good, and the positions with
entries `< n` inside `T`. -/
noncomputable def M (n : ℕ) (T : Fin 8 → Bool) : ℕ := by
  classical
  exact ((univ : Finset (Fin 8 → Fin (n + 1))).filter
    (fun x => (∀ p, (x p : ℕ) < n → T p = true) ∧ ∀ v < n, GoodF (Tv x v))).card

theorem M_zero (T : Fin 8 → Bool) : M 0 T = 1 := by
  classical
  unfold M
  rw [Finset.filter_true_of_mem]
  · simp
  · intro x _
    exact ⟨fun p hp => absurd hp (Nat.not_lt_zero _), fun v hv => absurd hv (Nat.not_lt_zero _)⟩

/-- Restriction of an array with entries in `0..n+1` to entries in `0..n`. -/
def lower {n : ℕ} (x : Fin 8 → Fin (n + 2)) : Fin 8 → Fin (n + 1) :=
  fun p => ⟨min (x p : ℕ) n, by omega⟩

/-- Extension of an array with entries in `0..n` by the top value `n + 1` outside `S`. -/
def raise {n : ℕ} (S : Fin 8 → Bool) (x : Fin 8 → Fin (n + 1)) : Fin 8 → Fin (n + 2) :=
  fun p => if S p = true then ⟨x p, by omega⟩ else ⟨n + 1, by omega⟩

theorem Tv_lower {n : ℕ} (x : Fin 8 → Fin (n + 2)) (v : ℕ) (hv : v < n) :
    Tv (lower x) v = Tv x v := by
  funext p
  show decide (min (x p : ℕ) n ≤ v) = decide ((x p : ℕ) ≤ v)
  rw [decide_eq_decide]
  constructor <;> intro h <;> omega

theorem raise_val {n : ℕ} (S : Fin 8 → Bool) (x : Fin 8 → Fin (n + 1)) (p : Fin 8) :
    ((raise S x p : Fin (n + 2)) : ℕ) = if S p = true then (x p : ℕ) else n + 1 := by
  unfold raise
  split_ifs <;> rfl

theorem M_succ (n : ℕ) (T : Fin 8 → Bool) :
    M (n + 1) T = ∑ S : Fin 8 → Bool,
      if GoodF S ∧ (∀ p, S p = true → T p = true) then M n S else 0 := by
  classical
  unfold M
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => Tv x n) (t := univ)
    (fun x _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.filter_filter]
  split_ifs with hS
  · -- the fibre over a good `S ⊆ T`
    apply Finset.card_bij' (fun x _ => lower x) (fun x _ => raise S x)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨⟨_, h2⟩, h3⟩ := hx
      refine ⟨fun p hp => ?_, fun v hv => ?_⟩
      · have hp' : min (x p : ℕ) n < n := hp
        rw [← h3]
        exact decide_eq_true (by omega)
      · rw [Tv_lower x v hv]
        exact h2 v (by omega)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      have hTS : Tv (raise S x) n = S := by
        funext p
        show decide (((raise S x p : Fin (n + 2)) : ℕ) ≤ n) = S p
        rw [raise_val]
        by_cases hp : S p = true
        · rw [if_pos hp, hp]
          have := (x p).isLt
          exact decide_eq_true (by omega)
        · rw [if_neg hp]
          simp only [Bool.not_eq_true] at hp
          rw [hp]
          exact decide_eq_false (by omega)
      have hlow : ∀ v < n, Tv (raise S x) v = Tv x v := by
        intro v hv
        funext p
        show decide (((raise S x p : Fin (n + 2)) : ℕ) ≤ v) = decide ((x p : ℕ) ≤ v)
        rw [raise_val]
        split_ifs with hp
        · rfl
        · have hxp : ¬ (x p : ℕ) < n := fun h => hp (h1 p h)
          rw [decide_eq_decide]
          omega
      refine ⟨⟨fun p hp => ?_, fun v hv => ?_⟩, hTS⟩
      · rw [raise_val] at hp
        split_ifs at hp with hSp
        · exact hS.2 p hSp
        · omega
      · rcases Nat.lt_or_ge v n with hv' | hv'
        · rw [hlow v hv']
          exact h2 v hv'
        · obtain rfl : v = n := by omega
          rw [hTS]
          exact hS.1
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨_, h3⟩ := hx
      funext p
      apply Fin.ext
      rw [raise_val]
      have hiff : S p = true ↔ (x p : ℕ) ≤ n := by
        rw [← h3]
        exact decide_eq_true_iff
      split_ifs with hp
      · show min (x p : ℕ) n = x p
        have := hiff.1 hp
        omega
      · have : ¬ (x p : ℕ) ≤ n := fun h => hp (hiff.2 h)
        have := (x p).isLt
        omega
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨h1, _⟩ := hx
      funext p
      apply Fin.ext
      show min ((raise S x p : Fin (n + 2)) : ℕ) n = x p
      rw [raise_val]
      split_ifs with hp
      · have := (x p).isLt
        omega
      · have hxp : ¬ (x p : ℕ) < n := fun h => hp (h1 p h)
        have := (x p).isLt
        omega
  · -- otherwise the fibre is empty
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _
    rintro ⟨⟨h1, h2⟩, h3⟩
    apply hS
    refine ⟨?_, fun p hp => ?_⟩
    · rw [← h3]
      exact h2 n (by omega)
    · apply h1 p
      rw [← h3] at hp
      have hp' : (x p : ℕ) ≤ n := of_decide_eq_true hp
      omega

/-! ### Codes -/

/-- The set of positions with code `u`: position `p` is in it iff bit `p` of `u` is set. -/
def row (u : Fin 256) : Fin 8 → Bool := fun p => Nat.testBit u.val p.val

/-- The code of a set of positions. -/
def code (f : Fin 8 → Bool) : ℕ := ∑ p : Fin 8, if f p = true then 2 ^ p.val else 0

theorem code_row : ∀ u : Fin 256, code (row u) = u.val := by
  decide +kernel

theorem row_injective : Function.Injective row := by
  intro a b h
  apply Fin.ext
  rw [← code_row a, ← code_row b, h]

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩

/-- Number of set bits among the low 8 bits. -/
def pc8 (m : ℕ) : ℕ :=
  m % 2 + m / 2 % 2 + m / 4 % 2 + m / 8 % 2 + m / 16 % 2 + m / 32 % 2 + m / 64 % 2 + m / 128 % 2

/-- `GoodF` on codes: the three windows have masks 63, 126, 252. -/
def goodc (u : ℕ) : Bool :=
  !(pc8 (u &&& 63) == 2) && !(pc8 (u &&& 126) == 2) && !(pc8 (u &&& 252) == 2)

theorem goodc_iff : ∀ u : Fin 256, GoodF (row u) ↔ goodc u.val = true := by
  decide +kernel

theorem sub_iff (w u : Fin 256) : (∀ p, row w p = true → row u p = true) ↔
    (w.val &&& u.val == w.val) = true := by
  rw [beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land]
    by_cases hi : i < 8
    · have := h ⟨i, hi⟩
      unfold row at this
      cases hw : w.val.testBit i <;> simp_all
    · have hw : w.val.testBit i = false := by
        apply Nat.testBit_eq_false_of_lt
        have h1 : (256 : ℕ) ≤ 2 ^ i := by
          calc (256 : ℕ) = 2 ^ 8 := by norm_num
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
        have := w.isLt
        omega
      simp [hw]
  · intro h p hp
    unfold row at hp ⊢
    rw [← h, Nat.testBit_land] at hp
    simp only [Bool.and_eq_true] at hp
    exact hp.2

/-- The good codes. -/
def goodSet : Finset (Fin 256) := univ.filter (fun w => goodc w.val = true)

/-- The chain recursion on codes. -/
def G : ℕ → Fin 256 → ℕ
  | 0, _ => 1
  | n + 1, u => ∑ w ∈ goodSet, if (w.val &&& u.val == w.val) = true then G n w else 0

theorem M_eq_G (n : ℕ) : ∀ u : Fin 256, M n (row u) = G n u := by
  induction n with
  | zero =>
    intro u
    rw [M_zero]
    rfl
  | succ n ih =>
    intro u
    rw [M_succ, ← row_bijective.sum_comp]
    simp only [G, goodSet]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ih w]
    by_cases hg : goodc w.val = true
    · rw [if_pos hg]
      refine if_congr ?_ rfl rfl
      rw [goodc_iff, sub_iff]
      exact and_iff_right hg
    · rw [if_neg hg, if_neg]
      rw [goodc_iff]
      exact fun h => hg h.1

theorem a_eq_G (n : ℕ) : a n = (G n 255 : ℤ) := by
  have h1 : (univ.filter (fun x : Fin 8 → Fin (n + 1) => good x)) =
      univ.filter (fun x => (∀ p, (x p : ℕ) < n → row 255 p = true) ∧ ∀ v < n, GoodF (Tv x v)) := by
    apply Finset.filter_congr
    intro x _
    rw [good_iff]
    have hr : ∀ p, row 255 p = true := by decide
    exact ⟨fun h => ⟨fun p _ => hr p, h⟩, fun h => h.2⟩
  unfold a
  rw [h1, ← M_eq_G]
  unfold M
  congr 2

/-! ### The recurrence -/

theorem G_succ (n : ℕ) (u : Fin 256) :
    G (n + 1) u = ∑ w ∈ goodSet, if (w.val &&& u.val == w.val) = true then G n w else 0 :=
  rfl

theorem G_base : ∀ u : Fin 256, goodc u.val = true →
    G 8 u + 28 * G 6 u + 70 * G 4 u + 28 * G 2 u + G 0 u =
      8 * G 7 u + 56 * G 5 u + 56 * G 3 u + 8 * G 1 u := by
  decide +kernel

theorem G_rec (m : ℕ) : ∀ u : Fin 256, goodc u.val = true →
    G (m + 8) u + 28 * G (m + 6) u + 70 * G (m + 4) u + 28 * G (m + 2) u + G m u =
      8 * G (m + 7) u + 56 * G (m + 5) u + 56 * G (m + 3) u + 8 * G (m + 1) u := by
  induction m with
  | zero => exact G_base
  | succ m ih =>
    intro u _
    rw [show m + 1 + 8 = (m + 8) + 1 by omega, show m + 1 + 6 = (m + 6) + 1 by omega,
      show m + 1 + 4 = (m + 4) + 1 by omega, show m + 1 + 2 = (m + 2) + 1 by omega,
      show m + 1 + 7 = (m + 7) + 1 by omega, show m + 1 + 5 = (m + 5) + 1 by omega,
      show m + 1 + 3 = (m + 3) + 1 by omega]
    rw [G_succ (m + 8), G_succ (m + 6), G_succ (m + 4), G_succ (m + 2), G_succ m,
      G_succ (m + 7), G_succ (m + 5), G_succ (m + 3), G_succ (m + 1)]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w hw => ?_
    have hg : goodc w.val = true := (Finset.mem_filter.1 hw).2
    split_ifs
    · exact ih w hg
    · rfl

theorem a_rec (m : ℕ) :
    a (m + 8) + 28 * a (m + 6) + 70 * a (m + 4) + 28 * a (m + 2) + a m =
      8 * a (m + 7) + 56 * a (m + 5) + 56 * a (m + 3) + 8 * a (m + 1) := by
  simp only [a_eq_G]
  exact_mod_cast G_rec m 255 (by decide)

theorem G_vals : G 1 255 = 144 ∧ G 2 255 = 2228 ∧ G 3 255 = 15472 ∧ G 4 255 = 68863 ∧
    G 5 255 = 232096 ∧ G 6 255 = 647122 ∧ G 7 255 = 1572320 ∧ G 8 255 = 3441309 := by
  decide +kernel

theorem a_vals : a 1 = 144 ∧ a 2 = 2228 ∧ a 3 = 15472 ∧ a 4 = 68863 ∧ a 5 = 232096 ∧
    a 6 = 647122 ∧ a 7 = 1572320 ∧ a 8 = 3441309 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := G_vals
  simp only [a_eq_G, h1, h2, h3, h4, h5, h6, h7, h8]
  norm_num

theorem recurrence (n : ℕ) (hn : 9 ≤ n) :
    (a n : ℚ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) +
      56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  have h := a_rec m
  have hq : ((a (m + 8) + 28 * a (m + 6) + 70 * a (m + 4) + 28 * a (m + 2) + a m : ℤ) : ℚ) =
      ((8 * a (m + 7) + 56 * a (m + 5) + 56 * a (m + 3) + 8 * a (m + 1) : ℤ) : ℚ) := by
    rw [h]
  push_cast at hq
  rw [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
    show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega,
    show m + 8 - 5 = m + 3 by omega, show m + 8 - 6 = m + 2 by omega,
    show m + 8 - 7 = m + 1 by omega, show m + 8 - 8 = m by omega]
  linarith

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 8 : PowerSeries ℚ) =
      X * (144 + 1076 * X + 1680 * X ^ 2 - 593 * X ^ 3 - 280 * X ^ 4 - 18 * X ^ 5 + 8 * X ^ 6 -
        X ^ 7) := by
  set F : ℕ → ℚ := fun n => if n < 1 then 0 else (a n : ℚ) with hF
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := a_vals
  have key : PowerSeries.mk F * (1 - X) ^ 8 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 8 * (PowerSeries.mk F * X ^ 1) +
        C 28 * (PowerSeries.mk F * X ^ 2) - C 56 * (PowerSeries.mk F * X ^ 3) +
        C 70 * (PowerSeries.mk F * X ^ 4) - C 56 * (PowerSeries.mk F * X ^ 5) +
        C 28 * (PowerSeries.mk F * X ^ 6) - C 8 * (PowerSeries.mk F * X ^ 7) +
        C 1 * (PowerSeries.mk F * X ^ 8) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (144 + 1076 * X + 1680 * X ^ 2 - 593 * X ^ 3 - 280 * X ^ 4 - 18 * X ^ 5 +
      8 * X ^ 6 - X ^ 7) =
      C 144 * X ^ 1 + C 1076 * X ^ 2 + C 1680 * X ^ 3 - C 593 * X ^ 4 - C 280 * X ^ 5 -
        C 18 * X ^ 6 + C 8 * X ^ 7 - C 1 * X ^ 8 := by
    simp only [map_ofNat, map_one]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 9
  · interval_cases k <;> norm_num [hF, v1, v2, v3, v4, v5, v6, v7, v8]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 9 := ⟨k - 9, by omega⟩
    have hr := recurrence (j + 9) (by omega)
    simp only [show j + 9 - 1 = j + 8 by omega, show j + 9 - 2 = j + 7 by omega,
      show j + 9 - 3 = j + 6 by omega, show j + 9 - 4 = j + 5 by omega,
      show j + 9 - 5 = j + 4 by omega, show j + 9 - 6 = j + 3 by omega,
      show j + 9 - 7 = j + 2 by omega, show j + 9 - 8 = j + 1 by omega] at hr
    simp only [show 0 ≤ j + 9 by omega, show 1 ≤ j + 9 by omega, show 2 ≤ j + 9 by omega,
      show 3 ≤ j + 9 by omega, show 4 ≤ j + 9 by omega, show 5 ≤ j + 9 by omega,
      show 6 ≤ j + 9 by omega, show 7 ≤ j + 9 by omega, show 8 ≤ j + 9 by omega,
      show j + 9 - 0 = j + 9 by omega, show j + 9 - 1 = j + 8 by omega,
      show j + 9 - 2 = j + 7 by omega, show j + 9 - 3 = j + 6 by omega,
      show j + 9 - 4 = j + 5 by omega, show j + 9 - 5 = j + 4 by omega,
      show j + 9 - 6 = j + 3 by omega, show j + 9 - 7 = j + 2 by omega,
      show j + 9 - 8 = j + 1 by omega,
      show ¬ (j + 9 = 1) by omega, show ¬ (j + 9 = 2) by omega, show ¬ (j + 9 = 3) by omega,
      show ¬ (j + 9 = 4) by omega, show ¬ (j + 9 = 5) by omega, show ¬ (j + 9 = 6) by omega,
      show ¬ (j + 9 = 7) by omega, show ¬ (j + 9 = 8) by omega,
      show ¬ (j + 9 < 1) by omega, show ¬ (j + 8 < 1) by omega, show ¬ (j + 7 < 1) by omega,
      show ¬ (j + 6 < 1) by omega, show ¬ (j + 5 < 1) by omega, show ¬ (j + 4 < 1) by omega,
      show ¬ (j + 3 < 1) by omega, show ¬ (j + 2 < 1) by omega, show ¬ (j + 1 < 1) by omega,
      if_true, if_false, hF]
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a250084.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
