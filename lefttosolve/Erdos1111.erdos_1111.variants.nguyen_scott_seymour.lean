import FormalConjectures.ErdosProblems.«1111»

/-
Erdos problem 1111, the Nguyen--Scott--Seymour variant.

Proof outline (induction on the clique bound t, everything relative to a finset U of vertices):
* by induction every neighbourhood inside U is d'-colourable;
* take a rock A inside U: a nonempty set with ed A >= 4c |A| (ed = twice the edge count),
  of minimum size and then with the maximum number of edges; a swapping argument shows that
  every vertex of U outside A has at most 4c+1 neighbours in A, and A is (4c+1)-colourable;
* X = the vertices of A of degree > ed A / (8r), r = 4c+1; there are fewer than 8r of them;
  the rest of A is split greedily into at most 8r bins, each of total degree <= ed A / (4r);
* a vertex w of U outside A and not adjacent to X sees at most r bins; deleting those bins from A
  leaves at least half of the edges, hence a set containing a subgraph of minimum degree >= c
  that is anticomplete to w; grouping the vertices w by the set of bins they see gives at most
  2^(8r) classes, each (c-1)-colourable when no good pair (A, B) exists.
-/

namespace OMA.Helpers

open Classical

variable {V : Type*}

/-- number of neighbours of `v` inside the finset `A` -/
noncomputable def dg (G : SimpleGraph V) (A : Finset V) (v : V) : ℕ :=
  (A.filter (fun x => G.Adj v x)).card

/-- twice the number of edges with both ends in `A` -/
noncomputable def ed (G : SimpleGraph V) (A : Finset V) : ℕ := ∑ v ∈ A, dg G A v

/-- the finset `U` can be properly coloured with colours `< n` -/
def PC (G : SimpleGraph V) (U : Finset V) (n : ℕ) : Prop :=
  ∃ f : V → ℕ, (∀ v ∈ U, f v < n) ∧ ∀ u ∈ U, ∀ v ∈ U, G.Adj u v → f u ≠ f v

theorem dg_mono (G : SimpleGraph V) {A B : Finset V} (h : A ⊆ B) (v : V) :
    dg G A v ≤ dg G B v :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem dg_insert (G : SimpleGraph V) (B : Finset V) (v u : V) (hv : v ∉ B) :
    dg G (insert v B) u = dg G B u + (if G.Adj u v then 1 else 0) := by
  unfold dg
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    simp [hv]
  · simp

theorem dg_self_insert (G : SimpleGraph V) (B : Finset V) (v : V) (hv : v ∉ B) :
    dg G (insert v B) v = dg G B v := by
  rw [dg_insert G B v v hv]; simp

theorem ed_insert (G : SimpleGraph V) (B : Finset V) (v : V) (hv : v ∉ B) :
    ed G (insert v B) = ed G B + 2 * dg G B v := by
  unfold ed
  rw [Finset.sum_insert hv, dg_self_insert G B v hv]
  have h1 : ∑ u ∈ B, dg G (insert v B) u
      = ∑ u ∈ B, dg G B u + ∑ u ∈ B, (if G.Adj u v then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun u _ => dg_insert G B v u hv)
  have h2 : ∑ u ∈ B, (if G.Adj u v then 1 else 0) = dg G B v := by
    unfold dg
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl (fun u _ => by simp [G.adj_comm])
  rw [h1, h2]; ring

theorem dg_erase_self (G : SimpleGraph V) (A : Finset V) (u : V) :
    dg G (A.erase u) u = dg G A u := by
  unfold dg
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_, hx⟩, h⟩; exact ⟨hx, h⟩
  · rintro ⟨hx, h⟩; exact ⟨⟨fun e => G.irrefl (e ▸ h), hx⟩, h⟩

theorem ed_erase (G : SimpleGraph V) (A : Finset V) (u : V) (hu : u ∈ A) :
    ed G A = ed G (A.erase u) + 2 * dg G A u := by
  have h := ed_insert G (A.erase u) u (Finset.notMem_erase u A)
  rw [Finset.insert_erase hu, dg_erase_self] at h
  exact h

theorem mul_card_le_ed (G : SimpleGraph V) (S : Finset V) (m : ℕ)
    (h : ∀ v ∈ S, m ≤ dg G S v) : m * S.card ≤ ed G S := by
  unfold ed
  have := Finset.card_nsmul_le_sum S (fun v => dg G S v) m h
  simpa [mul_comm] using this

theorem exists_dg_lt (G : SimpleGraph V) (S : Finset V) (m : ℕ)
    (h : ed G S < m * S.card) : ∃ v ∈ S, dg G S v < m := by
  by_contra hcon
  push Not at hcon
  have := mul_card_le_ed G S m hcon
  omega

theorem dg_lt_card (G : SimpleGraph V) (A : Finset V) (u : V) (hu : u ∈ A) :
    dg G A u < A.card := by
  rw [← dg_erase_self]
  have h1 : dg G (A.erase u) u ≤ (A.erase u).card := Finset.card_filter_le _ _
  have h2 := Finset.card_erase_lt_of_mem hu
  omega


/- ### colourings of finsets -/

theorem PC.mono_set {G : SimpleGraph V} {U W : Finset V} {n : ℕ} (h : W ⊆ U)
    (hU : PC G U n) : PC G W n := by
  obtain ⟨f, h1, h2⟩ := hU
  exact ⟨f, fun v hv => h1 v (h hv), fun u hu v hv => h2 u (h hu) v (h hv)⟩

theorem PC.mono_n {G : SimpleGraph V} {U : Finset V} {n m : ℕ} (h : n ≤ m)
    (hU : PC G U n) : PC G U m := by
  obtain ⟨f, h1, h2⟩ := hU
  exact ⟨f, fun v hv => lt_of_lt_of_le (h1 v hv) h, h2⟩

theorem PC.empty (G : SimpleGraph V) (n : ℕ) : PC G ∅ n :=
  ⟨fun _ => 0, by simp, by simp⟩

theorem PC.union {G : SimpleGraph V} {U W : Finset V} {m n : ℕ}
    (hU : PC G U m) (hW : PC G W n) : PC G (U ∪ W) (m + n) := by
  obtain ⟨f, f1, f2⟩ := hU
  obtain ⟨g, g1, g2⟩ := hW
  refine ⟨fun v => if v ∈ U then f v else m + g v, ?_, ?_⟩
  · intro v hv
    by_cases hvU : v ∈ U
    · simp only [hvU, if_true]
      have := f1 v hvU
      omega
    · simp only [hvU, if_false]
      have hvW : v ∈ W := by
        rcases Finset.mem_union.mp hv with h | h
        · exact absurd h hvU
        · exact h
      have := g1 v hvW
      omega
  · intro u hu v hv hadj
    by_cases huU : u ∈ U <;> by_cases hvU : v ∈ U
    · simp only [huU, hvU, if_true]
      exact f2 u huU v hvU hadj
    · simp only [huU, hvU, if_true, if_false]
      have := f1 u huU
      omega
    · simp only [huU, hvU, if_true, if_false]
      have := f1 v hvU
      omega
    · simp only [huU, hvU, if_false]
      have huW : u ∈ W := by
        rcases Finset.mem_union.mp hu with h | h
        · exact absurd h huU
        · exact h
      have hvW : v ∈ W := by
        rcases Finset.mem_union.mp hv with h | h
        · exact absurd h hvU
        · exact h
      have := g2 u huW v hvW hadj
      omega

theorem PC.biUnion {ι : Type*} {G : SimpleGraph V} (I : Finset ι) (S : ι → Finset V) (n : ℕ)
    (h : ∀ i ∈ I, PC G (S i) n) : PC G (I.biUnion S) (I.card * n) := by
  induction I using Finset.induction_on with
  | empty => simpa using PC.empty G 0
  | insert a I ha ih =>
    rw [Finset.biUnion_insert, Finset.card_insert_of_notMem ha]
    have h1 := h a (Finset.mem_insert_self a I)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have := PC.union h1 h2
    have e : (I.card + 1) * n = n + I.card * n := by ring
    rw [e]
    exact this

/-- greedy colouring of a degenerate finset -/
theorem PC_of_degenerate (G : SimpleGraph V) (m : ℕ) (U : Finset V)
    (hU : ∀ S ⊆ U, S.Nonempty → ∃ v ∈ S, dg G S v < m) : PC G U m := by
  induction U using Finset.strongInduction with
  | H U ih =>
    rcases U.eq_empty_or_nonempty with rfl | hne
    · exact PC.empty G m
    · obtain ⟨v, hvU, hv⟩ := hU U (Finset.Subset.refl _) hne
      obtain ⟨f, hf1, hf2⟩ := ih (U.erase v) (Finset.erase_ssubset hvU)
        (fun S hS hSne => hU S (hS.trans (Finset.erase_subset _ _)) hSne)
      have hex : ∃ j ∈ Finset.range m, j ∉ (U.filter (fun x => G.Adj v x)).image f := by
        by_contra hcon
        push Not at hcon
        have h1 : Finset.range m ⊆ (U.filter (fun x => G.Adj v x)).image f := hcon
        have h2 := Finset.card_le_card h1
        have h3 := Finset.card_image_le (s := U.filter (fun x => G.Adj v x)) (f := f)
        rw [Finset.card_range] at h2
        unfold dg at hv
        omega
      obtain ⟨j, hj, hjn⟩ := hex
      rw [Finset.mem_range] at hj
      have hjn' : ∀ x ∈ U, G.Adj v x → f x ≠ j := by
        intro x hx hadj e
        exact hjn (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hadj⟩, e⟩)
      refine ⟨Function.update f v j, ?_, ?_⟩
      · intro x hx
        by_cases hxv : x = v
        · subst hxv; simpa using hj
        · rw [Function.update_of_ne hxv]
          exact hf1 x (Finset.mem_erase.mpr ⟨hxv, hx⟩)
      · intro x hx y hy hadj
        by_cases hxv : x = v
        · subst hxv
          have hyx : y ≠ x := fun e => G.irrefl (e ▸ hadj)
          rw [Function.update_self, Function.update_of_ne hyx]
          exact fun e => hjn' y hy hadj e.symm
        · by_cases hyv : y = v
          · subst hyv
            rw [Function.update_self, Function.update_of_ne hxv]
            exact hjn' x hx hadj.symm
          · rw [Function.update_of_ne hxv, Function.update_of_ne hyv]
            exact hf2 x (Finset.mem_erase.mpr ⟨hxv, hx⟩) y (Finset.mem_erase.mpr ⟨hyv, hy⟩) hadj


/- ### rocks: minimal dense subsets -/

theorem exists_rock (G : SimpleGraph V) (q : ℕ) (U : Finset V)
    (h : ∃ S ⊆ U, S.Nonempty ∧ 2 * q * S.card ≤ ed G S) :
    ∃ A ⊆ U, A.Nonempty ∧ 2 * q * A.card ≤ ed G A ∧
      (∀ S ⊆ U, S.Nonempty → 2 * q * S.card ≤ ed G S → A.card ≤ S.card) ∧
      (∀ S ⊆ U, S.card = A.card → ed G S ≤ ed G A) := by
  obtain ⟨S0, hS0U, hS0ne, hS0⟩ := h
  let F : Finset (Finset V) :=
    U.powerset.filter (fun S => S.Nonempty ∧ 2 * q * S.card ≤ ed G S)
  have hF : F.Nonempty :=
    ⟨S0, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS0U, hS0ne, hS0⟩⟩
  obtain ⟨A0, hA0F, hA0min⟩ := Finset.exists_min_image F Finset.card hF
  let F' : Finset (Finset V) := F.filter (fun S => S.card = A0.card)
  have hF' : F'.Nonempty := ⟨A0, Finset.mem_filter.mpr ⟨hA0F, rfl⟩⟩
  obtain ⟨A, hAF', hAmax⟩ := Finset.exists_max_image F' (ed G) hF'
  obtain ⟨hAF, hAcard⟩ := Finset.mem_filter.mp hAF'
  obtain ⟨hAU, hAne, hAd⟩ := Finset.mem_filter.mp hAF
  rw [Finset.mem_powerset] at hAU
  refine ⟨A, hAU, hAne, hAd, ?_, ?_⟩
  · intro S hSU hSne hSd
    rw [hAcard]
    exact hA0min S (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSU, hSne, hSd⟩)
  · intro S hSU hScard
    by_contra hcon
    push Not at hcon
    have hSne : S.Nonempty := by
      rw [← Finset.card_pos, hScard]; exact Finset.card_pos.mpr hAne
    have hSd : 2 * q * S.card ≤ ed G S := by rw [hScard]; omega
    have hSF' : S ∈ F' :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSU, hSne, hSd⟩,
        by rw [hScard, hAcard]⟩
    have := hAmax S hSF'
    omega

theorem rock_erase (G : SimpleGraph V) (q : ℕ) (hq : 1 ≤ q) (U A : Finset V) (hAU : A ⊆ U)
    (hAd : 2 * q * A.card ≤ ed G A)
    (hmin : ∀ S ⊆ U, S.Nonempty → 2 * q * S.card ≤ ed G S → A.card ≤ S.card)
    (u : V) (hu : u ∈ A) : ed G A + 2 * q < 2 * q * A.card + 2 * dg G A u := by
  have he := ed_erase G A u hu
  have hc := Finset.card_erase_of_mem hu
  have hpos : 0 < A.card := Finset.card_pos.mpr ⟨u, hu⟩
  obtain ⟨n, hn⟩ : ∃ n, A.card = n + 1 := ⟨A.card - 1, by omega⟩
  have e : 2 * q * (n + 1) = 2 * q * n + 2 * q := by ring
  rw [hn] at hc hAd ⊢
  rw [e] at hAd ⊢
  rcases (A.erase u).eq_empty_or_nonempty with hE | hne
  · rw [hE] at hc
    have hn0 : n = 0 := by simpa using hc.symm
    have hd := dg_lt_card G A u hu
    have hE0 : ed G (∅ : Finset V) = 0 := by simp [ed]
    rw [hE, hE0] at he
    rw [hn, hn0] at hd
    subst hn0
    omega
  · have hlt : ¬ (2 * q * (A.erase u).card ≤ ed G (A.erase u)) := by
      intro hle
      have := hmin (A.erase u) ((Finset.erase_subset _ _).trans hAU) hne hle
      omega
    rw [hc] at hlt
    simp only [Nat.add_sub_cancel] at hlt
    omega

theorem rock_deg (G : SimpleGraph V) (q : ℕ) (hq : 1 ≤ q) (U A : Finset V) (hAU : A ⊆ U)
    (hAd : 2 * q * A.card ≤ ed G A)
    (hmin : ∀ S ⊆ U, S.Nonempty → 2 * q * S.card ≤ ed G S → A.card ≤ S.card)
    (u : V) (hu : u ∈ A) : q < dg G A u := by
  have := rock_erase G q hq U A hAU hAd hmin u hu
  omega

theorem rock_min_deg (G : SimpleGraph V) (q : ℕ) (hq : 1 ≤ q) (U A : Finset V) (hAU : A ⊆ U)
    (hAne : A.Nonempty) (hAd : 2 * q * A.card ≤ ed G A)
    (hmin : ∀ S ⊆ U, S.Nonempty → 2 * q * S.card ≤ ed G S → A.card ≤ S.card) :
    ∃ u ∈ A, dg G A u ≤ 2 * q := by
  obtain ⟨u0, hu0, hu0min⟩ := Finset.exists_min_image A (dg G A) hAne
  refine ⟨u0, hu0, ?_⟩
  by_contra hcon
  push Not at hcon
  have h1 := mul_card_le_ed G A (dg G A u0) hu0min
  have h2 := rock_erase G q hq U A hAU hAd hmin u0 hu0
  have h3 := dg_lt_card G A u0 hu0
  generalize dg G A u0 = δ at *
  generalize A.card = a at *
  generalize ed G A = E at *
  zify at *
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ δ - 2 * q by linarith) (show (0 : ℤ) ≤ a - δ - 1 by linarith),
    mul_nonneg (show (0 : ℤ) ≤ δ - 2 * q - 1 by linarith) (show (0 : ℤ) ≤ δ by linarith)]

theorem rock_out (G : SimpleGraph V) (U A : Finset V) (hAU : A ⊆ U)
    (hmax : ∀ S ⊆ U, S.card = A.card → ed G S ≤ ed G A)
    (v : V) (hvU : v ∈ U) (hvA : v ∉ A) (u : V) (hu : u ∈ A) :
    dg G A v ≤ dg G A u + 1 := by
  have hv' : v ∉ A.erase u := fun h => hvA (Finset.mem_of_mem_erase h)
  have hS : insert v (A.erase u) ⊆ U := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hvU
    · exact hAU (Finset.mem_of_mem_erase hx)
  have hpos : 0 < A.card := Finset.card_pos.mpr ⟨u, hu⟩
  have hcard : (insert v (A.erase u)).card = A.card := by
    rw [Finset.card_insert_of_notMem hv', Finset.card_erase_of_mem hu]
    omega
  have h1 := hmax _ hS hcard
  rw [ed_insert G _ v hv', ed_erase G A u hu] at h1
  have h2 : dg G A v ≤ dg G (A.erase u) v + 1 := by
    have e : dg G A v = dg G (insert u (A.erase u)) v := by rw [Finset.insert_erase hu]
    rw [e, dg_insert G (A.erase u) u v (Finset.notMem_erase u A)]
    split_ifs <;> omega
  omega

theorem ed_sdiff (G : SimpleGraph V) (A : Finset V) (R : Finset V) (hR : R ⊆ A) :
    ed G A ≤ ed G (A \ R) + 2 * ∑ v ∈ R, dg G A v := by
  induction R using Finset.induction_on with
  | empty => simp
  | insert v R hv ih =>
    have hvA : v ∈ A := hR (Finset.mem_insert_self v R)
    have hRA : R ⊆ A := (Finset.subset_insert v R).trans hR
    have h1 := ih hRA
    have hmem : v ∈ A \ R := Finset.mem_sdiff.mpr ⟨hvA, hv⟩
    have h2 := ed_erase G (A \ R) v hmem
    have h3 : dg G (A \ R) v ≤ dg G A v := dg_mono G Finset.sdiff_subset v
    rw [Finset.sdiff_insert, Finset.sum_insert hv]
    omega

/- ### greedy bins -/

theorem bins (w : V → ℕ) (θ : ℕ) (s : Finset V) (hw : ∀ v ∈ s, w v ≤ θ) :
    ∃ (f : V → ℕ) (N : ℕ), (∀ v ∈ s, f v ≤ N) ∧
      (∀ j, ∑ v ∈ s, (if f v = j then w v else 0) ≤ 2 * θ) ∧
      N * (θ + 1) + ∑ v ∈ s, (if f v = N then w v else 0) ≤ ∑ v ∈ s, w v := by
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, 0, by simp, by simp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨f, N, h1, h2, h3⟩ := ih (fun v hv => hw v (Finset.mem_insert_of_mem hv))
    have hwa : w a ≤ θ := hw a (Finset.mem_insert_self a s)
    have key : ∀ (c j : ℕ), ∑ v ∈ s, (if Function.update f a c v = j then w v else 0)
        = ∑ v ∈ s, (if f v = j then w v else 0) := by
      intro c j
      apply Finset.sum_congr rfl
      intro v hv
      have : v ≠ a := fun e => ha (e ▸ hv)
      rw [Function.update_of_ne this]
    by_cases hL : ∑ v ∈ s, (if f v = N then w v else 0) ≤ θ
    · refine ⟨Function.update f a N, N, ?_, ?_, ?_⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · simp
        · have : v ≠ a := fun e => ha (e ▸ hv)
          rw [Function.update_of_ne this]; exact h1 v hv
      · intro j
        rw [Finset.sum_insert ha, key, Function.update_self]
        by_cases hj : N = j
        · subst hj; simp only [if_true]; omega
        · simp only [hj, if_false]; have := h2 j; omega
      · rw [Finset.sum_insert ha, key, Function.update_self, Finset.sum_insert ha]
        simp only [if_true]; omega
    · push Not at hL
      have hz : ∑ v ∈ s, (if f v = N + 1 then w v else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        have := h1 v hv
        have hne : f v ≠ N + 1 := by omega
        simp [hne]
      refine ⟨Function.update f a (N + 1), N + 1, ?_, ?_, ?_⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · simp
        · have : v ≠ a := fun e => ha (e ▸ hv)
          rw [Function.update_of_ne this]; have := h1 v hv; omega
      · intro j
        rw [Finset.sum_insert ha, key, Function.update_self]
        by_cases hj : N + 1 = j
        · subst hj; simp only [if_true]; omega
        · simp only [hj, if_false]; have := h2 j; omega
      · rw [Finset.sum_insert ha, key, Function.update_self, Finset.sum_insert ha]
        have e : (N + 1) * (θ + 1) = N * (θ + 1) + (θ + 1) := by ring
        simp only [if_true]
        omega


/- ### the main step -/

theorem main_step (G : SimpleGraph V) (c d' : ℕ) (hc : 1 ≤ c)
    (H : ∀ A B : Finset V, A.Nonempty → (∀ v ∈ A, c ≤ dg G A v) →
        (∀ a ∈ A, ∀ b ∈ B, a ≠ b ∧ ¬ G.Adj a b) → PC G B (c - 1))
    (U : Finset V) (hN : ∀ x ∈ U, PC G (U.filter (fun y => G.Adj x y)) d') :
    PC G U ((4 * c + 1) + (8 * (4 * c + 1)) * d' + 2 ^ (8 * (4 * c + 1)) * (c - 1)) := by
  have e4 : ∀ n : ℕ, 2 * (2 * c) * n = 4 * c * n := fun n => by ring
  by_cases hex : ∃ S ⊆ U, S.Nonempty ∧ 2 * (2 * c) * S.card ≤ ed G S
  swap
  · -- no dense subset at all: colour greedily
    have h4 : PC G U (4 * c) := by
      apply PC_of_degenerate
      intro S hSU hSne
      apply exists_dg_lt
      by_contra hcon
      push Not at hcon
      exact hex ⟨S, hSU, hSne, by rw [e4]; exact hcon⟩
    exact h4.mono_n (by omega)
  obtain ⟨A, hAU, hAne, hAd, hmin, hmax⟩ := exists_rock G (2 * c) U hex
  have hq : 1 ≤ 2 * c := by omega
  obtain ⟨u0, hu0, hu0d⟩ := rock_min_deg G (2 * c) hq U A hAU hAne hAd hmin
  -- vertices outside the rock have at most 4c+1 neighbours in it
  have hout : ∀ v ∈ U, v ∉ A → dg G A v ≤ 4 * c + 1 := by
    intro v hvU hvA
    have := rock_out G U A hAU hmax v hvU hvA u0 hu0
    omega
  -- the rock itself is (4c+1)-colourable
  have hA : PC G A (4 * c + 1) := by
    apply PC_of_degenerate
    intro S hSA hSne
    by_cases hSeq : S = A
    · subst hSeq; exact ⟨u0, hu0, by omega⟩
    · have hlt : S.card < A.card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hSA, hSeq⟩)
      have hnd : ed G S < 4 * c * S.card := by
        by_contra hcon
        push Not at hcon
        have := hmin S (hSA.trans hAU) hSne (by rw [e4]; exact hcon)
        omega
      obtain ⟨v, hv, hvd⟩ := exists_dg_lt G S (4 * c) hnd
      exact ⟨v, hv, by omega⟩
  -- parameters
  obtain ⟨r, hr⟩ : ∃ r, r = 4 * c + 1 := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = ed G A := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = E / (8 * r) := ⟨_, rfl⟩
  have hr0 : 0 < 8 * r := by omega
  have hθ1 : 8 * r * θ ≤ E := by rw [hθ]; exact Nat.mul_div_le E (8 * r)
  have hθ2 : E < 8 * r * (θ + 1) := by
    have := Nat.lt_div_mul_add (a := E) hr0
    rw [← hθ] at this
    have e : 8 * r * (θ + 1) = θ * (8 * r) + 8 * r := by ring
    omega
  rw [← hE] at hAd
  -- X: the vertices of large degree in the rock
  obtain ⟨X, hX⟩ : ∃ X, X = A.filter (fun v => θ < dg G A v) := ⟨_, rfl⟩
  have hXA : X ⊆ A := by rw [hX]; exact Finset.filter_subset _ _
  have hXcard : X.card < 8 * r := by
    have h1 : X.card * (θ + 1) ≤ ∑ v ∈ X, dg G A v := by
      have := Finset.card_nsmul_le_sum X (fun v => dg G A v) (θ + 1)
        (fun v hv => by rw [hX] at hv; exact (Finset.mem_filter.mp hv).2)
      simpa [mul_comm] using this
    have h2 : ∑ v ∈ X, dg G A v ≤ E := by
      rw [hE]; exact Finset.sum_le_sum_of_subset hXA
    by_contra hcon
    push Not at hcon
    have h3 := Nat.mul_le_mul_right (θ + 1) hcon
    omega
  -- bins on A \ X
  obtain ⟨f, N, hf1, hf2, hf3⟩ := bins (dg G A) θ (A \ X) (by
    intro v hv
    rw [Finset.mem_sdiff] at hv
    by_contra hcon
    push Not at hcon
    exact hv.2 (by rw [hX]; exact Finset.mem_filter.mpr ⟨hv.1, hcon⟩))
  have hN8 : N < 8 * r := by
    have h2 : ∑ v ∈ A \ X, dg G A v ≤ E := by
      rw [hE]; exact Finset.sum_le_sum_of_subset Finset.sdiff_subset
    by_contra hcon
    push Not at hcon
    have h3 := Nat.mul_le_mul_right (θ + 1) hcon
    omega
  -- neighbours of X
  obtain ⟨NX, hNX⟩ : ∃ NX, NX = X.biUnion (fun x => U.filter (fun y => G.Adj x y)) := ⟨_, rfl⟩
  have hNXc : PC G NX (X.card * d') := by
    rw [hNX]
    exact PC.biUnion X _ d' (fun x hx => hN x (hAU (hXA hx)))
  -- the remaining vertices
  obtain ⟨W, hW⟩ : ∃ W, W = (U \ A) \ NX := ⟨_, rfl⟩
  have hWmem : ∀ w ∈ W, w ∈ U ∧ w ∉ A ∧ ∀ x ∈ X, ¬ G.Adj x w := by
    intro w hw
    rw [hW, Finset.mem_sdiff, Finset.mem_sdiff] at hw
    refine ⟨hw.1.1, hw.1.2, fun x hx hadj => hw.2 ?_⟩
    rw [hNX]
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr ⟨hw.1.1, hadj⟩⟩
  have hWc : PC G W ((Finset.range (N + 1)).powerset.card * (c - 1)) := by
    have hcover : W ⊆ (Finset.range (N + 1)).powerset.biUnion
        (fun t => W.filter (fun w => (A.filter (fun x => G.Adj w x)).image f = t)) := by
      intro w hw
      rw [Finset.mem_biUnion]
      refine ⟨(A.filter (fun x => G.Adj w x)).image f, ?_, Finset.mem_filter.mpr ⟨hw, rfl⟩⟩
      rw [Finset.mem_powerset]
      intro j hj
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hj
      rw [Finset.mem_filter] at hx
      have hxX : x ∉ X := fun hxX => (hWmem w hw).2.2 x hxX hx.2.symm
      have := hf1 x (Finset.mem_sdiff.mpr ⟨hx.1, hxX⟩)
      rw [Finset.mem_range]; omega
    refine PC.mono_set hcover (PC.biUnion _ _ _ ?_)
    intro t _
    rcases (W.filter (fun w => (A.filter (fun x => G.Adj w x)).image f = t)).eq_empty_or_nonempty
      with he | ⟨w0, hw0⟩
    · rw [he]; exact PC.empty G _
    · rw [Finset.mem_filter] at hw0
      obtain ⟨hw0W, hw0t⟩ := hw0
      have htcard : t.card ≤ r := by
        rw [← hw0t]
        have h1 := Finset.card_image_le (s := A.filter (fun x => G.Adj w0 x)) (f := f)
        have h2 := hout w0 (hWmem w0 hw0W).1 (hWmem w0 hw0W).2.1
        unfold dg at h2
        omega
      -- the removed part
      obtain ⟨R, hR⟩ : ∃ R, R = (A \ X).filter (fun v => f v ∈ t) := ⟨_, rfl⟩
      have hRA : R ⊆ A := by
        rw [hR]; exact (Finset.filter_subset _ _).trans Finset.sdiff_subset
      have hvol : ∑ v ∈ R, dg G A v ≤ t.card * (2 * θ) := by
        rw [hR, Finset.sum_filter]
        have h1 : ∀ v ∈ A \ X, (if f v ∈ t then dg G A v else 0)
            = ∑ j ∈ t, (if f v = j then dg G A v else 0) := by
          intro v _
          rw [Finset.sum_ite_eq]
        rw [Finset.sum_congr rfl h1, Finset.sum_comm]
        have h2 := Finset.sum_le_card_nsmul t
          (fun j => ∑ v ∈ A \ X, (if f v = j then dg G A v else 0)) (2 * θ) (fun j _ => hf2 j)
        simpa using h2
      have hsd := ed_sdiff G A R hRA
      rw [← hE] at hsd
      have hvol2 : t.card * (2 * θ) ≤ r * (2 * θ) := Nat.mul_le_mul_right _ htcard
      have e1 : r * (2 * θ) = 2 * (r * θ) := by ring
      have e2 : 8 * r * θ = 8 * (r * θ) := by ring
      have hcardD : (A \ R).card ≤ A.card := Finset.card_le_card Finset.sdiff_subset
      have hmul : 2 * c * (A \ R).card ≤ 2 * c * A.card := Nat.mul_le_mul_left _ hcardD
      have e3 : 2 * (2 * c) * A.card = 2 * (2 * c * A.card) := by ring
      have hApos : 0 < A.card := Finset.card_pos.mpr hAne
      have hcA : 2 * c * 1 ≤ 2 * c * A.card := Nat.mul_le_mul_left _ hApos
      have hdense : 2 * c * (A \ R).card ≤ ed G (A \ R) := by omega
      have hDne : (A \ R).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        have hz : ed G (A \ R) = 0 := by rw [hemp]; simp [ed]
        omega
      obtain ⟨A', hA'D, hA'ne, hA'd, hmin', -⟩ :=
        exists_rock G c (A \ R) ⟨A \ R, Finset.Subset.refl _, hDne, hdense⟩
      apply H A' _ hA'ne
      · intro u hu
        exact le_of_lt (rock_deg G c hc (A \ R) A' hA'D hA'd hmin' u hu)
      · intro a ha b hb
        rw [Finset.mem_filter] at hb
        obtain ⟨hbW, hbt⟩ := hb
        have haD := hA'D ha
        rw [Finset.mem_sdiff] at haD
        refine ⟨fun e => (hWmem b hbW).2.1 (e ▸ haD.1), fun hadj => haD.2 ?_⟩
        have haX : a ∉ X := fun haX => (hWmem b hbW).2.2 a haX hadj
        rw [hR, Finset.mem_filter]
        refine ⟨Finset.mem_sdiff.mpr ⟨haD.1, haX⟩, ?_⟩
        rw [← hbt]
        exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨haD.1, hadj.symm⟩, rfl⟩
  -- assemble
  have hcov : U ⊆ A ∪ NX ∪ W := by
    intro v hv
    by_cases h1 : v ∈ A
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ h1)
    · by_cases h2 : v ∈ NX
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h2)
      · refine Finset.mem_union_right _ ?_
        rw [hW]
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hv, h1⟩, h2⟩
  have hfin := PC.mono_set hcov ((hA.union hNXc).union hWc)
  refine hfin.mono_n ?_
  rw [Finset.card_powerset, Finset.card_range]
  have b1 : X.card * d' ≤ 8 * r * d' := Nat.mul_le_mul_right _ (le_of_lt hXcard)
  have b2 : 2 ^ (N + 1) ≤ 2 ^ (8 * r) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have b3 : 2 ^ (N + 1) * (c - 1) ≤ 2 ^ (8 * r) * (c - 1) := Nat.mul_le_mul_right _ b2
  rw [← hr]
  omega


/- ### induction on the clique bound -/

theorem key (c : ℕ) (hc : 1 ≤ c) (t : ℕ) : ∃ d : ℕ, ∀ (V : Type*) (G : SimpleGraph V),
    (∀ A B : Finset V, A.Nonempty → (∀ v ∈ A, c ≤ dg G A v) →
        (∀ a ∈ A, ∀ b ∈ B, a ≠ b ∧ ¬ G.Adj a b) → PC G B (c - 1)) →
    ∀ U : Finset V, (∀ s ⊆ U, ¬ G.IsNClique t s) → PC G U d := by
  induction t with
  | zero =>
    refine ⟨0, fun V G _ U hU => ?_⟩
    exact absurd (SimpleGraph.isNClique_zero.mpr rfl) (hU ∅ (Finset.empty_subset _))
  | succ t ih =>
    obtain ⟨d', hd'⟩ := ih
    refine ⟨(4 * c + 1) + (8 * (4 * c + 1)) * d' + 2 ^ (8 * (4 * c + 1)) * (c - 1),
      fun V G H U hU => ?_⟩
    apply main_step G c d' hc H U
    intro x hx
    apply hd' V G H
    intro s hs hcl
    have hins : G.IsNClique (t + 1) (insert x s) :=
      hcl.insert (fun b hb => (Finset.mem_filter.mp (hs hb)).2)
    refine hU (insert x s) ?_ hins
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hx
    · exact (Finset.mem_filter.mp (hs hy)).1

/- ### translation to and from Mathlib colourings -/

theorem PC_of_colorable_induce (G : SimpleGraph V) (B : Finset V) (n : ℕ)
    (h : (G.induce (B : Set V)).Colorable n) : PC G B n := by
  obtain ⟨C⟩ := h
  refine ⟨fun v => if hv : v ∈ B then (C ⟨v, hv⟩ : ℕ) else 0, ?_, ?_⟩
  · intro v hv
    simp only [hv, dif_pos]
    exact (C ⟨v, hv⟩).isLt
  · intro u hu v hv hadj
    simp only [hu, hv, dif_pos]
    have hadj' : (G.induce (B : Set V)).Adj ⟨u, hu⟩ ⟨v, hv⟩ := hadj
    have hne := C.valid hadj'
    exact fun e => hne (Fin.ext e)

theorem colorable_of_PC_univ [Fintype V] (G : SimpleGraph V) (n : ℕ)
    (h : PC G Finset.univ n) : G.Colorable n := by
  obtain ⟨f, h1, h2⟩ := h
  exact ⟨SimpleGraph.Coloring.mk (fun v => (⟨f v, h1 v (Finset.mem_univ v)⟩ : Fin n))
    (fun {u v} hadj e =>
      h2 u (Finset.mem_univ u) v (Finset.mem_univ v) hadj (congrArg Fin.val e))⟩

theorem ncard_inter_neighborSet (G : SimpleGraph V) (A : Finset V) (v : V) :
    ((A : Set V) ∩ G.neighborSet v).ncard = dg G A v := by
  have e : ((A : Set V) ∩ G.neighborSet v)
      = ((A.filter (fun x => G.Adj v x) : Finset V) : Set V) := by
    ext x; simp
  rw [e, Set.ncard_coe_finset]
  rfl

end OMA.Helpers

theorem OMA.solution : type_of% @Erdos1111.erdos_1111.variants.nguyen_scott_seymour := by
  intro t c _ hc
  obtain ⟨d, hd⟩ := OMA.Helpers.key c hc t
  refine ⟨d + 1, by omega, ?_⟩
  intro V _ G hchi hfree
  by_contra hno
  have hfin : Fintype V := Fintype.ofFinite V
  have H : ∀ A B : Finset V, A.Nonempty → (∀ v ∈ A, c ≤ OMA.Helpers.dg G A v) →
      (∀ a ∈ A, ∀ b ∈ B, a ≠ b ∧ ¬ G.Adj a b) → OMA.Helpers.PC G B (c - 1) := by
    intro A B hA hdeg hanti
    by_contra hB
    apply hno
    have hAB : Erdos1111.Anticomplete G (A : Set V) (B : Set V) := by
      unfold Erdos1111.Anticomplete
      refine ⟨?_, fun a ha b hb => (hanti a ha b hb).2⟩
      rw [Set.disjoint_left]
      intro a ha hb
      exact (hanti a ha a hb).1 rfl
    refine ⟨(A : Set V), (B : Set V), hAB, ?_, ?_, ?_⟩
    · exact Finset.coe_nonempty.mpr hA
    · intro v hv
      rw [OMA.Helpers.ncard_inter_neighborSet]
      exact hdeg v hv
    · by_contra hlt
      apply hB
      rw [not_le] at hlt
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      have hle : (G.induce (B : Set V)).chromaticNumber ≤ (c' : ℕ∞) := by
        rw [Nat.cast_add, Nat.cast_one] at hlt
        exact (ENat.lt_add_one_iff (ENat.natCast_ne_top c')).mp hlt
      have hcol := SimpleGraph.chromaticNumber_le_iff_colorable.mp hle
      simpa using OMA.Helpers.PC_of_colorable_induce G B c' hcol
  have hU := hd V G H Finset.univ (fun s _ => hfree s)
  have hcol : G.Colorable d := OMA.Helpers.colorable_of_PC_univ G d hU
  have h1 := SimpleGraph.Colorable.chromaticNumber_le hcol
  have h2 := le_trans hchi h1
  rw [Nat.cast_le] at h2
  omega

