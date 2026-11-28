import FormalConjectures.Wikipedia.ReconstructionConjecture
import Mathlib

namespace OMA.Helpers

/-- list encoding -/
def encL : List ℕ → ℕ
  | [] => 0
  | a :: l => Nat.pair a (encL l) + 1

def decL : ℕ → List ℕ
  | 0 => []
  | k + 1 => (Nat.unpair k).1 :: decL (Nat.unpair k).2
termination_by k => k
decreasing_by exact Nat.lt_succ_of_le (Nat.unpair_right_le k)

theorem decL_encL : ∀ l, decL (encL l) = l
  | [] => by simp [encL, decL]
  | a :: l => by
    rw [encL, decL]
    simp [Nat.unpair_pair, decL_encL l]

theorem encL_decL : ∀ k, encL (decL k) = k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero => simp [decL, encL]
    | succ k =>
      rw [decL, encL, ih _ (Nat.lt_succ_of_le (Nat.unpair_right_le k))]
      simp [Nat.pair_unpair]

/-- sum bound: every element of the raised list is below the code -/
theorem lt_encL_lower : ∀ (l : List ℕ) (n : ℕ), (n :: l).SortedLE →
    ∀ a ∈ l, a < encL (Denumerable.lower l n) + n
  | [], _, _ => by simp
  | m :: l, n, h => by
    intro a ha
    have hnm : n ≤ m := List.rel_of_pairwise_cons h.pairwise List.mem_cons_self
    have hs : (m :: l).SortedLE := h.pairwise.of_cons.sortedLE
    have ih := lt_encL_lower l m hs
    simp only [Denumerable.lower, encL]
    have hp : (m - n) + encL (Denumerable.lower l m) ≤ Nat.pair (m - n) (encL (Denumerable.lower l m)) :=
      Nat.add_le_pair _ _
    rcases List.mem_cons.1 ha with rfl | ha
    · omega
    · have := ih a ha
      omega

def enc (M : Multiset ℕ) : ℕ := encL (Denumerable.lower (M.sort (· ≤ ·)) 0)

def dec (t : ℕ) : Multiset ℕ := (Denumerable.raise (decL t) 0 : List ℕ)

theorem dec_enc (M : Multiset ℕ) : dec (enc M) = M := by
  unfold dec enc
  rw [decL_encL]
  have := Denumerable.raise_lower (List.pairwise_cons.2 ⟨fun n _ => Nat.zero_le n,
        M.pairwise_sort _⟩).sortedLE
  rw [this, Multiset.sort_eq]

theorem enc_dec (t : ℕ) : enc (dec t) = t := by
  unfold dec enc
  have h1 : Multiset.sort (↑(Denumerable.raise (decL t) 0) : Multiset ℕ) (· ≤ ·)
      = Denumerable.raise (decL t) 0 := by
    rw [Multiset.coe_sort]
    exact List.mergeSort_eq_self _ (Denumerable.raise_sorted _ _).pairwise
  rw [h1, Denumerable.lower_raise, encL_decL]

theorem lt_enc_of_mem {M : Multiset ℕ} {a : ℕ} (ha : a ∈ M) : a < enc M := by
  have h := lt_encL_lower (M.sort (· ≤ ·)) 0
    (List.pairwise_cons.2 ⟨fun n _ => Nat.zero_le n, M.pairwise_sort _⟩).sortedLE a
    ((Multiset.mem_sort _).2 ha)
  unfold enc
  omega

theorem mem_dec_lt {t a : ℕ} (ha : a ∈ dec t) : a < t := by
  have := lt_enc_of_mem ha
  rwa [enc_dec] at this

theorem enc_injective : Function.Injective enc := fun a b h => by
  have := congrArg dec h
  rwa [dec_enc, dec_enc] at this

/-- size of a code -/
def sz (t : ℕ) : ℕ := 1 + ((dec t).attach.map (fun a => sz a.1)).sum
termination_by t
decreasing_by exact mem_dec_lt a.2

theorem sz_eq (t : ℕ) : sz t = 1 + ((dec t).map sz).sum := by
  rw [sz]
  congr 1
  conv_rhs => rw [← Multiset.attach_map_val (dec t)]
  rw [Multiset.map_map]
  rfl

theorem sz_enc (M : Multiset ℕ) : sz (enc M) = 1 + (M.map sz).sum := by
  rw [sz_eq, dec_enc]

theorem sz_pos (t : ℕ) : 0 < sz t := by rw [sz_eq]; omega

/-- one-leaf deletion relation on codes -/
inductive Del : ℕ → ℕ → Prop
  | here (M : Multiset ℕ) (h : enc 0 ∈ M) : Del (enc M) (enc (M.erase (enc 0)))
  | there (M : Multiset ℕ) (a c : ℕ) (ha : a ∈ M) (h : Del a c) :
      Del (enc M) (enc (c ::ₘ M.erase a))

theorem del_enc_iff (M : Multiset ℕ) (c : ℕ) :
    Del (enc M) c ↔ (enc 0 ∈ M ∧ c = enc (M.erase (enc 0))) ∨
      ∃ a ∈ M, ∃ c0, Del a c0 ∧ c = enc (c0 ::ₘ M.erase a) := by
  constructor
  · intro h
    generalize ht : enc M = t at h
    cases h with
    | here M' h' =>
      have := enc_injective ht; subst this
      exact Or.inl ⟨h', rfl⟩
    | there M' a c0 ha h' =>
      have := enc_injective ht; subst this
      exact Or.inr ⟨a, ha, c0, h', rfl⟩
  · rintro (⟨h, rfl⟩ | ⟨a, ha, c0, h, rfl⟩)
    · exact Del.here M h
    · exact Del.there M a c0 ha h

theorem sz_del {t c : ℕ} (h : Del t c) : sz t = sz c + 1 := by
  induction h with
  | here M h =>
    rw [sz_enc, sz_enc]
    have : (M.map sz) = sz (enc 0) ::ₘ ((M.erase (enc 0)).map sz) := by
      rw [← Multiset.map_cons, Multiset.cons_erase h]
    rw [this, Multiset.sum_cons, sz_enc]
    simp
    omega
  | there M a c ha h ih =>
    rw [sz_enc, sz_enc, Multiset.map_cons, Multiset.sum_cons]
    have : (M.map sz) = sz a ::ₘ ((M.erase a).map sz) := by
      rw [← Multiset.map_cons, Multiset.cons_erase ha]
    rw [this, Multiset.sum_cons, ih]
    omega


def pt : ℕ := enc 0

theorem dec_pt : dec pt = 0 := dec_enc 0

theorem enc_eq_iff {M : Multiset ℕ} {t : ℕ} : enc M = t ↔ M = dec t := by
  constructor
  · rintro rfl; exact (dec_enc M).symm
  · rintro rfl; exact enc_dec t

theorem eq_pt_of_dec {t : ℕ} (h : dec t = 0) : t = pt := by
  rw [← enc_dec t, h]; rfl

theorem sz_eq_one_iff {t : ℕ} : sz t = 1 ↔ t = pt := by
  constructor
  · intro h
    apply eq_pt_of_dec
    rw [sz_eq] at h
    by_contra hne
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
    have h1 : sz a ≤ ((dec t).map sz).sum :=
      Multiset.le_sum_of_mem (Multiset.mem_map_of_mem sz ha)
    have := sz_pos a
    omega
  · rintro rfl
    rw [sz_eq, dec_pt]; simp

theorem not_del_pt {c : ℕ} : ¬ Del pt c := by
  intro h
  have := sz_del h
  have h1 : sz pt = 1 := sz_eq_one_iff.2 rfl
  have := sz_pos c
  omega

theorem exists_del : ∀ t : ℕ, t ≠ pt → ∃ c, Del t c := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro hne
    have hd : dec t ≠ 0 := fun h => hne (eq_pt_of_dec h)
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hd
    by_cases hpt : pt ∈ dec t
    · exact ⟨_, by have := Del.here (dec t) hpt; rwa [enc_dec] at this⟩
    · have hane : a ≠ pt := fun h => hpt (h ▸ ha)
      obtain ⟨c, hc⟩ := ih a (mem_dec_lt ha) hane
      exact ⟨_, by have := Del.there (dec t) a c ha hc; rwa [enc_dec] at this⟩

/-- if a child has all but one of the vertices, it is the only child -/
theorem dec_eq_singleton {t c : ℕ} (hc : c ∈ dec t) (hs : sz c + 1 = sz t) : dec t = {c} := by
  obtain ⟨r, hr⟩ := Multiset.exists_cons_of_mem hc
  rw [sz_eq t, hr, Multiset.map_cons, Multiset.sum_cons] at hs
  have hr0 : r = 0 := by
    by_contra hne
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
    have h1 : sz a ≤ (r.map sz).sum := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem sz ha)
    have := sz_pos a
    omega
  rw [hr, hr0]; rfl

theorem del_single_iff {z c : ℕ} (hz : z ≠ pt) :
    Del (enc {z}) c ↔ ∃ c0, Del z c0 ∧ c = enc {c0} := by
  rw [del_enc_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨a, ha, c0, hdel, rfl⟩)
    · exact absurd (Multiset.mem_singleton.1 h).symm hz
    · have : a = z := Multiset.mem_singleton.1 ha
      subst this
      exact ⟨c0, hdel, by simp⟩
  · rintro ⟨c0, hdel, rfl⟩
    exact Or.inr ⟨z, Multiset.mem_singleton_self z, c0, hdel, by simp⟩

/-- code of the rooted path with `k+1` vertices -/
def pathc : ℕ → ℕ
  | 0 => pt
  | k + 1 => enc {pathc k}

theorem path_lemma : ∀ n t : ℕ, sz t = n + 1 → (∀ c, Del (enc {t}) c → c = t) → t = pathc n := by
  intro n
  induction n with
  | zero => intro t ht _; exact sz_eq_one_iff.1 ht
  | succ n ih =>
    intro t ht hall
    have hne : t ≠ pt := fun h => by rw [h, sz_eq_one_iff.2 rfl] at ht; omega
    obtain ⟨c0, hc0⟩ := exists_del t hne
    have h1 : enc {c0} = t := hall _ ((del_single_iff hne).2 ⟨c0, hc0, rfl⟩)
    have hsz : sz c0 = n + 1 := by have := sz_del hc0; omega
    have hc0' : c0 = pathc n := by
      apply ih c0 hsz
      intro c hc
      rw [h1] at hc
      have := hall _ ((del_single_iff hne).2 ⟨c, hc, rfl⟩)
      rw [← h1] at this
      have := enc_injective this
      simpa using this
    rw [← h1, hc0']; rfl


theorem cons_dich {c c' : ℕ} {A A' : Multiset ℕ} (h : c ::ₘ A = c' ::ₘ A') :
    (c = c' ∧ A = A') ∨ (c ≠ c' ∧ c ∈ A' ∧ c' ∈ A) := by
  rcases Multiset.cons_eq_cons.1 h with ⟨h1, h2⟩ | ⟨hne, cs, h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · refine Or.inr ⟨hne, ?_, ?_⟩
    · rw [h2]; exact Multiset.mem_cons_self _ _
    · rw [h1]; exact Multiset.mem_cons_self _ _

theorem rel_cases {m xi xo yj yo c c' : ℕ} (hxi : sz xi = m) (hxo : sz xo = m)
    (hyj : sz yj = m) (hyo : sz yo = m) (hc : Del xi c) (hc' : Del yj c')
    (h : c ::ₘ dec xo = c' ::ₘ dec yo) :
    (dec xo).card = (dec yo).card ∧
    ((c = c' ∧ xo = yo) ∨ (c ≠ c' ∧ dec yo = {c} ∧ dec xo = {c'})) := by
  refine ⟨by simpa using congrArg Multiset.card h, ?_⟩
  rcases cons_dich h with ⟨h1, h2⟩ | ⟨hne, h1, h2⟩
  · left; refine ⟨h1, ?_⟩; rw [← enc_dec xo, ← enc_dec yo, h2]
  · right
    have s1 := sz_del hc
    have s2 := sz_del hc'
    exact ⟨hne, dec_eq_singleton h1 (by omega), dec_eq_singleton h2 (by omega)⟩

theorem pair_single {c c' z z' : ℕ} (h : c ::ₘ ({z} : Multiset ℕ) = c' ::ₘ {z'}) :
    (c = c' ∧ z = z') ∨ (c = z' ∧ z = c') := by
  rcases Multiset.cons_eq_cons.1 h with ⟨h1, h2⟩ | ⟨_, cs, h1, h2⟩
  · exact Or.inl ⟨h1, by simpa using h2⟩
  · have hz : c' ∈ ({z} : Multiset ℕ) := by rw [h1]; exact Multiset.mem_cons_self _ _
    have hz' : c ∈ ({z'} : Multiset ℕ) := by rw [h2]; exact Multiset.mem_cons_self _ _
    exact Or.inr ⟨Multiset.mem_singleton.1 hz', (Multiset.mem_singleton.1 hz).symm⟩

theorem lemB_b (m : ℕ) (x y : Bool → ℕ) (hx : ∀ i, sz (x i) = m) (hy : ∀ j, sz (y j) = m)
    (hxne : ∀ i, x i ≠ pt)
    (hG : ∀ i c, Del (x i) c → ∃ j c', Del (y j) c' ∧ c ::ₘ dec (x (!i)) = c' ::ₘ dec (y (!j)))
    (hH : ∀ j c', Del (y j) c' → ∃ i c, Del (x i) c ∧ c ::ₘ dec (x (!i)) = c' ::ₘ dec (y (!j)))
    (a : Bool) (ha : (dec (x a)).card ≠ 1) (hb : (dec (x (!a))).card = 1) :
    ∃ J : Bool, x a = y J ∧ x (!a) = y (!J) := by
  obtain ⟨c, hc⟩ := exists_del _ (hxne (!a))
  obtain ⟨j, c', hc', E⟩ := hG (!a) c hc
  rw [Bool.not_not] at E
  obtain ⟨hcard, hcase⟩ := rel_cases (hx (!a)) (hx a) (hy j) (hy (!j)) hc hc' E
  have hxa : x a = y (!j) := by
    rcases hcase with ⟨_, h⟩ | ⟨_, _, h⟩
    · exact h
    · exact absurd (by rw [h]; rfl) ha
  refine ⟨!j, hxa, ?_⟩
  have hJ : (dec (y (!j))).card ≠ 1 := by rw [← hcard]; exact ha
  -- the other y has a single child
  obtain ⟨c2, hc2⟩ := exists_del _ (hxne a)
  have hother : ∀ j1 : Bool, (dec (y (!j1))).card = 1 → (!j1) = (!(!j)) := by
    intro j1 h1
    cases j1 <;> cases j <;> simp_all
  obtain ⟨j2, c2', hc2', E2⟩ := hG a c2 hc2
  have hcard2 := (rel_cases (hx a) (hx (!a)) (hy j2) (hy (!j2)) hc2 hc2' E2).1
  have hJ' : (dec (y (!(!j)))).card = 1 := by
    rw [← hother j2 (by rw [← hcard2]; exact hb)]; rw [← hcard2]; exact hb
  obtain ⟨z, hz⟩ := Multiset.card_eq_one.1 hb
  obtain ⟨z', hz'⟩ := Multiset.card_eq_one.1 hJ'
  by_cases hzz : z = z'
  · rw [← enc_dec (x (!a)), ← enc_dec (y (!(!j))), hz, hz', hzz]
  · exfalso
    have claimG : ∀ c, Del (x a) c → c = z' := by
      intro c1 hc1
      obtain ⟨j1, c1', hc1', E1⟩ := hG a c1 hc1
      have hcard1 := (rel_cases (hx a) (hx (!a)) (hy j1) (hy (!j1)) hc1 hc1' E1).1
      have hj1 := hother j1 (by rw [← hcard1]; exact hb)
      rw [hj1, hz, hz'] at E1
      rcases pair_single E1 with ⟨_, h⟩ | ⟨h, _⟩
      · exact absurd h hzz
      · exact h
    have claimH : ∀ c', Del (y (!j)) c' → c' = z := by
      intro c1' hc1'
      obtain ⟨i, c1, hc1, E1⟩ := hH (!j) c1' hc1'
      have hcard1 := (rel_cases (hx i) (hx (!i)) (hy (!j)) (hy (!(!j))) hc1 hc1' E1).1
      have hi : (!i) = (!a) := by
        have h1 : (dec (x (!i))).card = 1 := by rw [hcard1]; exact hJ'
        cases i <;> cases a <;> simp_all
      rw [hi, hz, hz'] at E1
      rcases pair_single E1 with ⟨_, h⟩ | ⟨_, h⟩
      · exact absurd h hzz
      · exact h.symm
    have e1 := claimG c2 hc2
    rw [hxa] at hc2
    have e2 := claimH c2 hc2
    exact hzz (e2.symm.trans e1)


theorem lemB : ∀ m : ℕ, ∀ x y : Bool → ℕ, (∀ i, sz (x i) = m) → (∀ j, sz (y j) = m) →
    (∀ i c, Del (x i) c → ∃ j c', Del (y j) c' ∧ c ::ₘ dec (x (!i)) = c' ::ₘ dec (y (!j))) →
    (∀ j c', Del (y j) c' → ∃ i c, Del (x i) c ∧ c ::ₘ dec (x (!i)) = c' ::ₘ dec (y (!j))) →
    (x true = y true ∧ x false = y false) ∨ (x true = y false ∧ x false = y true) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro x y hx hy hG hH
  by_cases hm1 : m = 1
  · left
    have h1 := fun i => sz_eq_one_iff.1 ((hx i).trans hm1)
    have h2 := fun j => sz_eq_one_iff.1 ((hy j).trans hm1)
    exact ⟨(h1 true).trans (h2 true).symm, (h1 false).trans (h2 false).symm⟩
  have hm : 2 ≤ m := by have := sz_pos (x true); have := hx true; omega
  have hxne : ∀ i, x i ≠ pt := fun i h => by
    have := hx i; rw [h, sz_eq_one_iff.2 rfl] at this; omega
  have hyne : ∀ j, y j ≠ pt := fun j h => by
    have := hy j; rw [h, sz_eq_one_iff.2 rfl] at this; omega
  by_cases h1 : (dec (x true)).card = 1
  · by_cases h2 : (dec (x false)).card = 1
    · -- case (c): all roots have a single child
      have hdx : ∀ i, (dec (x i)).card = 1 := fun i => by cases i <;> assumption
      have hdy : ∀ j, (dec (y j)).card = 1 := by
        intro j
        obtain ⟨c', hc'⟩ := exists_del _ (hyne (!j))
        obtain ⟨i, c, hc, E⟩ := hH (!j) c' hc'
        have := (rel_cases (hx i) (hx (!i)) (hy (!j)) (hy (!(!j))) hc hc' E).1
        rw [Bool.not_not] at this
        rw [← this]; exact hdx _
      choose z hz using fun i => Multiset.card_eq_one.1 (hdx i)
      choose z' hz' using fun j => Multiset.card_eq_one.1 (hdy j)
      have hxz : ∀ i, x i = enc {z i} := fun i => by rw [← hz i, enc_dec]
      have hyz : ∀ j, y j = enc {z' j} := fun j => by rw [← hz' j, enc_dec]
      have hsz : ∀ i, sz (z i) = m - 1 := fun i => by
        have := hx i; rw [sz_eq, hz i] at this; simp at this; omega
      have hsz' : ∀ j, sz (z' j) = m - 1 := fun j => by
        have := hy j; rw [sz_eq, hz' j] at this; simp at this; omega
      by_cases hm2 : m = 2
      · left
        have e1 : ∀ i, z i = pt := fun i => sz_eq_one_iff.1 (by rw [hsz i]; omega)
        have e2 : ∀ j, z' j = pt := fun j => sz_eq_one_iff.1 (by rw [hsz' j]; omega)
        exact ⟨by rw [hxz, hyz, e1, e2], by rw [hxz, hyz, e1, e2]⟩
      have hzne : ∀ i, z i ≠ pt := fun i h => by
        have := hsz i; rw [h, sz_eq_one_iff.2 rfl] at this; omega
      have hzne' : ∀ j, z' j ≠ pt := fun j h => by
        have := hsz' j; rw [h, sz_eq_one_iff.2 rfl] at this; omega
      have descend : ∀ i j c0 c0', enc {c0} ::ₘ dec (x (!i)) = enc {c0'} ::ₘ dec (y (!j)) →
          c0 ::ₘ dec (z (!i)) = c0' ::ₘ dec (z' (!j)) := by
        intro i j c0 c0' E
        rw [hz (!i), hz' (!j)] at E
        rcases pair_single E with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · have := enc_injective e1
          have hc : c0 = c0' := by simpa using this
          rw [hc, e2]
        · have d1 : dec (z' (!j)) = {c0} := by rw [← e1, dec_enc]
          have d2 : dec (z (!i)) = {c0'} := by rw [e2, dec_enc]
          rw [d1, d2]; exact Multiset.cons_swap _ _ _
      have hG' : ∀ i c, Del (z i) c → ∃ j c', Del (z' j) c' ∧
          c ::ₘ dec (z (!i)) = c' ::ₘ dec (z' (!j)) := by
        intro i c0 hc0
        have hd : Del (x i) (enc {c0}) := by
          rw [hxz i]; exact (del_single_iff (hzne i)).2 ⟨c0, hc0, rfl⟩
        obtain ⟨j, c', hc', E⟩ := hG i _ hd
        rw [hyz j] at hc'
        obtain ⟨c0', hc0', rfl⟩ := (del_single_iff (hzne' j)).1 hc'
        exact ⟨j, c0', hc0', descend i j c0 c0' E⟩
      have hH' : ∀ j c', Del (z' j) c' → ∃ i c, Del (z i) c ∧
          c ::ₘ dec (z (!i)) = c' ::ₘ dec (z' (!j)) := by
        intro j c0' hc0'
        have hd : Del (y j) (enc {c0'}) := by
          rw [hyz j]; exact (del_single_iff (hzne' j)).2 ⟨c0', hc0', rfl⟩
        obtain ⟨i, c, hc, E⟩ := hH j _ hd
        rw [hxz i] at hc
        obtain ⟨c0, hc0, rfl⟩ := (del_single_iff (hzne i)).1 hc
        exact ⟨i, c0, hc0, descend i j c0 c0' E⟩
      rcases ih (m - 1) (by omega) z z' hsz hsz' hG' hH' with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · left; exact ⟨by rw [hxz, hyz, e1], by rw [hxz, hyz, e2]⟩
      · right; exact ⟨by rw [hxz, hyz, e1], by rw [hxz, hyz, e2]⟩
    · -- x false has several children, x true a single one
      obtain ⟨J, e1, e2⟩ := lemB_b m x y hx hy hxne hG hH false h2 (by simpa using h1)
      cases J
      · left; exact ⟨by simpa using e2, e1⟩
      · right; exact ⟨by simpa using e2, e1⟩
  · by_cases h2 : (dec (x false)).card = 1
    · obtain ⟨J, e1, e2⟩ := lemB_b m x y hx hy hxne hG hH true h1 (by simpa using h2)
      cases J
      · right; exact ⟨e1, by simpa using e2⟩
      · left; exact ⟨e1, by simpa using e2⟩
    · -- case (a): all related pairs are straight
      have straightG : ∀ i, ∃ j, x (!i) = y (!j) := by
        intro i
        obtain ⟨c, hc⟩ := exists_del _ (hxne i)
        obtain ⟨j, c', hc', E⟩ := hG i c hc
        refine ⟨j, ?_⟩
        rcases (rel_cases (hx i) (hx (!i)) (hy j) (hy (!j)) hc hc' E).2 with ⟨_, h⟩ | ⟨_, _, h⟩
        · exact h
        · exfalso
          have hc1 : (dec (x (!i))).card = 1 := by rw [h]; rfl
          cases i
          · exact h1 hc1
          · exact h2 hc1
      have straightH : ∀ j, ∃ i, x (!i) = y (!j) := by
        intro j
        obtain ⟨c', hc'⟩ := exists_del _ (hyne j)
        obtain ⟨i, c, hc, E⟩ := hH j c' hc'
        refine ⟨i, ?_⟩
        rcases (rel_cases (hx i) (hx (!i)) (hy j) (hy (!j)) hc hc' E).2 with ⟨_, h⟩ | ⟨_, _, h⟩
        · exact h
        · exfalso
          have hc1 : (dec (x (!i))).card = 1 := by rw [h]; rfl
          cases i
          · exact h1 hc1
          · exact h2 hc1
      obtain ⟨j1, e1⟩ := straightG true
      obtain ⟨j2, e2⟩ := straightG false
      obtain ⟨i1, e3⟩ := straightH true
      obtain ⟨i2, e4⟩ := straightH false
      cases j1 <;> cases j2 <;> cases i1 <;> cases i2 <;>
        (simp only [Bool.not_true, Bool.not_false] at e1 e2 e3 e4; omega)


/-! graph side -/

open Classical

variable {V W : Type} [Fintype V] [Fintype W]

noncomputable def nb (G : SimpleGraph V) (x : V) : Finset V :=
  Finset.univ.filter (fun y => G.Adj x y)

theorem mem_nb {G : SimpleGraph V} {x y : V} : y ∈ nb G x ↔ G.Adj x y := by
  simp [nb]

noncomputable def codeF (G : SimpleGraph V) : ℕ → V → V → ℕ
  | 0, _, _ => 0
  | k + 1, p, x => enc (((nb G x).erase p).val.map (fun y => codeF G k x y))

theorem codeF_iso {G : SimpleGraph V} {H : SimpleGraph W} (e : V ≃ W)
    (hadj : ∀ a b, G.Adj a b ↔ H.Adj (e a) (e b)) :
    ∀ k p x, codeF H k (e p) (e x) = codeF G k p x := by
  intro k
  induction k with
  | zero => intro p x; rfl
  | succ k ih =>
    intro p x
    simp only [codeF]
    congr 1
    have hset : (nb H (e x)).erase (e p) = ((nb G x).erase p).map e.toEmbedding := by
      ext w
      simp only [Finset.mem_erase, mem_nb, Finset.mem_map, Equiv.coe_toEmbedding]
      constructor
      · rintro ⟨hne, hw⟩
        refine ⟨e.symm w, ⟨?_, ?_⟩, by simp⟩
        · intro h; apply hne; rw [← h]; simp
        · rw [hadj]; simpa using hw
      · rintro ⟨y, ⟨hne, hy⟩, rfl⟩
        exact ⟨fun h => hne (e.injective h), (hadj _ _).1 hy⟩
    rw [hset, Finset.map_val, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro y _
    exact ih x y

noncomputable def limb (G : SimpleGraph V) (p x : V) : Finset V :=
  Finset.univ.filter (fun z => G.dist x z < G.dist p z)

theorem mem_limb {G : SimpleGraph V} {p x z : V} : z ∈ limb G p x ↔ G.dist x z < G.dist p z := by
  simp [limb]

/-- two parents lemma -/
theorem two_parents {G : SimpleGraph V} (hG : G.IsTree) {z w y1 y2 : V}
    (h1 : G.Adj y1 w) (h2 : G.Adj y2 w)
    (d1 : G.dist z y1 + 1 = G.dist z w) (d2 : G.dist z y2 + 1 = G.dist z w) : y1 = y2 := by
  obtain ⟨q1, hq1, hl1⟩ := hG.connected.exists_path_of_dist z y1
  obtain ⟨q2, hq2, hl2⟩ := hG.connected.exists_path_of_dist z y2
  have hp1 : (q1.concat h1).IsPath :=
    SimpleGraph.Walk.isPath_of_length_eq_dist _ (by rw [SimpleGraph.Walk.length_concat, hl1, d1])
  have hp2 : (q2.concat h2).IsPath :=
    SimpleGraph.Walk.isPath_of_length_eq_dist _ (by rw [SimpleGraph.Walk.length_concat, hl2, d2])
  have heq := (hG.isAcyclic.subsingleton_path _ _).elim ⟨_, hp1⟩ ⟨_, hp2⟩
  have heq' : q1.concat h1 = q2.concat h2 := congrArg Subtype.val heq
  have := congrArg SimpleGraph.Walk.penultimate heq'
  simpa using this

/-- adjacent vertices differ by exactly one in distance from any vertex -/
theorem dist_adj_cases {G : SimpleGraph V} (hG : G.IsTree) (z : V) {x y : V} (h : G.Adj x y) :
    G.dist z x = G.dist z y + 1 ∨ G.dist z y = G.dist z x + 1 :=
  hG.dist_eq_dist_add_one_of_adj z h

theorem limb_sub {G : SimpleGraph V} (hG : G.IsTree) {p x y : V}
    (hpx : G.Adj p x) (hxy : G.Adj x y) (hne : y ≠ p) : limb G x y ⊆ limb G p x := by
  intro z hz
  rw [mem_limb] at hz ⊢
  have e1 : G.dist y z = G.dist z y := SimpleGraph.dist_comm
  have e2 : G.dist x z = G.dist z x := SimpleGraph.dist_comm
  have e3 : G.dist p z = G.dist z p := SimpleGraph.dist_comm
  rw [e1, e2] at hz
  rw [e2, e3]
  rcases dist_adj_cases hG z hpx with h | h
  · omega
  · exfalso
    rcases dist_adj_cases hG z hxy with h' | h'
    · have := two_parents hG (z := z) hpx hxy.symm (by omega) (by omega)
      exact hne this.symm
    · omega

theorem self_mem_limb {G : SimpleGraph V} {p x : V} (hpx : G.Adj p x) : x ∈ limb G p x := by
  rw [mem_limb, SimpleGraph.dist_self]
  have := (SimpleGraph.dist_eq_one_iff_adj).2 hpx
  omega

theorem not_mem_limb_child {G : SimpleGraph V} {x y : V} : x ∉ limb G x y := by
  rw [mem_limb, SimpleGraph.dist_self]; omega

theorem limb_card_lt {G : SimpleGraph V} (hG : G.IsTree) {p x y : V}
    (hpx : G.Adj p x) (hxy : G.Adj x y) (hne : y ≠ p) :
    (limb G x y).card < (limb G p x).card := by
  apply Finset.card_lt_card
  refine ⟨limb_sub hG hpx hxy hne, fun h => ?_⟩
  exact not_mem_limb_child (h (self_mem_limb hpx))

/-- stability of fuel codes for subgraphs of a tree -/
theorem codeF_stable {G G' : SimpleGraph V} (hG : G.IsTree) (hle : G' ≤ G) :
    ∀ s p x, G.Adj p x → (limb G p x).card ≤ s → ∀ k, s ≤ k → codeF G' k p x = codeF G' s p x := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro p x hpx hs k hk
    have hpos : 0 < (limb G p x).card := Finset.card_pos.2 ⟨x, self_mem_limb hpx⟩
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [codeF]
    congr 1
    apply Multiset.map_congr rfl
    intro y hy
    rw [Finset.mem_val, Finset.mem_erase, mem_nb] at hy
    have hxy : G.Adj x y := hle hy.2
    have hlt := limb_card_lt hG hpx hxy hy.1
    rw [ih s' (Nat.lt_succ_self _) x y hxy (by omega) k' (by omega)]


noncomputable def kap (G : SimpleGraph V) (p x : V) : ℕ := codeF G (Fintype.card V) p x

theorem kap_unfold {G G' : SimpleGraph V} (hG : G.IsTree) (hle : G' ≤ G) {p x : V}
    (hpx : G.Adj p x) :
    kap G' p x = enc (((nb G' x).erase p).val.map (fun y => kap G' x y)) := by
  unfold kap
  have h1 := codeF_stable hG hle (Fintype.card V) p x hpx (Finset.card_le_univ _)
    (Fintype.card V + 1) (Nat.le_succ _)
  rw [← h1]
  simp only [codeF]

theorem mem_limb_iff {G : SimpleGraph V} (hG : G.IsTree) {x y z : V} (hxy : G.Adj x y) :
    z ∈ limb G x y ↔ G.dist z x = G.dist z y + 1 := by
  rw [mem_limb, SimpleGraph.dist_comm (u := y), SimpleGraph.dist_comm (u := x)]
  rcases dist_adj_cases hG z hxy with h | h <;> omega

theorem limb_compl {G : SimpleGraph V} (hG : G.IsTree) {p x z : V} (hpx : G.Adj p x) :
    z ∈ limb G x p ↔ z ∉ limb G p x := by
  rw [mem_limb_iff hG hpx.symm, mem_limb_iff hG hpx]
  rcases dist_adj_cases hG z hpx with h | h <;> omega

theorem exists_toward {G : SimpleGraph V} (hG : G.IsTree) {x z : V} (hne : x ≠ z) :
    ∃ y, G.Adj x y ∧ z ∈ limb G x y := by
  obtain ⟨q, hq, hl⟩ := hG.connected.exists_path_of_dist x z
  cases q with
  | nil => exact absurd rfl hne
  | cons h q' =>
    rename_i y
    refine ⟨y, h, ?_⟩
    rw [mem_limb]
    have := SimpleGraph.dist_le q'
    rw [SimpleGraph.Walk.length_cons] at hl
    omega

theorem limb_disjoint {G : SimpleGraph V} (hG : G.IsTree) {x y y' z : V} (h1 : G.Adj x y)
    (h2 : G.Adj x y') (hz : z ∈ limb G x y) (hz' : z ∈ limb G x y') : y = y' := by
  rw [mem_limb_iff hG h1] at hz
  rw [mem_limb_iff hG h2] at hz'
  exact two_parents hG (z := z) h1.symm h2.symm (by omega) (by omega)

theorem mem_limb_cases {G : SimpleGraph V} (hG : G.IsTree) {p x z : V} (hpx : G.Adj p x) :
    z ∈ limb G p x ↔ z = x ∨ ∃ y, G.Adj x y ∧ y ≠ p ∧ z ∈ limb G x y := by
  constructor
  · intro hz
    by_cases hzx : z = x
    · exact Or.inl hzx
    · obtain ⟨y, hy, hzy⟩ := exists_toward hG (x := x) (z := z) (fun h => hzx h.symm)
      refine Or.inr ⟨y, hy, ?_, hzy⟩
      rintro rfl
      exact (limb_compl hG hpx).1 hzy hz
  · rintro (rfl | ⟨y, hy, hne, hzy⟩)
    · exact self_mem_limb hpx
    · exact limb_sub hG hpx hy hne hzy

theorem limb_eq {G : SimpleGraph V} (hG : G.IsTree) {p x : V} (hpx : G.Adj p x) :
    limb G p x = insert x (((nb G x).erase p).biUnion (fun y => limb G x y)) := by
  ext z
  rw [mem_limb_cases hG hpx]
  simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_erase, mem_nb]
  constructor
  · rintro (h | ⟨y, hy, hne, hz⟩)
    · exact Or.inl h
    · exact Or.inr ⟨y, ⟨hne, hy⟩, hz⟩
  · rintro (h | ⟨y, ⟨hne, hy⟩, hz⟩)
    · exact Or.inl h
    · exact Or.inr ⟨y, hy, hne, hz⟩

theorem card_limb {G : SimpleGraph V} (hG : G.IsTree) {p x : V} (hpx : G.Adj p x) :
    (limb G p x).card = 1 + ∑ y ∈ (nb G x).erase p, (limb G x y).card := by
  rw [limb_eq hG hpx, Finset.card_insert_of_notMem, Finset.card_biUnion, add_comm]
  · intro y hy y' hy' hne
    rw [Finset.mem_coe, Finset.mem_erase, mem_nb] at hy hy'
    rw [Function.onFun, Finset.disjoint_left]
    intro z hz hz'
    exact hne (limb_disjoint hG hy.2 hy'.2 hz hz')
  · simp only [Finset.mem_biUnion, not_exists, not_and]
    intro y _
    exact not_mem_limb_child


theorem sz_kap {G : SimpleGraph V} (hG : G.IsTree) :
    ∀ s p x, G.Adj p x → (limb G p x).card ≤ s → sz (kap G p x) = (limb G p x).card := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro p x hpx hs
    rw [kap_unfold hG le_rfl hpx, sz_enc, card_limb hG hpx, Multiset.map_map,
      Finset.sum_eq_multiset_sum]
    congr 2
    apply Multiset.map_congr rfl
    intro y hy
    rw [Finset.mem_val, Finset.mem_erase, mem_nb] at hy
    exact ih _ (lt_of_lt_of_le (limb_card_lt hG hpx hy.2 hy.1) hs) x y hy.2 le_rfl

/-- the vertex-deleted graph, on the same vertex type (the deleted vertex becomes isolated) -/
def delV (G : SimpleGraph V) (v : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ≠ v ∧ b ≠ v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩

theorem delV_le (G : SimpleGraph V) (v : V) : delV G v ≤ G := fun _ _ h => h.1

theorem nb_delV {G : SimpleGraph V} {v x : V} (hx : x ≠ v) :
    nb (delV G v) x = (nb G x).erase v := by
  ext y
  simp only [mem_nb, delV, Finset.mem_erase]
  constructor
  · rintro ⟨h1, _, h3⟩; exact ⟨h3, h1⟩
  · rintro ⟨h3, h1⟩; exact ⟨h1, hx, h3⟩

/-- a leaf: exactly one neighbour -/
def Leaf (G : SimpleGraph V) (v : V) : Prop := (nb G v).card = 1

theorem Leaf.nb_eq {G : SimpleGraph V} {v x : V} (hv : Leaf G v) (hx : G.Adj x v) :
    nb G v = {x} := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hv
  have : x ∈ nb G v := mem_nb.2 hx.symm
  rw [ha, Finset.mem_singleton] at this
  rw [ha, this]

theorem kap_leaf {G : SimpleGraph V} (hG : G.IsTree) {v x : V} (hv : Leaf G v) (hx : G.Adj x v) :
    kap G x v = pt := by
  rw [kap_unfold hG le_rfl hx, hv.nb_eq hx]
  simp [pt]

theorem kap_delV_of_notMem {G : SimpleGraph V} (hG : G.IsTree) (v : V) :
    ∀ s p x, G.Adj p x → (limb G p x).card ≤ s → v ∉ limb G p x →
      kap (delV G v) p x = kap G p x := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro p x hpx hs hv
    have hxv : x ≠ v := fun h => hv (h ▸ self_mem_limb hpx)
    rw [kap_unfold hG (delV_le G v) hpx, kap_unfold hG le_rfl hpx, nb_delV hxv]
    have hset : ((nb G x).erase v).erase p = (nb G x).erase p := by
      ext y
      simp only [Finset.mem_erase, mem_nb]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        refine ⟨h1, ?_, h3⟩
        rintro rfl
        exact hv (limb_sub hG hpx h3 h1 (self_mem_limb h3))
    rw [hset]
    congr 1
    apply Multiset.map_congr rfl
    intro y hy
    rw [Finset.mem_val, Finset.mem_erase, mem_nb] at hy
    exact ih _ (lt_of_lt_of_le (limb_card_lt hG hpx hy.2 hy.1) hs) x y hy.2 le_rfl
      (fun h => hv (limb_sub hG hpx hy.2 hy.1 h))

/-- children codes after deleting a leaf child -/
theorem children_a {G : SimpleGraph V} (hG : G.IsTree) {v x : V} (hv : Leaf G v)
    {C : Finset V} (hC : C ⊆ nb G x) (hvC : v ∈ C) :
    (C.erase v).val.map (kap (delV G v) x) = (C.val.map (kap G x)).erase pt := by
  have hxv : G.Adj x v := mem_nb.1 (hC hvC)
  rw [← kap_leaf hG hv hxv, ← Multiset.map_erase_of_mem _ _ hvC,
    ← Finset.erase_val]
  apply Multiset.map_congr rfl
  intro y hy
  rw [Finset.mem_val, Finset.mem_erase] at hy
  have hxy : G.Adj x y := mem_nb.1 (hC hy.2)
  exact kap_delV_of_notMem hG v _ x y hxy le_rfl
    (fun h => hy.1 (limb_disjoint hG hxy hxv h (self_mem_limb hxv)))

/-- children codes after deleting a leaf deeper inside the limb of the child `y` -/
theorem children_b {G : SimpleGraph V} (hG : G.IsTree) {v x y : V}
    {C : Finset V} (hC : C ⊆ nb G x) (hyC : y ∈ C) (hvy : v ∈ limb G x y) :
    C.val.map (kap (delV G v) x) =
      kap (delV G v) x y ::ₘ (C.val.map (kap G x)).erase (kap G x y) := by
  have hxy : G.Adj x y := mem_nb.1 (hC hyC)
  rw [← Multiset.map_erase_of_mem _ _ hyC, ← Finset.erase_val]
  conv_lhs => rw [← Finset.insert_erase hyC]
  rw [Finset.insert_val_of_notMem (Finset.notMem_erase y C), Multiset.map_cons]
  congr 1
  apply Multiset.map_congr rfl
  intro y' hy'
  rw [Finset.mem_val, Finset.mem_erase] at hy'
  have hxy' : G.Adj x y' := mem_nb.1 (hC hy'.2)
  exact kap_delV_of_notMem hG v _ x y' hxy' le_rfl
    (fun h => hy'.1 (limb_disjoint hG hxy' hxy h hvy))


theorem kap_del_child {G : SimpleGraph V} (hG : G.IsTree) {v p x : V} (hv : Leaf G v)
    (hpx : G.Adj p x) (hxv : G.Adj x v) (hvp : v ≠ p) :
    kap (delV G v) p x = enc ((((nb G x).erase p).val.map (kap G x)).erase pt) := by
  rw [kap_unfold hG (delV_le G v) hpx, nb_delV hxv.ne, Finset.erase_right_comm,
    children_a hG hv (Finset.erase_subset _ _) (Finset.mem_erase.2 ⟨hvp, mem_nb.2 hxv⟩)]

theorem kap_del_deep {G : SimpleGraph V} (hG : G.IsTree) {v p x y : V}
    (hpx : G.Adj p x) (hxy : G.Adj x y) (hyp : y ≠ p) (hvy : v ∈ limb G x y) (hvne : v ≠ y) :
    kap (delV G v) p x =
      enc (kap (delV G v) x y ::ₘ (((nb G x).erase p).val.map (kap G x)).erase (kap G x y)) := by
  have hxv : x ≠ v := fun h => not_mem_limb_child (h ▸ hvy)
  have hnadj : v ∉ nb G x := fun h =>
    hvne (limb_disjoint hG (mem_nb.1 h) hxy (self_mem_limb (mem_nb.1 h)) hvy)
  rw [kap_unfold hG (delV_le G v) hpx, nb_delV hxv, Finset.erase_eq_of_notMem hnadj,
    children_b hG (Finset.erase_subset _ _) (Finset.mem_erase.2 ⟨hyp, mem_nb.2 hxy⟩) hvy]

theorem del_kap {G : SimpleGraph V} (hG : G.IsTree) {v : V} (hv : Leaf G v) :
    ∀ s p x, G.Adj p x → (limb G p x).card ≤ s → v ∈ limb G p x → v ≠ x →
      Del (kap G p x) (kap (delV G v) p x) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro p x hpx hs hvl hvx
    rcases (mem_limb_cases hG hpx).1 hvl with h | ⟨y, hxy, hyp, hvy⟩
    · exact absurd h hvx
    · have hmem : kap G x y ∈ ((nb G x).erase p).val.map (kap G x) :=
        Multiset.mem_map_of_mem _ (Finset.mem_erase.2 ⟨hyp, mem_nb.2 hxy⟩)
      by_cases hvy' : v = y
      · subst hvy'
        rw [kap_del_child hG hv hpx hxy hyp, kap_unfold hG le_rfl hpx]
        rw [kap_leaf hG hv hxy] at hmem
        exact Del.here _ hmem
      · rw [kap_del_deep hG hpx hxy hyp hvy hvy', kap_unfold hG le_rfl hpx]
        exact Del.there _ _ _ hmem
          (ih _ (lt_of_lt_of_le (limb_card_lt hG hpx hxy hyp) hs) x y hxy le_rfl hvy hvy')

theorem leaf_of_kap_eq_pt {G : SimpleGraph V} (hG : G.IsTree) {x y : V} (hxy : G.Adj x y)
    (h : kap G x y = pt) : Leaf G y := by
  rw [kap_unfold hG le_rfl hxy] at h
  have h0 := enc_injective (h.trans rfl : _ = enc 0)
  rw [Multiset.map_eq_zero, Finset.val_eq_zero, Finset.erase_eq_empty_iff] at h0
  have hx : x ∈ nb G y := mem_nb.2 hxy.symm
  rcases h0 with h0 | h0
  · rw [h0] at hx; exact absurd hx (Finset.notMem_empty _)
  · unfold Leaf; rw [h0]; rfl

theorem exists_leaf_of_del {G : SimpleGraph V} (hG : G.IsTree) :
    ∀ s p x c, G.Adj p x → (limb G p x).card ≤ s → Del (kap G p x) c →
      ∃ v, Leaf G v ∧ v ∈ limb G p x ∧ v ≠ x ∧ kap (delV G v) p x = c := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro p x c hpx hs hdel
    rw [kap_unfold hG le_rfl hpx, del_enc_iff] at hdel
    rcases hdel with ⟨hpt, rfl⟩ | ⟨a, ha, c0, hdel0, rfl⟩
    · obtain ⟨y, hy, hky⟩ := Multiset.mem_map.1 hpt
      rw [Finset.mem_val, Finset.mem_erase, mem_nb] at hy
      have hleaf : Leaf G y := leaf_of_kap_eq_pt hG hy.2 hky
      exact ⟨y, hleaf, limb_sub hG hpx hy.2 hy.1 (self_mem_limb hy.2), hy.2.ne.symm,
        kap_del_child hG hleaf hpx hy.2 hy.1⟩
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 ha
      rw [Finset.mem_val, Finset.mem_erase, mem_nb] at hy
      obtain ⟨v, hv, hvl, hvy, hk⟩ :=
        ih _ (lt_of_lt_of_le (limb_card_lt hG hpx hy.2 hy.1) hs) x y c0 hy.2 le_rfl hdel0
      refine ⟨v, hv, limb_sub hG hpx hy.2 hy.1 hvl, ?_, ?_⟩
      · rintro rfl; exact not_mem_limb_child hvl
      · rw [kap_del_deep hG hpx hy.2 hy.1 hvl hvy, hk]

noncomputable def rho (G : SimpleGraph V) (r : V) : Multiset ℕ := (nb G r).val.map (kap G r)

def DelO (t : ℕ) (C : Multiset ℕ) : Prop := (t = pt ∧ C = 0) ∨ ∃ c, Del t c ∧ C = {c}

/-- the root code multiset of a leaf-deleted card, seen from a vertex `r` -/
theorem rho_card {G : SimpleGraph V} (hG : G.IsTree) {v r : V} (hv : Leaf G v) (hrv : r ≠ v) :
    ∃ y, G.Adj r y ∧ v ∈ limb G r y ∧ ∃ C, DelO (kap G r y) C ∧
      rho (delV G v) r = (rho G r).erase (kap G r y) + C := by
  obtain ⟨y, hry, hvy⟩ := exists_toward hG hrv
  refine ⟨y, hry, hvy, ?_⟩
  by_cases hvy' : v = y
  · subst hvy'
    refine ⟨0, Or.inl ⟨kap_leaf hG hv hry, rfl⟩, ?_⟩
    unfold rho
    rw [nb_delV hrv, children_a hG hv (Finset.Subset.refl _) (mem_nb.2 hry),
      kap_leaf hG hv hry, add_zero]
  · refine ⟨{kap (delV G v) r y}, Or.inr ⟨_, del_kap hG hv _ r y hry le_rfl hvy hvy', rfl⟩, ?_⟩
    have hnadj : v ∉ nb G r := fun h =>
      hvy' (limb_disjoint hG (mem_nb.1 h) hry (self_mem_limb (mem_nb.1 h)) hvy)
    unfold rho
    rw [nb_delV hrv, Finset.erase_eq_of_notMem hnadj,
      children_b hG (Finset.Subset.refl _) (mem_nb.2 hry) hvy, Multiset.add_comm]
    rfl

theorem exists_leaf_card {G : SimpleGraph V} (hG : G.IsTree) {r y : V} (hry : G.Adj r y)
    {C : Multiset ℕ} (hC : DelO (kap G r y) C) :
    ∃ v, Leaf G v ∧ v ∈ limb G r y ∧ rho (delV G v) r = (rho G r).erase (kap G r y) + C := by
  rcases hC with ⟨hpt, rfl⟩ | ⟨c, hdel, rfl⟩
  · have hleaf := leaf_of_kap_eq_pt hG hry hpt
    refine ⟨y, hleaf, self_mem_limb hry, ?_⟩
    unfold rho
    rw [nb_delV hry.ne, children_a hG hleaf (Finset.Subset.refl _) (mem_nb.2 hry), hpt, add_zero]
  · obtain ⟨v, hv, hvl, hvy, hk⟩ := exists_leaf_of_del hG _ r y c hry le_rfl hdel
    refine ⟨v, hv, hvl, ?_⟩
    have hrv : r ≠ v := fun h => not_mem_limb_child (h ▸ hvl)
    have hnadj : v ∉ nb G r := fun h =>
      hvy (limb_disjoint hG (mem_nb.1 h) hry (self_mem_limb (mem_nb.1 h)) hvl)
    unfold rho
    rw [nb_delV hrv, Finset.erase_eq_of_notMem hnadj,
      children_b hG (Finset.Subset.refl _) (mem_nb.2 hry) hvl, hk, Multiset.add_comm]
    rfl


theorem adj_closure {G : SimpleGraph V} (hG : G.IsTree) {p x a b : V} (hpx : G.Adj p x)
    (hab : G.Adj a b) (ha : a ∈ limb G p x) (hb : b ∉ limb G p x) : a = x ∧ b = p := by
  have hb' : b ∈ limb G x p := (limb_compl hG hpx).2 hb
  rw [mem_limb_iff hG hpx] at ha
  rw [mem_limb_iff hG hpx.symm] at hb'
  have c1 : G.dist x a = G.dist a x := SimpleGraph.dist_comm
  have c2 : G.dist x b = G.dist b x := SimpleGraph.dist_comm
  have c3 : G.dist p a = G.dist a p := SimpleGraph.dist_comm
  have c4 : G.dist p b = G.dist b p := SimpleGraph.dist_comm
  have h1 := dist_adj_cases hG x hab
  have h2 := dist_adj_cases hG p hab
  have heq : G.dist a x = G.dist b p := by omega
  by_cases h0 : G.dist a x = 0
  · constructor
    · exact (hG.connected.dist_eq_zero_iff).1 h0
    · exact (hG.connected.dist_eq_zero_iff).1 (heq ▸ h0)
  · exfalso
    have hbp : b ≠ p := fun h => by
      rw [h, SimpleGraph.dist_self] at heq; exact h0 heq
    obtain ⟨b', hbb', hpb'⟩ := exists_toward hG hbp
    rw [mem_limb_iff hG hbb'] at hpb'
    have tri := hG.connected.dist_triangle (u := x) (v := p) (w := b')
    have hxp : G.dist x p = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hpx.symm
    have h3 := dist_adj_cases hG x hbb'
    have e1 : G.dist x b' + 1 = G.dist x b := by omega
    have e2 : G.dist x a + 1 = G.dist x b := by omega
    have := two_parents hG (z := x) hab hbb'.symm e2 e1
    subst this
    omega

theorem exists_bij_of_map_eq {α β : Type} (d : β) (f : α → ℕ) (g : β → ℕ) :
    ∀ (C : Finset α) (C' : Finset β), C.val.map f = C'.val.map g →
      ∃ π : α → β, (∀ y ∈ C, π y ∈ C') ∧ Set.InjOn π C ∧ ∀ y ∈ C, g (π y) = f y := by
  intro C
  induction C using Finset.induction_on with
  | empty =>
    intro C' _
    exact ⟨fun _ => d, by simp, by simp, by simp⟩
  | insert a C0 ha ih =>
    intro C' h
    rw [Finset.insert_val_of_notMem ha, Multiset.map_cons] at h
    have hmem : f a ∈ C'.val.map g := by rw [← h]; exact Multiset.mem_cons_self _ _
    obtain ⟨a', ha', hga'⟩ := Multiset.mem_map.1 hmem
    have ha'C : a' ∈ C' := ha'
    have h' : C0.val.map f = (C'.erase a').val.map g := by
      have e : C'.val.map g = g a' ::ₘ (C'.erase a').val.map g := by
        conv_lhs => rw [← Finset.insert_erase ha'C]
        rw [Finset.insert_val_of_notMem (Finset.notMem_erase a' C'), Multiset.map_cons]
      rw [e, hga'] at h
      exact (Multiset.cons_inj_right _).1 h
    obtain ⟨π0, h1, h2, h3⟩ := ih (C'.erase a') h'
    refine ⟨fun y => if y = a then a' else π0 y, ?_, ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · simpa using ha'C
      · have hne : y ≠ a := fun h => ha (h ▸ hy)
        simp only [hne, if_false]
        exact Finset.mem_of_mem_erase (h1 y hy)
    · intro y hy z hz hyz
      have hy' := Finset.mem_insert.1 (Finset.mem_coe.1 hy)
      have hz' := Finset.mem_insert.1 (Finset.mem_coe.1 hz)
      simp only at hyz
      by_cases hya : y = a
      · by_cases hza : z = a
        · rw [hya, hza]
        · have hzC : z ∈ C0 := hz'.resolve_left hza
          rw [if_pos hya, if_neg hza] at hyz
          exact absurd hyz.symm (Finset.ne_of_mem_erase (h1 z hzC))
      · have hyC : y ∈ C0 := hy'.resolve_left hya
        by_cases hza : z = a
        · rw [if_neg hya, if_pos hza] at hyz
          exact absurd hyz (Finset.ne_of_mem_erase (h1 y hyC))
        · have hzC : z ∈ C0 := hz'.resolve_left hza
          rw [if_neg hya, if_neg hza] at hyz
          exact h2 hyC hzC hyz
    · intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · simpa using hga'
      · have hne : y ≠ a := fun h => ha (h ▸ hy)
        simp only [hne, if_false]
        exact h3 y hy


theorem glue {G : SimpleGraph V} {H : SimpleGraph W} (hG : G.IsTree) (hH : H.IsTree)
    {x : V} {x' : W} {C : Finset V} {C' : Finset W} (hC : C ⊆ nb G x) (hC' : C' ⊆ nb H x')
    (π : V → W) (hπ : ∀ y ∈ C, π y ∈ C') (hπinj : Set.InjOn π C)
    (F : V → V → W)
    (hF : ∀ y ∈ C, F y y = π y ∧ (∀ z ∈ limb G x y, F y z ∈ limb H x' (π y)) ∧
      Set.InjOn (F y) (limb G x y) ∧
      ∀ a ∈ limb G x y, ∀ b ∈ limb G x y, (G.Adj a b ↔ H.Adj (F y a) (F y b))) :
    ∃ f : V → W, f x = x' ∧
      (∀ z ∈ insert x (C.biUnion (fun y => limb G x y)),
        f z ∈ insert x' (C'.biUnion (fun y => limb H x' y))) ∧
      (∀ a ∈ insert x (C.biUnion (fun y => limb G x y)),
        ∀ b ∈ insert x (C.biUnion (fun y => limb G x y)), f a = f b → a = b) ∧
      ∀ a ∈ insert x (C.biUnion (fun y => limb G x y)),
        ∀ b ∈ insert x (C.biUnion (fun y => limb G x y)), (G.Adj a b ↔ H.Adj (f a) (f b)) := by
  let f : V → W := fun z => if z = x then x' else
    if h : ∃ y, y ∈ C ∧ z ∈ limb G x y then F (Classical.choose h) z else x'
  have hfx : f x = x' := by simp [f]
  have key : ∀ y ∈ C, ∀ z ∈ limb G x y, f z = F y z := by
    intro y hy z hz
    have hzx : z ≠ x := fun h => not_mem_limb_child (h ▸ hz)
    have hex : ∃ y, y ∈ C ∧ z ∈ limb G x y := ⟨y, hy, hz⟩
    have hsp := Classical.choose_spec hex
    have : Classical.choose hex = y :=
      limb_disjoint hG (mem_nb.1 (hC hsp.1)) (mem_nb.1 (hC hy)) hsp.2 hz
    simp only [f, hzx, if_false, dif_pos hex, this]
  have hD : ∀ z ∈ insert x (C.biUnion (fun y => limb G x y)),
      z = x ∨ ∃ y ∈ C, z ∈ limb G x y := by
    intro z hz
    rcases Finset.mem_insert.1 hz with h | h
    · exact Or.inl h
    · obtain ⟨y, hy, hzy⟩ := Finset.mem_biUnion.1 h
      exact Or.inr ⟨y, hy, hzy⟩
  have hadjx : ∀ y ∈ C, G.Adj x y := fun y hy => mem_nb.1 (hC hy)
  have hadjx' : ∀ y ∈ C, H.Adj x' (π y) := fun y hy => mem_nb.1 (hC' (hπ y hy))
  have hfin : ∀ y ∈ C, ∀ z ∈ limb G x y, f z ∈ limb H x' (π y) := by
    intro y hy z hz; rw [key y hy z hz]; exact (hF y hy).2.1 z hz
  have hne : ∀ y ∈ C, ∀ z ∈ limb G x y, f z ≠ x' := by
    intro y hy z hz h
    exact not_mem_limb_child (h ▸ hfin y hy z hz)
  -- two vertices in limbs whose images lie in the same limb are in the same limb
  have same : ∀ y ∈ C, ∀ y2 ∈ C, ∀ a ∈ limb G x y, ∀ b ∈ limb G x y2,
      f b ∈ limb H x' (π y) → y2 = y := by
    intro y hy y2 hy2 a _ b hb hfb
    exact hπinj hy2 hy (limb_disjoint hH (hadjx' y2 hy2) (hadjx' y hy) (hfin y2 hy2 b hb) hfb)
  refine ⟨f, hfx, ?_, ?_, ?_⟩
  · intro z hz
    rcases hD z hz with rfl | ⟨y, hy, hzy⟩
    · rw [hfx]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨π y, hπ y hy, hfin y hy z hzy⟩)
  · intro a ha b hb hab
    rcases hD a ha with rfl | ⟨y, hy, hay⟩
    · rcases hD b hb with rfl | ⟨y2, hy2, hby⟩
      · rfl
      · exact absurd (hab ▸ hfx : f b = x') (hne y2 hy2 b hby)
    · rcases hD b hb with rfl | ⟨y2, hy2, hby⟩
      · exact absurd (hab.trans hfx) (hne y hy a hay)
      · have h2 : y2 = y := same y hy y2 hy2 a hay b hby (hab ▸ hfin y hy a hay)
        subst h2
        rw [key y2 hy a hay, key y2 hy b hby] at hab
        exact (hF y2 hy).2.2.1 hay hby hab
  · intro a ha b hb
    rcases hD a ha with rfl | ⟨y, hy, hay⟩
    · rcases hD b hb with rfl | ⟨y2, hy2, hby⟩
      · rw [hfx]
        exact ⟨fun h => absurd h (G.loopless.irrefl _), fun h => absurd h (H.loopless.irrefl _)⟩
      · rw [hfx]
        constructor
        · intro h
          have : y2 = b := limb_disjoint hG (hadjx y2 hy2) h hby (self_mem_limb h)
          subst this
          rw [key y2 hy2 y2 hby, (hF y2 hy2).1]
          exact hadjx' y2 hy2
        · intro h
          have h1 : π y2 = f b :=
            limb_disjoint hH (hadjx' y2 hy2) h (hfin y2 hy2 b hby) (self_mem_limb h)
          rw [key y2 hy2 b hby, ← (hF y2 hy2).1] at h1
          have : y2 = b := (hF y2 hy2).2.2.1 (self_mem_limb (hadjx y2 hy2)) hby h1
          subst this
          exact hadjx y2 hy2
    · rcases hD b hb with rfl | ⟨y2, hy2, hby⟩
      · rw [hfx]
        constructor
        · intro h
          have : y = a := limb_disjoint hG (hadjx y hy) h.symm hay (self_mem_limb h.symm)
          subst this
          rw [key y hy y hay, (hF y hy).1]
          exact (hadjx' y hy).symm
        · intro h
          have h1 : π y = f a :=
            limb_disjoint hH (hadjx' y hy) h.symm (hfin y hy a hay) (self_mem_limb h.symm)
          rw [key y hy a hay, ← (hF y hy).1] at h1
          have : y = a := (hF y hy).2.2.1 (self_mem_limb (hadjx y hy)) hay h1
          subst this
          exact (hadjx y hy).symm
      · constructor
        · intro h
          have hb2 : b ∈ limb G x y := by
            by_contra hcon
            have := adj_closure hG (hadjx y hy) h hay hcon
            exact not_mem_limb_child (this.2 ▸ hby)
          have h2 : y2 = y := limb_disjoint hG (hadjx y2 hy2) (hadjx y hy) hby hb2
          subst h2
          rw [key y2 hy a hay, key y2 hy b hby]
          exact ((hF y2 hy).2.2.2 a hay b hby).1 h
        · intro h
          have hb2 : f b ∈ limb H x' (π y) := by
            by_contra hcon
            have := adj_closure hH (hadjx' y hy) h (hfin y hy a hay) hcon
            exact hne y2 hy2 b hby this.2
          have h2 : y2 = y := same y hy y2 hy2 a hay b hby hb2
          subst h2
          rw [key y2 hy a hay, key y2 hy b hby] at h
          exact ((hF y2 hy).2.2.2 a hay b hby).2 h


theorem limb_iso {G : SimpleGraph V} {H : SimpleGraph W} (hG : G.IsTree) (hH : H.IsTree) (d : W) :
    ∀ s p x p' x', G.Adj p x → H.Adj p' x' → (limb G p x).card ≤ s → kap G p x = kap H p' x' →
      ∃ f : V → W, f x = x' ∧ (∀ z ∈ limb G p x, f z ∈ limb H p' x') ∧
        Set.InjOn f (limb G p x) ∧
        ∀ a ∈ limb G p x, ∀ b ∈ limb G p x, (G.Adj a b ↔ H.Adj (f a) (f b)) := by
  haveI : Nonempty W := ⟨d⟩
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro p x p' x' hpx hpx' hs hk
    rw [kap_unfold hG le_rfl hpx, kap_unfold hH le_rfl hpx'] at hk
    have hM := enc_injective hk
    obtain ⟨π, hπ1, hπ2, hπ3⟩ := exists_bij_of_map_eq d (kap G x) (kap H x') _ _ hM
    have hch : ∀ y ∈ (nb G x).erase p, ∃ f : V → W, f y = π y ∧
        (∀ z ∈ limb G x y, f z ∈ limb H x' (π y)) ∧ Set.InjOn f (limb G x y) ∧
        ∀ a ∈ limb G x y, ∀ b ∈ limb G x y, (G.Adj a b ↔ H.Adj (f a) (f b)) := by
      intro y hy
      have hy' := Finset.mem_erase.1 hy
      have hxy : G.Adj x y := mem_nb.1 hy'.2
      have hπy := Finset.mem_erase.1 (hπ1 y hy)
      exact ih _ (lt_of_lt_of_le (limb_card_lt hG hpx hxy hy'.1) hs) x y x' (π y) hxy
        (mem_nb.1 hπy.2) le_rfl (hπ3 y hy).symm
    choose! F hF using hch
    obtain ⟨f, hfx, hf1, hf2, hf3⟩ := glue hG hH (Finset.erase_subset _ _)
      (Finset.erase_subset _ _) π hπ1 hπ2 F hF
    rw [← limb_eq hG hpx] at hf1 hf2 hf3
    rw [← limb_eq hH hpx'] at hf1
    exact ⟨f, hfx, hf1, fun a ha b hb h => hf2 a (Finset.mem_coe.1 ha) b (Finset.mem_coe.1 hb) h,
      hf3⟩

theorem iso_of_rho_eq {G : SimpleGraph V} {H : SimpleGraph W} (hG : G.IsTree) (hH : H.IsTree)
    (hcard : Fintype.card V = Fintype.card W) {r : V} {r' : W} (h : rho G r = rho H r') :
    Nonempty (G ≃g H) := by
  haveI : Nonempty W := ⟨r'⟩
  unfold rho at h
  obtain ⟨π, hπ1, hπ2, hπ3⟩ := exists_bij_of_map_eq r' (kap G r) (kap H r') _ _ h
  have hch : ∀ y ∈ nb G r, ∃ f : V → W, f y = π y ∧
      (∀ z ∈ limb G r y, f z ∈ limb H r' (π y)) ∧ Set.InjOn f (limb G r y) ∧
      ∀ a ∈ limb G r y, ∀ b ∈ limb G r y, (G.Adj a b ↔ H.Adj (f a) (f b)) := by
    intro y hy
    exact limb_iso hG hH r' _ r y r' (π y) (mem_nb.1 hy) (mem_nb.1 (hπ1 y hy)) le_rfl
      (hπ3 y hy).symm
  choose! F hF using hch
  obtain ⟨f, hfx, hf1, hf2, hf3⟩ := glue hG hH (Finset.Subset.refl _) (Finset.Subset.refl _)
    π hπ1 hπ2 F hF
  have huniv : ∀ z : V, z ∈ insert r ((nb G r).biUnion (fun y => limb G r y)) := by
    intro z
    by_cases hz : z = r
    · exact hz ▸ Finset.mem_insert_self _ _
    · obtain ⟨y, hy, hzy⟩ := exists_toward hG (x := r) (z := z) (fun h => hz h.symm)
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨y, mem_nb.2 hy, hzy⟩)
  have hinj : Function.Injective f := fun a b hab => hf2 a (huniv a) b (huniv b) hab
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩
  exact ⟨⟨Equiv.ofBijective f hbij, fun {a b} => (hf3 a (huniv a) b (huniv b)).symm⟩⟩


/-- a bijection of the vertex sets which is an isomorphism of the cards at `v` and `w` -/
def CardIso (G : SimpleGraph V) (H : SimpleGraph W) (v : V) (w : W) (e : V ≃ W) : Prop :=
  e v = w ∧ ∀ a b, a ≠ v → b ≠ v → (G.Adj a b ↔ H.Adj (e a) (e b))

theorem exists_cardIso {G : SimpleGraph V} {H : SimpleGraph W} {v : V} {w : W}
    (hcard : Fintype.card V = Fintype.card W)
    (ψ : G.induce {v}ᶜ ≃g H.induce {w}ᶜ) : ∃ e : V ≃ W, CardIso G H v w e := by
  let f : V → W := fun x => if h : x = v then w else (ψ ⟨x, h⟩ : W)
  have hfv : f v = w := by simp [f]
  have hf : ∀ x (h : x ≠ v), f x = (ψ ⟨x, h⟩ : W) := fun x h => by simp [f, h]
  have hne : ∀ x, x ≠ v → f x ≠ w := fun x h => by
    rw [hf x h]; exact (ψ ⟨x, h⟩).2
  have hinj : Function.Injective f := by
    intro a b hab
    by_cases ha : a = v
    · by_cases hb : b = v
      · rw [ha, hb]
      · rw [ha, hfv] at hab; exact absurd hab.symm (hne b hb)
    · by_cases hb : b = v
      · rw [hb, hfv] at hab; exact absurd hab (hne a ha)
      · rw [hf a ha, hf b hb] at hab
        have := ψ.injective (Subtype.ext hab)
        exact congrArg Subtype.val this
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩
  refine ⟨Equiv.ofBijective f hbij, hfv, ?_⟩
  intro a b ha hb
  show G.Adj a b ↔ H.Adj (f a) (f b)
  rw [hf a ha, hf b hb]
  exact (ψ.map_rel_iff (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)).symm

theorem CardIso.delV_adj {G : SimpleGraph V} {H : SimpleGraph W} {v : V} {w : W} {e : V ≃ W}
    (he : CardIso G H v w e) (a b : V) :
    (delV G v).Adj a b ↔ (delV H w).Adj (e a) (e b) := by
  have h1 : ∀ x, e x ≠ w ↔ x ≠ v := fun x => by
    rw [← he.1]; exact e.injective.ne_iff
  show (G.Adj a b ∧ a ≠ v ∧ b ≠ v) ↔ (H.Adj (e a) (e b) ∧ e a ≠ w ∧ e b ≠ w)
  rw [h1, h1]
  constructor
  · rintro ⟨h, ha, hb⟩; exact ⟨(he.2 a b ha hb).1 h, ha, hb⟩
  · rintro ⟨h, ha, hb⟩; exact ⟨(he.2 a b ha hb).2 h, ha, hb⟩

theorem nb_map {G : SimpleGraph V} {H : SimpleGraph W} (e : V ≃ W)
    (hadj : ∀ a b, G.Adj a b ↔ H.Adj (e a) (e b)) (x : V) :
    nb H (e x) = (nb G x).map e.toEmbedding := by
  ext w
  simp only [mem_nb, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · intro hw
    exact ⟨e.symm w, by rw [hadj]; simpa using hw, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    exact (hadj _ _).1 hy

theorem kap_iso {G : SimpleGraph V} {H : SimpleGraph W} (e : V ≃ W)
    (hadj : ∀ a b, G.Adj a b ↔ H.Adj (e a) (e b)) (p x : V) :
    kap H (e p) (e x) = kap G p x := by
  unfold kap
  rw [← Fintype.card_congr e]
  exact codeF_iso e hadj _ p x

theorem rho_iso {G : SimpleGraph V} {H : SimpleGraph W} (e : V ≃ W)
    (hadj : ∀ a b, G.Adj a b ↔ H.Adj (e a) (e b)) (r : V) :
    rho H (e r) = rho G r := by
  unfold rho
  rw [nb_map e hadj, Finset.map_val, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro y _
  exact kap_iso e hadj r y

theorem CardIso.rho_eq {G : SimpleGraph V} {H : SimpleGraph W} {v : V} {w : W} {e : V ≃ W}
    (he : CardIso G H v w e) (r : V) : rho (delV H w) (e r) = rho (delV G v) r :=
  rho_iso e he.delV_adj r

theorem CardIso.kap_eq {G : SimpleGraph V} {H : SimpleGraph W} {v : V} {w : W} {e : V ≃ W}
    (he : CardIso G H v w e) (p x : V) : kap (delV H w) (e p) (e x) = kap (delV G v) p x :=
  kap_iso e he.delV_adj p x


/-- twice the number of edges -/
noncomputable def msum (G : SimpleGraph V) : ℕ := ∑ x, (nb G x).card

theorem msum_iso {G : SimpleGraph V} {H : SimpleGraph W} (e : V ≃ W)
    (hadj : ∀ a b, G.Adj a b ↔ H.Adj (e a) (e b)) : msum H = msum G := by
  unfold msum
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro x _
  rw [nb_map e hadj, Finset.card_map]

theorem msum_delV (G : SimpleGraph V) (v : V) :
    msum G = msum (delV G v) + 2 * (nb G v).card := by
  unfold msum
  have hpt : ∀ x, (nb G x).card = (nb (delV G v) x).card + (if G.Adj v x then 1 else 0)
      + (if x = v then (nb G v).card else 0) := by
    intro x
    by_cases hx : x = v
    · subst hx
      have h0 : nb (delV G x) x = ∅ := by
        ext y; simp [mem_nb, delV]
      simp [h0]
    · rw [nb_delV hx, if_neg hx, add_zero]
      by_cases hadj : G.Adj v x
      · rw [if_pos hadj, Finset.card_erase_of_mem (mem_nb.2 hadj.symm)]
        have : 0 < (nb G x).card := Finset.card_pos.2 ⟨v, mem_nb.2 hadj.symm⟩
        omega
      · rw [if_neg hadj, Finset.erase_eq_of_notMem (fun h => hadj (mem_nb.1 h).symm), add_zero]
  rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h1 : (∑ x : V, if G.Adj v x then 1 else 0) = (nb G v).card := by
    rw [nb, Finset.card_filter]
  have h2 : (∑ x : V, if x = v then (nb G v).card else 0) = (nb G v).card := by
    simp
  rw [h1, h2]; ring

theorem nb_card_eq_degree (G : SimpleGraph V) (x : V) : (nb G x).card = G.degree x := by
  unfold SimpleGraph.degree
  congr 1
  ext y
  simp [nb]

theorem msum_eq_edges (G : SimpleGraph V) : msum G = 2 * G.edgeFinset.card := by
  unfold msum
  rw [← G.sum_degrees_eq_twice_card_edges]
  exact Finset.sum_congr rfl (fun x _ => nb_card_eq_degree G x)

theorem connected_of_card {H : SimpleGraph W} {w u : W} (hc : (H.induce {w}ᶜ).Connected)
    (hwu : H.Adj w u) : H.Connected := by
  have huw : u ≠ w := hwu.ne.symm
  have hall : ∀ a, H.Reachable u a := by
    intro a
    by_cases ha : a = w
    · rw [ha]; exact hwu.symm.reachable
    · have := hc.preconnected ⟨u, huw⟩ ⟨a, ha⟩
      exact this.map (SimpleGraph.Embedding.induce _).toHom
  exact { preconnected := fun a b => (hall a).symm.trans (hall b), nonempty := ⟨w⟩ }

theorem prelim {G : SimpleGraph V} {H : SimpleGraph W} (hV : 3 ≤ Fintype.card V)
    (hG : G.IsTree) (σ : V ≃ W)
    (hσ : ∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) :
    H.IsTree ∧ (∀ v, (nb G v).card = (nb H (σ v)).card) ∧
      ∀ v, ∃ e : V ≃ W, CardIso G H v (σ v) e := by
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr σ
  have hci : ∀ v, ∃ e : V ≃ W, CardIso G H v (σ v) e := fun v =>
    exists_cardIso hcard (hσ v).some
  have hm : ∀ v, msum (delV H (σ v)) = msum (delV G v) := fun v => by
    obtain ⟨e, he⟩ := hci v
    exact msum_iso e he.delV_adj
  have hsumG : Fintype.card V * msum G = (∑ v, msum (delV G v)) + 2 * msum G := by
    have : ∀ v, msum G = msum (delV G v) + 2 * (nb G v).card := msum_delV G
    calc Fintype.card V * msum G = ∑ _v : V, msum G := by simp
      _ = ∑ v, (msum (delV G v) + 2 * (nb G v).card) := Finset.sum_congr rfl (fun v _ => this v)
      _ = (∑ v, msum (delV G v)) + 2 * msum G := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]; rfl
  have hsumH : Fintype.card V * msum H = (∑ v, msum (delV G v)) + 2 * msum H := by
    have : ∀ v, msum H = msum (delV G v) + 2 * (nb H (σ v)).card := fun v => by
      rw [← hm v]; exact msum_delV H (σ v)
    calc Fintype.card V * msum H = ∑ _v : V, msum H := by simp
      _ = ∑ v, (msum (delV G v) + 2 * (nb H (σ v)).card) :=
          Finset.sum_congr rfl (fun v _ => this v)
      _ = (∑ v, msum (delV G v)) + 2 * msum H := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          congr 2
          exact Equiv.sum_comp σ (fun w => (nb H w).card)
  have hmm : msum G = msum H := by
    obtain ⟨k, hk⟩ : ∃ k, Fintype.card V = k + 3 := ⟨Fintype.card V - 3, by omega⟩
    rw [hk] at hsumG hsumH
    have h1 : (k + 1) * msum G = (k + 1) * msum H := by nlinarith
    exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) h1
  have hdeg : ∀ v, (nb G v).card = (nb H (σ v)).card := fun v => by
    have h1 := msum_delV G v
    have h2 := msum_delV H (σ v)
    rw [hm v] at h2
    omega
  refine ⟨?_, hdeg, hci⟩
  -- H is a tree
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨v0, hv0⟩ := hG.exists_vert_degree_one_of_nontrivial
  have hc1 : (G.induce {v0}ᶜ).Connected :=
    hG.connected.induce_compl_singleton_of_degree_eq_one hv0
  have hc2 : (H.induce {σ v0}ᶜ).Connected := ((hσ v0).some.connected_iff).1 hc1
  have hd0 : (nb H (σ v0)).card = 1 := by rw [← hdeg v0, nb_card_eq_degree, hv0]
  obtain ⟨u, hu⟩ := Finset.card_pos.1 (by omega : 0 < (nb H (σ v0)).card)
  have hHc : H.Connected := connected_of_card hc2 (mem_nb.1 hu)
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hHc, ?_⟩
  have e1 := hG.card_edgeFinset
  have e2 := msum_eq_edges G
  have e3 := msum_eq_edges H
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  omega


theorem card_limb_add {G : SimpleGraph V} (hG : G.IsTree) {p x : V} (hpx : G.Adj p x) :
    (limb G p x).card + (limb G x p).card = Fintype.card V := by
  have h : limb G x p = (limb G p x)ᶜ := by
    ext z; rw [Finset.mem_compl]; exact limb_compl hG hpx
  rw [h, Finset.card_compl]
  have := Finset.card_le_univ (limb G p x)
  omega

/-- additivity of distances through `x` for vertices on different sides of the edge `x b` -/
theorem dist_add_of_limb {G : SimpleGraph V} (hG : G.IsTree) {x b : V} (hxb : G.Adj x b) {w : V}
    (hw : w ∉ limb G x b) :
    ∀ k z, z ∈ limb G x b → G.dist x z = k → G.dist w z = G.dist w x + G.dist x z := by
  have hwb : G.dist w b = G.dist w x + 1 := by
    rw [mem_limb_iff hG hxb] at hw
    rcases dist_adj_cases hG w hxb with h | h <;> omega
  intro k
  induction k with
  | zero =>
    intro z hz hk
    have : x = z := (hG.connected.dist_eq_zero_iff).1 hk
    exact absurd (this ▸ hz) not_mem_limb_child
  | succ k ih =>
    intro z hz hk
    by_cases hzb : z = b
    · rw [hzb, hwb, SimpleGraph.dist_eq_one_iff_adj.2 hxb]
    · have hzx : z ≠ x := fun h => not_mem_limb_child (h ▸ hz)
      obtain ⟨z', hzz', hxz'⟩ := exists_toward hG hzx
      rw [mem_limb_iff hG hzz'] at hxz'
      have hz'l : z' ∈ limb G x b := by
        by_contra hcon
        exact hzb (adj_closure hG hxb hzz' hz hcon).1
      have hk' : G.dist x z' = k := by omega
      have hih := ih z' hz'l hk'
      rcases dist_adj_cases hG w hzz' with h | h
      · omega
      · exfalso
        have hz'x : z' ≠ x := fun h => not_mem_limb_child (h ▸ hz'l)
        obtain ⟨z'', hz'z'', hxz''⟩ := exists_toward hG hz'x
        rw [mem_limb_iff hG hz'z''] at hxz''
        have tri := hG.connected.dist_triangle (u := w) (v := x) (w := z'')
        have h3 := dist_adj_cases hG w hz'z''
        have e1 : G.dist w z'' + 1 = G.dist w z' := by omega
        have e2 : G.dist w z + 1 = G.dist w z' := by omega
        have := two_parents hG (z := w) hzz' hz'z''.symm e2 e1
        subst this
        omega

theorem cov {G : SimpleGraph V} (hG : G.IsTree) {x z : V} (hne : x ≠ z) :
    ∃ a b, G.Adj z a ∧ G.Adj x b ∧ x ∈ limb G z a ∧ z ∈ limb G x b ∧
      Fintype.card V ≤ (limb G z a).card + (limb G x b).card ∧
      (b ≠ z → Fintype.card V + 1 ≤ (limb G z a).card + (limb G x b).card) := by
  obtain ⟨a, hza, hxa⟩ := exists_toward hG (x := z) (z := x) (fun h => hne h.symm)
  obtain ⟨b, hxb, hzb⟩ := exists_toward hG hne
  have hxa' := (mem_limb_iff hG hza).1 hxa
  have hcover : ∀ w, w ∈ limb G z a ∪ limb G x b := by
    intro w
    rw [Finset.mem_union]
    by_cases hw : w ∈ limb G x b
    · exact Or.inr hw
    · left
      rw [mem_limb_iff hG hza]
      have had := dist_add_of_limb hG hxb hw _ z hzb rfl
      have tri := hG.connected.dist_triangle (u := w) (v := x) (w := a)
      rcases dist_adj_cases hG w hza with h | h <;> omega
  have huniv : limb G z a ∪ limb G x b = Finset.univ := Finset.eq_univ_of_forall hcover
  refine ⟨a, b, hza, hxb, hxa, hzb, ?_, ?_⟩
  · have := Finset.card_union_le (limb G z a) (limb G x b)
    rw [huniv, Finset.card_univ] at this
    exact this
  · intro hbz
    obtain ⟨a', hza', hba'⟩ := exists_toward hG (x := z) (z := b) (fun h => hbz h.symm)
    rw [mem_limb_iff hG hza'] at hba'
    have hzb' := (mem_limb_iff hG hxb).1 hzb
    have tri := hG.connected.dist_triangle (u := x) (v := b) (w := a')
    have hxb1 : G.dist x b = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hxb
    have c1 : G.dist b z = G.dist z b := SimpleGraph.dist_comm
    have c2 : G.dist x z = G.dist z x := SimpleGraph.dist_comm
    have h3 := dist_adj_cases hG x hza'
    have e1 : G.dist x a' + 1 = G.dist x z := by omega
    have e2 : G.dist x a + 1 = G.dist x z := by omega
    have haa : a = a' := two_parents hG (z := x) hza.symm hza'.symm e2 e1
    have hb_in : b ∈ limb G z a ∩ limb G x b := by
      rw [Finset.mem_inter]
      refine ⟨?_, self_mem_limb hxb⟩
      rw [haa, mem_limb_iff hG hza']; exact hba'
    have h1 := Finset.card_union_add_card_inter (limb G z a) (limb G x b)
    rw [huniv, Finset.card_univ] at h1
    have h2 : 0 < (limb G z a ∩ limb G x b).card := Finset.card_pos.2 ⟨b, hb_in⟩
    omega

theorem exists_centroid {G : SimpleGraph V} (hG : G.IsTree) :
    ∃ c, ∀ y, G.Adj c y → 2 * (limb G c y).card ≤ Fintype.card V := by
  haveI : Nonempty V := hG.connected.nonempty
  let μ : V → ℕ := fun x => (nb G x).sup (fun y => (limb G x y).card)
  obtain ⟨c, _, hc⟩ := Finset.exists_min_image Finset.univ μ Finset.univ_nonempty
  refine ⟨c, ?_⟩
  intro y hcy
  by_contra hcon
  have hL : Fintype.card V < 2 * (limb G c y).card := by omega
  have hμc : (limb G c y).card ≤ μ c :=
    Finset.le_sup (f := fun y => (limb G c y).card) (mem_nb.2 hcy)
  have hμy : μ y < (limb G c y).card := by
    have hpos : 0 < (limb G c y).card := Finset.card_pos.2 ⟨y, self_mem_limb hcy⟩
    rw [Finset.sup_lt_iff (by simpa using hpos)]
    intro y' hy'
    rw [mem_nb] at hy'
    by_cases hy'c : y' = c
    · rw [hy'c]
      have := card_limb_add hG hcy
      omega
    · exact limb_card_lt hG hcy hy' hy'c
  have := hc y (Finset.mem_univ y)
  omega


theorem CardIso.symm {G : SimpleGraph V} {H : SimpleGraph W} {v : V} {w : W} {e : V ≃ W}
    (he : CardIso G H v w e) : CardIso H G w v e.symm := by
  refine ⟨by rw [← he.1]; simp, ?_⟩
  intro a b ha hb
  have h1 : ∀ x : W, x ≠ w → e.symm x ≠ v := fun x hx h => hx (by rw [← he.1, ← h]; simp)
  have := he.2 (e.symm a) (e.symm b) (h1 a ha) (h1 b hb)
  simpa using this.symm

theorem limb_map {G : SimpleGraph V} {H : SimpleGraph W} (hG : G.IsTree) (hH : H.IsTree)
    {x : V} {x' : W} {e : V ≃ W} (he : CardIso G H x x' e) {y : V} (hy : G.Adj x y) {y' : W}
    (hy' : H.Adj x' y') (hey : e y ∈ limb H x' y') :
    ∀ k z, z ∈ limb G x y → G.dist y z = k → e z ∈ limb H x' y' := by
  intro k
  induction k with
  | zero =>
    intro z _ hk
    have : y = z := (hG.connected.dist_eq_zero_iff).1 hk
    exact this ▸ hey
  | succ k ih =>
    intro z hz hk
    have hzy : z ≠ y := fun h => by rw [h, SimpleGraph.dist_self] at hk; omega
    obtain ⟨z0, hzz0, hyz0⟩ := exists_toward hG hzy
    rw [mem_limb_iff hG hzz0] at hyz0
    have hz0l : z0 ∈ limb G x y := by
      by_contra hcon
      exact hzy (adj_closure hG hy hzz0 hz hcon).1
    have hk0 : G.dist y z0 = k := by omega
    have hih := ih z0 hz0l hk0
    have hzx : z ≠ x := fun h => not_mem_limb_child (h ▸ hz)
    have hz0x : z0 ≠ x := fun h => not_mem_limb_child (h ▸ hz0l)
    have hadj : H.Adj (e z0) (e z) := (he.2 z0 z hz0x hzx).1 hzz0.symm
    by_contra hcon
    have := (adj_closure hH hy' hadj hih hcon).2
    rw [← he.1] at this
    exact hzx (e.injective this)

theorem sizes_eq {G : SimpleGraph V} {H : SimpleGraph W} (hG : G.IsTree) (hH : H.IsTree)
    {x : V} {x' : W} {e : V ≃ W} (he : CardIso G H x x' e) :
    (rho G x).map sz = (rho H x').map sz := by
  have hex : ∀ y, G.Adj x y → ∃ y', H.Adj x' y' ∧ e y ∈ limb H x' y' := by
    intro y hy
    have hne : x' ≠ e y := by
      rw [← he.1]; exact fun h => hy.ne (e.injective h)
    exact exists_toward hH hne
  have hex' : ∀ y', H.Adj x' y' → ∃ y, G.Adj x y ∧ e.symm y' ∈ limb G x y := by
    intro y' hy'
    have hne : x ≠ e.symm y' := by
      intro h
      apply hy'.ne
      rw [← he.1, h]; simp
    exact exists_toward hG hne
  have hle : ∀ y (hy : G.Adj x y) y' (hy' : H.Adj x' y'), e y ∈ limb H x' y' →
      (limb G x y).card ≤ (limb H x' y').card := by
    intro y hy y' hy' hey
    apply Finset.card_le_card_of_injOn e
    · intro z hz
      exact limb_map hG hH he hy hy' hey _ z hz rfl
    · exact e.injective.injOn
  have hle' : ∀ y' (hy' : H.Adj x' y') y (hy : G.Adj x y), e.symm y' ∈ limb G x y →
      (limb H x' y').card ≤ (limb G x y).card := by
    intro y' hy' y hy hey
    apply Finset.card_le_card_of_injOn e.symm
    · intro z hz
      exact limb_map hH hG he.symm hy' hy hey _ z hz rfl
    · exact e.symm.injective.injOn
  unfold rho
  rw [Multiset.map_map, Multiset.map_map]
  refine Multiset.map_eq_map_of_bij_of_nodup _ _ (nb G x).nodup (nb H x').nodup
    (fun y hy => Classical.choose (hex y (mem_nb.1 hy))) ?_ ?_ ?_ ?_
  · intro y hy
    exact mem_nb.2 (Classical.choose_spec (hex y (mem_nb.1 hy))).1
  · intro y1 hy1 y2 hy2 h
    have s1 := Classical.choose_spec (hex y1 (mem_nb.1 hy1))
    have s2 := Classical.choose_spec (hex y2 (mem_nb.1 hy2))
    rw [h] at s1
    obtain ⟨y0, hy0, hy0l⟩ := hex' _ s2.1
    have m1 := limb_map hH hG he.symm s2.1 hy0 hy0l _ _ s1.2 rfl
    have m2 := limb_map hH hG he.symm s2.1 hy0 hy0l _ _ s2.2 rfl
    simp only [Equiv.symm_apply_apply] at m1 m2
    have e1 := limb_disjoint hG (mem_nb.1 hy1) hy0 (self_mem_limb (mem_nb.1 hy1)) m1
    have e2 := limb_disjoint hG (mem_nb.1 hy2) hy0 (self_mem_limb (mem_nb.1 hy2)) m2
    rw [e1, e2]
  · intro y' hy'
    obtain ⟨y, hy, hyl⟩ := hex' y' (mem_nb.1 hy')
    refine ⟨y, mem_nb.2 hy, ?_⟩
    have s := Classical.choose_spec (hex y hy)
    have m := limb_map hG hH he hy s.1 s.2 _ _ hyl rfl
    simp only [Equiv.apply_symm_apply] at m
    exact limb_disjoint hH s.1 (mem_nb.1 hy') m (self_mem_limb (mem_nb.1 hy'))
  · intro y hy
    have hy0 := mem_nb.1 hy
    have s := Classical.choose_spec (hex y hy0)
    simp only [Function.comp]
    generalize Classical.choose (hex y hy0) = y' at s ⊢
    rw [sz_kap hG _ x y hy0 le_rfl, sz_kap hH _ x' y' s.1 le_rfl]
    apply le_antisymm (hle y hy0 y' s.1 s.2)
    obtain ⟨y0, hy0', hy0l⟩ := hex' y' s.1
    have m := limb_map hH hG he.symm s.1 hy0' hy0l _ _ s.2 rfl
    simp only [Equiv.symm_apply_apply] at m
    have e1 := limb_disjoint hG hy0 hy0' (self_mem_limb hy0) m
    subst e1
    exact hle' y' s.1 y hy0' hy0l


theorem delO_exists (t : ℕ) : ∃ C, DelO t C := by
  by_cases h : t = pt
  · exact ⟨0, Or.inl ⟨h, rfl⟩⟩
  · obtain ⟨c, hc⟩ := exists_del t h
    exact ⟨{c}, Or.inr ⟨c, hc, rfl⟩⟩

theorem delO_mem {t p : ℕ} {C : Multiset ℕ} (h : DelO t C) (hp : p ∈ C) : C = {p} ∧ Del t p := by
  rcases h with ⟨_, rfl⟩ | ⟨c, hc, rfl⟩
  · simp at hp
  · have : p = c := Multiset.mem_singleton.1 hp
    subst this
    exact ⟨rfl, hc⟩

theorem delO_card {t : ℕ} {C : Multiset ℕ} (h : DelO t C) : C.card ≤ 1 := by
  rcases h with ⟨_, rfl⟩ | ⟨c, _, rfl⟩ <;> simp

theorem rel_le {M M' C C' : Multiset ℕ} {β β' : ℕ} (hβ : β ∈ M) (hβ' : β' ∈ M')
    (E : M.erase β + C = M'.erase β' + C') :
    M - M' ≤ β ::ₘ C' ∧ M' - M ≤ β' ::ₘ C := by
  have h1 : M + C = β ::ₘ (M.erase β + C) := by
    rw [← Multiset.cons_add, Multiset.cons_erase hβ]
  have h2 : M' + C' = β' ::ₘ (M'.erase β' + C') := by
    rw [← Multiset.cons_add, Multiset.cons_erase hβ']
  have E2 : M + (β' ::ₘ C) = M' + (β ::ₘ C') := by
    rw [Multiset.add_cons, Multiset.add_cons, h1, h2, E, Multiset.cons_swap]
  constructor
  · rw [Multiset.le_iff_count]
    intro a
    have := congrArg (Multiset.count a) E2
    rw [Multiset.count_add, Multiset.count_add] at this
    rw [Multiset.count_sub]
    omega
  · rw [Multiset.le_iff_count]
    intro a
    have := congrArg (Multiset.count a) E2
    rw [Multiset.count_add, Multiset.count_add] at this
    rw [Multiset.count_sub]
    omega


theorem lemR (M M' : Multiset ℕ) (h2 : 2 ≤ M.card) (hsz : M.map sz = M'.map sz)
    (hG : ∀ β ∈ M, ∀ C, DelO β C → ∃ β' ∈ M', ∃ C', DelO β' C' ∧
      M.erase β + C = M'.erase β' + C')
    (hH : ∀ β' ∈ M', ∀ C', DelO β' C' → ∃ β ∈ M, ∃ C, DelO β C ∧
      M.erase β + C = M'.erase β' + C') : M = M' := by
  have hcard : M.card = M'.card := by simpa using congrArg Multiset.card hsz
  have F3 : M + (M' - M) = M' + (M - M') := by
    rw [Multiset.ext]
    intro a
    simp only [Multiset.count_add, Multiset.count_sub]
    omega
  have F4 : (M - M').card = (M' - M).card := by
    have := congrArg Multiset.card F3
    simp only [Multiset.card_add] at this
    omega
  have F5 : (M - M').map sz = (M' - M).map sz := by
    have := congrArg (Multiset.map sz) F3
    rw [Multiset.map_add, Multiset.map_add, hsz] at this
    exact (add_left_cancel this).symm
  have F2 : ∀ t, t ∈ M - M' → t ∉ M' - M := by
    intro t ht ht'
    rw [← Multiset.count_pos, Multiset.count_sub] at ht ht'
    omega
  by_contra hne
  have hP0 : M - M' ≠ 0 := by
    intro h0
    have h0' : M' - M = 0 := by
      rw [← Multiset.card_eq_zero, ← F4, h0]; rfl
    rw [h0, h0', add_zero, add_zero] at F3
    exact hne F3
  have hPpos : 0 < (M - M').card := Multiset.card_pos.2 hP0
  obtain ⟨β0, hβ0⟩ := Multiset.card_pos_iff_exists_mem.1 (by omega : 0 < M.card)
  have hPle : (M - M').card ≤ 2 := by
    obtain ⟨C, hC⟩ := delO_exists β0
    obtain ⟨β', hβ', C', hC', E⟩ := hG β0 hβ0 C hC
    have := Multiset.card_le_card (rel_le hβ0 hβ' E).1
    have := delO_card hC'
    rw [Multiset.card_cons] at *
    omega
  by_cases hP2 : (M - M').card = 2
  · -- every element of M lies in P, every element of M' lies in P'
    have hMP : ∀ β ∈ M, ∀ C, DelO β C → ∃ β' ∈ M', ∃ C', DelO β' C' ∧ M - M' = β ::ₘ C' := by
      intro β hβ C hC
      obtain ⟨β', hβ', C', hC', E⟩ := hG β hβ C hC
      refine ⟨β', hβ', C', hC', ?_⟩
      apply Multiset.eq_of_le_of_card_le (rel_le hβ hβ' E).1
      have := delO_card hC'
      rw [Multiset.card_cons]; omega
    have hM'P : ∀ β' ∈ M', β' ∈ M' - M := by
      intro β' hβ'
      obtain ⟨C', hC'⟩ := delO_exists β'
      obtain ⟨β, hβ, C, hC, E⟩ := hH β' hβ' C' hC'
      have : M' - M = β' ::ₘ C := by
        apply Multiset.eq_of_le_of_card_le (rel_le hβ hβ' E).2
        have := delO_card hC
        rw [Multiset.card_cons]; omega
      rw [this]; exact Multiset.mem_cons_self _ _
    have hdisj : ∀ t ∈ M, t ∉ M' := by
      intro t ht ht'
      obtain ⟨C, hC⟩ := delO_exists t
      obtain ⟨β', _, C', _, hP⟩ := hMP t ht C hC
      exact F2 t (by rw [hP]; exact Multiset.mem_cons_self _ _) (hM'P t ht')
    have hPM : M - M' = M := by
      rw [Multiset.ext]
      intro a
      rw [Multiset.count_sub]
      by_cases ha : a ∈ M
      · rw [Multiset.count_eq_zero_of_notMem (hdisj a ha)]; rfl
      · rw [Multiset.count_eq_zero_of_notMem ha, Nat.zero_sub]
    rw [hPM] at hP2 hMP
    obtain ⟨p1, p2, hM⟩ := Multiset.card_eq_two.1 hP2
    have hszM : ∀ β' ∈ M', sz β' = sz p1 ∨ sz β' = sz p2 := by
      intro β' hβ'
      have : sz β' ∈ M'.map sz := Multiset.mem_map_of_mem sz hβ'
      rw [← hsz, hM] at this
      simpa using this
    have hp1 : p1 ∈ M := by rw [hM]; simp
    have hp2 : p2 ∈ M := by rw [hM]; simp
    obtain ⟨C1, hC1⟩ := delO_exists p1
    obtain ⟨β1, hβ1, C1', hC1', hP1⟩ := hMP p1 hp1 C1 hC1
    obtain ⟨C2, hC2⟩ := delO_exists p2
    obtain ⟨β2, hβ2, C2', hC2', hP2'⟩ := hMP p2 hp2 C2 hC2
    have e1 : C1' = {p2} := by
      have : p1 ::ₘ ({p2} : Multiset ℕ) = p1 ::ₘ C1' := by rw [← hP1, hM]; rfl
      exact ((Multiset.cons_inj_right _).1 this).symm
    have e2 : C2' = {p1} := by
      have : p2 ::ₘ ({p1} : Multiset ℕ) = p2 ::ₘ C2' := by
        rw [← hP2', hM]; exact Multiset.cons_swap _ _ _
      exact ((Multiset.cons_inj_right _).1 this).symm
    have d1 := sz_del (delO_mem (p := p2) hC1' (by rw [e1]; simp)).2
    have d2 := sz_del (delO_mem (p := p1) hC2' (by rw [e2]; simp)).2
    rcases hszM β1 hβ1 with h | h <;> rcases hszM β2 hβ2 with h' | h' <;> omega
  · have hP1 : (M - M').card = 1 := by omega
    obtain ⟨p, hp⟩ := Multiset.card_eq_one.1 hP1
    obtain ⟨p', hp'⟩ := Multiset.card_eq_one.1 (F4 ▸ hP1)
    have hpp : p ≠ p' := by
      intro h
      apply F2 p (by rw [hp]; simp)
      rw [hp', h]; simp
    have hszp : sz p = sz p' := by
      rw [hp, hp'] at F5
      simpa using F5
    have G1 : ∀ β ∈ M, β ≠ p → ∀ C, DelO β C → C = {p'} := by
      intro β hβ hβp C hC
      obtain ⟨β', hβ', C', hC', E⟩ := hG β hβ C hC
      obtain ⟨l1, l2⟩ := rel_le hβ hβ' E
      rw [hp, Multiset.singleton_le, Multiset.mem_cons] at l1
      rw [hp', Multiset.singleton_le, Multiset.mem_cons] at l2
      have hpC' : p ∈ C' := l1.resolve_left (fun h => hβp h.symm)
      have d := sz_del (delO_mem hC' hpC').2
      have hβ'p' : p' ≠ β' := fun h => by rw [← h] at d; omega
      exact (delO_mem hC (l2.resolve_left hβ'p')).1
    have H1 : ∀ β' ∈ M', β' ≠ p' → ∀ C', DelO β' C' → C' = {p} := by
      intro β' hβ' hβp C' hC'
      obtain ⟨β, hβ, C, hC, E⟩ := hH β' hβ' C' hC'
      obtain ⟨l1, l2⟩ := rel_le hβ hβ' E
      rw [hp, Multiset.singleton_le, Multiset.mem_cons] at l1
      rw [hp', Multiset.singleton_le, Multiset.mem_cons] at l2
      have hpC : p' ∈ C := l2.resolve_left (fun h => hβp h.symm)
      have d := sz_del (delO_mem hC hpC).2
      have hβp2 : p ≠ β := fun h => by rw [← h] at d; omega
      exact (delO_mem hC' (l1.resolve_left hβp2)).1
    -- a common element
    obtain ⟨k, hk⟩ : ∃ k, Multiset.count k (M - M') < Multiset.count k M := by
      by_contra hcon
      push_neg at hcon
      have := Multiset.card_le_card (Multiset.le_iff_count.2 hcon)
      omega
    rw [Multiset.count_sub] at hk
    have hkM : k ∈ M := Multiset.count_pos.1 (by omega)
    have hkM' : k ∈ M' := Multiset.count_pos.1 (by omega)
    obtain ⟨C0, hC0⟩ := delO_exists k
    have hkp : k ≠ p := by
      intro h
      have := H1 k hkM' (h ▸ hpp) C0 hC0
      have d := sz_del (delO_mem (p := p) hC0 (by rw [this]; simp)).2
      rw [h] at d; omega
    have hkp' : k ≠ p' := by
      intro h
      have := G1 k hkM (h ▸ hpp.symm) C0 hC0
      have d := sz_del (delO_mem (p := p') hC0 (by rw [this]; simp)).2
      rw [h] at d; omega
    have a1 := G1 k hkM hkp C0 hC0
    have a2 := H1 k hkM' hkp' C0 hC0
    rw [a1] at a2
    exact hpp (Multiset.singleton_inj.1 a2).symm


theorem del_pair_pt {b c : ℕ} (hb : b ≠ pt) :
    Del (enc (b ::ₘ {pt})) c ↔ c = enc {b} ∨ ∃ c0, Del b c0 ∧ c = enc (c0 ::ₘ {pt}) := by
  have e1 : (b ::ₘ ({pt} : Multiset ℕ)).erase pt = {b} := by
    rw [Multiset.erase_cons_tail_of_mem (by simp)]; simp
  have e2 : (b ::ₘ ({pt} : Multiset ℕ)).erase b = {pt} := by simp
  rw [del_enc_iff]
  constructor
  · rintro (⟨_, rfl⟩ | ⟨a1, ha1, c0, hdel, rfl⟩)
    · left; show enc ((b ::ₘ {pt}).erase pt) = enc {b}; rw [e1]
    · rcases Multiset.mem_cons.1 ha1 with rfl | h
      · right; exact ⟨c0, hdel, by rw [e2]⟩
      · rw [Multiset.mem_singleton.1 h] at hdel
        exact absurd hdel not_del_pt
  · rintro (rfl | ⟨c0, hdel, rfl⟩)
    · left
      exact ⟨by show pt ∈ b ::ₘ ({pt} : Multiset ℕ); simp,
        by show enc {b} = enc ((b ::ₘ {pt}).erase pt); rw [e1]⟩
    · right
      exact ⟨b, Multiset.mem_cons_self _ _, c0, hdel, by rw [e2]⟩

theorem card_le_sum_sz (N : Multiset ℕ) : N.card ≤ (N.map sz).sum := by
  induction N using Multiset.induction_on with
  | empty => simp
  | cons a N ih =>
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons]
    have := sz_pos a
    omega

/-- structure of a two-step multiset equation with a size constraint -/
theorem twist_shape {m c c' : ℕ} {N N' : Multiset ℕ} (hNs : (N.map sz).sum = m)
    (hN's : (N'.map sz).sum = m) (hN : 2 ≤ N.card) (hc : sz c + 1 = m) (hc' : sz c' + 1 = m)
    (E : c ::ₘ N = c' ::ₘ N') (hne : N ≠ N') :
    c ≠ c' ∧ N = c' ::ₘ {pt} ∧ N' = c ::ₘ {pt} := by
  rcases Multiset.cons_eq_cons.1 E with ⟨_, h⟩ | ⟨hcc, cs, h1, h2⟩
  · exact absurd h hne
  · have hsum : (cs.map sz).sum = 1 := by
      rw [h1, Multiset.map_cons, Multiset.sum_cons] at hNs; omega
    have hcard : cs.card = 1 := by
      have := card_le_sum_sz cs
      rw [h1, Multiset.card_cons] at hN
      omega
    obtain ⟨k, hk⟩ := Multiset.card_eq_one.1 hcard
    have hk1 : k = pt := by
      rw [hk] at hsum
      exact sz_eq_one_iff.1 (by simpa using hsum)
    rw [hk, hk1] at h1 h2
    exact ⟨hcc, h1, h2⟩


theorem lem3a (m a a' : ℕ) (N N' : Multiset ℕ) (ha : sz a = m) (ha' : sz a' = m)
    (hN : 2 ≤ N.card) (hN' : 2 ≤ N'.card)
    (hNs : (N.map sz).sum = m) (hN's : (N'.map sz).sum = m)
    (iiiG : ∀ c, Del a c → ∃ c', Del a' c' ∧ c ::ₘ N = c' ::ₘ N')
    (iiiH : ∀ c', Del a' c' → ∃ c, Del a c ∧ c ::ₘ N = c' ::ₘ N')
    (iG : ∀ c, Del (enc N) c → ∃ c', Del (enc N') c' ∧
      ((a = a' ∧ c = c') ∨ (a = c' ∧ a' = c)))
    (iH : ∀ c', Del (enc N') c' → ∃ c, Del (enc N) c ∧
      ((a = a' ∧ c = c') ∨ (a = c' ∧ a' = c))) : a = a' ∧ N = N' := by
  have hm : 2 ≤ m := by have := card_le_sum_sz N; omega
  have hapt : a ≠ pt := fun h => by rw [h, sz_eq_one_iff.2 rfl] at ha; omega
  by_cases hNN : N = N'
  · refine ⟨?_, hNN⟩
    subst hNN
    by_contra hne
    have hNpt : enc N ≠ pt := by
      intro h
      have := enc_injective (h.trans rfl : enc N = enc 0)
      rw [this] at hN; simp at hN
    obtain ⟨c, hc⟩ := exists_del _ hNpt
    obtain ⟨c1, _, h1⟩ := iG c hc
    obtain ⟨c2, _, h2⟩ := iH c hc
    rcases h1 with ⟨h, _⟩ | ⟨_, h1⟩
    · exact hne h
    · rcases h2 with ⟨h, _⟩ | ⟨h2, _⟩
      · exact hne h
      · exact hne (h2.trans h1.symm)
  · exfalso
    obtain ⟨c0, hc0⟩ := exists_del a hapt
    obtain ⟨c0', hc0', E0⟩ := iiiG c0 hc0
    have s0 := sz_del hc0
    have s0' := sz_del hc0'
    obtain ⟨hbb, hNb, hN'b⟩ := twist_shape hNs hN's hN (by omega) (by omega) E0 hNN
    -- b := c0', b' := c0
    have hm3 : 3 ≤ m := by
      by_contra hcon
      have e1 : c0 = pt := sz_eq_one_iff.1 (by omega)
      have e2 : c0' = pt := sz_eq_one_iff.1 (by omega)
      exact hbb (e1.trans e2.symm)
    have hbpt : c0' ≠ pt := fun h => by rw [h, sz_eq_one_iff.2 rfl] at s0'; omega
    have hb'pt : c0 ≠ pt := fun h => by rw [h, sz_eq_one_iff.2 rfl] at s0; omega
    have allA : ∀ c, Del a c → c = c0 := by
      intro c hc
      obtain ⟨c', hc', E⟩ := iiiG c hc
      have s := sz_del hc
      have s' := sz_del hc'
      obtain ⟨_, _, h⟩ := twist_shape hNs hN's hN (by omega) (by omega) E hNN
      rw [hN'b] at h
      rcases pair_single h with ⟨h1, _⟩ | ⟨h2, _⟩
      · exact h1.symm
      · exact absurd h2 hb'pt
    have allA' : ∀ c', Del a' c' → c' = c0' := by
      intro c' hc'
      obtain ⟨c, hc, E⟩ := iiiH c' hc'
      have s := sz_del hc
      have s' := sz_del hc'
      obtain ⟨_, h, _⟩ := twist_shape hNs hN's hN (by omega) (by omega) E hNN
      rw [hNb] at h
      rcases pair_single h with ⟨h1, _⟩ | ⟨h2, _⟩
      · exact h1.symm
      · exact absurd h2 hbpt
    -- the card obtained by deleting the leaf at the centroid
    have hdG : Del (enc N) (enc {c0'}) := by rw [hNb]; exact (del_pair_pt hbpt).2 (Or.inl rfl)
    have hdH : Del (enc N') (enc {c0}) := by rw [hN'b]; exact (del_pair_pt hb'pt).2 (Or.inl rfl)
    have hne_shape : ∀ b1 b2 c, Del (enc (b2 ::ₘ {pt})) c → b2 ≠ pt → b1 ≠ b2 → enc {b1} ≠ c := by
      intro b1 b2 c hc hb2 hne h
      rcases (del_pair_pt hb2).1 hc with rfl | ⟨c1, _, rfl⟩
      · have := enc_injective h
        exact hne (by simpa using this)
      · have := congrArg Multiset.card (enc_injective h)
        simp at this
    have ha'eq : a' = enc {c0'} := by
      obtain ⟨c', hc', h⟩ := iG _ hdG
      rcases h with ⟨_, h⟩ | ⟨_, h⟩
      · rw [hN'b] at hc'
        exact absurd h (hne_shape c0' c0 c' hc' hb'pt (fun h => hbb h.symm))
      · exact h
    have haeq : a = enc {c0} := by
      obtain ⟨c, hc, h⟩ := iH _ hdH
      rcases h with ⟨_, h⟩ | ⟨h, _⟩
      · rw [hNb] at hc
        exact absurd h.symm (hne_shape c0 c0' c hc hbpt hbb)
      · exact h
    have p1 : c0 = pathc (m - 2) := by
      apply path_lemma (m - 2) c0 (by omega)
      intro c hc
      rw [← haeq] at hc
      exact allA c hc
    have p2 : c0' = pathc (m - 2) := by
      apply path_lemma (m - 2) c0' (by omega)
      intro c hc
      rw [← ha'eq] at hc
      exact allA' c hc
    exact hbb (p1.trans p2.symm)


theorem mem_rho {G : SimpleGraph V} {r : V} {a : ℕ} :
    a ∈ rho G r ↔ ∃ y, G.Adj r y ∧ kap G r y = a := by
  unfold rho
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, mem_nb.1 hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, mem_nb.2 hy, rfl⟩

theorem rho_erase {G : SimpleGraph V} {r y : V} (hry : G.Adj r y) :
    (rho G r).erase (kap G r y) = ((nb G r).erase y).val.map (kap G r) := by
  unfold rho
  rw [Finset.erase_val, Multiset.map_erase_of_mem _ _ (mem_nb.2 hry)]

theorem dec_kap {G : SimpleGraph V} (hG : G.IsTree) {p x : V} (hpx : G.Adj p x) :
    dec (kap G p x) = (rho G x).erase (kap G x p) := by
  rw [kap_unfold hG le_rfl hpx, dec_enc, rho_erase hpx.symm]

theorem rho_cons {G : SimpleGraph V} {r y : V} (hry : G.Adj r y) :
    rho G r = kap G r y ::ₘ (rho G r).erase (kap G r y) :=
  (Multiset.cons_erase (mem_rho.2 ⟨y, hry, rfl⟩)).symm

theorem card_univ_limbs {G : SimpleGraph V} (hG : G.IsTree) (x : V) :
    1 + ∑ y ∈ nb G x, (limb G x y).card = Fintype.card V := by
  have huniv : (Finset.univ : Finset V) = insert x ((nb G x).biUnion (fun y => limb G x y)) := by
    symm
    apply Finset.eq_univ_of_forall
    intro z
    by_cases hz : z = x
    · exact hz ▸ Finset.mem_insert_self _ _
    · obtain ⟨y, hy, hzy⟩ := exists_toward hG (x := x) (z := z) (fun h => hz h.symm)
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨y, mem_nb.2 hy, hzy⟩)
  rw [← Finset.card_univ, huniv, Finset.card_insert_of_notMem, Finset.card_biUnion, add_comm]
  · intro y hy y' hy' hne
    rw [Finset.mem_coe, mem_nb] at hy hy'
    rw [Function.onFun, Finset.disjoint_left]
    intro z hz hz'
    exact hne (limb_disjoint hG hy hy' hz hz')
  · simp only [Finset.mem_biUnion, not_exists, not_and]
    intro y _
    exact not_mem_limb_child

theorem sz_mem_rho {G : SimpleGraph V} (hG : G.IsTree) {r : V} {a : ℕ} (ha : a ∈ rho G r) :
    ∃ y, G.Adj r y ∧ kap G r y = a ∧ sz a = (limb G r y).card := by
  obtain ⟨y, hy, rfl⟩ := mem_rho.1 ha
  exact ⟨y, hy, rfl, sz_kap hG _ r y hy le_rfl⟩

/-- sizes of the limbs at a vertex, from the sizes seen in a leaf-deleted card -/
theorem limb_le_of_card {G : SimpleGraph V} (hG : G.IsTree) {v x : V} (hv : Leaf G v)
    (hx : x ≠ v) (B : ℕ) (hR : ∀ a ∈ rho (delV G v) x, sz a ≤ B) :
    ∀ y, G.Adj x y → (limb G x y).card ≤ B + 1 := by
  obtain ⟨y0, hy0, hvy0, C, hC, hrho⟩ := rho_card hG hv hx
  intro y hy
  rw [← sz_kap hG _ x y hy le_rfl]
  by_cases hyy : y = y0
  · subst hyy
    rcases hC with ⟨hpt, _⟩ | ⟨c, hdel, rfl⟩
    · rw [hpt, sz_eq_one_iff.2 rfl]; omega
    · have := sz_del hdel
      have := hR c (by rw [hrho]; simp)
      omega
  · have hmem : kap G x y ∈ rho (delV G v) x := by
      rw [hrho, rho_erase hy0]
      apply Multiset.mem_add.2
      left
      exact Multiset.mem_map_of_mem _ (Finset.mem_erase.2 ⟨hyy, mem_nb.2 hy⟩)
    have := hR _ hmem
    omega

theorem not_leaf_of_limbs {G : SimpleGraph V} (hG : G.IsTree) {c : V} (hV : 3 ≤ Fintype.card V)
    (hc : ∀ y, G.Adj c y → 2 * (limb G c y).card ≤ Fintype.card V) : 2 ≤ (nb G c).card := by
  have hsum := card_univ_limbs hG c
  by_contra hcon
  have hle : (nb G c).card ≤ 1 := by omega
  rcases Nat.lt_or_ge (nb G c).card 1 with h0 | h1
  · have : nb G c = ∅ := Finset.card_eq_zero.1 (by omega)
    rw [this] at hsum
    simp at hsum
    omega
  · obtain ⟨y, hy⟩ := Finset.card_eq_one.1 (by omega : (nb G c).card = 1)
    rw [hy] at hsum
    simp at hsum
    have := hc y (mem_nb.1 (by rw [hy]; simp))
    omega


theorem case1 {G : SimpleGraph V} {H : SimpleGraph W} (hV : 3 ≤ Fintype.card V)
    (hG : G.IsTree) (hH : H.IsTree) (σ : V ≃ W)
    (hdeg : ∀ v, (nb G v).card = (nb H (σ v)).card)
    (hci : ∀ v, ∃ e : V ≃ W, CardIso G H v (σ v) e) (c : V)
    (hc : ∀ y, G.Adj c y → 2 * (limb G c y).card + 2 ≤ Fintype.card V) :
    Nonempty (G ≃g H) := by
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr σ
  obtain ⟨ec, hec⟩ := hci c
  have hsz := sizes_eq hG hH hec
  have hc' : ∀ y', H.Adj (σ c) y' → 2 * (limb H (σ c) y').card + 2 ≤ Fintype.card V := by
    intro y' hy'
    have h1 : sz (kap H (σ c) y') ∈ (rho H (σ c)).map sz :=
      Multiset.mem_map_of_mem _ (mem_rho.2 ⟨y', hy', rfl⟩)
    rw [← hsz] at h1
    obtain ⟨a, ha, hsa⟩ := Multiset.mem_map.1 h1
    obtain ⟨y, hy, _, hs⟩ := sz_mem_rho hG ha
    have := hc y hy
    have hs' := sz_kap hH _ _ _ hy' le_rfl
    omega
  have h2c : 2 ≤ (nb G c).card :=
    not_leaf_of_limbs hG hV (fun y hy => by have := hc y hy; omega)
  have hnl : ∀ v, Leaf G v → c ≠ v := fun v hv h => by
    rw [h] at h2c; unfold Leaf at hv; omega
  have hcardsz : ∀ v, Leaf G v → ∀ a ∈ rho (delV G v) c, 2 * sz a + 2 ≤ Fintype.card V := by
    intro v hv a ha
    obtain ⟨y, hy, _, C, hC, hrho⟩ := rho_card hG hv (hnl v hv)
    rw [hrho] at ha
    rcases Multiset.mem_add.1 ha with h | h
    · obtain ⟨y1, hy1, _, hs⟩ := sz_mem_rho hG (Multiset.mem_of_mem_erase h)
      have := hc y1 hy1
      omega
    · obtain ⟨_, hdel⟩ := delO_mem hC h
      have := sz_del hdel
      have := hc y hy
      have hs := sz_kap hG _ c y hy le_rfl
      omega
  have key : ∀ v, Leaf G v → ∀ e : V ≃ W, CardIso G H v (σ v) e → e c = σ c := by
    intro v hv e he
    have hw : Leaf H (σ v) := by unfold Leaf; rw [← hdeg v]; exact hv
    have hxw : e c ≠ σ v := by
      rw [← he.1]; exact fun h => hnl v hv (e.injective h)
    by_contra hne
    have hR : ∀ a ∈ rho (delV H (σ v)) (e c), sz a ≤ (Fintype.card V - 2) / 2 := by
      intro a ha
      rw [he.rho_eq c] at ha
      have := hcardsz v hv a ha
      omega
    have hlimb := limb_le_of_card hH hw hxw _ hR
    obtain ⟨a, b, ha, hb, _, _, hcov, _⟩ := cov hH (x := σ c) (z := e c) (fun h => hne h.symm)
    have h1 := hlimb a ha
    have h2 := hc' b hb
    rw [← hcard] at hcov
    omega
  apply iso_of_rho_eq hG hH hcard (r := c) (r' := σ c)
  apply lemR _ _ (by unfold rho; simpa using h2c) hsz
  · intro β hβ C hC
    obtain ⟨y, hy, rfl⟩ := mem_rho.1 hβ
    obtain ⟨v, hv, _, hrho⟩ := exists_leaf_card hG hy hC
    obtain ⟨e, he⟩ := hci v
    have hw : Leaf H (σ v) := by unfold Leaf; rw [← hdeg v]; exact hv
    have hk := key v hv e he
    have hxw : σ c ≠ σ v := fun h => hnl v hv (σ.injective h)
    obtain ⟨y', hy', _, C', hC', hrho'⟩ := rho_card hH hw hxw
    refine ⟨kap H (σ c) y', mem_rho.2 ⟨y', hy', rfl⟩, C', hC', ?_⟩
    rw [← hrho, ← hrho', ← hk, he.rho_eq c]
  · intro β' hβ' C' hC'
    obtain ⟨y', hy', rfl⟩ := mem_rho.1 hβ'
    obtain ⟨w, hw, _, hrho'⟩ := exists_leaf_card hH hy' hC'
    obtain ⟨v, rfl⟩ := σ.surjective w
    have hv : Leaf G v := by unfold Leaf; rw [hdeg v]; exact hw
    obtain ⟨e, he⟩ := hci v
    have hk := key v hv e he
    obtain ⟨y, hy, _, C, hC, hrho⟩ := rho_card hG hv (hnl v hv)
    refine ⟨kap G c y, mem_rho.2 ⟨y, hy, rfl⟩, C, hC, ?_⟩
    rw [← hrho, ← hrho', ← hk, he.rho_eq c]


theorem rho_deep {G : SimpleGraph V} (hG : G.IsTree) {v r y : V} (hry : G.Adj r y)
    (hvy : v ∈ limb G r y) (hne : v ≠ y) :
    rho (delV G v) r = kap (delV G v) r y ::ₘ (rho G r).erase (kap G r y) := by
  have hrv : r ≠ v := fun h => not_mem_limb_child (h ▸ hvy)
  have hnadj : v ∉ nb G r := fun h =>
    hne (limb_disjoint hG (mem_nb.1 h) hry (self_mem_limb (mem_nb.1 h)) hvy)
  unfold rho
  rw [nb_delV hrv, Finset.erase_eq_of_notMem hnadj,
    children_b hG (Finset.Subset.refl _) (mem_nb.2 hry) hvy]

theorem leaf_ne_of_big {G : SimpleGraph V} (hG : G.IsTree) {v r s : V} (hv : Leaf G v)
    (hrs : G.Adj r s) (hbig : 2 ≤ (limb G r s).card) : v ≠ s := by
  rintro rfl
  have h1 := kap_leaf hG hv hrs
  have h2 := sz_kap hG _ r v hrs le_rfl
  rw [h1, sz_eq_one_iff.2 rfl] at h2
  omega

theorem mem_rho_delV_of_notMem {G : SimpleGraph V} (hG : G.IsTree) {v r y : V} (hrv : r ≠ v)
    (hry : G.Adj r y) (hvy : v ∉ limb G r y) : kap G r y ∈ rho (delV G v) r := by
  unfold rho
  rw [Multiset.mem_map]
  refine ⟨y, ?_, kap_delV_of_notMem hG v _ r y hry le_rfl hvy⟩
  rw [nb_delV hrv]
  exact Finset.mem_erase.2 ⟨fun h => hvy (h ▸ self_mem_limb hry), mem_nb.2 hry⟩

theorem bic_symm {G : SimpleGraph V} (hG : G.IsTree) {t s : V} (hts : G.Adj t s)
    (hh : 2 * (limb G t s).card = Fintype.card V) : 2 * (limb G s t).card = Fintype.card V := by
  have := card_limb_add hG hts
  omega

theorem bic_small {G : SimpleGraph V} (hG : G.IsTree) {t s y : V} (hts : G.Adj t s)
    (hh : 2 * (limb G t s).card = Fintype.card V) (hty : G.Adj t y) (hys : y ≠ s) :
    2 * (limb G t y).card + 2 ≤ Fintype.card V := by
  have h1 := limb_card_lt hG hts.symm hty hys
  have h2 := bic_symm hG hts hh
  omega

theorem bic_unique {G : SimpleGraph V} (hG : G.IsTree) {t s z : V} (hts : G.Adj t s)
    (hh : 2 * (limb G t s).card = Fintype.card V)
    (hz : ∀ y, G.Adj z y → 2 * (limb G z y).card ≤ Fintype.card V) : z = t ∨ z = s := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨a, b, ha, hb, _, _, hcov, hcov'⟩ := cov hG (x := t) (z := z) hcon.1.symm
  have h1 := hz a ha
  by_cases hbs : b = s
  · subst hbs
    have := hcov' (fun h => hcon.2 h.symm)
    omega
  · have := bic_small hG hts hh hb hbs
    omega


theorem pl2 {G : SimpleGraph V} {H : SimpleGraph W} (hG : G.IsTree) (hH : H.IsTree)
    (hV : 3 ≤ Fintype.card V) (hcard : Fintype.card V = Fintype.card W)
    {v : V} {w : W} {e : V ≃ W} (he : CardIso G H v w e) (hv : Leaf G v) (hw : Leaf H w)
    {r s : V} (hrs : G.Adj r s) (hh : 2 * (limb G r s).card = Fintype.card V)
    (hvl : v ∈ limb G r s) {d₁ d₂ : W} (hd : H.Adj d₁ d₂)
    (hdh : 2 * (limb H d₁ d₂).card = Fintype.card W) :
    ∃ r' s', ((r' = d₁ ∧ s' = d₂) ∨ (r' = d₂ ∧ s' = d₁)) ∧ w ∈ limb H r' s' ∧ w ≠ s' ∧ v ≠ s ∧
      kap (delV G v) r s ::ₘ (rho G r).erase (kap G r s) =
        kap (delV H w) r' s' ::ₘ (rho H r').erase (kap H r' s') := by
  have hbig : 2 ≤ (limb G r s).card := by omega
  have hvs : v ≠ s := leaf_ne_of_big hG hv hrs hbig
  have hrv : r ≠ v := fun h => not_mem_limb_child (h ▸ hvl)
  have hrho := rho_deep hG hrs hvl hvs
  have hdel := del_kap hG hv _ r s hrs le_rfl hvl hvs
  have hsizes : ∀ a ∈ rho (delV G v) r, 2 * sz a + 2 ≤ Fintype.card V := by
    intro a ha
    rw [hrho, Multiset.mem_cons] at ha
    rcases ha with rfl | ha
    · have := sz_del hdel
      have := sz_kap hG _ r s hrs le_rfl
      omega
    · rw [rho_erase hrs, Multiset.mem_map] at ha
      obtain ⟨y, hy, rfl⟩ := ha
      rw [Finset.mem_val, Finset.mem_erase, mem_nb] at hy
      have := bic_small hG hrs hh hy.2 hy.1
      have := sz_kap hG _ r y hy.2 le_rfl
      omega
  have hxw : e r ≠ w := by
    rw [← he.1]; exact fun h => hrv (e.injective h)
  have hR : ∀ a ∈ rho (delV H w) (e r), sz a ≤ (Fintype.card V - 2) / 2 := by
    intro a ha
    rw [he.rho_eq r] at ha
    have := hsizes a ha
    omega
  have hlimb := limb_le_of_card hH hw hxw _ hR
  have hx' : e r = d₁ ∨ e r = d₂ := by
    apply bic_unique hH hd hdh
    intro y hy
    have := hlimb y hy
    omega
  have main : ∀ r' s', H.Adj r' s' → 2 * (limb H r' s').card = Fintype.card W → e r = r' →
      w ∈ limb H r' s' ∧ w ≠ s' ∧
      kap (delV G v) r s ::ₘ (rho G r).erase (kap G r s) =
        kap (delV H w) r' s' ::ₘ (rho H r').erase (kap H r' s') := by
    intro r' s' hr's' hh' her
    subst her
    have hwl : w ∈ limb H (e r) s' := by
      by_contra hcon
      have hmem := mem_rho_delV_of_notMem hH hxw hr's' hcon
      have := hR _ hmem
      have := sz_kap hH _ (e r) s' hr's' le_rfl
      omega
    have hws : w ≠ s' := leaf_ne_of_big hH hw hr's' (by omega)
    refine ⟨hwl, hws, ?_⟩
    rw [← hrho, ← rho_deep hH hr's' hwl hws, he.rho_eq r]
  rcases hx' with h | h
  · obtain ⟨m1, m2, m3⟩ := main d₁ d₂ hd hdh h
    exact ⟨d₁, d₂, Or.inl ⟨rfl, rfl⟩, m1, m2, hvs, m3⟩
  · obtain ⟨m1, m2, m3⟩ := main d₂ d₁ hd.symm (bic_symm hH hd hdh) h
    exact ⟨d₂, d₁, Or.inr ⟨rfl, rfl⟩, m1, m2, hvs, m3⟩


theorem rho_eq_cons_dec {G : SimpleGraph V} (hG : G.IsTree) {t s : V} (hts : G.Adj t s) :
    rho G t = kap G t s ::ₘ dec (kap G s t) := by
  rw [dec_kap hG hts.symm]; exact rho_cons hts

theorem case2 {G : SimpleGraph V} {H : SimpleGraph W} (hV : 3 ≤ Fintype.card V)
    (hG : G.IsTree) (hH : H.IsTree) (σ : V ≃ W)
    (hdeg : ∀ v, (nb G v).card = (nb H (σ v)).card)
    (hci : ∀ v, ∃ e : V ≃ W, CardIso G H v (σ v) e) (c₁ c₂ : V) (h12 : G.Adj c₁ c₂)
    (hhalf : 2 * (limb G c₁ c₂).card = Fintype.card V) : Nonempty (G ≃g H) := by
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr σ
  obtain ⟨e1, he1⟩ := hci c₁
  have hsz := sizes_eq hG hH he1
  have h1 : sz (kap G c₁ c₂) ∈ (rho H (σ c₁)).map sz := by
    rw [← hsz]; exact Multiset.mem_map_of_mem _ (mem_rho.2 ⟨c₂, h12, rfl⟩)
  obtain ⟨a', ha', hsa'⟩ := Multiset.mem_map.1 h1
  obtain ⟨d₂, hd, rfl, hs'⟩ := sz_mem_rho hH ha'
  have hdh : 2 * (limb H (σ c₁) d₂).card = Fintype.card W := by
    have := sz_kap hG _ c₁ c₂ h12 le_rfl
    omega
  generalize σ c₁ = d₁ at hd hdh
  let cc : Bool → V := fun i => cond i c₁ c₂
  let dd : Bool → W := fun j => cond j d₁ d₂
  have hcc : ∀ i, G.Adj (cc (!i)) (cc i) ∧
      2 * (limb G (cc (!i)) (cc i)).card = Fintype.card V := by
    intro i
    cases i
    · exact ⟨h12, hhalf⟩
    · exact ⟨h12.symm, bic_symm hG h12 hhalf⟩
  have hdd : ∀ j, H.Adj (dd (!j)) (dd j) ∧
      2 * (limb H (dd (!j)) (dd j)).card = Fintype.card W := by
    intro j
    cases j
    · exact ⟨hd, hdh⟩
    · exact ⟨hd.symm, bic_symm hH hd hdh⟩
  have hdecx : ∀ i, dec (kap G (cc i) (cc (!i))) =
      (rho G (cc (!i))).erase (kap G (cc (!i)) (cc i)) := fun i => dec_kap hG (hcc i).1.symm
  have hdecy : ∀ j, dec (kap H (dd j) (dd (!j))) =
      (rho H (dd (!j))).erase (kap H (dd (!j)) (dd j)) := fun j => dec_kap hH (hdd j).1.symm
  have hleaf : ∀ v, Leaf G v ↔ Leaf H (σ v) := fun v => by unfold Leaf; rw [hdeg v]
  -- the per-leaf statement in Boolean form
  have per : ∀ v, Leaf G v → ∀ i, v ∈ limb G (cc (!i)) (cc i) →
      ∃ j, σ v ∈ limb H (dd (!j)) (dd j) ∧ σ v ≠ dd j ∧ v ≠ cc i ∧
        kap (delV G v) (cc (!i)) (cc i) ::ₘ dec (kap G (cc i) (cc (!i))) =
          kap (delV H (σ v)) (dd (!j)) (dd j) ::ₘ dec (kap H (dd j) (dd (!j))) := by
    intro v hv i hvl
    obtain ⟨e, he⟩ := hci v
    obtain ⟨r', s', hrs', m1, m2, m3, m4⟩ := pl2 hG hH hV hcard he hv ((hleaf v).1 hv)
      (hcc i).1 (hcc i).2 hvl hd hdh
    rcases hrs' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨false, m1, m2, m3, by rw [hdecx i, hdecy false]; exact m4⟩
    · exact ⟨true, m1, m2, m3, by rw [hdecx i, hdecy true]; exact m4⟩
  have hB := lemB (limb G c₁ c₂).card (fun i => kap G (cc (!i)) (cc i))
    (fun j => kap H (dd (!j)) (dd j))
    (fun i => by
      have := sz_kap hG _ _ _ (hcc i).1 le_rfl
      have := (hcc i).2
      show sz (kap G (cc (!i)) (cc i)) = _
      omega)
    (fun j => by
      have := sz_kap hH _ _ _ (hdd j).1 le_rfl
      have := (hdd j).2
      show sz (kap H (dd (!j)) (dd j)) = _
      omega)
    (by
      intro i c hc
      obtain ⟨v, hv, hvl, _, hk⟩ := exists_leaf_of_del hG _ _ _ c (hcc i).1 le_rfl hc
      obtain ⟨j, m1, m2, _, m4⟩ := per v hv i hvl
      refine ⟨j, kap (delV H (σ v)) (dd (!j)) (dd j),
        del_kap hH ((hleaf v).1 hv) _ _ _ (hdd j).1 le_rfl m1 m2, ?_⟩
      show c ::ₘ dec (kap G (cc (!(!i))) (cc (!i))) = _ ::ₘ dec (kap H (dd (!(!j))) (dd (!j)))
      rw [Bool.not_not, Bool.not_not, ← hk]
      exact m4)
    (by
      intro j c' hc'
      obtain ⟨w, hw, hwl, _, hk⟩ := exists_leaf_of_del hH _ _ _ c' (hdd j).1 le_rfl hc'
      obtain ⟨v, rfl⟩ := σ.surjective w
      have hv : Leaf G v := (hleaf v).2 hw
      have hi : ∃ i, v ∈ limb G (cc (!i)) (cc i) := by
        by_cases h : v ∈ limb G c₁ c₂
        · exact ⟨false, h⟩
        · exact ⟨true, (limb_compl hG h12).2 h⟩
      obtain ⟨i, hvl⟩ := hi
      obtain ⟨j', m1, m2, m3, m4⟩ := per v hv i hvl
      have hjj : j' = j := by
        by_contra hne
        have hj' : j' = !j := by cases j <;> cases j' <;> simp_all
        rw [hj', Bool.not_not] at m1
        exact (limb_compl hH (hdd j).1).1 m1 hwl
      subst hjj
      refine ⟨i, kap (delV G v) (cc (!i)) (cc i),
        del_kap hG hv _ _ _ (hcc i).1 le_rfl hvl m3, ?_⟩
      show _ ::ₘ dec (kap G (cc (!(!i))) (cc (!i))) = c' ::ₘ dec (kap H (dd (!(!j'))) (dd (!j')))
      rw [Bool.not_not, Bool.not_not, ← hk]
      exact m4)
  rcases hB with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · apply iso_of_rho_eq hG hH hcard (r := c₁) (r' := d₁)
    rw [rho_eq_cons_dec hG h12, rho_eq_cons_dec hH hd]
    have e1' : kap G c₂ c₁ = kap H d₂ d₁ := e1
    have e2' : kap G c₁ c₂ = kap H d₁ d₂ := e2
    rw [e1', e2']
  · apply iso_of_rho_eq hG hH hcard (r := c₁) (r' := d₂)
    rw [rho_eq_cons_dec hG h12, rho_eq_cons_dec hH hd.symm]
    have e1' : kap G c₂ c₁ = kap H d₁ d₂ := e1
    have e2' : kap G c₁ c₂ = kap H d₂ d₁ := e2
    rw [e1', e2']


/-- general identification of the image of a vertex under a card isomorphism -/
theorem ident {G : SimpleGraph V} {H : SimpleGraph W} (hH : H.IsTree)
    (hcard : Fintype.card V = Fintype.card W)
    {v : V} {w : W} {e : V ≃ W} (he : CardIso G H v w e) (hw : Leaf H w)
    {r : V} (hrv : r ≠ v) {r' : W} (B B' : ℕ)
    (hB : ∀ a ∈ rho (delV G v) r, sz a ≤ B)
    (hB' : ∀ y', H.Adj r' y' → (limb H r' y').card ≤ B')
    (hlt : B + 1 + B' < Fintype.card V) : e r = r' := by
  have hxw : e r ≠ w := by
    rw [← he.1]; exact fun h => hrv (e.injective h)
  by_contra hne
  have hR : ∀ a ∈ rho (delV H w) (e r), sz a ≤ B := by
    intro a ha
    rw [he.rho_eq r] at ha
    exact hB a ha
  have hlimb := limb_le_of_card hH hw hxw _ hR
  obtain ⟨a, b, ha, hb, _, _, hcov, _⟩ := cov hH (x := r') (z := e r) (fun h => hne h.symm)
  have h1 := hlimb a ha
  have h2 := hB' b hb
  rw [← hcard] at hcov
  omega

/-- a vertex whose limbs are almost as small as those of a centroid is adjacent to it -/
theorem near_centroid {H : SimpleGraph W} (hH : H.IsTree) {r' z : W} (B B' : ℕ)
    (hB' : ∀ y', H.Adj r' y' → (limb H r' y').card ≤ B')
    (hz : ∀ y, H.Adj z y → (limb H z y).card ≤ B)
    (hsum : B + B' = Fintype.card W) (hzr : z ≠ r') :
    H.Adj r' z ∧ (limb H r' z).card = B' := by
  obtain ⟨a, b, ha, hb, _, _, hcov, hcov'⟩ := cov hH (x := r') (z := z) hzr.symm
  have h1 := hz a ha
  have h2 := hB' b hb
  have hbz : b = z := by
    by_contra hbz
    have := hcov' hbz
    omega
  subst hbz
  exact ⟨hb, by omega⟩

theorem rho_eq_cons_dec' {G G' : SimpleGraph V} (hG : G.IsTree) (hle : G' ≤ G) {t s : V}
    (hts : G'.Adj t s) : rho G' t = kap G' t s ::ₘ dec (kap G' s t) := by
  rw [kap_unfold hG hle (hle hts).symm, dec_enc]
  unfold rho
  rw [Finset.erase_val, Multiset.map_erase_of_mem _ _ (mem_nb.2 hts)]
  exact (Multiset.cons_erase (Multiset.mem_map_of_mem _ (mem_nb.2 hts))).symm

/-- sizes of the children of a code are bounded by the size of the code -/
theorem sz_lt_of_mem_dec {t a : ℕ} (ha : a ∈ dec t) : sz a + 1 ≤ sz t := by
  rw [sz_eq t]
  have := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem sz ha)
  omega

/-- cancellation of the unique largest element -/
theorem cons_cancel_big {a a' : ℕ} {D D' : Multiset ℕ} (h : a ::ₘ D = a' ::ₘ D')
    (hD : ∀ b ∈ D, sz b < sz a') (hD' : ∀ b ∈ D', sz b < sz a) : a = a' ∧ D = D' := by
  rcases Multiset.cons_eq_cons.1 h with ⟨h1, h2⟩ | ⟨_, cs, h1, h2⟩
  · exact ⟨h1, h2⟩
  · exfalso
    have := hD a' (by rw [h1]; exact Multiset.mem_cons_self _ _)
    omega


/-- an odd centroid `c` with a unique heaviest branch at `c₁` -/
def OC (G : SimpleGraph V) (c c₁ : V) : Prop :=
  G.Adj c c₁ ∧ 2 * (limb G c c₁).card + 1 = Fintype.card V ∧
    ∀ y, G.Adj c y → y ≠ c₁ → 2 * (limb G c y).card + 3 ≤ Fintype.card V

theorem OC.le {G : SimpleGraph V} {c c₁ : V} (h : OC G c c₁) :
    ∀ y, G.Adj c y → (limb G c y).card ≤ (Fintype.card V - 1) / 2 := by
  intro y hy
  by_cases hyc : y = c₁
  · rw [hyc]; have := h.2.1; omega
  · have := h.2.2 y hy hyc; omega

theorem pl3a_in {G : SimpleGraph V} {H : SimpleGraph W} (hG : G.IsTree) (hH : H.IsTree)
    (hV : 5 ≤ Fintype.card V) (hcard : Fintype.card V = Fintype.card W)
    {v : V} {w : W} {e : V ≃ W} (he : CardIso G H v w e) (hv : Leaf G v) (hw : Leaf H w)
    {c c₁ : V} {c' c₁' : W} (hoc : OC G c c₁) (hoc' : OC H c' c₁')
    (hvl : v ∈ limb G c c₁) :
    w ∈ limb H c' c₁' ∧ v ≠ c₁ ∧ w ≠ c₁' ∧
      kap (delV G v) c c₁ ::ₘ (rho G c).erase (kap G c c₁) =
        kap (delV H w) c' c₁' ::ₘ (rho H c').erase (kap H c' c₁') := by
  have h2m := hoc.2.1
  have h2m' := hoc'.2.1
  have hvc₁ : v ≠ c₁ := leaf_ne_of_big hG hv hoc.1 (by omega)
  have hcv : c ≠ v := fun h => not_mem_limb_child (h ▸ hvl)
  have hrho := rho_deep hG hoc.1 hvl hvc₁
  have hdel := del_kap hG hv _ c c₁ hoc.1 le_rfl hvl hvc₁
  have hB : ∀ a ∈ rho (delV G v) c, sz a ≤ (Fintype.card V - 3) / 2 := by
    intro a ha
    rw [hrho, Multiset.mem_cons] at ha
    rcases ha with rfl | ha
    · have := sz_del hdel
      have := sz_kap hG _ c c₁ hoc.1 le_rfl
      omega
    · rw [rho_erase hoc.1, Multiset.mem_map] at ha
      obtain ⟨y, hy, rfl⟩ := ha
      rw [Finset.mem_val, Finset.mem_erase, mem_nb] at hy
      have := hoc.2.2 y hy.2 hy.1
      have := sz_kap hG _ c y hy.2 le_rfl
      omega
  have hB' : ∀ y', H.Adj c' y' → (limb H c' y').card ≤ (Fintype.card V - 1) / 2 := by
    intro y' hy'; have := hoc'.le y' hy'; rw [hcard]; exact this
  have hec : e c = c' := ident hH hcard he hw hcv _ _ hB hB' (by omega)
  subst hec
  have hxw : e c ≠ w := by
    rw [← he.1]; exact fun h => hcv (e.injective h)
  have hwl : w ∈ limb H (e c) c₁' := by
    by_contra hcon
    have hmem := mem_rho_delV_of_notMem hH hxw hoc'.1 hcon
    rw [he.rho_eq c] at hmem
    have := hB _ hmem
    have := sz_kap hH _ (e c) c₁' hoc'.1 le_rfl
    omega
  have hwc₁ : w ≠ c₁' := leaf_ne_of_big hH hw hoc'.1 (by omega)
  refine ⟨hwl, hvc₁, hwc₁, ?_⟩
  rw [← hrho, ← rho_deep hH hoc'.1 hwl hwc₁, he.rho_eq c]


theorem pl3a_out {G : SimpleGraph V} {H : SimpleGraph W} (hG : G.IsTree) (hH : H.IsTree)
    (hV : 5 ≤ Fintype.card V) (hcard : Fintype.card V = Fintype.card W)
    {v : V} {w : W} {e : V ≃ W} (he : CardIso G H v w e) (hv : Leaf G v) (hw : Leaf H w)
    {c c₁ : V} {c' c₁' : W} (hoc : OC G c c₁) (hoc' : OC H c' c₁')
    (hvl : v ∉ limb G c c₁) (hvc : v ≠ c) :
    w ∉ limb H c' c₁' ∧ w ≠ c' ∧
      ((kap G c c₁ = kap H c' c₁' ∧ kap (delV G v) c₁ c = kap (delV H w) c₁' c') ∨
       (kap G c c₁ = kap (delV H w) c₁' c' ∧ kap H c' c₁' = kap (delV G v) c₁ c)) := by
  have h2m := hoc.2.1
  have h2m' := hoc'.2.1
  have hv' : v ∈ limb G c₁ c := (limb_compl hG hoc.1).2 hvl
  have hc₁v : c₁ ≠ v := fun h => hvl (h ▸ self_mem_limb hoc.1)
  have hadj' : (delV G v).Adj c c₁ := ⟨hoc.1, hvc.symm, hc₁v⟩
  have hrho := rho_eq_cons_dec' hG (delV_le G v) hadj'
  rw [kap_delV_of_notMem hG v _ c c₁ hoc.1 le_rfl hvl] at hrho
  have hdel := del_kap hG hv _ c₁ c hoc.1.symm le_rfl hv' hvc
  have hsa : sz (kap G c c₁) = (Fintype.card V - 1) / 2 := by
    have := sz_kap hG _ c c₁ hoc.1 le_rfl; omega
  have hscd : sz (kap (delV G v) c₁ c) = (Fintype.card V - 1) / 2 := by
    have := sz_del hdel
    have := sz_kap hG _ c₁ c hoc.1.symm le_rfl
    have := card_limb_add hG hoc.1
    omega
  have hsa' : sz (kap H c' c₁') = (Fintype.card V - 1) / 2 := by
    have := sz_kap hH _ c' c₁' hoc'.1 le_rfl; omega
  have hR0 : ∀ a ∈ rho (delV G v) c, sz a ≤ (Fintype.card V - 1) / 2 := by
    intro a ha
    rw [hrho, Multiset.mem_cons] at ha
    rcases ha with rfl | ha
    · omega
    · have := sz_lt_of_mem_dec ha; omega
  have hxw : e c ≠ w := by
    rw [← he.1]; exact fun h => hvc (e.injective h).symm
  have hR : ∀ a ∈ rho (delV H w) (e c), sz a ≤ (Fintype.card V - 1) / 2 := by
    intro a ha
    rw [he.rho_eq c] at ha
    exact hR0 a ha
  have hlimb := limb_le_of_card hH hw hxw _ hR
  have hB' : ∀ y', H.Adj c' y' → (limb H c' y').card ≤ (Fintype.card V - 1) / 2 := by
    intro y' hy'; have := hoc'.le y' hy'; rw [hcard]; exact this
  by_cases hx : e c = c'
  · subst hx
    have hwout : w ∉ limb H (e c) c₁' := by
      intro hin
      have hwc₁ : w ≠ c₁' := leaf_ne_of_big hH hw hoc'.1 (by omega)
      have h1 := rho_deep hH hoc'.1 hin hwc₁
      have hd1 := del_kap hH hw _ (e c) c₁' hoc'.1 le_rfl hin hwc₁
      have hmem : kap G c c₁ ∈ rho (delV H w) (e c) := by
        rw [he.rho_eq c, hrho]; exact Multiset.mem_cons_self _ _
      rw [h1, Multiset.mem_cons] at hmem
      rcases hmem with h | h
      · have := sz_del hd1
        rw [← h] at this
        omega
      · rw [rho_erase hoc'.1, Multiset.mem_map] at h
        obtain ⟨y, hy, hky⟩ := h
        rw [Finset.mem_val, Finset.mem_erase, mem_nb] at hy
        have := hoc'.2.2 y hy.2 hy.1
        have := sz_kap hH _ (e c) y hy.2 le_rfl
        rw [hky] at this
        omega
    have hw' : w ∈ limb H c₁' (e c) := (limb_compl hH hoc'.1).2 hwout
    have hc₁w : c₁' ≠ w := fun h => hwout (h ▸ self_mem_limb hoc'.1)
    have hadjH : (delV H w).Adj (e c) c₁' := ⟨hoc'.1, hxw, hc₁w⟩
    have hrhoH := rho_eq_cons_dec' hH (delV_le H w) hadjH
    rw [kap_delV_of_notMem hH w _ (e c) c₁' hoc'.1 le_rfl hwout, he.rho_eq c, hrho] at hrhoH
    have hdelH := del_kap hH hw _ c₁' (e c) hoc'.1.symm le_rfl hw' hxw.symm
    have hscd' : sz (kap (delV H w) c₁' (e c)) = (Fintype.card V - 1) / 2 := by
      have := sz_del hdelH
      have := sz_kap hH _ c₁' (e c) hoc'.1.symm le_rfl
      have := card_limb_add hH hoc'.1
      omega
    obtain ⟨e1, e2⟩ := cons_cancel_big hrhoH
      (fun b hb => by have := sz_lt_of_mem_dec hb; omega)
      (fun b hb => by have := sz_lt_of_mem_dec hb; omega)
    refine ⟨hwout, hxw.symm, Or.inl ⟨e1, ?_⟩⟩
    rw [← enc_dec (kap (delV G v) c₁ c), e2, enc_dec]
  · obtain ⟨hadj, hsize⟩ := near_centroid hH ((Fintype.card V - 1) / 2 + 1)
      ((Fintype.card V - 1) / 2) hB' hlimb (by omega) hx
    have hxc₁ : e c = c₁' := by
      by_contra hne
      have := hoc'.2.2 _ hadj hne
      omega
    rw [hxc₁] at hxw hR
    have hwin : w ∈ limb H c₁' c' := by
      by_contra hout
      have hmem := mem_rho_delV_of_notMem hH hxw hoc'.1.symm hout
      have := hR _ hmem
      have := sz_kap hH _ c₁' c' hoc'.1.symm le_rfl
      have := card_limb_add hH hoc'.1
      omega
    have hwc' : w ≠ c' := leaf_ne_of_big hH hw hoc'.1.symm (by
      have := card_limb_add hH hoc'.1; omega)
    have h1 := rho_deep hH hoc'.1.symm hwin hwc'
    rw [← dec_kap hH hoc'.1, ← hxc₁, he.rho_eq c, hrho] at h1
    have hdelH := del_kap hH hw _ c₁' c' hoc'.1.symm le_rfl hwin hwc'
    have hscd' : sz (kap (delV H w) c₁' c') = (Fintype.card V - 1) / 2 := by
      have := sz_del hdelH
      have := sz_kap hH _ c₁' c' hoc'.1.symm le_rfl
      have := card_limb_add hH hoc'.1
      omega
    rw [hxc₁] at h1
    obtain ⟨e1, e2⟩ := cons_cancel_big h1
      (fun b hb => by have := sz_lt_of_mem_dec hb; omega)
      (fun b hb => by have := sz_lt_of_mem_dec hb; omega)
    refine ⟨(limb_compl hH hoc'.1).1 hwin, hwc', Or.inr ⟨e1, ?_⟩⟩
    rw [← enc_dec (kap H c' c₁'), ← e2, enc_dec]


theorem OC.other {G : SimpleGraph V} (hG : G.IsTree) {c c₁ : V} (hoc : OC G c c₁) :
    ∃ y, G.Adj c y ∧ y ≠ c₁ := by
  have hsum := card_univ_limbs hG c
  rw [← Finset.add_sum_erase _ _ (mem_nb.2 hoc.1)] at hsum
  by_contra hcon
  push_neg at hcon
  have hempty : (nb G c).erase c₁ = ∅ := by
    ext y
    simp only [Finset.mem_erase, mem_nb, Finset.notMem_empty, iff_false, not_and]
    intro hne hy
    exact hne (hcon y hy)
  rw [hempty, Finset.sum_empty] at hsum
  have h1 := hoc.2.1
  have : 0 < (limb G c c₁).card := Finset.card_pos.2 ⟨c₁, self_mem_limb hoc.1⟩
  omega

theorem OC.five {G : SimpleGraph V} (hG : G.IsTree) {c c₁ : V} (hoc : OC G c c₁) :
    5 ≤ Fintype.card V := by
  obtain ⟨y, hy, hne⟩ := hoc.other hG
  have := hoc.2.2 y hy hne
  have : 0 < (limb G c y).card := Finset.card_pos.2 ⟨y, self_mem_limb hy⟩
  omega

theorem OC.not_leaf {G : SimpleGraph V} (hG : G.IsTree) {c c₁ : V} (hoc : OC G c c₁) {v : V}
    (hv : Leaf G v) : v ≠ c := by
  rintro rfl
  obtain ⟨y, hy, hne⟩ := hoc.other hG
  have : 1 < (nb G v).card :=
    Finset.one_lt_card.2 ⟨c₁, mem_nb.2 hoc.1, y, mem_nb.2 hy, hne.symm⟩
  unfold Leaf at hv
  omega

/-- data about the multiset of the other branches at an odd centroid -/
theorem OC.data {G : SimpleGraph V} (hG : G.IsTree) {c c₁ : V} (hoc : OC G c c₁) :
    enc ((rho G c).erase (kap G c c₁)) = kap G c₁ c ∧
    sz (kap G c c₁) = (Fintype.card V - 1) / 2 ∧
    (((rho G c).erase (kap G c c₁)).map sz).sum = (Fintype.card V - 1) / 2 ∧
    2 ≤ ((rho G c).erase (kap G c c₁)).card := by
  have h5 := hoc.five hG
  have h2m := hoc.2.1
  have hdec := dec_kap hG hoc.1.symm
  have henc : enc ((rho G c).erase (kap G c c₁)) = kap G c₁ c := by rw [← hdec, enc_dec]
  have hsa : sz (kap G c c₁) = (Fintype.card V - 1) / 2 := by
    have := sz_kap hG _ c c₁ hoc.1 le_rfl; omega
  have hsum : (((rho G c).erase (kap G c c₁)).map sz).sum = (Fintype.card V - 1) / 2 := by
    have h1 := sz_kap hG _ c₁ c hoc.1.symm le_rfl
    rw [sz_eq, hdec] at h1
    have := card_limb_add hG hoc.1
    omega
  refine ⟨henc, hsa, hsum, ?_⟩
  have hsmall : ∀ b ∈ (rho G c).erase (kap G c c₁), 2 * sz b + 3 ≤ Fintype.card V := by
    intro b hb
    rw [rho_erase hoc.1, Multiset.mem_map] at hb
    obtain ⟨y, hy, rfl⟩ := hb
    rw [Finset.mem_val, Finset.mem_erase, mem_nb] at hy
    have := hoc.2.2 y hy.2 hy.1
    have := sz_kap hG _ c y hy.2 le_rfl
    omega
  by_contra hcon
  have hle : ((rho G c).erase (kap G c c₁)).card ≤ 1 := by omega
  rcases Nat.lt_or_ge ((rho G c).erase (kap G c c₁)).card 1 with h0 | h1
  · have : (rho G c).erase (kap G c c₁) = 0 := Multiset.card_eq_zero.1 (by omega)
    rw [this] at hsum
    simp at hsum
    omega
  · obtain ⟨b, hb⟩ := Multiset.card_eq_one.1 (by omega :
      ((rho G c).erase (kap G c c₁)).card = 1)
    have := hsmall b (by rw [hb]; simp)
    rw [hb] at hsum
    simp at hsum
    omega


theorem OC.transfer {G : SimpleGraph V} {H : SimpleGraph W} (hG : G.IsTree) (hH : H.IsTree)
    (hcard : Fintype.card V = Fintype.card W) {c c₁ : V} {c' : W} (hoc : OC G c c₁)
    (hsz : (rho G c).map sz = (rho H c').map sz) : ∃ c₁', OC H c' c₁' := by
  have h1 : sz (kap G c c₁) ∈ (rho H c').map sz := by
    rw [← hsz]; exact Multiset.mem_map_of_mem _ (mem_rho.2 ⟨c₁, hoc.1, rfl⟩)
  obtain ⟨a', ha', hsa'⟩ := Multiset.mem_map.1 h1
  obtain ⟨c₁', hadj, rfl, hs'⟩ := sz_mem_rho hH ha'
  have hsG := sz_kap hG _ c c₁ hoc.1 le_rfl
  have h2m := hoc.2.1
  refine ⟨c₁', hadj, by omega, ?_⟩
  intro y' hy' hne
  have eG : (rho G c).map sz = sz (kap G c c₁) ::ₘ ((rho G c).erase (kap G c c₁)).map sz := by
    rw [← Multiset.map_cons, ← rho_cons hoc.1]
  have eH : (rho H c').map sz =
      sz (kap H c' c₁') ::ₘ ((rho H c').erase (kap H c' c₁')).map sz := by
    rw [← Multiset.map_cons, ← rho_cons hadj]
  rw [eG, eH, hsa'] at hsz
  have ht := (Multiset.cons_inj_right _).1 hsz
  have hmem : sz (kap H c' y') ∈ ((rho H c').erase (kap H c' c₁')).map sz := by
    apply Multiset.mem_map_of_mem
    rw [rho_erase hadj]
    exact Multiset.mem_map_of_mem _ (Finset.mem_erase.2 ⟨hne, mem_nb.2 hy'⟩)
  rw [← ht] at hmem
  obtain ⟨b, hb, hsb⟩ := Multiset.mem_map.1 hmem
  rw [rho_erase hoc.1, Multiset.mem_map] at hb
  obtain ⟨y, hy, rfl⟩ := hb
  rw [Finset.mem_val, Finset.mem_erase, mem_nb] at hy
  have := hoc.2.2 y hy.2 hy.1
  have := sz_kap hG _ c y hy.2 le_rfl
  have := sz_kap hH _ c' y' hy' le_rfl
  omega

theorem case3a {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : G.IsTree) (hH : H.IsTree) (σ : V ≃ W)
    (hdeg : ∀ v, (nb G v).card = (nb H (σ v)).card)
    (hci : ∀ v, ∃ e : V ≃ W, CardIso G H v (σ v) e) (c c₁ : V) (hoc : OC G c c₁) :
    Nonempty (G ≃g H) := by
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr σ
  have h5 := hoc.five hG
  obtain ⟨ec, hec⟩ := hci c
  have hsz := sizes_eq hG hH hec
  obtain ⟨c₁', hoc'⟩ := hoc.transfer hG hH hcard hsz
  generalize σ c = c' at hsz hoc'
  have hleaf : ∀ v, Leaf G v ↔ Leaf H (σ v) := fun v => by unfold Leaf; rw [hdeg v]
  obtain ⟨dG1, dG2, dG3, dG4⟩ := hoc.data hG
  obtain ⟨dH1, dH2, dH3, dH4⟩ := hoc'.data hH
  rw [← hcard] at dH2 dH3
  have key := lem3a ((Fintype.card V - 1) / 2) (kap G c c₁) (kap H c' c₁')
    ((rho G c).erase (kap G c c₁)) ((rho H c').erase (kap H c' c₁')) dG2 dH2 dG4 dH4 dG3 dH3
    (by
      intro c0 hc0
      obtain ⟨v, hv, hvl, _, hk⟩ := exists_leaf_of_del hG _ c c₁ c0 hoc.1 le_rfl hc0
      obtain ⟨e, he⟩ := hci v
      have hw := (hleaf v).1 hv
      obtain ⟨m1, _, m3, m4⟩ := pl3a_in hG hH h5 hcard he hv hw hoc hoc' hvl
      refine ⟨_, del_kap hH hw _ c' c₁' hoc'.1 le_rfl m1 m3, ?_⟩
      rw [← hk]; exact m4)
    (by
      intro c0' hc0'
      obtain ⟨w, hw, hwl, _, hk⟩ := exists_leaf_of_del hH _ c' c₁' c0' hoc'.1 le_rfl hc0'
      obtain ⟨v, rfl⟩ := σ.surjective w
      have hv := (hleaf v).2 hw
      obtain ⟨e, he⟩ := hci v
      have hvl : v ∈ limb G c c₁ := by
        by_contra hout
        exact (pl3a_out hG hH h5 hcard he hv hw hoc hoc' hout (hoc.not_leaf hG hv)).1 hwl
      obtain ⟨_, m2, _, m4⟩ := pl3a_in hG hH h5 hcard he hv hw hoc hoc' hvl
      refine ⟨_, del_kap hG hv _ c c₁ hoc.1 le_rfl hvl m2, ?_⟩
      rw [← hk]; exact m4)
    (by
      intro cd hcd
      rw [dG1] at hcd
      obtain ⟨v, hv, hvl, hvc, hk⟩ := exists_leaf_of_del hG _ c₁ c cd hoc.1.symm le_rfl hcd
      obtain ⟨e, he⟩ := hci v
      have hw := (hleaf v).1 hv
      have hout : v ∉ limb G c c₁ := (limb_compl hG hoc.1).1 hvl
      obtain ⟨m1, m2, m3⟩ := pl3a_out hG hH h5 hcard he hv hw hoc hoc' hout hvc
      refine ⟨kap (delV H (σ v)) c₁' c', ?_, ?_⟩
      · rw [dH1]
        exact del_kap hH hw _ c₁' c' hoc'.1.symm le_rfl ((limb_compl hH hoc'.1).2 m1) m2
      · rw [← hk]; exact m3)
    (by
      intro cd' hcd'
      rw [dH1] at hcd'
      obtain ⟨w, hw, hwl, hwc, hk⟩ :=
        exists_leaf_of_del hH _ c₁' c' cd' hoc'.1.symm le_rfl hcd'
      obtain ⟨v, rfl⟩ := σ.surjective w
      have hv := (hleaf v).2 hw
      obtain ⟨e, he⟩ := hci v
      have hout : v ∉ limb G c c₁ := by
        intro hin
        exact (limb_compl hH hoc'.1).1 hwl
          (pl3a_in hG hH h5 hcard he hv hw hoc hoc' hin).1
      have hvc := hoc.not_leaf hG hv
      obtain ⟨_, _, m3⟩ := pl3a_out hG hH h5 hcard he hv hw hoc hoc' hout hvc
      refine ⟨kap (delV G v) c₁ c, ?_, ?_⟩
      · rw [dG1]
        exact del_kap hG hv _ c₁ c hoc.1.symm le_rfl ((limb_compl hG hoc.1).2 hout) hvc
      · rw [← hk]; exact m3)
  apply iso_of_rho_eq hG hH hcard (r := c) (r' := c')
  rw [rho_cons hoc.1, rho_cons hoc'.1, key.2, key.1]


theorem nb_pair {G : SimpleGraph V} (hG : G.IsTree) {c s t : V} (hcs : G.Adj c s)
    (hct : G.Adj c t) (hst : s ≠ t) (hs : 2 * (limb G c s).card + 1 = Fintype.card V)
    (ht : 2 * (limb G c t).card + 1 = Fintype.card V) : nb G c = {s, t} := by
  have hsum := card_univ_limbs hG c
  rw [← Finset.add_sum_erase _ _ (mem_nb.2 hcs),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hst.symm, mem_nb.2 hct⟩)] at hsum
  ext y
  simp only [Finset.mem_insert, Finset.mem_singleton, mem_nb]
  constructor
  · intro hy
    by_contra hcon
    push_neg at hcon
    have hmem : y ∈ ((nb G c).erase s).erase t :=
      Finset.mem_erase.2 ⟨hcon.2, Finset.mem_erase.2 ⟨hcon.1, mem_nb.2 hy⟩⟩
    have h1 := Finset.single_le_sum (f := fun y => (limb G c y).card)
      (fun _ _ => Nat.zero_le _) hmem
    have h2 : 0 < (limb G c y).card := Finset.card_pos.2 ⟨y, self_mem_limb hy⟩
    omega
  · rintro (rfl | rfl)
    · exact hcs
    · exact hct

theorem rho_pair {G : SimpleGraph V} {c s t : V} (hnb : nb G c = {s, t}) (hst : s ≠ t) :
    rho G c = kap G c s ::ₘ {kap G c t} := by
  unfold rho
  rw [hnb, Finset.insert_val_of_notMem (by simpa using hst), Multiset.map_cons]
  rfl

theorem rho_pair_erase {G : SimpleGraph V} {c s t : V} (hnb : nb G c = {s, t}) (hst : s ≠ t) :
    (rho G c).erase (kap G c s) = {kap G c t} := by
  rw [rho_pair hnb hst, Multiset.erase_cons_head]


theorem pl3b {G : SimpleGraph V} {H : SimpleGraph W} (hG : G.IsTree) (hH : H.IsTree)
    (hV : 5 ≤ Fintype.card V) (hcard : Fintype.card V = Fintype.card W)
    {v : V} {w : W} {e : V ≃ W} (he : CardIso G H v w e) (hv : Leaf G v) (hw : Leaf H w)
    {c s t : V} (hnb : nb G c = {s, t}) (hst : s ≠ t)
    (hs : 2 * (limb G c s).card + 1 = Fintype.card V)
    (ht : 2 * (limb G c t).card + 1 = Fintype.card V)
    {c' d₁ d₂ : W} (hnb' : nb H c' = {d₁, d₂}) (hdd : d₁ ≠ d₂)
    (hs₁ : 2 * (limb H c' d₁).card + 1 = Fintype.card W)
    (hs₂ : 2 * (limb H c' d₂).card + 1 = Fintype.card W)
    (hvl : v ∈ limb G c s) :
    ∃ s' t', ((s' = d₁ ∧ t' = d₂) ∨ (s' = d₂ ∧ t' = d₁)) ∧ w ∈ limb H c' s' ∧ w ≠ s' ∧ v ≠ s ∧
      kap (delV G v) c s ::ₘ dec (kap G c t) =
        kap (delV H w) c' s' ::ₘ dec (kap H c' t') := by
  have hcs : G.Adj c s := mem_nb.1 (by rw [hnb]; simp)
  have hct : G.Adj c t := mem_nb.1 (by rw [hnb]; simp)
  have hvs : v ≠ s := leaf_ne_of_big hG hv hcs (by omega)
  have hcv : c ≠ v := fun h => not_mem_limb_child (h ▸ hvl)
  have hrho := rho_deep hG hcs hvl hvs
  rw [rho_pair_erase hnb hst] at hrho
  have hdel := del_kap hG hv _ c s hcs le_rfl hvl hvs
  have hsκ : sz (kap (delV G v) c s) + 1 = (Fintype.card V - 1) / 2 := by
    have := sz_del hdel
    have := sz_kap hG _ c s hcs le_rfl
    omega
  have hsat : sz (kap G c t) = (Fintype.card V - 1) / 2 := by
    have := sz_kap hG _ c t hct le_rfl; omega
  have hxw : e c ≠ w := by
    rw [← he.1]; exact fun h => hcv (e.injective h)
  have hR : ∀ a ∈ rho (delV H w) (e c), sz a ≤ (Fintype.card V - 1) / 2 := by
    intro a ha
    rw [he.rho_eq c, hrho] at ha
    rcases Multiset.mem_cons.1 ha with rfl | ha
    · omega
    · rw [Multiset.mem_singleton.1 ha]; omega
  have hlimb := limb_le_of_card hH hw hxw _ hR
  have hnbH : ∀ y', H.Adj c' y' → y' = d₁ ∨ y' = d₂ := by
    intro y' hy'
    have := mem_nb.2 hy'
    rw [hnb'] at this
    simpa using this
  have hB' : ∀ y', H.Adj c' y' → (limb H c' y').card ≤ (Fintype.card V - 1) / 2 := by
    intro y' hy'
    rcases hnbH y' hy' with rfl | rfl <;> omega
  -- the two possible shapes, for an ordered pair (s', t') of the neighbours of c'
  have main : ∀ s' t', nb H c' = {s', t'} → s' ≠ t' →
      2 * (limb H c' s').card + 1 = Fintype.card W →
      2 * (limb H c' t').card + 1 = Fintype.card W →
      ((e c = c' ∧ w ∈ limb H c' s') ∨ e c = t') →
      w ∈ limb H c' s' ∧ w ≠ s' ∧
        kap (delV G v) c s ::ₘ dec (kap G c t) =
          kap (delV H w) c' s' ::ₘ dec (kap H c' t') := by
    intro s' t' hnb2 hne2 hsz1 hsz2 hcase
    have hcs' : H.Adj c' s' := mem_nb.1 (by rw [hnb2]; simp)
    have hct' : H.Adj c' t' := mem_nb.1 (by rw [hnb2]; simp)
    have hsat' : sz (kap H c' t') = (Fintype.card V - 1) / 2 := by
      have := sz_kap hH _ c' t' hct' le_rfl; omega
    rcases hcase with ⟨hec, hwl⟩ | hec
    · have hws : w ≠ s' := leaf_ne_of_big hH hw hcs' (by omega)
      have h1 := rho_deep hH hcs' hwl hws
      rw [rho_pair_erase hnb2 hne2, ← hec, he.rho_eq c, hrho] at h1
      refine ⟨hwl, hws, ?_⟩
      rcases pair_single h1 with ⟨e1, e2⟩ | ⟨e1, _⟩
      · rw [← hec, e1, e2]
      · exfalso
        rw [← hec] at hsat'
        rw [e1] at hsκ
        omega
    · -- e c = t' is the heavy neighbour of c'
      subst hec
      have hwin : w ∈ limb H (e c) c' := by
        by_contra hout
        have hmem := mem_rho_delV_of_notMem hH hxw hct'.symm hout
        have := hR _ hmem
        have := sz_kap hH _ (e c) c' hct'.symm le_rfl
        have := card_limb_add hH hct'
        omega
      have hwc' : w ≠ c' := leaf_ne_of_big hH hw hct'.symm (by
        have := card_limb_add hH hct'; omega)
      have hwl : w ∈ limb H c' s' := by
        obtain ⟨y', hy', hwy'⟩ := exists_toward hH (x := c') (z := w) (fun h => hwc' h.symm)
        have hy2 : y' = s' ∨ y' = e c := by
          have := mem_nb.2 hy'
          rw [hnb2] at this
          simpa using this
        rcases hy2 with rfl | rfl
        · exact hwy'
        · exact absurd hwy' ((limb_compl hH hy').1 hwin)
      have hws : w ≠ s' := leaf_ne_of_big hH hw hcs' (by omega)
      have hdelH := del_kap hH hw _ c' s' hcs' le_rfl hwl hws
      have hnadj : w ∉ nb H c' := fun h =>
        hws (limb_disjoint hH (mem_nb.1 h) hcs' (self_mem_limb (mem_nb.1 h)) hwl)
      have hk : kap (delV H w) (e c) c' = enc {kap (delV H w) c' s'} := by
        rw [kap_unfold hH (delV_le H w) hct'.symm, nb_delV (fun h => hwc' h.symm),
          Finset.erase_eq_of_notMem hnadj, hnb2, Finset.pair_comm,
          Finset.erase_insert (by simpa using hne2.symm)]
        rfl
      have h1 := rho_deep hH hct'.symm hwin hwc'
      rw [← dec_kap hH hct', hk, he.rho_eq c, hrho] at h1
      have hsk' : sz (kap (delV H w) c' s') + 1 = (Fintype.card V - 1) / 2 := by
        have := sz_del hdelH
        have := sz_kap hH _ c' s' hcs' le_rfl
        omega
      have hsenc : sz (enc {kap (delV H w) c' s'}) = (Fintype.card V - 1) / 2 := by
        rw [sz_enc]; simp; omega
      have h1' : kap G c t ::ₘ {kap (delV G v) c s} =
          enc {kap (delV H w) c' s'} ::ₘ dec (kap H c' (e c)) := by
        rw [← h1]; exact Multiset.cons_swap _ _ _
      obtain ⟨e1, e2⟩ := cons_cancel_big h1'
        (fun b hb => by rw [Multiset.mem_singleton.1 hb]; omega)
        (fun b hb => by
          have := sz_lt_of_mem_dec hb
          omega)
      refine ⟨hwl, hws, ?_⟩
      rw [e1, dec_enc, ← e2]
      exact Multiset.cons_swap _ _ _
  by_cases hx : e c = c'
  · have hxw' : c' ≠ w := hx ▸ hxw
    obtain ⟨y', hy', hwy'⟩ := exists_toward hH hxw'
    rcases hnbH y' hy' with rfl | rfl
    · obtain ⟨m1, m2, m3⟩ := main y' d₂ hnb' hdd hs₁ hs₂ (Or.inl ⟨hx, hwy'⟩)
      exact ⟨y', d₂, Or.inl ⟨rfl, rfl⟩, m1, m2, hvs, m3⟩
    · obtain ⟨m1, m2, m3⟩ := main y' d₁ (by rw [hnb', Finset.pair_comm]) hdd.symm hs₂ hs₁
        (Or.inl ⟨hx, hwy'⟩)
      exact ⟨y', d₁, Or.inr ⟨rfl, rfl⟩, m1, m2, hvs, m3⟩
  · obtain ⟨hadj, _⟩ := near_centroid hH ((Fintype.card V - 1) / 2 + 1)
      ((Fintype.card V - 1) / 2) hB' hlimb (by omega) hx
    rcases hnbH _ hadj with h | h
    · obtain ⟨m1, m2, m3⟩ := main d₂ d₁ (by rw [hnb', Finset.pair_comm]) hdd.symm hs₂ hs₁
        (Or.inr h)
      exact ⟨d₂, d₁, Or.inr ⟨rfl, rfl⟩, m1, m2, hvs, m3⟩
    · obtain ⟨m1, m2, m3⟩ := main d₁ d₂ hnb' hdd hs₁ hs₂ (Or.inr h)
      exact ⟨d₁, d₂, Or.inl ⟨rfl, rfl⟩, m1, m2, hvs, m3⟩


theorem case3b {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : G.IsTree) (hH : H.IsTree) (σ : V ≃ W)
    (hdeg : ∀ v, (nb G v).card = (nb H (σ v)).card)
    (hci : ∀ v, ∃ e : V ≃ W, CardIso G H v (σ v) e) (c c₁ c₂ : V)
    (hc1 : G.Adj c c₁) (hc2 : G.Adj c c₂) (hne : c₁ ≠ c₂)
    (h1 : 2 * (limb G c c₁).card + 1 = Fintype.card V)
    (h2 : 2 * (limb G c c₂).card + 1 = Fintype.card V) : Nonempty (G ≃g H) := by
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr σ
  have hnb := nb_pair hG hc1 hc2 hne h1 h2
  obtain ⟨ec, hec⟩ := hci c
  have hsz := sizes_eq hG hH hec
  have hleaf : ∀ v, Leaf G v ↔ Leaf H (σ v) := fun v => by unfold Leaf; rw [hdeg v]
  have hcnl : ∀ v, Leaf G v → v ≠ c := by
    rintro v hv rfl
    unfold Leaf at hv
    rw [hnb, Finset.card_pair hne] at hv
    omega
  generalize σ c = c' at hsz
  have hsa1 := sz_kap hG _ c c₁ hc1 le_rfl
  have hsa2 := sz_kap hG _ c c₂ hc2 le_rfl
  have hmapG : (rho G c).map sz =
      ((Fintype.card V - 1) / 2) ::ₘ {(Fintype.card V - 1) / 2} := by
    rw [rho_pair hnb hne]
    simp only [Multiset.map_cons, Multiset.map_singleton]
    rw [hsa1, hsa2]
    congr 1
    · omega
    · congr 1; omega
  have hcardH : (nb H c').card = 2 := by
    have := congrArg Multiset.card hsz
    rw [hmapG] at this
    unfold rho at this
    simpa using this.symm
  obtain ⟨d₁, d₂, hdd, hnb'⟩ := Finset.card_eq_two.1 hcardH
  have hd1 : H.Adj c' d₁ := mem_nb.1 (by rw [hnb']; simp)
  have hd2 : H.Adj c' d₂ := mem_nb.1 (by rw [hnb']; simp)
  have hszH : ∀ d, H.Adj c' d → 2 * (limb H c' d).card + 1 = Fintype.card W := by
    intro d hd
    have hm : sz (kap H c' d) ∈ (rho H c').map sz :=
      Multiset.mem_map_of_mem _ (mem_rho.2 ⟨d, hd, rfl⟩)
    rw [← hsz, hmapG] at hm
    have hm' : sz (kap H c' d) = (Fintype.card V - 1) / 2 := by simpa using hm
    have := sz_kap hH _ c' d hd le_rfl
    omega
  let cc : Bool → V := fun i => cond i c₁ c₂
  let dd : Bool → W := fun j => cond j d₁ d₂
  have hcc : ∀ i, nb G c = {cc i, cc (!i)} ∧ cc i ≠ cc (!i) ∧
      2 * (limb G c (cc i)).card + 1 = Fintype.card V ∧
      2 * (limb G c (cc (!i))).card + 1 = Fintype.card V ∧ G.Adj c (cc i) := by
    intro i
    cases i
    · exact ⟨by rw [hnb]; exact Finset.pair_comm _ _, hne.symm, h2, h1, hc2⟩
    · exact ⟨hnb, hne, h1, h2, hc1⟩
  have hddadj : ∀ j, H.Adj c' (dd j) := by
    intro j; cases j
    · exact hd2
    · exact hd1
  have hB := lemB ((Fintype.card V - 1) / 2) (fun i => kap G c (cc i)) (fun j => kap H c' (dd j))
    (fun i => by
      have := sz_kap hG _ c (cc i) (hcc i).2.2.2.2 le_rfl
      have := (hcc i).2.2.1
      show sz (kap G c (cc i)) = _
      omega)
    (fun j => by
      have := sz_kap hH _ c' (dd j) (hddadj j) le_rfl
      have := hszH (dd j) (hddadj j)
      show sz (kap H c' (dd j)) = _
      omega)
    (by
      intro i cd hcd
      obtain ⟨hnbi, hnei, hsi, hti, hadji⟩ := hcc i
      obtain ⟨v, hv, hvl, hvne, hk⟩ := exists_leaf_of_del hG _ c (cc i) cd hadji le_rfl hcd
      have h5 : 5 ≤ Fintype.card V := by
        have : 1 < (limb G c (cc i)).card :=
          Finset.one_lt_card.2 ⟨v, hvl, cc i, self_mem_limb hadji, hvne⟩
        omega
      obtain ⟨e, he⟩ := hci v
      have hw := (hleaf v).1 hv
      obtain ⟨s', t', alt, m1, m2, _, m4⟩ := pl3b hG hH h5 hcard he hv hw hnbi hnei hsi hti
        hnb' hdd (hszH d₁ hd1) (hszH d₂ hd2) hvl
      rcases alt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨true, _, del_kap hH hw _ c' s' hd1 le_rfl m1 m2, ?_⟩
        rw [← hk]; exact m4
      · refine ⟨false, _, del_kap hH hw _ c' s' hd2 le_rfl m1 m2, ?_⟩
        rw [← hk]; exact m4)
    (by
      intro j cd' hcd'
      obtain ⟨w, hw, hwl, hwne, hk⟩ :=
        exists_leaf_of_del hH _ c' (dd j) cd' (hddadj j) le_rfl hcd'
      have h5 : 5 ≤ Fintype.card V := by
        have : 1 < (limb H c' (dd j)).card :=
          Finset.one_lt_card.2 ⟨w, hwl, dd j, self_mem_limb (hddadj j), hwne⟩
        have := hszH (dd j) (hddadj j)
        omega
      obtain ⟨v, rfl⟩ := σ.surjective w
      have hv := (hleaf v).2 hw
      obtain ⟨e, he⟩ := hci v
      obtain ⟨y, hy, hvy⟩ := exists_toward hG (x := c) (z := v) (fun h => hcnl v hv h.symm)
      have hyi : ∃ i, y = cc i := by
        have := mem_nb.2 hy
        rw [hnb] at this
        rcases Finset.mem_insert.1 this with h | h
        · exact ⟨true, h⟩
        · exact ⟨false, Finset.mem_singleton.1 h⟩
      obtain ⟨i, rfl⟩ := hyi
      obtain ⟨hnbi, hnei, hsi, hti, hadji⟩ := hcc i
      obtain ⟨s', t', alt, m1, _, m3, m4⟩ := pl3b hG hH h5 hcard he hv hw hnbi hnei hsi hti
        hnb' hdd (hszH d₁ hd1) (hszH d₂ hd2) hvy
      have hs' : H.Adj c' s' := by
        rcases alt with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact hd1
        · exact hd2
      have hsj : s' = dd j := limb_disjoint hH hs' (hddadj j) m1 hwl
      have htj : t' = dd (!j) := by
        rcases alt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · cases j
          · exact absurd hsj hdd
          · rfl
        · cases j
          · rfl
          · exact absurd hsj hdd.symm
      refine ⟨i, _, del_kap hG hv _ c (cc i) hadji le_rfl hvy m3, ?_⟩
      rw [← hk, ← hsj, ← htj]; exact m4)
  rcases hB with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · apply iso_of_rho_eq hG hH hcard (r := c) (r' := c')
    rw [rho_pair hnb hne, rho_pair hnb' hdd]
    have e1' : kap G c c₁ = kap H c' d₁ := e1
    have e2' : kap G c c₂ = kap H c' d₂ := e2
    rw [e1', e2']
  · apply iso_of_rho_eq hG hH hcard (r := c) (r' := c')
    rw [rho_pair hnb hne, rho_pair (by rw [hnb']; exact Finset.pair_comm _ _) hdd.symm]
    have e1' : kap G c c₁ = kap H c' d₂ := e1
    have e2' : kap G c c₂ = kap H c' d₁ := e2
    rw [e1', e2']

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution :
    type_of% @ReconstructionConjecture.reconstruction_conjecture.variants.tree := by
  intro V W _ _ hV G H hc ha h
  have hG : G.IsTree := ⟨hc, ha⟩
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨hH, hdeg, hci⟩ := prelim hV hG σ hσ
  obtain ⟨c, hcen⟩ := exists_centroid hG
  by_cases h1 : ∀ y, G.Adj c y → 2 * (limb G c y).card + 2 ≤ Fintype.card V
  · exact case1 hV hG hH σ hdeg hci c h1
  · push_neg at h1
    obtain ⟨c₁, hc1, hbig⟩ := h1
    have hle := hcen c₁ hc1
    by_cases h2 : 2 * (limb G c c₁).card = Fintype.card V
    · exact case2 hV hG hH σ hdeg hci c c₁ hc1 h2
    · have h3 : 2 * (limb G c c₁).card + 1 = Fintype.card V := by omega
      by_cases h4 : ∃ c₂, G.Adj c c₂ ∧ c₂ ≠ c₁ ∧ 2 * (limb G c c₂).card + 1 = Fintype.card V
      · obtain ⟨c₂, hc2, hne, h5⟩ := h4
        exact case3b hG hH σ hdeg hci c c₁ c₂ hc1 hc2 hne.symm h3 h5
      · push_neg at h4
        refine case3a hG hH σ hdeg hci c c₁ ⟨hc1, h3, ?_⟩
        intro y hy hne
        have := h4 y hy hne
        have := hcen y hy
        omega
