import OMAReductions.R_ScholzConjecture_scholz_conjecture_R1

/-!
# Brauer's bound for numbers with an optimal star chain

If `n` has an addition chain of optimal length `l(n)` in which every entry is the previous
entry plus some entry of the chain (a star chain), then `l(2 ^ n - 1) ≤ n - 1 + l(n)`.

Construction (Brauer 1939). Write the star chain as `c 0 = 1, c 1, ..., c r = n` with
`c (m + 1) = c m + j`, where `j` is an earlier entry. From a chain ending at `2 ^ (c m) - 1`
that contains `2 ^ (c i) - 1` for every `i ≤ m`, double the last entry `j` times to reach
`2 ^ j * (2 ^ (c m) - 1)`, then add `2 ^ j - 1` to reach `2 ^ (c m + j) - 1`. Each star step
costs `j + 1` entries, so the chain for `2 ^ (c m) - 1` has `c m + m` entries, and at `m = r`
this gives `n + l(n) - 1` steps.

Only the upstream definitions `IsAdditionChain` and `additionChainLength` are used; the basic
facts about them are proved below.
-/

namespace OMA.Helpers

/-- Every entry of an addition chain is at least `1`. -/
theorem scholz_one_le_of_mem {c : List ℕ} (h : IsAdditionChain c) {x : ℕ} (hx : x ∈ c) :
    1 ≤ x := by
  rcases c with _ | ⟨a, t⟩
  · exact absurd hx List.not_mem_nil
  · have ha : a = 1 := by simpa using h.1
    subst ha
    rcases List.mem_cons.mp hx with hx | hx
    · omega
    · exact Nat.le_of_lt (List.rel_of_pairwise_cons h.2.1 hx)

/-- The one-entry chain `[1]`. -/
theorem scholz_chain_one : IsAdditionChain [1] :=
  ⟨rfl, List.pairwise_singleton _ _, fun _x hx hx1 => absurd (List.mem_singleton.mp hx) hx1⟩

/-- An explicit chain bounds the addition chain length from above. -/
theorem scholz_length_le {n r : ℕ} (c : List ℕ) (hc : IsAdditionChain c)
    (hlast : c.getLast? = some n) (hlen : c.length = r + 1) : additionChainLength n ≤ r := by
  unfold additionChainLength
  exact Nat.sInf_le ⟨c, hc, hlast, hlen⟩

/-- Appending an entry that exceeds every entry and is a sum of two entries keeps a chain. -/
theorem scholz_snoc_chain {ds : List ℕ} {y : ℕ} (h : IsAdditionChain ds) (hne : ds ≠ [])
    (hlt : ∀ x ∈ ds, x < y) (hsum : ∃ a ∈ ds, ∃ b ∈ ds, y = a + b) :
    IsAdditionChain (ds ++ [y]) := by
  obtain ⟨hhead, hpw, hs⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · cases ds with
    | nil => exact absurd rfl hne
    | cons a t => simpa using hhead
  · rw [List.pairwise_append]
    refine ⟨hpw, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    exact hlt a ha
  · intro x hx hx1
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨a, ha, b, hb, rfl⟩ := hs x hx hx1
      exact ⟨a, List.mem_append_left _ ha, b, List.mem_append_left _ hb, rfl⟩
    · rw [List.mem_singleton] at hx
      subst hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hsum
      exact ⟨a, List.mem_append_left _ ha, b, List.mem_append_left _ hb, rfl⟩

/-- `k` successive doublings of the last entry `A` of a chain whose entries are all `≤ A`. -/
theorem scholz_double_steps (ds : List ℕ) (A : ℕ) (hA : 1 ≤ A) (h : IsAdditionChain ds)
    (hlast : ds.getLast? = some A) (hle : ∀ x ∈ ds, x ≤ A) :
    ∀ k : ℕ, ∃ es : List ℕ, IsAdditionChain es ∧ es.getLast? = some (2 ^ k * A) ∧
      (∀ x ∈ es, x ≤ 2 ^ k * A) ∧ es.length = ds.length + k ∧ (∀ x ∈ ds, x ∈ es) := by
  intro k
  induction k with
  | zero => exact ⟨ds, h, by simpa using hlast, by simpa using hle, rfl, fun x hx => hx⟩
  | succ k ih =>
    obtain ⟨es, hes, heslast, hesle, heslen, hsub⟩ := ih
    have hmem : 2 ^ k * A ∈ es := List.mem_of_getLast? heslast
    have hne : es ≠ [] := List.ne_nil_of_mem hmem
    have hpos : 0 < 2 ^ k * A := Nat.mul_pos (pow_pos (by norm_num : (0 : ℕ) < 2) k) hA
    have hdouble : 2 ^ (k + 1) * A = 2 ^ k * A + 2 ^ k * A := by ring
    refine ⟨es ++ [2 ^ (k + 1) * A], ?_, ?_, ?_, ?_, ?_⟩
    · apply scholz_snoc_chain hes hne
      · intro x hx
        have := hesle x hx
        omega
      · exact ⟨_, hmem, _, hmem, hdouble⟩
    · simp
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · have := hesle x hx
        omega
      · rw [List.mem_singleton] at hx
        omega
    · simp [heslen]
      omega
    · intro x hx
      exact List.mem_append_left _ (hsub x hx)

/-- `2 ^ j * (2 ^ c - 1) + (2 ^ j - 1) = 2 ^ (c + j) - 1`. -/
theorem scholz_pow_identity (c j : ℕ) :
    2 ^ j * (2 ^ c - 1) + (2 ^ j - 1) = 2 ^ (c + j) - 1 := by
  obtain ⟨p, hp⟩ : ∃ p, 2 ^ c = p + 1 := ⟨2 ^ c - 1, by have := Nat.one_le_two_pow (n := c); omega⟩
  obtain ⟨q, hq⟩ : ∃ q, 2 ^ j = q + 1 := ⟨2 ^ j - 1, by have := Nat.one_le_two_pow (n := j); omega⟩
  rw [pow_add, hp, hq]
  simp only [Nat.add_sub_cancel]
  have : (p + 1) * (q + 1) = p * q + p + q + 1 := by ring
  rw [this]
  simp only [Nat.add_sub_cancel]
  ring

/-- Brauer's construction along a star chain `cs`: for every index `m` there is a chain ending
at `2 ^ cs[m] - 1`, with all entries at most that value, with `cs[m] + m` entries, and
containing `2 ^ cs[i] - 1` for every `i ≤ m`. -/
theorem scholz_brauer (cs : List ℕ) (hc : IsAdditionChain cs)
    (hstar : ∀ (i : ℕ) (hi : i + 1 < cs.length), ∃ j ∈ cs, cs[i + 1] = cs[i] + j) :
    ∀ (m : ℕ) (hm : m < cs.length), ∃ ds : List ℕ, IsAdditionChain ds ∧
      ds.getLast? = some (2 ^ cs[m] - 1) ∧ (∀ x ∈ ds, x ≤ 2 ^ cs[m] - 1) ∧
      ds.length = cs[m] + m ∧
      (∀ (i : ℕ) (hi : i < cs.length), i ≤ m → 2 ^ cs[i] - 1 ∈ ds) := by
  have hpw : cs.Pairwise (· < ·) := hc.2.1
  have hone : ∀ (i : ℕ) (hi : i < cs.length), 1 ≤ cs[i] := fun i hi =>
    scholz_one_le_of_mem hc (List.getElem_mem hi)
  intro m
  induction m with
  | zero =>
    intro hm
    have h0 : cs[0] = 1 := by
      have hh := hc.1
      cases cs with
      | nil => simp at hm
      | cons a t => simpa using hh
    refine ⟨[1], scholz_chain_one, ?_, ?_, ?_, ?_⟩
    · simp [h0]
    · intro x hx
      simp [h0] at hx ⊢
      omega
    · simp [h0]
    · intro i hi hi0
      have : i = 0 := by omega
      subst this
      simp [h0]
  | succ m ih =>
    intro hm
    obtain ⟨ds, hds, hdslast, hdsle, hdslen, hdsmem⟩ := ih (by omega)
    obtain ⟨j, hj, hjeq⟩ := hstar m hm
    have hcm := hone m (by omega)
    have hj1 : 1 ≤ j := scholz_one_le_of_mem hc hj
    set A := 2 ^ cs[m] - 1 with hAdef
    have hA : 1 ≤ A := by
      have : 2 ≤ 2 ^ cs[m] := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ cs[m] := Nat.pow_le_pow_right (by norm_num) hcm
      omega
    obtain ⟨es, hes, heslast, hesle, heslen, hsub⟩ :=
      scholz_double_steps ds A hA hds hdslast hdsle j
    -- the summand 2 ^ j - 1 already occurs, since j is an entry before index m + 1
    obtain ⟨i, hi, hij⟩ := List.mem_iff_getElem.mp hj
    have hile : i ≤ m := by
      by_contra hlt
      have hlt' : m + 1 ≤ i := by omega
      rcases Nat.eq_or_lt_of_le hlt' with heq | hlt2
      · subst heq
        omega
      · have := (List.pairwise_iff_getElem.mp hpw) (m + 1) i hm hi hlt2
        omega
    have hjmem : 2 ^ j - 1 ∈ es := by
      have := hdsmem i hi hile
      rw [hij] at this
      exact hsub _ this
    have htop : 2 ^ j * A ∈ es := List.mem_of_getLast? heslast
    have hne : es ≠ [] := List.ne_nil_of_mem htop
    have hval : 2 ^ j * A + (2 ^ j - 1) = 2 ^ cs[m + 1] - 1 := by
      rw [hjeq, hAdef]
      exact scholz_pow_identity cs[m] j
    have hjpos : 1 ≤ 2 ^ j - 1 := by
      have : 2 ≤ 2 ^ j := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
      omega
    refine ⟨es ++ [2 ^ cs[m + 1] - 1], ?_, ?_, ?_, ?_, ?_⟩
    · apply scholz_snoc_chain hes hne
      · intro x hx
        have := hesle x hx
        omega
      · exact ⟨_, htop, _, hjmem, hval.symm⟩
    · simp
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · have := hesle x hx
        omega
      · rw [List.mem_singleton] at hx
        omega
    · simp [heslen, hdslen]
      omega
    · intro i' hi' hi'le
      rcases Nat.eq_or_lt_of_le hi'le with heq | hlt
      · subst heq
        simp
      · exact List.mem_append_left _ (hsub _ (hdsmem i' hi' (by omega)))

end OMA.Helpers

theorem OMA.solution : OMA.R_ScholzConjecture_scholz_conjecture_R1.H1 := by
  intro n hn hex
  obtain ⟨cs, hc, hlast, hlen, hstar⟩ := hex
  have hne : cs ≠ [] := by
    intro h
    subst h
    simp at hlast
  have hm : cs.length - 1 < cs.length := by
    have := List.length_pos_of_ne_nil hne
    omega
  have hlastm : cs[cs.length - 1] = n := by
    rw [List.getLast?_eq_getElem?] at hlast
    rw [List.getElem?_eq_getElem hm] at hlast
    exact Option.some.inj hlast
  obtain ⟨ds, hds, hdslast, -, hdslen, -⟩ := OMA.Helpers.scholz_brauer cs hc hstar _ hm
  rw [hlastm] at hdslast hdslen
  apply OMA.Helpers.scholz_length_le ds hds hdslast
  rw [hdslen, hlen]
  omega
