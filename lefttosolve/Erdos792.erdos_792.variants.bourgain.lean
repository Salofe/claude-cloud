import FormalConjectures.ErdosProblems.«792»

/-!
Bourgain's bound: every set `A` of `n ≥ 3` positive integers has a sum-free subset `B` with
`3 |B| ≥ n + 2`.

All sum-free sets used are of dilation type: for naturals `t` and `M > 0`,
`S t M A = {a ∈ A | ⌊a t / M⌋ ≡ 1 (mod 3)}` (the `a` with `a t / (3 M)` in the middle third mod one).
Such a set is sum-free, because `⌊(a + b) t / M⌋ - ⌊a t / M⌋ - ⌊b t / M⌋ ∈ {0, 1}`.

* Lifting. Replacing `t` by `t + M`, `t + 2 M` does not change the selection of multiples of three,
  while every non-multiple of three is selected for exactly one of the three shifts. Hence some
  shift selects at least `|S t M A₁| + |A₀| / 3` elements (`A₁` the multiples of three in `A`, `A₀`
  the rest), and strictly more if the three shifts do not split `A₀` evenly.
* Induction on a bound for the elements. If `|A₁| ≥ 3`, apply the statement to `A₁ / 3` and lift.
  If `A₁ = ∅`, one residue class mod three works; if `|A₁| = 1` or `A₁ = {x, y}` with `y ≠ 2 x`,
  all of `A₁` can be selected at once and the lift gives the bound.
* The remaining case `A₁ = {v, 2 v}`. Let `W` be the largest element of `A₀`. If `W < 2 v`, at
  `t / M = 1 / (2 v)` the element `2 v` is selected and no element of `A₀` is, so the split is
  uneven. If `W > 2 v`, pick a power of three `k` with `W < 2 v k < 3 W` and `j` with
  `k + j W ≡ 1 (mod 3)`. At `t / M = (k + j W) / W` one of `v`, `2 v` is selected. Passing to the
  slightly smaller ratio `((k + j W) W - 1) / W ^ 2` changes no floor `⌊a t / M⌋` with `a < W`
  (as `W ∤ a (k + j W)`), but drops `⌊W t / M⌋` from `k + j W` to `k + j W - 1`, so exactly one
  element of `A₀` leaves the selection. So the split of `A₀` is uneven at one of the two ratios.
-/

namespace OMA.Helpers

/-- The dilation-selected subset: those `a` with `⌊a t / M⌋ ≡ 1 (mod 3)`. -/
def S (t M : ℕ) (A : Finset ℕ) : Finset ℕ := A.filter (fun a => (a * t / M) % 3 = 1)

theorem mem_S {t M : ℕ} {A : Finset ℕ} {a : ℕ} :
    a ∈ S t M A ↔ a ∈ A ∧ (a * t / M) % 3 = 1 := by
  simp [S]

/-- Sum-freeness of the selection predicate. -/
theorem sel_add (t M a b : ℕ) (ha : (a * t / M) % 3 = 1) (hb : (b * t / M) % 3 = 1) :
    ((a + b) * t / M) % 3 ≠ 1 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp at ha
  · rw [add_mul, Nat.add_div hM]
    split_ifs <;> omega

theorem shift_mul3 (t M j a : ℕ) (hM : 0 < M) (h3 : 3 ∣ a) :
    (a * (t + j * M) / M) % 3 = (a * t / M) % 3 := by
  obtain ⟨c, rfl⟩ := h3
  have h : 3 * c * (t + j * M) = 3 * c * t + (3 * (c * j)) * M := by ring
  rw [h, Nat.add_mul_div_right _ _ hM]
  omega

theorem shift_non3 (t M a : ℕ) (hM : 0 < M) (h3 : ¬ 3 ∣ a) :
    (if (a * t / M) % 3 = 1 then 1 else 0) + (if (a * (t + M) / M) % 3 = 1 then 1 else 0)
      + (if (a * (t + 2 * M) / M) % 3 = 1 then 1 else 0) = 1 := by
  have h1 : a * (t + M) = a * t + a * M := by ring
  have h2 : a * (t + 2 * M) = a * t + (2 * a) * M := by ring
  rw [h1, h2, Nat.add_mul_div_right _ _ hM, Nat.add_mul_div_right _ _ hM]
  split_ifs <;> omega

/-- Splitting the selected set into the multiples of three and the rest. -/
theorem S_card_split (t M : ℕ) (A : Finset ℕ) :
    (S t M A).card = (S t M (A.filter (fun a => 3 ∣ a))).card
      + (S t M (A.filter (fun a => ¬ 3 ∣ a))).card := by
  have h := Finset.card_filter_add_card_filter_not (s := S t M A) (fun a => 3 ∣ a)
  have e1 : (S t M A).filter (fun a => 3 ∣ a) = S t M (A.filter (fun a => 3 ∣ a)) := by
    ext a
    simp only [S, Finset.mem_filter]
    tauto
  have e2 : (S t M A).filter (fun a => ¬ 3 ∣ a) = S t M (A.filter (fun a => ¬ 3 ∣ a)) := by
    ext a
    simp only [S, Finset.mem_filter]
    tauto
  rw [e1, e2] at h
  exact h.symm

/-- On multiples of three the selection does not see a shift of `t` by a multiple of `M`. -/
theorem S_shift_A1 (t M j : ℕ) (hM : 0 < M) (A : Finset ℕ) :
    S (t + j * M) M (A.filter (fun a => 3 ∣ a)) = S t M (A.filter (fun a => 3 ∣ a)) := by
  unfold S
  apply Finset.filter_congr
  intro a ha
  rw [shift_mul3 t M j a hM (Finset.mem_filter.mp ha).2]

/-- Each non-multiple of three is selected by exactly one of the three shifts. -/
theorem S_sum_A0 (t M : ℕ) (hM : 0 < M) (A0 : Finset ℕ) (h : ∀ a ∈ A0, ¬ 3 ∣ a) :
    (S t M A0).card + (S (t + M) M A0).card + (S (t + 2 * M) M A0).card = A0.card := by
  unfold S
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro a ha
  exact shift_non3 t M a hM (h a ha)

/-- The lifting lemma: some shift does at least as well as the average. -/
theorem lift1 (t M : ℕ) (hM : 0 < M) (A : Finset ℕ) :
    ∃ t', 3 * (S t M (A.filter (fun a => 3 ∣ a))).card + (A.filter (fun a => ¬ 3 ∣ a)).card
      ≤ 3 * (S t' M A).card := by
  have h0 := S_card_split t M A
  have h1 := S_card_split (t + M) M A
  have h2 := S_card_split (t + 2 * M) M A
  have e1 := S_shift_A1 t M 1 hM A
  have e2 := S_shift_A1 t M 2 hM A
  rw [one_mul] at e1
  rw [e1] at h1
  rw [e2] at h2
  have hs := S_sum_A0 t M hM (A.filter (fun a => ¬ 3 ∣ a)) (fun a ha => (Finset.mem_filter.mp ha).2)
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have c0 := hcon t
  have c1 := hcon (t + M)
  have c2 := hcon (t + 2 * M)
  omega

/-- The unbalanced lifting lemma: if the non-multiples of three are not split evenly at `t`,
some shift does strictly better than the average. -/
theorem lift2 (t M : ℕ) (hM : 0 < M) (A : Finset ℕ)
    (hne : 3 * (S t M (A.filter (fun a => ¬ 3 ∣ a))).card ≠ (A.filter (fun a => ¬ 3 ∣ a)).card) :
    ∃ t', 3 * (S t M (A.filter (fun a => 3 ∣ a))).card + (A.filter (fun a => ¬ 3 ∣ a)).card + 1
      ≤ 3 * (S t' M A).card := by
  have h0 := S_card_split t M A
  have h1 := S_card_split (t + M) M A
  have h2 := S_card_split (t + 2 * M) M A
  have e1 := S_shift_A1 t M 1 hM A
  have e2 := S_shift_A1 t M 2 hM A
  rw [one_mul] at e1
  rw [e1] at h1
  rw [e2] at h2
  have hs := S_sum_A0 t M hM (A.filter (fun a => ¬ 3 ∣ a)) (fun a ha => (Finset.mem_filter.mp ha).2)
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have c0 := hcon t
  have c1 := hcon (t + M)
  have c2 := hcon (t + 2 * M)
  omega


/-- Scaling by three: the selection on `3 • A'` with modulus `3 M` is the selection on `A'`. -/
theorem scale3 (t M : ℕ) (A' : Finset ℕ) :
    (S t (3 * M) (A'.image (fun b => 3 * b))).card = (S t M A').card := by
  unfold S
  rw [Finset.filter_image, Finset.card_image_of_injective _ (fun x y h => by simpa using h)]
  congr 1
  apply Finset.filter_congr
  intro b _
  rw [mul_assoc, Nat.mul_div_mul_left _ _ (by norm_num : 0 < 3)]

/-- Two positive integers whose ratio is not two can be selected simultaneously. -/
theorem pair (u u' : ℕ) (hu : 0 < u) (hlt : u < u') (hne : u' ≠ 2 * u) :
    ∃ t M, 0 < M ∧ (u * t / M) % 3 = 1 ∧ (u' * t / M) % 3 = 1 := by
  have hq := Nat.div_add_mod u' u
  have hr := Nat.mod_lt u' hu
  have hq1 : 1 ≤ u' / u := Nat.div_pos hlt.le hu
  generalize u' / u = q at hq hq1
  generalize u' % u = r at hq hr
  rcases (by omega : q % 3 = 1 ∨ q % 3 = 0 ∨ q % 3 = 2) with h | h | h
  · refine ⟨1, u, hu, ?_, ?_⟩
    · rw [mul_one, Nat.div_self hu]
    · have : u' * 1 / u = q := by
        rw [mul_one]
        exact Nat.div_eq_of_lt_le (by rw [mul_comm]; omega) (by rw [add_mul, mul_comm q u]; omega)
      rw [this]
      exact h
  · refine ⟨q + 1, u', by omega, ?_, ?_⟩
    · have e : u * (q + 1) = u * q + u := by ring
      have : u * (q + 1) / u' = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [this]
    · rw [Nat.mul_div_cancel_left _ (by omega : 0 < u')]
      omega
  · have hq2 : u * 2 ≤ u * q := Nat.mul_le_mul_left u (by omega)
    refine ⟨q + 2, u', by omega, ?_, ?_⟩
    · have e : u * (q + 2) = u * q + 2 * u := by ring
      have : u * (q + 2) / u' = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [this]
    · rw [Nat.mul_div_cancel_left _ (by omega : 0 < u')]
      omega

/-- Moving `t / M = k / W` slightly to the left does not change `⌊a t / M⌋` unless `W ∣ a k`. -/
theorem floor_left (a k W : ℕ) (ha : 0 < a) (haW : a < W) (hk : 0 < k) (hnd : ¬ W ∣ a * k) :
    a * (k * W - 1) / (W * W) = a * k / W := by
  have hW : 0 < W := by omega
  have hdm := Nat.div_add_mod (a * k) W
  have hr := Nat.mod_lt (a * k) hW
  have hr0 : a * k % W ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
  generalize a * k / W = q at hdm
  generalize a * k % W = r at hdm hr hr0
  have h1 : 1 ≤ k * W := Nat.mul_pos hk hW
  have e : a * (k * W - 1) + a = q * (W * W) + r * W := by
    have : a * (k * W - 1) + a = a * k * W := by
      have h2 : k * W - 1 + 1 = k * W := Nat.sub_add_cancel h1
      calc a * (k * W - 1) + a = a * (k * W - 1 + 1) := by ring
        _ = a * k * W := by rw [h2]; ring
    rw [this, ← hdm]
    ring
  have hrW : W ≤ r * W := Nat.le_mul_of_pos_left W (by omega)
  have hrW2 : r * W < W * W := Nat.mul_lt_mul_of_pos_right hr hW
  apply Nat.div_eq_of_lt_le
  · omega
  · have : (q + 1) * (W * W) = q * (W * W) + W * W := by ring
    omega

/-- At the element `W` itself the floor drops by one. -/
theorem floor_self (k W : ℕ) (hW : 0 < W) (hk : 0 < k) :
    W * (k * W - 1) / (W * W) = k - 1 := by
  rw [Nat.mul_div_mul_left _ _ hW]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have e : (k' + 1) * W = k' * W + W := by ring
  apply Nat.div_eq_of_lt_le
  · rw [Nat.add_sub_cancel]
    omega
  · rw [Nat.add_sub_cancel, Nat.add_mul, one_mul]
    omega

/-- A power of three in the window `(W / c, 3 W / c]`. -/
theorem exists_pow3 (c W : ℕ) (hc : 0 < c) (hW : c < W) :
    ∃ i : ℕ, 1 ≤ i ∧ W < c * 3 ^ i ∧ c * 3 ^ i ≤ 3 * W := by
  have hex : ∃ i, W < c * 3 ^ i :=
    ⟨W, lt_of_lt_of_le (Nat.lt_pow_self (by norm_num)) (Nat.le_mul_of_pos_left _ hc)⟩
  have hi : W < c * 3 ^ Nat.find hex := Nat.find_spec hex
  have hi0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hi
    simp at hi
    omega
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hi0
  have hmin : ¬ W < c * 3 ^ j := Nat.find_min hex (by omega)
  refine ⟨Nat.find hex, by omega, hi, ?_⟩
  rw [hj, pow_succ]
  have : c * (3 ^ j * 3) = 3 * (c * 3 ^ j) := by ring
  omega


/-- The hard base case: the multiples of three are exactly `v` and `2 v`. -/
theorem base_double (A : Finset ℕ) (v : ℕ) (hv : 0 < v) (h3 : 3 ∣ v)
    (hA1 : A.filter (fun a => 3 ∣ a) = {v, 2 * v})
    (hA0 : (A.filter (fun a => ¬ 3 ∣ a)).Nonempty) (hpos : ∀ a ∈ A, 0 < a) :
    ∃ t M, 0 < M ∧ A.card + 2 ≤ 3 * (S t M A).card := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := A) (fun a => 3 ∣ a)
  have hc2 : (A.filter (fun a => 3 ∣ a)).card = 2 := by
    rw [hA1]
    exact Finset.card_pair (by omega)
  have hn0 : 0 < (A.filter (fun a => ¬ 3 ∣ a)).card := Finset.card_pos.mpr hA0
  have hvA1 : v ∈ A.filter (fun a => 3 ∣ a) := by
    rw [hA1]
    simp
  have h2vA1 : 2 * v ∈ A.filter (fun a => 3 ∣ a) := by
    rw [hA1]
    simp
  obtain ⟨W, hWmem, hWmax⟩ : ∃ W ∈ A.filter (fun a => ¬ 3 ∣ a),
      ∀ a ∈ A.filter (fun a => ¬ 3 ∣ a), a ≤ W :=
    ⟨_, Finset.max'_mem _ hA0, fun a ha => Finset.le_max' _ a ha⟩
  have hW3 : ¬ 3 ∣ W := (Finset.mem_filter.mp hWmem).2
  have hWne : W ≠ 2 * v := fun h => hW3 (h ▸ Dvd.dvd.mul_left h3 2)
  rcases lt_or_gt_of_ne hWne with hlt | hgt
  · -- Case A: every non-multiple of three is below `2 v`.
    have hsel0 : S 1 (2 * v) (A.filter (fun a => ¬ 3 ∣ a)) = ∅ := by
      unfold S
      rw [Finset.filter_eq_empty_iff]
      intro a ha
      have := hWmax a ha
      rw [mul_one, Nat.div_eq_of_lt (by omega)]
      norm_num
    have hsel1 : 1 ≤ (S 1 (2 * v) (A.filter (fun a => 3 ∣ a))).card := by
      apply Finset.card_pos.mpr
      refine ⟨2 * v, mem_S.mpr ⟨h2vA1, ?_⟩⟩
      rw [mul_one, Nat.div_self (by omega)]
    obtain ⟨t', ht'⟩ := lift2 1 (2 * v) (by omega) A (by
      rw [hsel0, Finset.card_empty]
      omega)
    exact ⟨t', 2 * v, by omega, by omega⟩
  · -- Case B: the largest non-multiple of three exceeds `2 v`.
    obtain ⟨i, hi1, hilo, hihi⟩ := exists_pow3 (2 * v) W (by omega) hgt
    have hW0 : 0 < W := by omega
    have hk3 : 3 ∣ 3 ^ i := dvd_pow_self 3 (by omega)
    have hcop3 : Nat.Coprime (3 ^ i) W :=
      Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hW3)
    obtain ⟨j, hj⟩ : ∃ j, (j * W) % 3 = 1 := by
      rcases (by omega : W % 3 = 1 ∨ W % 3 = 2) with h | h
      · exact ⟨1, by omega⟩
      · exact ⟨2, by omega⟩
    generalize 3 ^ i = k at hilo hihi hk3 hcop3
    have hk1mod : (k + j * W) % 3 = 1 := by omega
    have hk1pos : 0 < k + j * W := by omega
    have hcop : Nat.Coprime (k + j * W) W := (Nat.coprime_add_mul_right_left k W j).mpr hcop3
    have hnd : ∀ a, 0 < a → a < W → ¬ W ∣ a * (k + j * W) := by
      intro a ha haW hdvd
      have := Nat.le_of_dvd ha (Nat.Coprime.dvd_of_dvd_mul_right hcop.symm hdvd)
      omega
    -- one of `v`, `2 v` is selected at `k1 / W`
    obtain ⟨b, hbA1, hbW, hbsel⟩ : ∃ b ∈ A.filter (fun a => 3 ∣ a),
        b < W ∧ (b * (k + j * W) / W) % 3 = 1 := by
      have hlo : W < 2 * (v * k) := by
        rw [← mul_assoc]
        exact hilo
      have hhi : 2 * (v * k) < 3 * W := by
        rcases Nat.lt_or_ge (2 * (v * k)) (3 * W) with h | h
        · exact h
        · exfalso
          have hihi' : 2 * (v * k) ≤ 3 * W := by
            rw [← mul_assoc]
            exact hihi
          have heq : 2 * v * k = 3 * W := by
            rw [mul_assoc]
            omega
          have hd : W ∣ 2 * v * k := ⟨3, by rw [heq]; ring⟩
          have := Nat.le_of_dvd (by omega) (Nat.Coprime.dvd_of_dvd_mul_right hcop3.symm hd)
          omega
      by_cases hc : 2 * (v * k) < 2 * W
      · refine ⟨2 * v, h2vA1, hgt, ?_⟩
        rw [shift_mul3 k W j (2 * v) hW0 (Dvd.dvd.mul_left h3 2)]
        have : 2 * v * k / W = 1 :=
          Nat.div_eq_of_lt_le (by rw [mul_assoc]; omega) (by rw [mul_assoc]; omega)
        rw [this]
      · refine ⟨v, hvA1, by omega, ?_⟩
        rw [shift_mul3 k W j v hW0 h3]
        have : v * k / W = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
        rw [this]
    have hbpos : 0 < b := hpos b (Finset.mem_filter.mp hbA1).1
    have hA1P1 : 1 ≤ (S (k + j * W) W (A.filter (fun a => 3 ∣ a))).card :=
      Finset.card_pos.mpr ⟨b, mem_S.mpr ⟨hbA1, hbsel⟩⟩
    have hA1P2 : 1 ≤ (S ((k + j * W) * W - 1) (W * W) (A.filter (fun a => 3 ∣ a))).card :=
      Finset.card_pos.mpr ⟨b, mem_S.mpr ⟨hbA1, by
        rw [floor_left b (k + j * W) W hbpos hbW hk1pos (hnd b hbpos hbW)]
        exact hbsel⟩⟩
    have hWnot : W ∉ S ((k + j * W) * W - 1) (W * W) (A.filter (fun a => ¬ 3 ∣ a)) := by
      intro h
      have := (mem_S.mp h).2
      rw [floor_self (k + j * W) W hW0 hk1pos] at this
      omega
    have hA0eq : S (k + j * W) W (A.filter (fun a => ¬ 3 ∣ a))
        = insert W (S ((k + j * W) * W - 1) (W * W) (A.filter (fun a => ¬ 3 ∣ a))) := by
      ext a
      simp only [mem_S, Finset.mem_insert]
      constructor
      · rintro ⟨haA0, hsel⟩
        by_cases haW : a = W
        · left
          exact haW
        · right
          have hle := hWmax a haA0
          have hapos := hpos a (Finset.mem_filter.mp haA0).1
          refine ⟨haA0, ?_⟩
          rw [floor_left a (k + j * W) W hapos (by omega) hk1pos (hnd a hapos (by omega))]
          exact hsel
      · rintro (haW | ⟨haA0, hsel⟩)
        · subst haW
          refine ⟨hWmem, ?_⟩
          rw [Nat.mul_div_cancel_left _ hW0]
          exact hk1mod
        · by_cases haW : a = W
          · exfalso
            subst haW
            exact hWnot (mem_S.mpr ⟨haA0, hsel⟩)
          · have hle := hWmax a haA0
            have hapos := hpos a (Finset.mem_filter.mp haA0).1
            refine ⟨haA0, ?_⟩
            rw [← floor_left a (k + j * W) W hapos (by omega) hk1pos (hnd a hapos (by omega))]
            exact hsel
    have hcardeq : (S (k + j * W) W (A.filter (fun a => ¬ 3 ∣ a))).card
        = (S ((k + j * W) * W - 1) (W * W) (A.filter (fun a => ¬ 3 ∣ a))).card + 1 := by
      rw [hA0eq, Finset.card_insert_of_notMem hWnot]
    by_cases hbal : 3 * (S (k + j * W) W (A.filter (fun a => ¬ 3 ∣ a))).card
        = (A.filter (fun a => ¬ 3 ∣ a)).card
    · obtain ⟨t', ht'⟩ := lift2 ((k + j * W) * W - 1) (W * W) (Nat.mul_pos hW0 hW0) A (by omega)
      exact ⟨t', W * W, Nat.mul_pos hW0 hW0, by omega⟩
    · obtain ⟨t', ht'⟩ := lift2 (k + j * W) W hW0 A hbal
      exact ⟨t', W, hW0, by omega⟩

/-- The case of exactly two multiples of three. -/
theorem two_case (A : Finset ℕ) (x y : ℕ) (hxy : x < y)
    (hA1 : A.filter (fun a => 3 ∣ a) = {x, y}) (hpos : ∀ a ∈ A, 0 < a) (hcard : 3 ≤ A.card) :
    ∃ t M, 0 < M ∧ A.card + 2 ≤ 3 * (S t M A).card := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := A) (fun a => 3 ∣ a)
  have hc2 : (A.filter (fun a => 3 ∣ a)).card = 2 := by
    rw [hA1]
    exact Finset.card_pair (by omega)
  have hxA1 : x ∈ A.filter (fun a => 3 ∣ a) := by
    rw [hA1]
    simp
  have hx0 : 0 < x := hpos x (Finset.mem_filter.mp hxA1).1
  by_cases hy : y = 2 * x
  · subst hy
    exact base_double A x hx0 (Finset.mem_filter.mp hxA1).2 hA1 (Finset.card_pos.mp (by omega)) hpos
  · obtain ⟨t, M, hM, hsx, hsy⟩ := pair x y hx0 hxy hy
    have hfull : S t M (A.filter (fun a => 3 ∣ a)) = A.filter (fun a => 3 ∣ a) := by
      unfold S
      rw [Finset.filter_eq_self]
      intro a ha
      rw [hA1] at ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hsx
      · exact hsy
    obtain ⟨t', ht'⟩ := lift1 t M hM A
    rw [hfull] at ht'
    exact ⟨t', M, hM, by omega⟩

/-- Bourgain's bound for finite sets of positive naturals, with a dilation-type witness. -/
theorem core : ∀ N : ℕ, ∀ A : Finset ℕ, (∀ a ∈ A, 0 < a ∧ a ≤ N) → 3 ≤ A.card →
    ∃ t M, 0 < M ∧ A.card + 2 ≤ 3 * (S t M A).card := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro A hA hcard
    have hsplit := Finset.card_filter_add_card_filter_not (s := A) (fun a => 3 ∣ a)
    have hpos : ∀ a ∈ A, 0 < a := fun a ha => (hA a ha).1
    by_cases h3 : 3 ≤ (A.filter (fun a => 3 ∣ a)).card
    · -- inductive step: divide the multiples of three by three
      have himg : ((Finset.range (N + 1)).filter (fun b => 3 * b ∈ A)).image (fun b => 3 * b)
          = A.filter (fun a => 3 ∣ a) := by
        ext a
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨b, ⟨_, hb⟩, rfl⟩
          exact ⟨hb, dvd_mul_right 3 b⟩
        · rintro ⟨ha, b, rfl⟩
          have := (hA _ ha).2
          exact ⟨b, ⟨by omega, ha⟩, rfl⟩
      have hcardA' : ((Finset.range (N + 1)).filter (fun b => 3 * b ∈ A)).card
          = (A.filter (fun a => 3 ∣ a)).card := by
        rw [← himg, Finset.card_image_of_injective _ (fun x y h => by simpa using h)]
      have hNpos : 0 < N := by
        obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
        have := hA a ha
        omega
      obtain ⟨t, M, hM, hle⟩ := ih (N / 3) (Nat.div_lt_self hNpos (by norm_num))
        ((Finset.range (N + 1)).filter (fun b => 3 * b ∈ A)) (by
          intro b hb
          simp only [Finset.mem_filter, Finset.mem_range] at hb
          have := hA _ hb.2
          omega) (by omega)
      have hsc := scale3 t M ((Finset.range (N + 1)).filter (fun b => 3 * b ∈ A))
      rw [himg] at hsc
      obtain ⟨t', ht'⟩ := lift1 t (3 * M) (by omega) A
      exact ⟨t', 3 * M, by omega, by omega⟩
    · -- at most two multiples of three
      have hle2 : (A.filter (fun a => 3 ∣ a)).card ≤ 2 := by omega
      rcases (by omega : (A.filter (fun a => 3 ∣ a)).card = 0 ∨ (A.filter (fun a => 3 ∣ a)).card = 1
          ∨ (A.filter (fun a => 3 ∣ a)).card = 2) with h0 | h1 | h2
      · -- no multiple of three: use the residue classes
        have hs := S_sum_A0 0 1 (by norm_num) (A.filter (fun a => ¬ 3 ∣ a))
          (fun a ha => (Finset.mem_filter.mp ha).2)
        have hz : (S 0 1 (A.filter (fun a => ¬ 3 ∣ a))).card = 0 := by
          rw [Finset.card_eq_zero]
          unfold S
          rw [Finset.filter_eq_empty_iff]
          intro a _
          simp
        have s1 := S_card_split (0 + 1) 1 A
        have s2 := S_card_split (0 + 2 * 1) 1 A
        by_contra hcon
        simp only [not_exists, not_and, not_le] at hcon
        have c1 := hcon (0 + 1) 1 (by norm_num)
        have c2 := hcon (0 + 2 * 1) 1 (by norm_num)
        omega
      · -- exactly one multiple of three
        obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h1
        have huA1 : u ∈ A.filter (fun a => 3 ∣ a) := by
          rw [hu]
          simp
        have hu0 : 0 < u := hpos u (Finset.mem_filter.mp huA1).1
        have hsel : 1 ≤ (S 1 u (A.filter (fun a => 3 ∣ a))).card := by
          apply Finset.card_pos.mpr
          refine ⟨u, mem_S.mpr ⟨huA1, ?_⟩⟩
          rw [mul_one, Nat.div_self hu0]
        obtain ⟨t', ht'⟩ := lift1 1 u hu0 A
        exact ⟨t', u, hu0, by omega⟩
      · -- exactly two multiples of three
        obtain ⟨x, y, hxy, hA1⟩ := Finset.card_eq_two.mp h2
        rcases lt_or_gt_of_ne hxy with hlt | hgt
        · exact two_case A x y hlt hA1 hpos hcard
        · exact two_case A y x hgt (by rw [hA1, Finset.pair_comm]) hpos hcard

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @Erdos792.erdos_792.variants.bourgain := by
  intro A h_positive h_card
  have hinj : Set.InjOn Int.toNat (A : Set ℤ) := by
    intro a ha b hb hab
    have ha' := h_positive a ha
    have hb' := h_positive b hb
    have h1 := Int.toNat_of_nonneg ha'.le
    have h2 := Int.toNat_of_nonneg hb'.le
    rw [← h1, ← h2, hab]
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range (A.image Int.toNat)
  have hcardA' : (A.image Int.toNat).card = A.card := Finset.card_image_of_injOn hinj
  obtain ⟨t, M, hM, hle⟩ := core N (A.image Int.toNat) (by
    intro a' ha'
    have hlt := Finset.mem_range.mp (hN ha')
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha'
    have := h_positive a ha
    constructor
    · omega
    · omega) (by omega)
  refine ⟨A.filter (fun a : ℤ => (a.toNat * t / M) % 3 = 1), Finset.filter_subset _ _, ?_, ?_⟩
  · unfold IsSumFree
    rw [Set.disjoint_left]
    rintro z ⟨x, hx, y, hy, rfl⟩ hz
    have hx' := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
    have hy' := Finset.mem_filter.mp (Finset.mem_coe.mp hy)
    have hz' := Finset.mem_filter.mp (Finset.mem_coe.mp hz)
    have hxp := h_positive x hx'.1
    have hyp := h_positive y hy'.1
    have hadd : (x + y).toNat = x.toNat + y.toNat := Int.toNat_add hxp.le hyp.le
    have := sel_add t M x.toNat y.toNat hx'.2 hy'.2
    rw [← hadd] at this
    exact this hz'.2
  · have hfe : (S t M (A.image Int.toNat)).card
        = (A.filter (fun a : ℤ => (a.toNat * t / M) % 3 = 1)).card := by
      unfold S
      rw [Finset.filter_image]
      exact Finset.card_image_of_injOn (hinj.mono (by
        intro a ha
        exact (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).1))
    omega
