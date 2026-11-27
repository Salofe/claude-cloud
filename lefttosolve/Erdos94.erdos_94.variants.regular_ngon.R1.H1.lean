import OMAReductions.R_Erdos94_erdos_94_variants_regular_ngon_R1

/-!
# Step H1 of the reduction Erdos94.erdos_94.variants.regular_ngon.R1

The regular n-gon reaches B(n). With m(u) the number of unordered pairs at distance u, the sum
of m(u)^2 is a quarter of the number of pairs of ordered pairs of distinct vertices at equal
distance. Index the vertices by ZMod n; the distance between the vertices k + e and k depends
only on e up to sign (it is the square root of 2 - 2 cos(2 pi e / n)). So every triple
(k, k', (e, e')) with e, e' nonzero and e = e' or e = -e' gives such a pair of pairs, injectively.
There are n^2 (2 (n - 1) - z) such triples, where z (the number of nonzero e with e = -e) is 0
for odd n and at most 1 for even n, which gives exactly the bound B(n).
-/

open EuclideanGeometry Erdos94 Real Finset

namespace OMA.Helpers

lemma sum_sq_fiber {α β : Type*} [DecidableEq α] [DecidableEq β] (S : Finset α) (g : α → β) :
    ∑ u ∈ S.image g, (#(S.filter (fun a => g a = u))) ^ 2 =
      #((S ×ˢ S).filter (fun p => g p.1 = g p.2)) := by
  rw [Finset.card_filter, Finset.sum_product]
  have h1 : ∀ a ∈ S, (∑ b ∈ S, if g a = g b then 1 else 0) =
      #(S.filter (fun b => g b = g a)) := by
    intro a _
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : g a = g b
    · simp [h]
    · simp [h, Ne.symm h]
  rw [Finset.sum_congr rfl h1, Finset.sum_comp (fun u => #(S.filter (fun b => g b = u))) g]
  apply Finset.sum_congr rfl
  intro u _
  rw [smul_eq_mul, sq]

/-- The ordered pairs of distinct points at distance `d` come two by two, a pair together with
its swap: every fibre of the map to unordered pairs has exactly two elements. -/
lemma even_card_dist {X : Type*} [MetricSpace X] [DecidableEq X] (P : Finset X) (d : ℝ) :
    Even #(P.offDiag.filter fun (pair : X × X) => dist pair.1 pair.2 = d) := by
  set F := P.offDiag.filter fun (pair : X × X) => dist pair.1 pair.2 = d with hF
  have fib : ∀ z ∈ F.image (fun p : X × X => s(p.1, p.2)),
      #(F.filter (fun a : X × X => s(a.1, a.2) = z)) = 2 := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨hoff, hd⟩ := Finset.mem_filter.1 hp
    obtain ⟨h1, h2, h12⟩ := Finset.mem_offDiag.1 hoff
    have hsw : p.swap ∈ F := by
      refine Finset.mem_filter.2 ⟨Finset.mem_offDiag.2 ⟨h2, h1, Ne.symm h12⟩, ?_⟩
      rw [Prod.fst_swap, Prod.snd_swap, dist_comm]
      exact hd
    have hne : p ≠ p.swap := fun h => h12 (by simpa using congrArg Prod.fst h)
    have hset : F.filter (fun a : X × X => s(a.1, a.2) = s(p.1, p.2)) = {p, p.swap} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hq⟩
        exact Sym2.mk_eq_mk_iff.1 hq
      · rintro (rfl | rfl)
        · exact ⟨hp, rfl⟩
        · exact ⟨hsw, Sym2.eq_swap⟩
    rw [hset, Finset.card_pair hne]
  rw [Finset.card_eq_sum_card_image (fun p : X × X => s(p.1, p.2)) F, Finset.sum_congr rfl fib,
    Finset.sum_const, smul_eq_mul]
  exact ⟨_, mul_two _⟩

/-- Sum of the squared multiplicities is a quarter of the number of pairs of ordered pairs at
equal distance. -/
lemma sum_mult_sq {X : Type*} [MetricSpace X] [DecidableEq X] (P : Finset X) :
    ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2 =
      (#((P.offDiag ×ˢ P.offDiag).filter
        (fun p => dist p.1.1 p.1.2 = dist p.2.1 p.2.2)) : ℝ) / 4 := by
  rw [← sum_sq_fiber P.offDiag (fun pair : X × X => dist pair.1 pair.2)]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  unfold distanceMultiplicity
  rw [Nat.cast_div (even_iff_two_dvd.1 (even_card_dist P u)) (by norm_num)]
  push_cast
  ring

noncomputable def q (n : ℕ) (a : ZMod n) : ℝ² :=
  !₂[Real.cos (2 * Real.pi * (a.val : ℝ) / n), Real.sin (2 * Real.pi * (a.val : ℝ) / n)]

lemma dist_q (n : ℕ) (a b : ZMod n) :
    dist (q n a) (q n b) =
      Real.sqrt (2 - 2 * Real.cos (2 * π * ((a.val : ℝ) - b.val) / n)) := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  have e : 2 * π * ((a.val : ℝ) - b.val) / n = 2 * π * a.val / n - 2 * π * b.val / n := by ring
  rw [e, Real.cos_sub]
  simp only [q, Fin.sum_univ_two, Real.dist_eq, sq_abs, PiLp.toLp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination Real.sin_sq_add_cos_sq (2 * π * a.val / n) +
    Real.sin_sq_add_cos_sq (2 * π * b.val / n)


lemma cos_eq_of_dvd (n : ℕ) (hn : n ≠ 0) (x y : ℤ) (h : (n : ℤ) ∣ x - y) :
    Real.cos (2 * π * (x : ℝ) / n) = Real.cos (2 * π * (y : ℝ) / n) := by
  obtain ⟨t, ht⟩ := h
  have hx : (x : ℝ) = y + n * t := by
    have : x = y + n * t := by linarith
    rw [this]; push_cast; ring
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have e : 2 * π * ((y : ℝ) + n * t) / n = 2 * π * y / n + t * (2 * π) := by
    field_simp
  rw [hx, e, Real.cos_add_int_mul_two_pi]

/-- The cosine attached to a difference class. -/
noncomputable def cq (n : ℕ) (e : ZMod n) : ℝ := Real.cos (2 * π * (e.val : ℝ) / n)

lemma cq_neg (n : ℕ) [NeZero n] (e : ZMod n) : cq n (-e) = cq n e := by
  unfold cq
  have h := cos_eq_of_dvd n (NeZero.ne n) ((-e).val : ℤ) (-(e.val : ℤ)) (by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring)
  push_cast at h
  rw [h, show 2 * π * (-(e.val : ℝ)) / n = -(2 * π * (e.val : ℝ) / n) by ring, Real.cos_neg]

lemma dist_q_add (n : ℕ) [NeZero n] (k e : ZMod n) :
    dist (q n (k + e)) (q n k) = Real.sqrt (2 - 2 * cq n e) := by
  rw [dist_q]
  congr 2
  have h := cos_eq_of_dvd n (NeZero.ne n) (((k + e).val : ℤ) - k.val) (e.val : ℤ) (by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring)
  push_cast at h
  rw [h]
  rfl

lemma q_injective (n : ℕ) [NeZero n] : Function.Injective (q n) := by
  intro a b hab
  have hd : dist (q n a) (q n b) = 0 := by rw [hab, dist_self]
  rw [dist_q, Real.sqrt_eq_zero'] at hd
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have ha : (a.val : ℝ) < n := by exact_mod_cast ZMod.val_lt a
  have hb : (b.val : ℝ) < n := by exact_mod_cast ZMod.val_lt b
  have hc : Real.cos (2 * π * ((a.val : ℝ) - b.val) / n) = 1 := by
    linarith [Real.cos_le_one (2 * π * ((a.val : ℝ) - b.val) / n)]
  have hpi := Real.pi_pos
  have h1 : -(2 * π) < 2 * π * ((a.val : ℝ) - b.val) / n := by
    rw [lt_div_iff₀ hn]
    nlinarith [(Nat.cast_nonneg a.val : (0 : ℝ) ≤ a.val)]
  have h2 : 2 * π * ((a.val : ℝ) - b.val) / n < 2 * π := by
    rw [div_lt_iff₀ hn]
    nlinarith [(Nat.cast_nonneg b.val : (0 : ℝ) ≤ b.val)]
  rw [Real.cos_eq_one_iff_of_lt_of_lt h1 h2] at hc
  have h3 : ((a.val : ℝ) - b.val) = 0 := by
    rcases mul_eq_zero.1 ((div_eq_zero_iff.1 hc).resolve_right hn.ne') with h | h
    · nlinarith
    · exact h
  apply ZMod.val_injective
  exact_mod_cast (sub_eq_zero.1 h3)

lemma q_mem (n : ℕ) (a : ZMod n) [NeZero n] : q n a ∈ regularNGon n := by
  unfold regularNGon
  exact Finset.mem_image.2 ⟨a.val, Finset.mem_range.2 (ZMod.val_lt a), rfl⟩


lemma two_val_eq (n : ℕ) [NeZero n] (e : ZMod n) (he : e ≠ 0) (h : e = -e) : 2 * e.val = n := by
  have h2 : e + e = 0 := by
    nth_rewrite 2 [h]
    exact add_neg_cancel e
  have h3 : (e + e).val = 0 := by rw [h2, ZMod.val_zero]
  rw [ZMod.val_add] at h3
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h3
  have hlt := ZMod.val_lt e
  have hpos : e.val ≠ 0 := by rwa [ne_eq, ZMod.val_eq_zero]
  rcases c with _ | _ | c
  · omega
  · simp at hc; omega
  · nlinarith

lemma card_E (n : ℕ) [NeZero n] :
    #((((univ : Finset (ZMod n)).filter (· ≠ 0)) ×ˢ ((univ : Finset (ZMod n)).filter (· ≠ 0))).filter
        (fun e => e.1 = e.2 ∨ e.1 = -e.2)) +
      #(((univ : Finset (ZMod n)).filter (· ≠ 0)).filter (fun e => e = -e)) =
      2 * #((univ : Finset (ZMod n)).filter (· ≠ 0)) := by
  set N := (univ : Finset (ZMod n)).filter (· ≠ 0) with hN
  rw [Finset.card_filter, Finset.sum_product, Finset.card_filter, ← Finset.sum_add_distrib,
    mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro a ha
  have ha0 : a ≠ 0 := (Finset.mem_filter.1 ha).2
  rw [← Finset.card_filter]
  have hset : N.filter (fun b => a = b ∨ a = -b) = {a, -a} := by
    ext b
    simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨_, h | h⟩
      · exact Or.inl h.symm
      · right; rw [h, neg_neg]
    · rintro (h | h)
      · exact ⟨h ▸ ha0, Or.inl h.symm⟩
      · refine ⟨?_, Or.inr ?_⟩
        · rw [h]; exact neg_ne_zero.2 ha0
        · rw [h, neg_neg]
  rw [hset]
  by_cases h : a = -a
  · rw [if_pos h, ← h]
    simp
  · rw [if_neg h, Finset.card_pair h]

theorem lower (n : ℕ) :
    (if n % 2 = 1 then (n : ℝ) ^ 2 * ((n : ℝ) - 1) / 2
      else (n : ℝ) ^ 3 / 2 - 3 * (n : ℝ) ^ 2 / 4) ≤
      ∑ u ∈ distanceSet (regularNGon n), (distanceMultiplicity (regularNGon n) u : ℝ) ^ 2 := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : (0 : ℝ) ≤ ∑ u ∈ distanceSet (regularNGon 0),
        (distanceMultiplicity (regularNGon 0) u : ℝ) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    simpa using h0
  have : NeZero n := ⟨hn.ne'⟩
  rw [sum_mult_sq]
  set P := regularNGon n with hP
  set N := (univ : Finset (ZMod n)).filter (· ≠ 0) with hN
  set E := (N ×ˢ N).filter (fun e => e.1 = e.2 ∨ e.1 = -e.2) with hE
  set Z := N.filter (fun e => e = -e) with hZ
  set D := (P.offDiag ×ˢ P.offDiag).filter (fun p => dist p.1.1 p.1.2 = dist p.2.1 p.2.2) with hD
  have hinj : #(((univ : Finset (ZMod n)) ×ˢ (univ : Finset (ZMod n))) ×ˢ E) ≤ #D := by
    apply Finset.card_le_card_of_injOn (fun x : (ZMod n × ZMod n) × (ZMod n × ZMod n) =>
      ((q n (x.1.1 + x.2.1), q n x.1.1), (q n (x.1.2 + x.2.2), q n x.1.2)))
    · intro x hx
      have hx' := Finset.mem_product.1 hx
      obtain ⟨hxN, hxr⟩ := Finset.mem_filter.1 hx'.2
      obtain ⟨h1, h2⟩ := Finset.mem_product.1 hxN
      have h1' : x.2.1 ≠ 0 := (Finset.mem_filter.1 h1).2
      have h2' : x.2.2 ≠ 0 := (Finset.mem_filter.1 h2).2
      simp only [hD, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, Finset.mem_offDiag]
      refine ⟨⟨⟨q_mem n _, q_mem n _, ?_⟩, ⟨q_mem n _, q_mem n _, ?_⟩⟩, ?_⟩
      · intro h
        exact h1' (by simpa using q_injective n h)
      · intro h
        exact h2' (by simpa using q_injective n h)
      · rw [dist_q_add, dist_q_add]
        rcases hxr with h | h
        · rw [h]
        · rw [h, cq_neg]
    · intro x _ y _ hxy
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩ := hxy
      have hb' := q_injective n hb
      have hd' := q_injective n hd
      have ha' := q_injective n ha
      have hc' := q_injective n hc
      rw [hb'] at ha'
      rw [hd'] at hc'
      have e1 := add_left_cancel ha'
      have e2 := add_left_cancel hc'
      exact Prod.ext (Prod.ext hb' hd') (Prod.ext e1 e2)
  have hcardD : #(((univ : Finset (ZMod n)) ×ˢ (univ : Finset (ZMod n))) ×ˢ E) = n * n * #E := by
    simp [Finset.card_product, ZMod.card]
  have hNc : #N = n - 1 := by
    have : N = (univ : Finset (ZMod n)).erase 0 := by
      ext x; simp [hN]
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  have hEZ : #E + #Z = 2 * #N := card_E n
  have hZval : ∀ e ∈ Z, 2 * e.val = n := by
    intro e he
    obtain ⟨heN, hee⟩ := Finset.mem_filter.1 he
    exact two_val_eq n e (Finset.mem_filter.1 heN).2 hee
  have hZ1 : #Z ≤ 1 := by
    apply Finset.card_le_one.2
    intro a ha b hb
    apply ZMod.val_injective
    have := hZval a ha
    have := hZval b hb
    omega
  have hDE : (n : ℝ) * n * #E ≤ #D := by
    have := hinj
    rw [hcardD] at this
    exact_mod_cast this
  have hEr : (#E : ℝ) = 2 * ((n : ℝ) - 1) - #Z := by
    have h1 : (#E : ℝ) + #Z = 2 * (#N : ℝ) := by exact_mod_cast hEZ
    have h2 : (#N : ℝ) = (n : ℝ) - 1 := by
      rw [hNc, Nat.cast_sub (by omega)]
      simp
    linarith
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  split_ifs with hodd
  · have hZ0 : #Z = 0 := by
      apply Finset.card_eq_zero.2
      apply Finset.eq_empty_of_forall_notMem
      intro e he
      have := hZval e he
      omega
    rw [hZ0] at hEr
    simp at hEr
    rw [hEr] at hDE
    have hnn : (0 : ℝ) ≤ n := by positivity
    nlinarith
  · have hZr : (#Z : ℝ) ≤ 1 := by exact_mod_cast hZ1
    have hE' : 2 * ((n : ℝ) - 1) - 1 ≤ #E := by linarith
    have hnn : (0 : ℝ) ≤ (n : ℝ) * n := by positivity
    have := mul_le_mul_of_nonneg_left hE' hnn
    nlinarith

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos94_erdos_94_variants_regular_ngon_R1.H1 := by
  intro n
  exact OMA.Helpers.lower n
