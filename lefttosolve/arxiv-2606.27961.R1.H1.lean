import OMAReductions.R_arxiv_2606_27961_R1

/-!
# Step H1 of the reduction arxiv-2606.27961.R1

Let `s` be a section of the reduction map from the plane over `ZMod (p^2)` to the plane over
`ZMod p`, and for a direction `t` let `D t x = s (x + t) - s x`. Every value of `D t` reduces
to `t`. Summing `D t` along an orbit of `x ↦ x + t` telescopes to `0`, so `D t` is never
constant when `t ≠ 0`; this gives at least two values in every nonzero direction.

If `D u` has exactly two values `a, b`, the orbit sum of the cross form `w ↦ a.1 * w.2 - a.2 * w.1`
along an orbit is `N • (a.1 * b.2 - a.2 * b.1)` with `0 < N < p`, hence the cross form of `a`
and `b` vanishes: all values of `D u` are parallel. With two independent such directions `u`
and `v`, the cocycle identity shows `D u` is invariant under translation by `v` and `D v` under
translation by `u` (an element of the kernel of the reduction that is parallel to lifts of two
independent directions is zero). Then for `w = i • u + j • v` the values of `D w` contain all sums
of a value of `D (i • u)` and a value of `D (j • v)`, and these sums are pairwise distinct. So
`c (α • u + β • v) ≥ h α * h β` with `h 0 = 1` and `h α = 2` otherwise, and summing over the basis
coordinates gives `(2p - 1)^2`.

Only upstream definitions are used (`Plane`, `reduce`); all lemmas below are proved here.
-/

namespace OMA.Helpers

open OMA.S_arxiv_2606_27961

theorem tsd_pmul_eq_zero_iff (p : ℕ) [NeZero p] (z : ZMod (p ^ 2)) :
    (p : ZMod (p ^ 2)) * z = 0 ↔ p ∣ z.val := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (NeZero.ne p)⟩
  have h : (p : ZMod (p ^ 2)) * z = ((p * z.val : ℕ) : ZMod (p ^ 2)) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [h, ZMod.natCast_eq_zero_iff]
  have key : ∀ m : ℕ, p ^ 2 ∣ p * m ↔ p ∣ m := by
    intro m
    rw [pow_two]
    exact Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero (NeZero.ne p))
  exact key z.val

theorem tsd_val_cast (p : ℕ) [NeZero p] (z : ZMod (p ^ 2)) :
    ((z.val : ℕ) : ZMod p) = ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) z := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (NeZero.ne p)⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

theorem tsd_reduce_sub (p : ℕ) [NeZero p] (a b : Plane (p ^ 2)) :
    reduce p (a - b) = reduce p a - reduce p b := by
  unfold reduce
  simp only [Prod.fst_sub, Prod.snd_sub, tsd_val_cast, map_sub, Prod.mk_sub_mk]

theorem tsd_reduce_eq_zero_of_nsmul (p : ℕ) [NeZero p] (z : Plane (p ^ 2))
    (h : p • z = 0) : reduce p z = 0 := by
  have h1 : (p : ZMod (p ^ 2)) * z.1 = 0 := by
    have := congrArg Prod.fst h
    simpa [nsmul_eq_mul] using this
  have h2 : (p : ZMod (p ^ 2)) * z.2 = 0 := by
    have := congrArg Prod.snd h
    simpa [nsmul_eq_mul] using this
  rw [tsd_pmul_eq_zero_iff] at h1 h2
  unfold reduce
  exact Prod.ext ((ZMod.natCast_eq_zero_iff _ _).mpr h1) ((ZMod.natCast_eq_zero_iff _ _).mpr h2)

/-- Two vectors of the square plane that are both orthogonal, for the cross form, to a
vector in the kernel of the reduction, force that vector to vanish when their reductions
are independent. -/
theorem tsd_sep (p : ℕ) [NeZero p] (hp : p.Prime) (U V z : Plane (p ^ 2))
    (hind : (reduce p U).1 * (reduce p V).2 ≠ (reduce p U).2 * (reduce p V).1)
    (hz : reduce p z = 0) (hU : U.1 * z.2 - U.2 * z.1 = 0)
    (hV : V.1 * z.2 - V.2 * z.1 = 0) : z = 0 := by
  have := Fact.mk hp
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (NeZero.ne p)⟩
  obtain ⟨χ, hχ⟩ : ∃ χ : ZMod (p ^ 2) →+* ZMod p, ∀ w, ((w.val : ℕ) : ZMod p) = χ w :=
    ⟨ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p), tsd_val_cast p⟩
  have hz1 : p ∣ z.1.val := by
    have h0 : ((z.1.val : ℕ) : ZMod p) = 0 := congrArg Prod.fst hz
    exact (ZMod.natCast_eq_zero_iff _ _).mp h0
  have hz2 : p ∣ z.2.val := by
    have h0 : ((z.2.val : ℕ) : ZMod p) = 0 := congrArg Prod.snd hz
    exact (ZMod.natCast_eq_zero_iff _ _).mp h0
  obtain ⟨m1, hm1⟩ := hz1
  obtain ⟨m2, hm2⟩ := hz2
  have e1 : z.1 = (p : ZMod (p ^ 2)) * (m1 : ZMod (p ^ 2)) := by
    rw [← ZMod.natCast_zmod_val z.1, hm1, Nat.cast_mul]
  have e2 : z.2 = (p : ZMod (p ^ 2)) * (m2 : ZMod (p ^ 2)) := by
    rw [← ZMod.natCast_zmod_val z.2, hm2, Nat.cast_mul]
  have key : ∀ W : Plane (p ^ 2), W.1 * z.2 - W.2 * z.1 = 0 →
      χ W.1 * (m2 : ZMod p) - χ W.2 * (m1 : ZMod p) = 0 := by
    intro W hW
    have h' : (p : ZMod (p ^ 2)) * (W.1 * m2 - W.2 * m1) = 0 := by
      rw [e1, e2] at hW
      linear_combination hW
    rw [tsd_pmul_eq_zero_iff] at h'
    have h'' := (ZMod.natCast_eq_zero_iff _ p).mpr h'
    rw [hχ, map_sub, map_mul, map_mul, map_natCast, map_natCast] at h''
    exact h''
  have k1 := key U hU
  have k2 := key V hV
  have hind' : χ U.1 * χ V.2 ≠ χ U.2 * χ V.1 := by
    have h0 := hind
    unfold reduce at h0
    simpa only [hχ] using h0
  have hD : χ U.1 * χ V.2 - χ U.2 * χ V.1 ≠ 0 := sub_ne_zero.mpr hind'
  have hA : (m1 : ZMod p) = 0 := by
    have h0 : (m1 : ZMod p) * (χ U.1 * χ V.2 - χ U.2 * χ V.1) = 0 := by
      linear_combination (-(χ U.1)) * k2 + χ V.1 * k1
    exact (mul_eq_zero.mp h0).resolve_right hD
  have hB : (m2 : ZMod p) = 0 := by
    have h0 : (m2 : ZMod p) * (χ U.1 * χ V.2 - χ U.2 * χ V.1) = 0 := by
      linear_combination χ V.2 * k1 - χ U.2 * k2
    exact (mul_eq_zero.mp h0).resolve_right hD
  have z1 : z.1 = 0 := by
    obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff m1 p).mp hA
    rw [e1, hk, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    exact ⟨k, by ring⟩
  have z2 : z.2 = 0 := by
    obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff m2 p).mp hB
    rw [e2, hk, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    exact ⟨k, by ring⟩
  exact Prod.ext z1 z2

theorem tsd_red (p : ℕ) [NeZero p] (s : Plane p → Plane (p ^ 2))
    (hs : Function.RightInverse s (reduce p)) (t x : Plane p) :
    reduce p (s (x + t) - s x) = t := by
  rw [tsd_reduce_sub, hs (x + t), hs x]
  abel

theorem tsd_tele (p : ℕ) [NeZero p] (s : Plane p → Plane (p ^ 2)) (t x : Plane p) :
    ∑ k ∈ Finset.range p, (s (x + k • t + t) - s (x + k • t)) = 0 := by
  have h := Finset.sum_range_sub (fun k : ℕ => s (x + k • t)) p
  have hpt : p • t = 0 := by
    ext <;> simp [nsmul_eq_mul]
  simp only [succ_nsmul, ← add_assoc, hpt, add_zero, zero_smul, sub_self] at h
  exact h

theorem tsd_const (p : ℕ) [NeZero p] (s : Plane p → Plane (p ^ 2))
    (hs : Function.RightInverse s (reduce p)) (t x : Plane p) (e : Plane (p ^ 2))
    (h : ∀ k ∈ Finset.range p, s (x + k • t + t) - s (x + k • t) = e) : t = 0 := by
  have h1 := tsd_tele p s t x
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range] at h1
  have h2 := tsd_reduce_eq_zero_of_nsmul p e h1
  have h3 := h 0 (Finset.mem_range.mpr (Nat.pos_of_ne_zero (NeZero.ne p)))
  have h4 := tsd_red p s hs t (x + (0 : ℕ) • t)
  rw [h3, h2] at h4
  exact h4.symm

theorem tsd_two (p : ℕ) [NeZero p] (s : Plane p → Plane (p ^ 2))
    (hs : Function.RightInverse s (reduce p)) (t : Plane p) (ht : t ≠ 0) :
    2 ≤ (Set.range (fun x : Plane p => s (x + t) - s x)).ncard := by
  by_contra hlt
  have hpos : 0 < (Set.range (fun x : Plane p => s (x + t) - s x)).ncard :=
    (Set.ncard_pos (Set.finite_range _)).mpr (Set.range_nonempty _)
  obtain ⟨e, he⟩ := Set.ncard_eq_one.mp
    (show (Set.range (fun x : Plane p => s (x + t) - s x)).ncard = 1 by omega)
  apply ht
  apply tsd_const p s hs t 0 e
  intro k _
  have hm : s (0 + k • t + t) - s (0 + k • t) ∈
      Set.range (fun x : Plane p => s (x + t) - s x) := ⟨_, rfl⟩
  rw [he] at hm
  exact hm

theorem tsd_cross_sum (p : ℕ) (a : Plane (p ^ 2)) (S : Finset ℕ) (g : ℕ → Plane (p ^ 2)) :
    ∑ k ∈ S, (a.1 * (g k).2 - a.2 * (g k).1) =
      a.1 * (∑ k ∈ S, g k).2 - a.2 * (∑ k ∈ S, g k).1 := by
  rw [Prod.fst_sum, Prod.snd_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_sub_distrib]

/-- In a direction with exactly two difference values, all these values are parallel for the
cross form. -/
theorem tsd_par (p : ℕ) [NeZero p] (hp : p.Prime) (s : Plane p → Plane (p ^ 2))
    (hs : Function.RightInverse s (reduce p)) (u : Plane p) (hu0 : u ≠ 0)
    (hu : (Set.range (fun x : Plane p => s (x + u) - s x)).ncard = 2) (x y : Plane p) :
    (s (x + u) - s x).1 * (s (y + u) - s y).2 - (s (x + u) - s x).2 * (s (y + u) - s y).1 = 0 := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (NeZero.ne p)⟩
  obtain ⟨a, b, hab, hr⟩ := Set.ncard_eq_two.mp hu
  have mem : ∀ z : Plane p, s (z + u) - s z = a ∨ s (z + u) - s z = b := by
    intro z
    have hm : s (z + u) - s z ∈ Set.range (fun x : Plane p => s (x + u) - s x) := ⟨z, rfl⟩
    rw [hr] at hm
    simpa using hm
  have hw : a.1 * b.2 - a.2 * b.1 = 0 := by
    obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S = (Finset.range p).filter
        (fun k : ℕ => s (0 + k • u + u) - s (0 + k • u) = b) := ⟨_, rfl⟩
    have hsum : ∑ k ∈ Finset.range p, (a.1 * (s (0 + k • u + u) - s (0 + k • u)).2 -
        a.2 * (s (0 + k • u + u) - s (0 + k • u)).1) = 0 := by
      have h := tsd_cross_sum p a (Finset.range p) (fun k => s (0 + k • u + u) - s (0 + k • u))
      beta_reduce at h
      rw [h, tsd_tele p s u 0]
      simp
    have hsum2 : ∑ k ∈ Finset.range p, (a.1 * (s (0 + k • u + u) - s (0 + k • u)).2 -
        a.2 * (s (0 + k • u + u) - s (0 + k • u)).1) = S.card • (a.1 * b.2 - a.2 * b.1) := by
      rw [← Finset.sum_const, hS, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k _
      rcases mem (0 + k • u) with h | h
      · rw [h, if_neg hab]
        ring
      · rw [h, if_pos rfl]
    have hN0 : S.card ≠ 0 := by
      intro h0
      rw [Finset.card_eq_zero] at h0
      apply hu0
      apply tsd_const p s hs u 0 a
      intro k hk
      rcases mem (0 + k • u) with h | h
      · exact h
      · exfalso
        have hk' : k ∈ S := by
          rw [hS]
          exact Finset.mem_filter.mpr ⟨hk, h⟩
        rw [h0] at hk'
        simp at hk'
    have hNle : S.card ≤ p := by
      rw [hS]
      exact (Finset.card_filter_le _ _).trans (Finset.card_range p).le
    have hNp : S.card ≠ p := by
      intro hp'
      have hSeq : S = Finset.range p := by
        apply Finset.eq_of_subset_of_card_le
        · rw [hS]
          exact Finset.filter_subset _ _
        · rw [Finset.card_range, hp']
      apply hu0
      apply tsd_const p s hs u 0 b
      intro k hk
      rw [← hSeq, hS] at hk
      exact (Finset.mem_filter.mp hk).2
    have hcop : Nat.Coprime S.card (p ^ 2) := by
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hN0) (lt_of_le_of_ne hNle hNp)
    have h0 : (S.card : ZMod (p ^ 2)) * (a.1 * b.2 - a.2 * b.1) = 0 := by
      rw [← nsmul_eq_mul, ← hsum2, hsum]
    have hunit : IsUnit (S.card : ZMod (p ^ 2)) := by
      have h1 := (ZMod.unitOfCoprime S.card hcop).isUnit
      rwa [ZMod.coe_unitOfCoprime] at h1
    exact (hunit.mul_right_eq_zero).mp h0
  rcases mem x with hx | hx <;> rcases mem y with hy | hy <;> rw [hx, hy]
  · ring
  · exact hw
  · linear_combination -hw
  · ring

theorem tsd_inv (p : ℕ) [NeZero p] (hp : p.Prime) (s : Plane p → Plane (p ^ 2))
    (hs : Function.RightInverse s (reduce p)) (u v : Plane p) (U V : Plane (p ^ 2))
    (hUu : reduce p U = u) (hVv : reduce p V = v) (hind : u.1 * v.2 ≠ u.2 * v.1)
    (hPu : ∀ x, U.1 * (s (x + u) - s x).2 - U.2 * (s (x + u) - s x).1 = 0)
    (hPv : ∀ x, V.1 * (s (x + v) - s x).2 - V.2 * (s (x + v) - s x).1 = 0) (x : Plane p) :
    s (x + v + u) - s (x + v) = s (x + u) - s x := by
  have hz := tsd_sep p hp U V ((s (x + v + u) - s (x + v)) - (s (x + u) - s x))
    (by rwa [hUu, hVv]) ?_ ?_ ?_
  · exact sub_eq_zero.mp hz
  · rw [tsd_reduce_sub, tsd_red p s hs, tsd_red p s hs, sub_self]
  · have h1 := hPu (x + v)
    have h2 := hPu x
    simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2 ⊢
    linear_combination h1 - h2
  · have h1 := hPv (x + u)
    have h2 := hPv x
    have e : (s (x + v + u) - s (x + v)) - (s (x + u) - s x) =
        (s (x + u + v) - s (x + u)) - (s (x + v) - s x) := by
      rw [add_right_comm x v u]
      abel
    rw [e]
    simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2 ⊢
    linear_combination h1 - h2

theorem tsd_lift (p : ℕ) (s : Plane p → Plane (p ^ 2)) (u v : Plane p)
    (U : Plane (p ^ 2))
    (hinv : ∀ x, s (x + v + u) - s (x + v) = s (x + u) - s x)
    (hPu : ∀ x, U.1 * (s (x + u) - s x).2 - U.2 * (s (x + u) - s x).1 = 0) (k : ℕ) :
    (∀ j : ℕ, ∀ x, s (x + j • v + k • u) - s (x + j • v) = s (x + k • u) - s x) ∧
    (∀ x, U.1 * (s (x + k • u) - s x).2 - U.2 * (s (x + k • u) - s x).1 = 0) := by
  have hinvj : ∀ j : ℕ, ∀ x, s (x + j • v + u) - s (x + j • v) = s (x + u) - s x := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [succ_nsmul, ← add_assoc, hinv (x + j • v), ih x]
  induction k with
  | zero =>
    exact ⟨fun j x => by simp, fun x => by simp⟩
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have coc : ∀ y, s (y + (k + 1) • u) - s y =
        (s (y + k • u + u) - s (y + k • u)) + (s (y + k • u) - s y) := by
      intro y
      rw [succ_nsmul, ← add_assoc]
      abel
    constructor
    · intro j x
      rw [coc, coc, ih1 j x, add_right_comm x (j • v) (k • u), hinvj j (x + k • u)]
    · intro x
      rw [coc]
      have h1 := hPu (x + k • u)
      have h2 := ih2 x
      simp only [Prod.fst_add, Prod.snd_add]
      linear_combination h1 + h2

theorem tsd_coc (p : ℕ) (s : Plane p → Plane (p ^ 2)) (x t t' : Plane p) :
    s (x + (t + t')) - s x = (s (x + t' + t) - s (x + t')) + (s (x + t') - s x) := by
  rw [show x + (t + t') = x + t' + t by abel]
  abel

theorem tsd_smul_ne_zero (p : ℕ) [Fact p.Prime] (α : ZMod p) (t : Plane p) (hα : α ≠ 0)
    (ht : t ≠ 0) : α • t ≠ 0 := by
  intro h
  apply ht
  have h1 : α * t.1 = 0 := congrArg Prod.fst h
  have h2 : α * t.2 = 0 := congrArg Prod.snd h
  exact Prod.ext ((mul_eq_zero.mp h1).resolve_left hα) ((mul_eq_zero.mp h2).resolve_left hα)

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_arxiv_2606_27961_R1.H1 := by
  intro p _ hp _ s hs c hex
  obtain ⟨u, v, huv, hu, hv⟩ := hex
  have := Fact.mk hp
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at huv
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at huv
  obtain ⟨U, hUdef⟩ : ∃ U : OMA.S_arxiv_2606_27961.Plane (p ^ 2), U = s (0 + u) - s 0 :=
    ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V : OMA.S_arxiv_2606_27961.Plane (p ^ 2), V = s (0 + v) - s 0 :=
    ⟨_, rfl⟩
  have hUu : OMA.S_arxiv_2606_27961.reduce p U = u := by
    rw [hUdef]
    exact tsd_red p s hs u 0
  have hVv : OMA.S_arxiv_2606_27961.reduce p V = v := by
    rw [hVdef]
    exact tsd_red p s hs v 0
  have hPu : ∀ x, U.1 * (s (x + u) - s x).2 - U.2 * (s (x + u) - s x).1 = 0 := by
    intro x
    rw [hUdef]
    exact tsd_par p hp s hs u hu0 hu 0 x
  have hPv : ∀ x, V.1 * (s (x + v) - s x).2 - V.2 * (s (x + v) - s x).1 = 0 := by
    intro x
    rw [hVdef]
    exact tsd_par p hp s hs v hv0 hv 0 x
  have hvu : v.1 * u.2 ≠ v.2 * u.1 := by
    intro h
    apply huv
    linear_combination -h
  have hinv_uv := tsd_inv p hp s hs u v U V hUu hVv huv hPu hPv
  have hinv_vu := tsd_inv p hp s hs v u V U hVv hUu hvu hPv hPu
  have lift_u := tsd_lift p s u v U hinv_uv hPu
  have lift_v := tsd_lift p s v u V hinv_vu hPv
  have he_inj : Function.Injective
      (fun q : ZMod p × ZMod p => (q.1 • u + q.2 • v : OMA.S_arxiv_2606_27961.Plane p)) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : a * u.1 + b * v.1 = a' * u.1 + b' * v.1 := congrArg Prod.fst h
    have h2 : a * u.2 + b * v.2 = a' * u.2 + b' * v.2 := congrArg Prod.snd h
    have hD : u.1 * v.2 - u.2 * v.1 ≠ 0 := sub_ne_zero.mpr huv
    have ha : (a - a') * (u.1 * v.2 - u.2 * v.1) = 0 := by
      linear_combination v.2 * h1 - v.1 * h2
    have hb : (b - b') * (u.1 * v.2 - u.2 * v.1) = 0 := by
      linear_combination u.1 * h2 - u.2 * h1
    have ha' := sub_eq_zero.mp ((mul_eq_zero.mp ha).resolve_right hD)
    have hb' := sub_eq_zero.mp ((mul_eq_zero.mp hb).resolve_right hD)
    rw [ha', hb']
  have he_bij := he_inj.bijective_of_finite
  have hdec : ∀ x : OMA.S_arxiv_2606_27961.Plane p, ∃ i j : ℕ, x = i • u + j • v := by
    intro x
    obtain ⟨⟨a, b⟩, hab⟩ := he_bij.2 x
    refine ⟨a.val, b.val, ?_⟩
    rw [← hab]
    simp only
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ← Nat.cast_smul_eq_nsmul (ZMod p),
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have hprod : ∀ i j : ℕ,
      (Set.range (fun x : OMA.S_arxiv_2606_27961.Plane p => s (x + i • u) - s x)).ncard *
      (Set.range (fun x : OMA.S_arxiv_2606_27961.Plane p => s (x + j • v) - s x)).ncard ≤
      (Set.range (fun x : OMA.S_arxiv_2606_27961.Plane p =>
        s (x + (i • u + j • v)) - s x)).ncard := by
    intro i j
    rw [← Set.ncard_prod]
    have hinj : Set.InjOn
        (fun q : OMA.S_arxiv_2606_27961.Plane (p ^ 2) × OMA.S_arxiv_2606_27961.Plane (p ^ 2) =>
          q.1 + q.2)
        ((Set.range (fun x : OMA.S_arxiv_2606_27961.Plane p => s (x + i • u) - s x)) ×ˢ
          (Set.range (fun x : OMA.S_arxiv_2606_27961.Plane p => s (x + j • v) - s x))) := by
      rintro ⟨y1, z1⟩ ⟨⟨x1, rfl⟩, ⟨x2, rfl⟩⟩ ⟨y2, z2⟩ ⟨⟨x3, rfl⟩, ⟨x4, rfl⟩⟩ h
      simp only at h
      have e : (s (x1 + i • u) - s x1) - (s (x3 + i • u) - s x3) =
          (s (x4 + j • v) - s x4) - (s (x2 + j • v) - s x2) := by
        rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
      have hz := tsd_sep p hp U V ((s (x1 + i • u) - s x1) - (s (x3 + i • u) - s x3))
        (by rwa [hUu, hVv]) ?_ ?_ ?_
      · have hy : s (x1 + i • u) - s x1 = s (x3 + i • u) - s x3 := sub_eq_zero.mp hz
        rw [hy] at h
        have hz' := add_left_cancel h
        simp only [hy, hz']
      · rw [tsd_reduce_sub, tsd_red p s hs, tsd_red p s hs, sub_self]
      · have h1 := (lift_u i).2 x1
        have h2 := (lift_u i).2 x3
        simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2 ⊢
        linear_combination h1 - h2
      · rw [e]
        have h1 := (lift_v j).2 x4
        have h2 := (lift_v j).2 x2
        simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2 ⊢
        linear_combination h1 - h2
    have hsub : (fun q : OMA.S_arxiv_2606_27961.Plane (p ^ 2) ×
          OMA.S_arxiv_2606_27961.Plane (p ^ 2) => q.1 + q.2) ''
        ((Set.range (fun x : OMA.S_arxiv_2606_27961.Plane p => s (x + i • u) - s x)) ×ˢ
          (Set.range (fun x : OMA.S_arxiv_2606_27961.Plane p => s (x + j • v) - s x))) ⊆
        Set.range (fun x : OMA.S_arxiv_2606_27961.Plane p =>
          s (x + (i • u + j • v)) - s x) := by
      rintro _ ⟨⟨y, z⟩, ⟨⟨x1, rfl⟩, ⟨x2, rfl⟩⟩, rfl⟩
      obtain ⟨i1, j1, rfl⟩ := hdec x1
      obtain ⟨i2, j2, rfl⟩ := hdec x2
      refine ⟨i1 • u + j2 • v, ?_⟩
      beta_reduce
      have e1 := (lift_u i).1 j (i1 • u + j2 • v)
      have e2 := (lift_u i).1 j2 (i1 • u)
      have e3 := (lift_u i).1 j1 (i1 • u)
      have e4 := (lift_v j).1 i1 (j2 • v)
      have e5 := (lift_v j).1 i2 (j2 • v)
      rw [tsd_coc p s (i1 • u + j2 • v) (i • u) (j • v), e1, e2, e3,
        add_comm (i1 • u) (j2 • v), add_comm (i2 • u) (j2 • v), e4, e5]
    calc _ = _ := hinj.ncard_image.symm
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.finite_range _)
  have hlow : ∀ t : OMA.S_arxiv_2606_27961.Plane p, t ≠ 0 → ∀ α : ZMod p,
      (if α = 0 then 1 else 2 : ℕ) ≤
        (Set.range (fun x : OMA.S_arxiv_2606_27961.Plane p => s (x + α.val • t) - s x)).ncard := by
    intro t ht α
    split_ifs with hα
    · exact (Set.ncard_pos (Set.finite_range _)).mpr (Set.range_nonempty _)
    · apply tsd_two p s hs
      rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
      exact tsd_smul_ne_zero p α t hα ht
  have hsum_h : ∑ α : ZMod p, (if α = 0 then 1 else 2 : ℕ) = 2 * p - 1 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p)), if_pos rfl,
      Finset.sum_congr rfl (fun x hx => if_neg (Finset.ne_of_mem_erase hx)),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ZMod.card, smul_eq_mul]
    have := hp.two_le
    omega
  calc (2 * p - 1) ^ 2
      = (∑ α : ZMod p, (if α = 0 then 1 else 2 : ℕ)) *
          (∑ β : ZMod p, (if β = 0 then 1 else 2 : ℕ)) := by
        rw [hsum_h, sq]
    _ = ∑ q : ZMod p × ZMod p, (if q.1 = 0 then 1 else 2 : ℕ) * (if q.2 = 0 then 1 else 2 : ℕ) := by
        rw [Fintype.sum_mul_sum, Fintype.sum_prod_type]
    _ ≤ ∑ q : ZMod p × ZMod p, c (q.1 • u + q.2 • v) := by
        apply Finset.sum_le_sum
        intro q _
        have e1 : q.1 • u = q.1.val • u := by
          rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
        have e2 : q.2 • v = q.2.val • v := by
          rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
        rw [e1, e2]
        exact (Nat.mul_le_mul (hlow u hu0 q.1) (hlow v hv0 q.2)).trans (hprod _ _)
    _ = ∑ w, c w := he_bij.sum_comp c
