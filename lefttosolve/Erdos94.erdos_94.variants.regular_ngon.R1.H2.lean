import OMAReductions.R_Erdos94_erdos_94_variants_regular_ngon_R1

/-!
# Step H2 of the reduction Erdos94.erdos_94.variants.regular_ngon.R1

Pure counting. Write f(u) for the multiplicities; they sum to n (n - 1) / 2 and each is at most n.
Then the sum of f(u)^2 equals n * (sum of f) minus the sum of g(f(u)) with g(x) = x (n - x) >= 0.
For odd n drop the g-terms. For even n = 2t, g(a) + g(r) >= g((a + r) mod n) for a <= n and
r < n, so the sum of the g-terms is at least g(t) = t^2, since the f(u) sum to t mod 2t.
-/

open EuclideanGeometry Erdos94 Finset

namespace OMA.Helpers

/-- Ordered pairs of distinct points at distance `d` come two by two (a pair and its swap). -/
lemma e94_even_card_dist {X : Type*} [MetricSpace X] [DecidableEq X] (P : Finset X) (d : ℝ) :
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

/-- Twice the sum of the multiplicities is the number of ordered pairs of distinct points. -/
lemma e94_two_sum {X : Type*} [MetricSpace X] [DecidableEq X] (P : Finset X) :
    2 * ∑ u ∈ distanceSet P, distanceMultiplicity P u = #P * #P - #P := by
  rw [← Finset.offDiag_card, Finset.mul_sum]
  have h : ∀ u ∈ distanceSet P, 2 * distanceMultiplicity P u =
      #(P.offDiag.filter fun (pair : X × X) => dist pair.1 pair.2 = u) := by
    intro u _
    unfold distanceMultiplicity
    exact Nat.two_mul_div_two_of_even (e94_even_card_dist P u)
  rw [Finset.sum_congr rfl h]
  unfold distanceSet
  exact (Finset.card_eq_sum_card_image (fun pair : X × X => dist pair.1 pair.2) P.offDiag).symm

/-- `g(a) + g(r) ≥ g((a + r) mod n)` for `g(x) = x (n - x)`, `a ≤ n`, `r < n`. -/
lemma e94_pair (a r n : ℕ) (hn : 0 < n) (ha : a ≤ n) (hr : r < n) :
    (((a + r) % n : ℕ) : ℝ) * ((n : ℝ) - (((a + r) % n : ℕ) : ℝ)) ≤
      (a : ℝ) * ((n : ℝ) - a) + (r : ℝ) * ((n : ℝ) - r) := by
  have h1 := Nat.div_add_mod (a + r) n
  have hq : (a + r) / n < 2 := (Nat.div_lt_iff_lt_mul hn).2 (by omega)
  set c := (a + r) % n with hc
  set q := (a + r) / n with hqdef
  have har : (a : ℝ) ≤ n := by exact_mod_cast ha
  have hrr : (r : ℝ) ≤ n := by exact_mod_cast hr.le
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have hr0 : (0 : ℝ) ≤ r := by positivity
  interval_cases q
  · have h2 : (c : ℝ) = a + r := by exact_mod_cast (by omega : c = a + r)
    rw [h2]
    nlinarith [mul_nonneg ha0 hr0]
  · have h2 : (c : ℝ) + n = a + r := by exact_mod_cast (by omega : c + n = a + r)
    have h3 : (c : ℝ) = a + r - n := by linarith
    rw [h3]
    nlinarith [mul_nonneg (sub_nonneg.2 har) (sub_nonneg.2 hrr)]

/-- The sum of the `g(f(u))` is at least `g` of the total modulo `n`. -/
lemma e94_g_sum (n : ℕ) (hn : 0 < n) (f : ℝ → ℕ) :
    ∀ s : Finset ℝ, (∀ u ∈ s, f u ≤ n) →
      (((∑ u ∈ s, f u) % n : ℕ) : ℝ) * ((n : ℝ) - (((∑ u ∈ s, f u) % n : ℕ) : ℝ)) ≤
        ∑ u ∈ s, (f u : ℝ) * ((n : ℝ) - f u) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp
  | insert a s has ih =>
    intro hf
    rw [Finset.sum_insert has, Finset.sum_insert has]
    have hfa : f a ≤ n := hf a (Finset.mem_insert_self a s)
    have hrest := ih (fun u hu => hf u (Finset.mem_insert_of_mem hu))
    have hmod := Nat.add_mod_mod (f a) (∑ u ∈ s, f u) n
    have hp := e94_pair (f a) ((∑ u ∈ s, f u) % n) n hn hfa (Nat.mod_lt _ hn)
    rw [hmod] at hp
    linarith

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos94_erdos_94_variants_regular_ngon_R1.H2 := by
  classical
  intro n P hP hmult
  set f : ℝ → ℕ := fun u => distanceMultiplicity P u with hfdef
  set D := distanceSet P with hD
  set S := ∑ u ∈ D, f u with hSdef
  have h2S : 2 * S = n * n - n := by
    rw [← hP]
    exact OMA.Helpers.e94_two_sum P
  have h2SR : 2 * (S : ℝ) = (n : ℝ) * n - n := by
    have hle : n ≤ n * n := Nat.le_mul_self n
    have := congrArg (fun x : ℕ => (x : ℝ)) h2S
    push_cast [Nat.cast_sub hle] at this
    linarith
  have hid : ∑ u ∈ D, (f u : ℝ) ^ 2 =
      (n : ℝ) * S - ∑ u ∈ D, (f u : ℝ) * ((n : ℝ) - f u) := by
    rw [hSdef]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u _
    ring
  have hnonneg : 0 ≤ ∑ u ∈ D, (f u : ℝ) * ((n : ℝ) - f u) := by
    apply Finset.sum_nonneg
    intro u hu
    have : (f u : ℝ) ≤ n := by exact_mod_cast hmult u hu
    have : (0 : ℝ) ≤ f u := by positivity
    nlinarith
  change ∑ u ∈ D, (f u : ℝ) ^ 2 ≤ _
  split_ifs with hodd
  · rw [hid]
    nlinarith
  · obtain ⟨t, ht⟩ : ∃ t, n = 2 * t := ⟨n / 2, by omega⟩
    have hg : (t : ℝ) ^ 2 ≤ ∑ u ∈ D, (f u : ℝ) * ((n : ℝ) - f u) := by
      rcases Nat.eq_zero_or_pos t with h0 | hpos
      · rw [h0]
        simpa using hnonneg
      · have hnpos : 0 < n := by omega
        have hgs := OMA.Helpers.e94_g_sum n hnpos f D (fun u hu => hmult u hu)
        have hSt : S % n = t := by
          have hS' : S = t + n * (t - 1) := by
            subst ht
            have : 2 * S = 2 * (t + 2 * t * (t - 1)) := by
              rw [h2S]
              obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
              simp only [Nat.add_sub_cancel]
              ring_nf
              omega
            omega
          rw [hS', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
        rw [← hSdef, hSt] at hgs
        have : (n : ℝ) = 2 * t := by exact_mod_cast ht
        rw [this] at hgs ⊢
        nlinarith
    rw [hid]
    have hnR : (n : ℝ) = 2 * t := by exact_mod_cast ht
    have hS : (S : ℝ) = ((n : ℝ) * n - n) / 2 := by linarith
    have ht2 : (t : ℝ) ^ 2 = (n : ℝ) ^ 2 / 4 := by rw [hnR]; ring
    rw [hS]
    nlinarith
