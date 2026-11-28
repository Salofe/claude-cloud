import OMAReductions.R_erdos_634_R1_H3_R1_H4_R1

/-!
# Step H2 of the reduction erdos-634.R1.H3.R1.H4.R1

For every 5-smooth n at most 200 outside the exceptional list 3, 4, 6, 8, 10, 12, 18, 24, 30, 60
and every positive triple a with sum n and gcd 1, the only rational vectors e killed by all the
sawtooth relations (k coprime to n) are the trivial ones (spanned by e i - e j with a i = a j and
e i with 2 a i = n).

Method (our own formalization):
* Scaling a relation by 2 n turns it into an integer relation with coefficients
  sw n k x = 2 (k x mod n) - n (or 0 when n divides k x).
* By permuting coordinates (good_perm, exists_sort) we may assume a 0 is at most a 1, which is at
  most a 2.
* For such a triple the kernel computation okR finds, using k = 1 and one or two further units k,
  either a nonzero 3 by 3 determinant (then e = 0 by the adjugate identity, caseA), or two rows
  whose cross product w is nonzero and parallel to the expected trivial vector (then e is a
  multiple of w by the identity (w.w) e = (e.w) w, caseB).
* The finite search over all triples is checked by the kernel, split into chunks by n and a.
* The 5-smoothness hypothesis is used only to place n in the explicit list Lgood (coverOK).
-/

namespace OMA.Helpers

def sw (n k x : ℕ) : ℤ := if k * x % n = 0 then 0 else 2 * ((k * x % n : ℕ) : ℤ) - (n : ℤ)

def det3 (p q r s t u v w x : ℤ) : ℤ :=
  p * (t * x - u * w) - q * (s * x - u * v) + r * (s * w - t * v)

def crossNZ (p q r s t u : ℤ) : Bool :=
  q * u - r * t != 0 || r * s - p * u != 0 || p * t - q * s != 0

def okA (n a b c : ℕ) : Bool :=
  (List.range n).any fun k => Nat.gcd k n == 1 &&
    crossNZ (sw n 1 a) (sw n 1 b) (sw n 1 c) (sw n k a) (sw n k b) (sw n k c) &&
    (List.range n).any fun l => Nat.gcd l n == 1 &&
      det3 (sw n 1 a) (sw n 1 b) (sw n 1 c) (sw n k a) (sw n k b) (sw n k c)
        (sw n l a) (sw n l b) (sw n l c) != 0

def vecOK (n a b c : ℕ) (w0 w1 w2 : ℤ) : Bool :=
  (2 * c == n && w0 == 0 && w1 == 0) || (a == b && w2 == 0 && w0 + w1 == 0) ||
  (b == c && w0 == 0 && w1 + w2 == 0)

def okB (n a b c : ℕ) : Bool :=
  (List.range n).any fun k => Nat.gcd k n == 1 &&
    (sw n 1 b * sw n k c - sw n 1 c * sw n k b) * (sw n 1 b * sw n k c - sw n 1 c * sw n k b) +
      (sw n 1 c * sw n k a - sw n 1 a * sw n k c) * (sw n 1 c * sw n k a - sw n 1 a * sw n k c) +
      (sw n 1 a * sw n k b - sw n 1 b * sw n k a) * (sw n 1 a * sw n k b - sw n 1 b * sw n k a) != 0 &&
    vecOK n a b c (sw n 1 b * sw n k c - sw n 1 c * sw n k b)
      (sw n 1 c * sw n k a - sw n 1 a * sw n k c) (sw n 1 a * sw n k b - sw n 1 b * sw n k a)

def ok (n a b c : ℕ) : Bool :=
  if 2 * c = n ∨ a = b ∨ b = c then okB n a b c else okA n a b c

def okR (n lo hi : ℕ) : Bool :=
  (List.range' lo (hi - lo)).all fun a => (List.range (n - a)).all fun b =>
    a == 0 || decide (b < a) || decide (n - a - b < b) || Nat.gcd a (Nat.gcd b (n - a - b)) != 1 ||
      ok n a b (n - a - b)

def okN (n : ℕ) : Bool := okR n 0 (n / 3 + 1)

def isExc (n : ℕ) : Bool :=
  n == 3 || n == 4 || n == 6 || n == 8 || n == 10 || n == 12 || n == 18 || n == 24 || n == 30 ||
    n == 60

def bigP : List ℕ := [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
  89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
  193, 197, 199]

/-- The 5-smooth numbers at most 200 outside the exceptional list. -/
def Lgood : List ℕ := [1, 2, 5, 9, 15, 16, 20, 25, 27, 32, 36, 40, 45, 48, 50, 54, 64, 72, 75, 80, 81, 
  90, 96, 100, 108, 120, 125, 128, 135, 144, 150, 160, 162, 180, 192, 200]

def coverOK : Bool :=
  (List.range 201).all fun n =>
    isExc n || bigP.any (fun l => n % l == 0) || Lgood.any (fun m => m == n)

theorem coverOK_true : coverOK = true := by decide +kernel

theorem bigP_prime : ∀ l ∈ bigP, 7 ≤ l ∧ l.Prime := by
  simp only [bigP, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, forall_const,
    and_true]
  norm_num

def Rel (n : ℕ) (a : Fin 3 → ℕ) (e : Fin 3 → ℚ) : Prop :=
  ∀ k : ℕ, k.Coprime n → ∑ i, (if Int.fract (((k * a i : ℕ) : ℚ) / (n : ℚ)) = 0 then 0
    else Int.fract (((k * a i : ℕ) : ℚ) / (n : ℚ)) - 1 / 2) * e i = 0

def Triv (n : ℕ) (a : Fin 3 → ℕ) : Set (Fin 3 → ℚ) :=
  {v | ∃ i j, i ≠ j ∧ a i = a j ∧ v = Pi.single i 1 - Pi.single j 1} ∪
    {v | ∃ i, 2 * a i = n ∧ v = Pi.single i 1}

def Good (n : ℕ) (a : Fin 3 → ℕ) : Prop :=
  ∀ e : Fin 3 → ℚ, Rel n a e → e ∈ Submodule.span ℚ (Triv n a)

theorem saw_eq (n k x : ℕ) (hn : 0 < n) :
    (if Int.fract (((k * x : ℕ) : ℚ) / (n : ℚ)) = 0 then 0
      else Int.fract (((k * x : ℕ) : ℚ) / (n : ℚ)) - 1 / 2) = ((sw n k x : ℤ) : ℚ) / (2 * n) := by
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  have hn' : (n : ℚ) ≠ 0 := by positivity
  unfold sw
  split_ifs with h1 h2 h2
  · simp
  · exfalso
    apply h2
    rcases div_eq_zero_iff.mp h1 with h | h
    · exact_mod_cast h
    · exact absurd h hn'
  · exfalso
    apply h1
    rw [h2]
    simp
  · simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    field_simp

theorem rel_int (n : ℕ) (hn : 0 < n) (a : Fin 3 → ℕ) (e : Fin 3 → ℚ) (k : ℕ)
    (h : ∑ i, (if Int.fract (((k * a i : ℕ) : ℚ) / (n : ℚ)) = 0 then 0
      else Int.fract (((k * a i : ℕ) : ℚ) / (n : ℚ)) - 1 / 2) * e i = 0) :
    (sw n k (a 0) : ℚ) * e 0 + (sw n k (a 1) : ℚ) * e 1 + (sw n k (a 2) : ℚ) * e 2 = 0 := by
  simp only [saw_eq n k _ hn, Fin.sum_univ_three] at h
  have hn' : (2 * n : ℚ) ≠ 0 := by positivity
  have h' := congrArg (fun t => t * (2 * n : ℚ)) h
  simp only [zero_mul, add_mul] at h'
  rw [← h']
  field_simp

theorem caseA (e : Fin 3 → ℚ) (p q r s t u v w x : ℚ)
    (h1 : p * e 0 + q * e 1 + r * e 2 = 0) (h2 : s * e 0 + t * e 1 + u * e 2 = 0)
    (h3 : v * e 0 + w * e 1 + x * e 2 = 0)
    (hd : p * (t * x - u * w) - q * (s * x - u * v) + r * (s * w - t * v) ≠ 0) : e = 0 := by
  have e0 : (p * (t * x - u * w) - q * (s * x - u * v) + r * (s * w - t * v)) * e 0 = 0 := by
    linear_combination (t * x - u * w) * h1 - (q * x - r * w) * h2 + (q * u - r * t) * h3
  have e1 : (p * (t * x - u * w) - q * (s * x - u * v) + r * (s * w - t * v)) * e 1 = 0 := by
    linear_combination -(s * x - u * v) * h1 + (p * x - r * v) * h2 - (p * u - r * s) * h3
  have e2 : (p * (t * x - u * w) - q * (s * x - u * v) + r * (s * w - t * v)) * e 2 = 0 := by
    linear_combination (s * w - t * v) * h1 - (p * w - q * v) * h2 + (p * t - q * s) * h3
  funext i
  fin_cases i
  · exact (mul_eq_zero.mp e0).resolve_left hd
  · exact (mul_eq_zero.mp e1).resolve_left hd
  · exact (mul_eq_zero.mp e2).resolve_left hd

theorem caseB (e : Fin 3 → ℚ) (p q r s t u : ℚ)
    (h1 : p * e 0 + q * e 1 + r * e 2 = 0) (h2 : s * e 0 + t * e 1 + u * e 2 = 0) :
    ((q * u - r * t) * (q * u - r * t) + (r * s - p * u) * (r * s - p * u) +
        (p * t - q * s) * (p * t - q * s)) * e 0 =
      (e 0 * (q * u - r * t) + e 1 * (r * s - p * u) + e 2 * (p * t - q * s)) * (q * u - r * t) ∧
    ((q * u - r * t) * (q * u - r * t) + (r * s - p * u) * (r * s - p * u) +
        (p * t - q * s) * (p * t - q * s)) * e 1 =
      (e 0 * (q * u - r * t) + e 1 * (r * s - p * u) + e 2 * (p * t - q * s)) * (r * s - p * u) ∧
    ((q * u - r * t) * (q * u - r * t) + (r * s - p * u) * (r * s - p * u) +
        (p * t - q * s) * (p * t - q * s)) * e 2 =
      (e 0 * (q * u - r * t) + e 1 * (r * s - p * u) + e 2 * (p * t - q * s)) * (p * t - q * s) := by
  refine ⟨?_, ?_, ?_⟩
  · linear_combination ((r * s - p * u) * r - (p * t - q * s) * q) * h2 -
      ((r * s - p * u) * u - (p * t - q * s) * t) * h1
  · linear_combination ((p * t - q * s) * p - (q * u - r * t) * r) * h2 -
      ((p * t - q * s) * s - (q * u - r * t) * u) * h1
  · linear_combination ((q * u - r * t) * q - (r * s - p * u) * p) * h2 -
      ((q * u - r * t) * t - (r * s - p * u) * s) * h1

theorem mem_span_of (n : ℕ) (a : Fin 3 → ℕ) (e v : Fin 3 → ℚ) (hv : v ∈ Triv n a) (c : ℚ)
    (h0 : e 0 = c * v 0) (h1 : e 1 = c * v 1) (h2 : e 2 = c * v 2) :
    e ∈ Submodule.span ℚ (Triv n a) := by
  have : e = c • v := by
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hv)

theorem zero_of (W D w x : ℚ) (hW : W ≠ 0) (E : W * x = D * w) (hw : w = 0) : x = 0 := by
  rw [hw, mul_zero] at E
  exact (mul_eq_zero.mp E).resolve_left hW

theorem neg_of (W D w0 w1 x0 x1 : ℚ) (hW : W ≠ 0) (E0 : W * x0 = D * w0) (E1 : W * x1 = D * w1)
    (hw : w0 + w1 = 0) : x1 = -x0 := by
  apply mul_left_cancel₀ hW
  linear_combination E1 + E0 + D * hw

theorem good_of_ok (n : ℕ) (hn : 0 < n) (a : Fin 3 → ℕ) (h : ok n (a 0) (a 1) (a 2) = true) :
    Good n a := by
  intro e he
  have r1 := rel_int n hn a e 1 (he 1 (Nat.coprime_one_left n))
  unfold ok at h
  split_ifs at h with hc
  · unfold okB at h
    obtain ⟨k, -, hk⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hk
    obtain ⟨⟨hgk, hW⟩, hv⟩ := hk
    have rk := rel_int n hn a e k (he k hgk)
    obtain ⟨E0, E1, E2⟩ := caseB e _ _ _ _ _ _ r1 rk
    have hWq : ((sw n 1 (a 1) : ℚ) * sw n k (a 2) - sw n 1 (a 2) * sw n k (a 1)) *
        ((sw n 1 (a 1) : ℚ) * sw n k (a 2) - sw n 1 (a 2) * sw n k (a 1)) +
        ((sw n 1 (a 2) : ℚ) * sw n k (a 0) - sw n 1 (a 0) * sw n k (a 2)) *
        ((sw n 1 (a 2) : ℚ) * sw n k (a 0) - sw n 1 (a 0) * sw n k (a 2)) +
        ((sw n 1 (a 0) : ℚ) * sw n k (a 1) - sw n 1 (a 1) * sw n k (a 0)) *
        ((sw n 1 (a 0) : ℚ) * sw n k (a 1) - sw n 1 (a 1) * sw n k (a 0)) ≠ 0 := by
      exact_mod_cast hW
    unfold vecOK at hv
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hv
    rcases hv with (⟨⟨h2c, hw0⟩, hw1⟩ | ⟨⟨hab, hw2⟩, hw01⟩) | ⟨⟨hbc, hw0⟩, hw12⟩
    · have z0 := zero_of _ _ _ _ hWq E0 (by exact_mod_cast hw0)
      have z1 := zero_of _ _ _ _ hWq E1 (by exact_mod_cast hw1)
      refine mem_span_of n a e (Pi.single 2 1) (Or.inr ⟨2, h2c, rfl⟩) (e 2) ?_ ?_ ?_
      · simp [z0]
      · simp [z1]
      · simp
    · have z2 := zero_of _ _ _ _ hWq E2 (by exact_mod_cast hw2)
      have n1 := neg_of _ _ _ _ _ _ hWq E0 E1 (by exact_mod_cast hw01)
      refine mem_span_of n a e (Pi.single 0 1 - Pi.single 1 1)
        (Or.inl ⟨0, 1, by decide, hab, rfl⟩) (e 0) ?_ ?_ ?_
      · simp
      · simp [n1]
      · simp [z2]
    · have z0 := zero_of _ _ _ _ hWq E0 (by exact_mod_cast hw0)
      have n2 := neg_of _ _ _ _ _ _ hWq E1 E2 (by exact_mod_cast hw12)
      refine mem_span_of n a e (Pi.single 1 1 - Pi.single 2 1)
        (Or.inl ⟨1, 2, by decide, hbc, rfl⟩) (e 1) ?_ ?_ ?_
      · simp [z0]
      · simp
      · simp [n2]
  · unfold okA at h
    obtain ⟨k, -, hk⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true, bne_iff_ne, ne_eq] at hk
    obtain ⟨⟨hgk, -⟩, l, -, hgl, hdet⟩ := hk
    have rk := rel_int n hn a e k (he k hgk)
    have rl := rel_int n hn a e l (he l hgl)
    have hdq : ((det3 (sw n 1 (a 0)) (sw n 1 (a 1)) (sw n 1 (a 2)) (sw n k (a 0)) (sw n k (a 1))
        (sw n k (a 2)) (sw n l (a 0)) (sw n l (a 1)) (sw n l (a 2)) : ℤ) : ℚ) ≠ 0 := by
      exact_mod_cast hdet
    unfold det3 at hdq
    push_cast at hdq
    rw [caseA e _ _ _ _ _ _ _ _ _ r1 rk rl hdq]
    exact Submodule.zero_mem _

theorem good_perm (n : ℕ) (a : Fin 3 → ℕ) (σ : Equiv.Perm (Fin 3)) (h : Good n (a ∘ σ)) :
    Good n a := by
  intro e he
  have he' : Rel n (a ∘ σ) (e ∘ σ) := by
    intro k hk
    exact (Equiv.sum_comp σ (fun i => (if Int.fract (((k * a i : ℕ) : ℚ) / (n : ℚ)) = 0 then 0
      else Int.fract (((k * a i : ℕ) : ℚ) / (n : ℚ)) - 1 / 2) * e i)).trans (he k hk)
  have hm := Submodule.apply_mem_span_image_of_mem_span (LinearMap.funLeft ℚ ℚ σ.symm)
    (h (e ∘ σ) he')
  have heq : LinearMap.funLeft ℚ ℚ σ.symm (e ∘ σ) = e := by
    funext x
    simp [LinearMap.funLeft_apply]
  rw [heq] at hm
  refine Submodule.span_mono ?_ hm
  rintro _ ⟨v, hv, rfl⟩
  rcases hv with ⟨i, j, hij, haij, rfl⟩ | ⟨i, hi, rfl⟩
  · left
    refine ⟨σ i, σ j, σ.injective.ne hij, haij, ?_⟩
    funext x
    simp [LinearMap.funLeft_apply, Pi.single_apply, Equiv.symm_apply_eq]
  · right
    refine ⟨σ i, hi, ?_⟩
    funext x
    simp [LinearMap.funLeft_apply, Pi.single_apply, Equiv.symm_apply_eq]

theorem exists_sort (a : Fin 3 → ℕ) : ∃ σ : Equiv.Perm (Fin 3), a (σ 0) ≤ a (σ 1) ∧
    a (σ 1) ≤ a (σ 2) ∧
    Nat.gcd (a (σ 0)) (Nat.gcd (a (σ 1)) (a (σ 2))) = Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) := by
  rcases le_total (a 0) (a 1) with h01 | h01 <;> rcases le_total (a 1) (a 2) with h12 | h12 <;>
    rcases le_total (a 0) (a 2) with h02 | h02
  · exact ⟨Equiv.refl _, h01, h12, rfl⟩
  · exact ⟨Equiv.refl _, h01, h12, rfl⟩
  · refine ⟨⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩, h02, h12, ?_⟩
    change Nat.gcd (a 0) (Nat.gcd (a 2) (a 1)) = _
    rw [Nat.gcd_comm (a 2)]
  · refine ⟨⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩, h02, h01, ?_⟩
    change Nat.gcd (a 2) (Nat.gcd (a 0) (a 1)) = _
    rw [Nat.gcd_comm (a 0) (a 1), ← Nat.gcd_assoc, Nat.gcd_comm (a 2) (a 1), Nat.gcd_assoc,
      Nat.gcd_comm (a 2) (a 0), ← Nat.gcd_assoc, Nat.gcd_comm (a 1) (a 0), Nat.gcd_assoc]
  · refine ⟨⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩, h01, h02, ?_⟩
    change Nat.gcd (a 1) (Nat.gcd (a 0) (a 2)) = _
    rw [Nat.gcd_left_comm]
  · refine ⟨⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩, h12, h02, ?_⟩
    change Nat.gcd (a 1) (Nat.gcd (a 2) (a 0)) = _
    rw [Nat.gcd_comm (a 2) (a 0), Nat.gcd_left_comm]
  · refine ⟨⟨![2, 1, 0], ![2, 1, 0], by decide, by decide⟩, h12, h01, ?_⟩
    change Nat.gcd (a 2) (Nat.gcd (a 1) (a 0)) = _
    rw [Nat.gcd_comm (a 1) (a 0), Nat.gcd_left_comm, Nat.gcd_comm (a 2) (a 1), Nat.gcd_left_comm]
  · refine ⟨⟨![2, 1, 0], ![2, 1, 0], by decide, by decide⟩, h12, h01, ?_⟩
    change Nat.gcd (a 2) (Nat.gcd (a 1) (a 0)) = _
    rw [Nat.gcd_comm (a 1) (a 0), Nat.gcd_left_comm, Nat.gcd_comm (a 2) (a 1), Nat.gcd_left_comm]

theorem okR_join (n lo mid hi : ℕ) (h1 : okR n lo mid = true) (h2 : okR n mid hi = true)
    (hlm : lo ≤ mid) (hmh : mid ≤ hi) : okR n lo hi = true := by
  unfold okR at *
  rw [List.all_eq_true] at *
  intro x hx
  rw [List.mem_range'_1] at hx
  by_cases hm : x < mid
  · exact h1 x (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  · exact h2 x (List.mem_range'_1.mpr ⟨by omega, by omega⟩)

theorem okN_sound (n : ℕ) (h : okN n = true) (x y z : ℕ) (hx : 0 < x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hs : x + y + z = n) (hg : Nat.gcd x (Nat.gcd y z) = 1) : ok n x y z = true := by
  unfold okN okR at h
  have h1 := List.all_eq_true.mp h x (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  have h2 := List.all_eq_true.mp h1 y (List.mem_range.mpr (by omega))
  have hz : n - x - y = z := by omega
  rw [hz] at h2
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at h2
  rcases h2 with (((h | h) | h) | h) | h
  · omega
  · omega
  · omega
  · exact absurd hg h
  · exact h

theorem chunk_1_0 : okR 1 0 1 = true := by decide +kernel

theorem okN_1 : okN 1 = true := chunk_1_0

theorem chunk_2_0 : okR 2 0 1 = true := by decide +kernel

theorem okN_2 : okN 2 = true := chunk_2_0

theorem chunk_5_0 : okR 5 0 2 = true := by decide +kernel

theorem okN_5 : okN 5 = true := chunk_5_0

theorem chunk_9_0 : okR 9 0 4 = true := by decide +kernel

theorem okN_9 : okN 9 = true := chunk_9_0

theorem chunk_15_0 : okR 15 0 6 = true := by decide +kernel

theorem okN_15 : okN 15 = true := chunk_15_0

theorem chunk_16_0 : okR 16 0 6 = true := by decide +kernel

theorem okN_16 : okN 16 = true := chunk_16_0

theorem chunk_20_0 : okR 20 0 7 = true := by decide +kernel

theorem okN_20 : okN 20 = true := chunk_20_0

theorem chunk_25_0 : okR 25 0 9 = true := by decide +kernel

theorem okN_25 : okN 25 = true := chunk_25_0

theorem chunk_27_0 : okR 27 0 10 = true := by decide +kernel

theorem okN_27 : okN 27 = true := chunk_27_0

theorem chunk_32_0 : okR 32 0 11 = true := by decide +kernel

theorem okN_32 : okN 32 = true := chunk_32_0

theorem chunk_36_0 : okR 36 0 13 = true := by decide +kernel

theorem okN_36 : okN 36 = true := chunk_36_0

theorem chunk_40_0 : okR 40 0 14 = true := by decide +kernel

theorem okN_40 : okN 40 = true := chunk_40_0

theorem chunk_45_0 : okR 45 0 16 = true := by decide +kernel

theorem okN_45 : okN 45 = true := chunk_45_0

theorem chunk_48_0 : okR 48 0 17 = true := by decide +kernel

theorem okN_48 : okN 48 = true := chunk_48_0

theorem chunk_50_0 : okR 50 0 17 = true := by decide +kernel

theorem okN_50 : okN 50 = true := chunk_50_0

theorem chunk_54_0 : okR 54 0 19 = true := by decide +kernel

theorem okN_54 : okN 54 = true := chunk_54_0

theorem chunk_64_0 : okR 64 0 22 = true := by decide +kernel

theorem okN_64 : okN 64 = true := chunk_64_0

theorem chunk_72_0 : okR 72 0 25 = true := by decide +kernel

theorem okN_72 : okN 72 = true := chunk_72_0

theorem chunk_75_0 : okR 75 0 26 = true := by decide +kernel

theorem okN_75 : okN 75 = true := chunk_75_0

theorem chunk_80_0 : okR 80 0 27 = true := by decide +kernel

theorem okN_80 : okN 80 = true := chunk_80_0

theorem chunk_81_0 : okR 81 0 28 = true := by decide +kernel

theorem okN_81 : okN 81 = true := chunk_81_0

theorem chunk_90_0 : okR 90 0 31 = true := by decide +kernel

theorem okN_90 : okN 90 = true := chunk_90_0

theorem chunk_96_0 : okR 96 0 33 = true := by decide +kernel

theorem okN_96 : okN 96 = true := chunk_96_0

theorem chunk_100_0 : okR 100 0 34 = true := by decide +kernel

theorem okN_100 : okN 100 = true := chunk_100_0

theorem chunk_108_0 : okR 108 0 26 = true := by decide +kernel

theorem chunk_108_1 : okR 108 26 37 = true := by decide +kernel

theorem okN_108 : okN 108 = true := okR_join 108 0 26 37 (chunk_108_0) chunk_108_1 (by norm_num) (by norm_num)

theorem chunk_120_0 : okR 120 0 22 = true := by decide +kernel

theorem chunk_120_1 : okR 120 22 41 = true := by decide +kernel

theorem okN_120 : okN 120 = true := okR_join 120 0 22 41 (chunk_120_0) chunk_120_1 (by norm_num) (by norm_num)

theorem chunk_125_0 : okR 125 0 12 = true := by decide +kernel

theorem chunk_125_1 : okR 125 12 32 = true := by decide +kernel

theorem chunk_125_2 : okR 125 32 42 = true := by decide +kernel

theorem okN_125 : okN 125 = true := okR_join 125 0 32 42 (okR_join 125 0 12 32 (chunk_125_0) chunk_125_1 (by norm_num) (by norm_num)) chunk_125_2 (by norm_num) (by norm_num)

theorem chunk_128_0 : okR 128 0 15 = true := by decide +kernel

theorem chunk_128_1 : okR 128 15 43 = true := by decide +kernel

theorem okN_128 : okN 128 = true := okR_join 128 0 15 43 (chunk_128_0) chunk_128_1 (by norm_num) (by norm_num)

theorem chunk_135_0 : okR 135 0 13 = true := by decide +kernel

theorem chunk_135_1 : okR 135 13 33 = true := by decide +kernel

theorem chunk_135_2 : okR 135 33 46 = true := by decide +kernel

theorem okN_135 : okN 135 = true := okR_join 135 0 33 46 (okR_join 135 0 13 33 (chunk_135_0) chunk_135_1 (by norm_num) (by norm_num)) chunk_135_2 (by norm_num) (by norm_num)

theorem chunk_144_0 : okR 144 0 15 = true := by decide +kernel

theorem chunk_144_1 : okR 144 15 49 = true := by decide +kernel

theorem okN_144 : okN 144 = true := okR_join 144 0 15 49 (chunk_144_0) chunk_144_1 (by norm_num) (by norm_num)

theorem chunk_150_0 : okR 150 0 15 = true := by decide +kernel

theorem chunk_150_1 : okR 150 15 46 = true := by decide +kernel

theorem chunk_150_2 : okR 150 46 51 = true := by decide +kernel

theorem okN_150 : okN 150 = true := okR_join 150 0 46 51 (okR_join 150 0 15 46 (chunk_150_0) chunk_150_1 (by norm_num) (by norm_num)) chunk_150_2 (by norm_num) (by norm_num)

theorem chunk_160_0 : okR 160 0 12 = true := by decide +kernel

theorem chunk_160_1 : okR 160 12 28 = true := by decide +kernel

theorem chunk_160_2 : okR 160 28 54 = true := by decide +kernel

theorem okN_160 : okN 160 = true := okR_join 160 0 28 54 (okR_join 160 0 12 28 (chunk_160_0) chunk_160_1 (by norm_num) (by norm_num)) chunk_160_2 (by norm_num) (by norm_num)

theorem chunk_162_0 : okR 162 0 13 = true := by decide +kernel

theorem chunk_162_1 : okR 162 13 31 = true := by decide +kernel

theorem chunk_162_2 : okR 162 31 55 = true := by decide +kernel

theorem okN_162 : okN 162 = true := okR_join 162 0 31 55 (okR_join 162 0 13 31 (chunk_162_0) chunk_162_1 (by norm_num) (by norm_num)) chunk_162_2 (by norm_num) (by norm_num)

theorem chunk_180_0 : okR 180 0 12 = true := by decide +kernel

theorem chunk_180_1 : okR 180 12 27 = true := by decide +kernel

theorem chunk_180_2 : okR 180 27 61 = true := by decide +kernel

theorem okN_180 : okN 180 = true := okR_join 180 0 27 61 (okR_join 180 0 12 27 (chunk_180_0) chunk_180_1 (by norm_num) (by norm_num)) chunk_180_2 (by norm_num) (by norm_num)

theorem chunk_192_0 : okR 192 0 11 = true := by decide +kernel

theorem chunk_192_1 : okR 192 11 23 = true := by decide +kernel

theorem chunk_192_2 : okR 192 23 41 = true := by decide +kernel

theorem chunk_192_3 : okR 192 41 65 = true := by decide +kernel

theorem okN_192 : okN 192 = true := okR_join 192 0 41 65 (okR_join 192 0 23 41 (okR_join 192 0 11 23 (chunk_192_0) chunk_192_1 (by norm_num) (by norm_num)) chunk_192_2 (by norm_num) (by norm_num)) chunk_192_3 (by norm_num) (by norm_num)

theorem chunk_200_0 : okR 200 0 9 = true := by decide +kernel

theorem chunk_200_1 : okR 200 9 19 = true := by decide +kernel

theorem chunk_200_2 : okR 200 19 31 = true := by decide +kernel

theorem chunk_200_3 : okR 200 31 52 = true := by decide +kernel

theorem chunk_200_4 : okR 200 52 67 = true := by decide +kernel

theorem okN_200 : okN 200 = true := okR_join 200 0 52 67 (okR_join 200 0 31 52 (okR_join 200 0 19 31 (okR_join 200 0 9 19 (chunk_200_0) chunk_200_1 (by norm_num) (by norm_num)) chunk_200_2 (by norm_num) (by norm_num)) chunk_200_3 (by norm_num) (by norm_num)) chunk_200_4 (by norm_num) (by norm_num)

theorem okN_all (n : ℕ) (hn : n ∈ Lgood) : okN n = true := by
  simp only [Lgood, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [okN_1, okN_2, okN_5, okN_9, okN_15, okN_16, okN_20, okN_25, okN_27, okN_32, okN_36, okN_40, okN_45, okN_48, okN_50, okN_54, okN_64, okN_72, okN_75, okN_80, okN_81, okN_90, okN_96, okN_100, okN_108, okN_120, okN_125, okN_128, okN_135, okN_144, okN_150, okN_160, okN_162, okN_180, okN_192, okN_200]

end OMA.Helpers

theorem OMA.solution : OMA.R_erdos_634_R1_H3_R1_H4_R1.H2 := by
  intro n a hsm h200 hexc hg hpos hsum e hrel
  have h3 : a 0 + a 1 + a 2 = n := by rw [← hsum, Fin.sum_univ_three]
  have hp0 := hpos 0
  have hp1 := hpos 1
  have hp2 := hpos 2
  have hn : 0 < n := by omega
  have hmem : n ∈ OMA.Helpers.Lgood := by
    have hc := OMA.Helpers.coverOK_true
    unfold OMA.Helpers.coverOK at hc
    have hall := List.all_eq_true.mp hc n (List.mem_range.mpr (by omega))
    simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at hall
    rcases hall with (hx | ⟨l, hl, hmod⟩) | ⟨m, hm, hmn⟩
    · exfalso
      apply hexc
      unfold OMA.Helpers.isExc at hx
      simp only [Bool.or_eq_true, beq_iff_eq] at hx
      omega
    · exfalso
      obtain ⟨h7, hlp⟩ := OMA.Helpers.bigP_prime l hl
      have := hsm l hlp (Nat.dvd_of_mod_eq_zero hmod)
      omega
    · exact hmn ▸ hm
  have hokN := OMA.Helpers.okN_all n hmem
  obtain ⟨σ, hs1, hs2, hgσ⟩ := OMA.Helpers.exists_sort a
  have hsσ : a (σ 0) + a (σ 1) + a (σ 2) = n := by
    have := Equiv.sum_comp σ a
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at this
    omega
  exact OMA.Helpers.good_perm n a σ (OMA.Helpers.good_of_ok n hn (a ∘ σ)
    (OMA.Helpers.okN_sound n hokN _ _ _ (hpos _) hs1 hs2 hsσ (hgσ.trans hg))) e hrel
