import OMAStatements.S_opg_distribution_and_upper_bound_of_mimic_numbers
import Mathlib

namespace OMA.Helpers

open OMA.S_opg_distribution_and_upper_bound_of_mimic_numbers
open scoped Polynomial

theorem step_zero (M D : ℕ) : step M D 0 = 0 := by
  simp [step]

theorem step_rec (M D q d : ℕ) (hM : 1 < M) (hd : d < M) :
    step M D (d + M * q) = d + (M - D) * step M D q := by
  by_cases h : d ≠ 0 ∨ q ≠ 0
  · unfold step
    rw [Nat.digits_add M hM d q hd h, Nat.ofDigits_cons]
  · have h1 : d = 0 := by tauto
    have h2 : q = 0 := by tauto
    subst h1; subst h2
    simp [step_zero]

theorem step_div (M D n : ℕ) (hM : 1 < M) :
    step M D n = n % M + (M - D) * step M D (n / M) := by
  have h := step_rec M D (n / M) (n % M) hM (Nat.mod_lt _ (by omega))
  rwa [Nat.mod_add_div] at h

theorem step_le (M D n : ℕ) : step M D n ≤ n := by
  have h := Nat.ofDigits_monotone (M.digits n) (Nat.sub_le M D)
  rwa [Nat.ofDigits_digits] at h

theorem step_modEq (M D n : ℕ) (hD : D ≤ M) : step M D n ≡ n [MOD D] := by
  have h1 : M - D ≡ M [MOD D] :=
    (Nat.modEq_iff_dvd' (Nat.sub_le M D)).mpr (by rw [Nat.sub_sub_self hD])
  have h := Nat.ofDigits_modEq' (M - D) M D h1 (M.digits n)
  rwa [Nat.ofDigits_digits] at h

theorem step_small (M D n : ℕ) (hM : 1 < M) (hn : n < M) : step M D n = n := by
  have h := step_rec M D 0 n hM hn
  simpa [step_zero] using h

theorem step_pos (M D : ℕ) (hM : 1 < M) (hD : D < M) : ∀ n, 0 < n → 0 < step M D n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < M
    · rw [step_small M D n hM hlt]; exact hn
    · have hq : 0 < n / M := Nat.div_pos (by omega) (by omega)
      have hq2 : n / M < n := Nat.div_lt_self hn hM
      have h1 := ih (n / M) hq2 hq
      rw [step_div M D n hM]
      have h2 : 0 < (M - D) * step M D (n / M) := Nat.mul_pos (by omega) h1
      omega

theorem step_lt_self (M D n : ℕ) (hM : 1 < M) (hD : 0 < D) (hn : M ≤ n) : step M D n < n := by
  have hq : 0 < n / M := Nat.div_pos hn (by omega)
  have h1 := step_le M D (n / M)
  have h2 := step_div M D n hM
  have h3 := Nat.mod_add_div n M
  have h4 : (M - D) * step M D (n / M) ≤ (M - D) * (n / M) := Nat.mul_le_mul_left _ h1
  have h5 : (M - D) * (n / M) < M * (n / M) := Nat.mul_lt_mul_of_pos_right (by omega) hq
  omega

theorem first_succ (M D h n : ℕ) :
    First M D (h + 1) n ↔ n ≠ D ∧ First M D h (step M D n) := by
  unfold First
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_, ?_⟩
    · exact h2 0 (by omega)
    · rwa [Function.iterate_succ_apply] at h1
    · intro j hj
      have := h2 (j + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
  · rintro ⟨h0, h1, h2⟩
    refine ⟨?_, ?_⟩
    · rwa [Function.iterate_succ_apply]
    · intro j hj
      cases j with
      | zero => exact h0
      | succ j =>
        rw [Function.iterate_succ_apply]
        exact h2 j (by omega)

theorem first_zero (M D n : ℕ) : First M D 0 n ↔ n = D := by
  unfold First
  simp

theorem first_dvd (M D : ℕ) (hD : D ≤ M) : ∀ h n, First M D h n → D ∣ n := by
  intro h
  induction h with
  | zero => intro n hn; rw [first_zero] at hn; rw [hn]
  | succ h ih =>
    intro n hn
    rw [first_succ] at hn
    have h1 := ih _ hn.2
    exact ((step_modEq M D n hD).dvd_iff (dvd_refl D)).mp h1

theorem first_pos (M D : ℕ) (hD : 0 < D) (h n : ℕ) (hf : First M D h n) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    have h1 := hf.1
    rw [Function.iterate_fixed (step_zero M D)] at h1
    omega
  · exact h0

theorem not_first_small (M D : ℕ) (hM : 1 < M) (h n : ℕ) (hn : n < M) (hne : n ≠ D) :
    ¬ First M D h n := by
  intro hf
  have h1 := hf.1
  rw [Function.iterate_fixed (step_small M D n hM hn)] at h1
  exact hne h1

/-! ### The histogram law -/

theorem window_mul (M D : ℕ) (hM : 1 < M) : ∀ q : ℕ,
    windowPoly M D (M * q) =
      (windowPoly M D q).comp (Polynomial.X ^ (M - D)) * digitPoly M := by
  intro q
  induction q with
  | zero => simp [windowPoly]
  | succ q ih =>
    have e1 : windowPoly M D (M * (q + 1)) = windowPoly M D (M * q) +
        ∑ d ∈ Finset.range M, Polynomial.X ^ step M D (M * q + d) := by
      unfold windowPoly
      rw [Nat.mul_succ, Finset.sum_range_add]
    have e2 : windowPoly M D (q + 1) = windowPoly M D q + Polynomial.X ^ step M D q := by
      unfold windowPoly
      rw [Finset.sum_range_succ]
    have e3 : ∑ d ∈ Finset.range M, (Polynomial.X : ℕ[X]) ^ step M D (M * q + d) =
        Polynomial.X ^ ((M - D) * step M D q) * digitPoly M := by
      unfold digitPoly
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.add_comm, step_rec M D q d hM (Finset.mem_range.mp hd), pow_add, mul_comm]
    rw [e1, e2, e3, ih, Polynomial.add_comp, Polynomial.X_pow_comp, add_mul, ← pow_mul]

theorem hist1 (M D : ℕ) (hM : 1 < M) (q r : ℕ) (hr : r ≤ M) :
    windowPoly M D (M * q + r) =
      (windowPoly M D q).comp (Polynomial.X ^ (M - D)) * digitPoly M +
        Polynomial.X ^ ((M - D) * step M D q) * digitPoly r := by
  have e1 : windowPoly M D (M * q + r) = windowPoly M D (M * q) +
      ∑ d ∈ Finset.range r, Polynomial.X ^ step M D (M * q + d) := by
    unfold windowPoly
    rw [Finset.sum_range_add]
  have e3 : ∑ d ∈ Finset.range r, (Polynomial.X : ℕ[X]) ^ step M D (M * q + d) =
      Polynomial.X ^ ((M - D) * step M D q) * digitPoly r := by
    unfold digitPoly
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hd' : d < M := lt_of_lt_of_le (Finset.mem_range.mp hd) hr
    rw [Nat.add_comm, step_rec M D q d hM hd', pow_add, mul_comm]
  rw [e1, e3, window_mul M D hM q]

open scoped Classical in
theorem window_coeff (M D N t : ℕ) :
    (windowPoly M D N).coeff t = ((Finset.range N).filter (fun n => step M D n = t)).card := by
  unfold windowPoly
  rw [Polynomial.finsetSum_coeff, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro n _
  rw [Polynomial.coeff_X_pow]
  by_cases h : step M D n = t
  · simp [h]
  · have h' : ¬ t = step M D n := fun e => h e.symm
    simp [h, h']

open scoped Classical in
theorem hist2 (M D N h : ℕ) :
    ((Finset.range N).filter (First M D (h+1))).card =
      (∑ t ∈ (Finset.range N).filter (First M D h), (windowPoly M D N).coeff t) -
        (if D < N ∧ First M D h (step M D D) then 1 else 0) := by
  have e1 : (Finset.range N).filter (First M D (h+1)) =
      ((Finset.range N).filter (fun n => First M D h (step M D n))).erase D := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range, first_succ]
    tauto
  have e2 : ∑ t ∈ (Finset.range N).filter (First M D h), (windowPoly M D N).coeff t =
      ((Finset.range N).filter (fun n => First M D h (step M D n))).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := step M D)
      (t := (Finset.range N).filter (First M D h))]
    · apply Finset.sum_congr rfl
      intro t ht
      rw [window_coeff]
      congr 1
      ext n
      simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, by rw [h2]; exact ht.2⟩, h2⟩
      · rintro ⟨⟨h1, _⟩, h2⟩
        exact ⟨h1, h2⟩
    · intro n hn
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn ⊢
      exact ⟨lt_of_le_of_lt (step_le M D n) hn.1, hn.2⟩
  rw [e1, e2, Finset.card_erase_eq_ite]
  simp only [Finset.mem_filter, Finset.mem_range]
  split_ifs <;> rfl

/-! ### Rigid case -/

theorem rigid_inv (M D : ℕ) (hM : 1 < M) (hD : D < M - D) (n : ℕ)
    (hn : (n < M ∧ n ≠ D) ∨ M - D ≤ n) :
    (step M D n < M ∧ step M D n ≠ D) ∨ M - D ≤ step M D n := by
  by_cases hlt : n < M
  · rw [step_small M D n hM hlt]
    rcases hn with h | h
    · left; exact h
    · right; exact h
  · right
    have hq : 0 < n / M := Nat.div_pos (by omega) (by omega)
    have h1 := step_pos M D hM (by omega) (n / M) hq
    rw [step_div M D n hM]
    have h2 : (M - D) * 1 ≤ (M - D) * step M D (n / M) := Nat.mul_le_mul_left _ h1
    omega

theorem rigid_iter (M D : ℕ) (hM : 1 < M) (hD : D < M - D) (n : ℕ)
    (hn : (n < M ∧ n ≠ D) ∨ M - D ≤ n) : ∀ h : ℕ,
    (((step M D)^[h] n < M ∧ (step M D)^[h] n ≠ D) ∨ M - D ≤ (step M D)^[h] n) := by
  intro h
  induction h with
  | zero => simpa using hn
  | succ h ih =>
    rw [Function.iterate_succ_apply']
    exact rigid_inv M D hM hD _ ih

theorem rigid (M D : ℕ) (hM : 1 < M) (hD0 : 0 < D) (hc : D = M ∨ D < M - D) (n h : ℕ)
    (hf : First M D h n) : n = D ∧ h = 0 := by
  have hn : n = D := by
    by_contra hne
    rcases hc with hc | hc
    · cases h with
      | zero => rw [first_zero] at hf; exact hne hf
      | succ h =>
        rw [first_succ] at hf
        have h1 : step M D n < M := by
          rw [step_div M D n hM]
          have : M - D = 0 := by omega
          rw [this, Nat.zero_mul]
          exact Nat.mod_lt _ (by omega)
        exact not_first_small M D hM h _ h1 (by omega) hf.2
    · have h1 := rigid_iter M D hM hc n (by omega) h
      have h2 := hf.1
      omega
  refine ⟨hn, ?_⟩
  by_contra hh
  have := hf.2 0 (by omega)
  exact this (by simpa using hn)

/-! ### Reaching case -/

theorem reach (M D : ℕ) (hM : 1 < M) (hD0 : 0 < D) (hDM : D < M) (hb : M - D ≤ D) :
    ∀ n, 0 < n → D ∣ n → ∃ h, (step M D)^[h] n = D := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hdvd
    by_cases hlt : n < M
    · refine ⟨0, ?_⟩
      obtain ⟨k, rfl⟩ := hdvd
      have hk : k = 1 := by
        have hk0 : 0 < k := Nat.pos_of_mul_pos_left hn
        by_contra hk1
        have : D * 2 ≤ D * k := Nat.mul_le_mul_left _ (by omega)
        omega
      subst hk
      simp
    · have h1 := step_lt_self M D n hM hD0 (by omega)
      have h2 := step_pos M D hM hDM n hn
      have h3 : D ∣ step M D n :=
        ((step_modEq M D n (by omega)).dvd_iff (dvd_refl D)).mpr hdvd
      obtain ⟨h, hh⟩ := ih _ h1 h2 h3
      exact ⟨h + 1, by rw [Function.iterate_succ_apply]; exact hh⟩

theorem reach_first (M D : ℕ) (hM : 1 < M) (hD0 : 0 < D) (hDM : D < M) (hb : M - D ≤ D)
    (n : ℕ) (hn : 0 < n) (hdvd : D ∣ n) : ∃ h, First M D h n := by
  classical
  have ex := reach M D hM hD0 hDM hb n hn hdvd
  exact ⟨Nat.find ex, Nat.find_spec ex, fun j hj => Nat.find_min ex hj⟩

theorem surj (M D : ℕ) (hM : 1 < M) (hD0 : 0 < D) (hDM : D < M) :
    ∀ t, ∃ n, step M D n = t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases hlt : t < M
    · exact ⟨t, step_small M D t hM hlt⟩
    · by_cases hb : M - D = 1
      · obtain ⟨q, hq⟩ := ih (t - 1) (by omega)
        refine ⟨1 + M * q, ?_⟩
        rw [step_rec M D q 1 hM hM, hq, hb]
        omega
      · have hb2 : 2 ≤ M - D := by omega
        have hdl : t / (M - D) < t := Nat.div_lt_self (by omega) hb2
        obtain ⟨q, hq⟩ := ih (t / (M - D)) hdl
        refine ⟨t % (M - D) + M * q, ?_⟩
        have hm : t % (M - D) < M - D := Nat.mod_lt _ (by omega)
        rw [step_rec M D q _ hM (by omega), hq]
        exact Nat.mod_add_div t (M - D)

theorem pre (M D : ℕ) (hM : 1 < M) (hD0 : 0 < D) (hDM : D < M) (hb : M - D ≤ D) :
    ∀ t, ∃ n, n ≠ D ∧ step M D n = t := by
  intro t
  by_cases ht : t = D
  · refine ⟨(D - (M - D)) + M * 1, by omega, ?_⟩
    rw [step_rec M D 1 _ hM (by omega), step_small M D 1 hM hM]
    omega
  · obtain ⟨n, hn⟩ := surj M D hM hD0 hDM t
    refine ⟨n, ?_, hn⟩
    intro e
    rw [e, step_small M D D hM hDM] at hn
    exact ht hn.symm

theorem chain (M D : ℕ) (hM : 1 < M) (hD0 : 0 < D) (hDM : D < M) (hb : M - D ≤ D) :
    ∀ h, ∃ n, First M D h n := by
  intro h
  induction h with
  | zero => exact ⟨D, (first_zero M D D).mpr rfl⟩
  | succ h ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨n, hn1, hn2⟩ := pre M D hM hD0 hDM hb m
    exact ⟨n, (first_succ M D h n).mpr ⟨hn1, by rw [hn2]; exact hm⟩⟩

/-! ### Boundedness for base at least two -/

theorem lt_pow (M D : ℕ) (hM : 1 < M) (hb : 2 ≤ M - D) :
    ∀ n, n < M ^ (step M D n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hlt : n < M
    · rw [step_small M D n hM hlt]
      calc n < M := hlt
        _ = M ^ 1 := (pow_one M).symm
        _ ≤ M ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    · have hn : 0 < n := by omega
      have hq : 0 < n / M := Nat.div_pos (by omega) (by omega)
      have hq2 : n / M < n := Nat.div_lt_self hn hM
      have h1 := ih (n / M) hq2
      have h2 := step_pos M D hM (by omega) (n / M) hq
      have h3 := step_div M D n hM
      have h4 : 2 * step M D (n / M) ≤ (M - D) * step M D (n / M) :=
        Nat.mul_le_mul_right _ hb
      have h5 : step M D (n / M) + 2 ≤ step M D n + 1 := by omega
      have h6 : n < M * (n / M + 1) := by
        have := Nat.mod_add_div n M
        have := Nat.mod_lt n (show 0 < M by omega)
        rw [Nat.mul_add]
        omega
      calc n < M * (n / M + 1) := h6
        _ ≤ M * M ^ (step M D (n / M) + 1) := Nat.mul_le_mul_left _ h1
        _ = M ^ (step M D (n / M) + 2) := by ring
        _ ≤ M ^ (step M D n + 1) := Nat.pow_le_pow_right (by omega) h5

theorem bound (M D : ℕ) (hM : 1 < M) (hb : 2 ≤ M - D) :
    ∀ h T : ℕ, ∃ N, ∀ n, (step M D)^[h] n ≤ T → n < N := by
  intro h
  induction h with
  | zero =>
    intro T
    exact ⟨T + 1, fun n hn => by simpa [Nat.lt_succ_iff] using hn⟩
  | succ h ih =>
    intro T
    obtain ⟨N, hN⟩ := ih T
    refine ⟨M ^ N, fun n hn => ?_⟩
    rw [Function.iterate_succ_apply] at hn
    have h1 := hN _ hn
    calc n < M ^ (step M D n + 1) := lt_pow M D hM hb n
      _ ≤ M ^ N := Nat.pow_le_pow_right (by omega) (by omega)

/-! ### Unbounded case for base one -/

theorem step_pow_mul (M D : ℕ) (hM : 1 < M) (hb : M - D = 1) (p : ℕ) :
    ∀ k, step M D (M ^ k * p) = step M D p := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h := step_rec M D (M ^ k * p) 0 hM (by omega)
    rw [hb] at h
    have e : M ^ (k + 1) * p = 0 + M * (M ^ k * p) := by ring
    rw [e, h, ih]
    omega

theorem unbounded (M D : ℕ) (hM : 1 < M) (hD0 : 0 < D) (hb : M - D = 1) (h K : ℕ) :
    ∃ n, K < n ∧ D ∣ n ∧ First M D (h + 1) n := by
  obtain ⟨m, hm⟩ := chain M D hM hD0 (by omega) (by omega) h
  have hm0 := first_pos M D hD0 h m hm
  obtain ⟨p, hp⟩ := surj M D hM hD0 (by omega) m
  have hp0 : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · rw [h0, step_zero] at hp; omega
    · exact h0
  have h1 : K + 1 < M ^ (K + 1) := Nat.lt_pow_self hM
  have h2 : M ^ 1 ≤ M ^ (K + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  rw [pow_one] at h2
  have h3 : M ^ (K + 1) * 1 ≤ M ^ (K + 1) * p := Nat.mul_le_mul_left _ hp0
  have hf : First M D (h + 1) (M ^ (K + 1) * p) := by
    rw [first_succ, step_pow_mul M D hM hb p (K + 1), hp]
    exact ⟨by omega, hm⟩
  exact ⟨M ^ (K + 1) * p, by omega, first_dvd M D (by omega) _ _ hf, hf⟩

end OMA.Helpers

open OMA.S_opg_distribution_and_upper_bound_of_mimic_numbers in
theorem OMA.solution : type_of% @OMA.S_opg_distribution_and_upper_bound_of_mimic_numbers.main := by
  intro M D hM hD0 hDM
  refine ⟨⟨fun q r hr => OMA.Helpers.hist1 M D hM q r hr, fun N h => ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · convert OMA.Helpers.hist2 M D N h
  · intro n h hf
    exact ⟨OMA.Helpers.first_pos M D hD0 h n hf, OMA.Helpers.first_dvd M D hDM h n hf⟩
  · intro hc n h _
    constructor
    · exact OMA.Helpers.rigid M D hM hD0 hc n h
    · rintro ⟨rfl, rfl⟩
      exact (OMA.Helpers.first_zero M n n).mpr rfl
  · rintro ⟨h1, h2⟩
    refine ⟨fun n hn hd => OMA.Helpers.reach_first M D hM hD0 h1 h2 n hn hd, fun h => ?_⟩
    obtain ⟨n, hn⟩ := OMA.Helpers.chain M D hM hD0 h1 h2 h
    have hd := OMA.Helpers.first_dvd M D hDM h n hn
    exact ⟨n, Nat.le_of_dvd (OMA.Helpers.first_pos M D hD0 h n hn) hd, hd, hn⟩
  · intro hb h
    obtain ⟨N, hN⟩ := OMA.Helpers.bound M D hM hb h D
    exact ⟨N, fun n hf => hN n (le_of_eq hf.1)⟩
  · intro hb h K
    exact OMA.Helpers.unbounded M D hM hD0 hb h K
