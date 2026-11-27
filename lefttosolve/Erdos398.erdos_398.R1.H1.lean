import OMAReductions.R_Erdos398_erdos_398_R1

/-!
# Step H1 of the reduction Erdos398.erdos_398.R1

For n at least four, four divides n factorial, so write n factorial as 4 k.
If 4 k + 1 is a square m ^ 2 then m is odd, m = 2 x + 1, and k = x (x + 1).
Conversely, if k = x (x + 1) then 4 k + 1 = (2 x + 1) ^ 2.
-/

theorem OMA.solution : OMA.R_Erdos398_erdos_398_R1.H1 := by
  intro n hn
  obtain ⟨k, hk⟩ : 4 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hn
  rw [hk, show 4 * k / 4 = k by omega]
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨x, rfl | rfl⟩ := Nat.even_or_odd' m
    · exfalso
      have h : 4 * k + 1 = 4 * (x * x) := by rw [hm]; ring
      omega
    · refine ⟨x, ?_⟩
      have h : 4 * k + 1 = 4 * (x * (x + 1)) + 1 := by rw [hm]; ring
      omega
  · rintro ⟨x, hx⟩
    exact ⟨2 * x + 1, by rw [← hx]; ring⟩
