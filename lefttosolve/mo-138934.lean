import OMAStatements.S_mo_138934
import Mathlib

open Polynomial
open scoped NumberField

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_138934.main) := by
  intro h
  obtain ⟨n, hn, hirr⟩ := h ℚ 1 (-2) one_ne_zero (by
    intro e
    have := congrArg (fun z : 𝓞 ℚ => (z : ℚ)) e
    norm_num at this)
  have hA : ((1 : 𝓞 ℚ) : ℚ) = 1 := by simp
  have hB : ((-2 : 𝓞 ℚ) : ℚ) = -2 := by
    simp only [map_neg, neg_inj]
    exact map_ofNat _ 2
  rw [hA, hB] at hirr
  have hroot : IsRoot ((X : ℚ[X]) ^ n + C (1 : ℚ) * X + C (-2 : ℚ)) 1 := by
    simp [IsRoot]
    norm_num
  have hdeg := degree_eq_one_of_irreducible_of_root hirr hroot
  have hnd : ((X : ℚ[X]) ^ n + C (1 : ℚ) * X + C (-2 : ℚ)).natDegree = n := by
    compute_degree!
    all_goals try simp [show n ≠ 1 by omega, show n ≠ 0 by omega]
    all_goals try omega
  have h1 : ((X : ℚ[X]) ^ n + C (1 : ℚ) * X + C (-2 : ℚ)).natDegree = 1 :=
    natDegree_eq_of_degree_eq_some hdeg
  omega
