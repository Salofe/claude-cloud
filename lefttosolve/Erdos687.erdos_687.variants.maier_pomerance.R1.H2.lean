import OMAReductions.R_Erdos687_erdos_687_variants_maier_pomerance_R1

/-!
Step H2 of reduction Erdos687.erdos_687.variants.maier_pomerance.R1: any fixed real power of
log log x is O of (log x)^ε, because (log y)^C = o(y^ε) as y tends to infinity, applied with
y = log x. Multiplying by x (log x)^2 and merging the powers of log x gives the claim.
-/

open Asymptotics Filter Real

theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R1.H2 := by
  intro C ε hε
  have hlog : Tendsto (fun x : ℕ => log (x : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : (fun x : ℕ => log (log (x : ℝ)) ^ C) =O[atTop] (fun x : ℕ => log (x : ℝ) ^ ε) :=
    ((isLittleO_log_rpow_rpow_atTop C hε).comp_tendsto hlog).isBigO
  have h2 := (isBigO_refl (fun x : ℕ => (x : ℝ) * log (x : ℝ) ^ (2 : ℝ)) atTop).mul h1
  refine h2.congr' (Eventually.of_forall fun x => rfl) ?_
  filter_upwards [hlog.eventually_gt_atTop 0] with x hx
  rw [rpow_add hx]
  ring
