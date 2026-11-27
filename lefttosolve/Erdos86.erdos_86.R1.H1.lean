import OMAReductions.R_Erdos86_erdos_86_R1

/-!
# Step H1 of the reduction Erdos86.erdos_86.R1

Monotonicity of the square-free edge density of hypercubes: a bound valid in some
dimension m propagates to every dimension n at least m. The reduction file already
contains the face-averaging argument as the theorem `face_averaging`, so the step
is closed by that theorem.
-/

theorem OMA.solution : OMA.R_Erdos86_erdos_86_R1.H1 :=
  OMA.R_Erdos86_erdos_86_R1.face_averaging
