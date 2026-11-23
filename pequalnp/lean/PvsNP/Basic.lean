import Mathlib

/-- Smoke test for the toolchain: Fischer's identity at three variables. -/
theorem fischer3 (R : Type) [CommRing R] (x y z : R) :
    24 * x * y * z = (x + y + z) ^ 3 - (x + y - z) ^ 3 - (x - y + z) ^ 3 + (x - y - z) ^ 3 := by
  ring
