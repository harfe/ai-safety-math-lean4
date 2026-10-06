module
public import AISafetyMath.Solutions.NL_Conjecture.DLorell.Constants
public import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# Exact constants for the improved `1771` theorem


The definitions in this file are symbolic.  In particular,
`logExpAbsMoment` is an actual Lebesgue integral and `infoFloor1771` contains
an actual logarithm.  Numerical-looking inequalities are proved separately;
none of these definitions uses floating-point evaluation.
-/

@[expose] public section

namespace stoch_to_det

open MeasureTheory

/-! ### Rational threshold data -/

/-! ### Scalar-channel constants -/

/-- The exact absolute first moment of `log T`, for `T ~ Exp(1)`. -/
noncomputable def logExpAbsMoment : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), |Real.log t| * Real.exp (-t)

/-- `alpha = 2/e + E|log T|`. -/
noncomputable def alpha1771 : ℝ :=
  2 / Real.exp 1 + logExpAbsMoment

/-- The exact additive off-diagonal charge, in nats. -/
noncomputable def cOff1771 : ℝ :=
  Real.log (2 * alpha1771) - Real.eulerMascheroniConstant

/-! ### Closing ledger -/

/-! ### Exact threshold identities and elementary positivity -/

end stoch_to_det
