
import AISafetyMath.Solutions.NL_Conjecture.Latents

/-
The main conjecture statement, `MainConjecture`. Proved as
`NaturalLatents.conjecture_solution` in `Bridge.lean`.
-/

namespace NaturalLatents

open MeasureTheory

section Conjecture

/- we will avoid the `variable` declarations for the conjecture,
to make negation of the conjecture easier.-/

open ProbabilityTheory

/-- The conjecture:
If there exists an approximate natural latent,
does there exist an approximate deterministic latent,
with a (globally) linear bound for the approximation error?

The `ε : ENNReal` does not cause issues here, as the `ε = ⊤` case
is trivial.
-/
def MainConjecture : Prop :=
  ∃ (cc : NNReal), cc > 0 ∧
  ∀ (X Y : Type) [Finite X] [Finite Y]
  [MeasurableSpace X] [MeasurableSpace Y] [DiscreteMeasurableSpace X] [DiscreteMeasurableSpace Y]
  (P : ProbabilityMeasure (X × Y)) (ε : ENNReal),
  HasStochasticNL P ε → HasDeterministicNL P (cc * ε)


/- PICK EXACTLY ONE of proof or disproof: proved as `NaturalLatents.conjecture_solution` in
`Bridge.lean` (via `Bridge.mainConjecture_of_T_le_Cstar`), since `Bridge.lean` imports this
file and so cannot be imported back here. -/

-- theorem conjecture_refutation : ¬MainConjecture := by sorry

/- Not both can be true, otherwise we could conclude `False` from it. -/
-- example : False := conjecture_refutation conjecture_solution

end Conjecture

end NaturalLatents
