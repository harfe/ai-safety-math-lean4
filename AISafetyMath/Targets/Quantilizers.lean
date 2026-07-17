import Mathlib

set_option linter.style.header false

/-! 
This file formalizes the definitions and theorems in
Articles/Quantilizers.md

The main results are
`cost_bound` and `quantilizer_optimality`

It also includes some additional sanity check lemmas.
-/

namespace Quantilizers

open ProbabilityTheory MeasureTheory


variable {A : Type*} -- actions
variable [MeasurableSpace A] [DiscreteMeasurableSpace A] [Finite A]
variable (U : A → unitInterval) -- utilities of actions
variable (γ : ProbabilityMeasure A) -- a prior over actions

-- half-open unit interval: 0 < q ≤ 1
abbrev qSpace := Set.Ioc (0 : ℝ) 1

/-- Defining sorted action functions.
It sorts actions by utility `U`, and represents `γ`
-/
def IsSortedActionFun (f : unitInterval → A) : Prop :=
  Measurable f
  ∧ Monotone (U ∘ f)
  ∧ ∀ (a : A), volume (f ⁻¹' {a}) = γ.toMeasure {a}




/-- Definition hole:
define a concrete sorted action function.
Later in `ok_mySortedActionFun` confirm
that it is actually a sorted action function.
Parameters `U` and `γ` re-declared,
to make sure they become part of the type, as the body likely will depend on it
-/
noncomputable
def mySortedActionFun (U : A → unitInterval) (γ : ProbabilityMeasure A) : unitInterval → A :=
  sorry


/-- check that `mySortedActionFun` is actually a sorted action function.
-/
lemma ok_mySortedActionFun : IsSortedActionFun U γ (mySortedActionFun U γ) := by
  sorry


/-- define the interval [1-q,1] as `Set unitInterval`
-/
def topQ (q : qSpace) : Set unitInterval :=
  Set.Icc ⟨1 - q, ⟨sub_nonneg_of_le q.2.2, sub_le_self 1 (le_of_lt q.2.1)⟩⟩ 1



/-- Definition hole:
Define a quantilizer based on mySortedActionFun.
Correctness is verified in `ok_quantilizer`.
Parameters `U` and `γ` re-declared,
to make sure they become part of the type, as the body likely will depend on it
-/
noncomputable
def quantilizer (U : A → unitInterval) (γ : ProbabilityMeasure A)
  (q : qSpace) : ProbabilityMeasure A := sorry


/-- required property of `quantilizer`.
`quantilizer` should pick randomly in the interval [1-q,1],
then pick the corresponding action.
`cond volume (topQ q)` is the uniform probability measure on [1-q,1].
`Measure.map` denotes the pushforward measure.
`Measure.map` has a junk value if the function is not AEMeasurable,
but because of `ok_mySortedActionFun` this is not applicable.
-/
lemma ok_quantilizer (q : qSpace) :
    (quantilizer U γ q).toMeasure = (cond volume (topQ q)).map (mySortedActionFun U γ) := by
  sorry

/-- sanity check:  the volume of `topQ q` is `q`.
-/
lemma volume_topQ (q : qSpace) :
    (volume (topQ q)).toReal = q.1 := by
  sorry



/-- sanity check:
if q = 1, then the quantilizer is the prior.
-/
lemma quantilizer_one_eq_gamma :
    quantilizer U γ ⟨1, by norm_num⟩ = γ := by
  sorry

/-- sanity check:
smaller q leads to higher expected utility
-/
lemma utility_quantilizer_antitone (q1 q2 : qSpace) (hq12 : q1.1 ≤ q2.1) :
    ∫ a, (U a).1 ∂(quantilizer U γ q2).toMeasure
    ≤ ∫ a, (U a).1 ∂(quantilizer U γ q1).toMeasure := by
  sorry

section Cost

/-- Lemma (cost bound on quantilizers)
If the prior expected cost is at most `1`,
then the expected cost with a quantilizer is at most 1 / q.
-/
lemma cost_bound (q : qSpace) (cost : A → NNReal)
    (hcost : ∫ a, (cost a).toReal ∂γ.toMeasure ≤ 1) :
    ∫ a, (cost a).toReal ∂ (quantilizer U γ q).toMeasure ≤ 1 / q.1 := by
  sorry

/-- Cost constraint on a probability measure p:
for all cost functions with cost under the prior at most `1`,
the cost under `p` is at most `t`.
Integrability is no problem because `A` is finite.
-/
def ConservativeCostConstraint (t : ℝ) (p : ProbabilityMeasure A) : Prop :=
    ∀ (cost : A → NNReal), ∫ a, (cost a).toReal ∂γ.toMeasure ≤ 1 →
    ∫ a, (cost a).toReal ∂p.toMeasure ≤ t


/-- define 1 / t in `qSpace` -/
noncomputable
def invInQSpace (t : ℝ) (ht : 1 < t) : qSpace :=
  ⟨ 1 / t, by
    have h2 : 0 < t := lt_trans Real.zero_lt_one ht
    exact ⟨one_div_pos.mpr h2,(div_le_one₀ h2).mpr (le_of_lt ht)⟩
  ⟩


/-- Theorem (quantilizer optimality):
a quantilizer with q = 1 / t has maximal utility
among measures that satisfy `conservative_cost_constraint`.
-/
theorem quantilizer_optimality (t : ℝ) (ht : 1 < t) :
    ConservativeCostConstraint γ t (quantilizer U γ (invInQSpace t ht))
    ∧ ∀ (p : ProbabilityMeasure A),
      ConservativeCostConstraint γ t p →
      ∫ a, (U a).1 ∂p.toMeasure
        ≤ ∫ a, (U a).1 ∂(quantilizer U γ (invInQSpace t ht)).toMeasure := by
  sorry

end Cost

end Quantilizers

