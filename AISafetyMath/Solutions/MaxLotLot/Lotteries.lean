module

public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.Probability.Notation

set_option linter.style.header false

/-!
# Maximal lottery-lotteries: definitions and the conjectures

Setting (Scott Garrabrant, *Maximal Lottery-Lotteries*,
https://www.lesswrong.com/s/gnAaZtdwjDBBRpDmw/p/CAKZsP2v7SqqEExz9):

* `C` is a finite set of candidates.
* A *lottery* is a probability measure `A : ProbabilityMeasure C`.
* A *voter* is a utility function `u : C → [0, 1]`; the electorate is a probability measure
  `V : ProbabilityMeasure (C → unitInterval)`. A voter `u` prefers lottery `A` to lottery `B` if
  `A[u] > B[u]` (`prefer_set`).
* A *lottery-lottery* is a probability measure on lotteries. `Dominates V AA BB` says: if `A ∼ AA`,
  `B ∼ BB` and `u ∼ V` are drawn independently, then `u` prefers `A` to `B` at least as often as
  `B` to `A`. A *maximal lottery-lottery* dominates every lottery-lottery.

`MainConjecture` says that a maximal lottery-lottery exists for every finite nonempty `C` and
every `V`; `finiteVotersConjecture` restricts this to `V` supported on finitely many voters
(`HasFiniteVoters`). Both are refuted in `Counterexample.lean`.
-/

@[expose] public section

namespace MaxLotLot

open ProbabilityTheory MeasureTheory

variable {C : Type} -- candidates
variable [Finite C] [MeasurableSpace C] [DiscreteMeasurableSpace C]

variable (V : ProbabilityMeasure (C → unitInterval))

/-- The triples `((A, B), u)` such that voter `u` strictly prefers lottery `A` to lottery `B`. -/
def prefer_set : Set ((ProbabilityMeasure C × ProbabilityMeasure C) × (C → unitInterval)) :=
  {x | x.1.1[Subtype.val ∘ x.2] > x.1.2[Subtype.val ∘ x.2]}

omit [DiscreteMeasurableSpace C] in
lemma measurable_integral_eval {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass C]
    {A : X → ProbabilityMeasure C} {f : X → C → unitInterval} (hA : Measurable A)
    (hf : Measurable f) : Measurable (fun x => (A x)[Subtype.val ∘ f x]) := by
  have := Fintype.ofFinite C
  have h : (fun x => (A x)[Subtype.val ∘ f x]) =
      fun x => ∑ c, ((A x : Measure C).real {c}) • ((f x c : unitInterval) : ℝ) := by
    funext x
    exact integral_fintype (Integrable.of_finite)
  rw [h]
  refine Finset.measurable_sum _ fun c _ =>
    Measurable.smul (f := fun x => (A x : Measure C).real {c})
    (g := fun x => ((f x c : unitInterval) : ℝ)) ?_ ?_
  · exact (Measure.measurable_coe (measurableSet_singleton c)).ennreal_toReal.comp
      (measurable_subtype_coe.comp hA)
  · exact measurable_subtype_coe.comp ((measurable_pi_apply c).comp hf)

lemma prefer_measurable : MeasurableSet (prefer_set (C := C)) := by
  exact measurableSet_lt (measurable_integral_eval (by fun_prop) (by fun_prop))
    (measurable_integral_eval (by fun_prop) (by fun_prop))

/-- `AA` dominates `BB`: a random voter prefers a lottery drawn from `AA` to an independent one
drawn from `BB` at least as often as the other way round. -/
def Dominates (AA BB : ProbabilityMeasure (ProbabilityMeasure C)) : Prop :=
  ((AA.prod BB).prod V) prefer_set ≥ ((BB.prod AA).prod V) prefer_set

section MainConjecture

/-- Every electorate admits a maximal lottery-lottery. -/
def MainConjecture : Prop :=
  ∀ {C : Type} [Finite C] [MeasurableSpace C] [DiscreteMeasurableSpace C] [Nonempty C],
  ∀ (V : ProbabilityMeasure (C → unitInterval)),
  ∃ MM, ∀ LL, Dominates V MM LL

end MainConjecture

section finiteVoters

/-- `V` is supported on finitely many voters. -/
def HasFiniteVoters : Prop := ∃ (S : Set (C → unitInterval)), S.Finite ∧ V S = 1

/-- Every electorate with finitely many voters admits a maximal lottery-lottery. -/
def finiteVotersConjecture : Prop :=
  ∀ {C : Type} [Finite C] [MeasurableSpace C] [DiscreteMeasurableSpace C] [Nonempty C],
  ∀ (V : ProbabilityMeasure (C → unitInterval)),
  HasFiniteVoters V → ∃ MM, ∀ LL, Dominates V MM LL

end finiteVoters

end MaxLotLot
