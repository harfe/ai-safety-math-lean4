import Mathlib

import AISafetyMath.Targets.IB_RL

set_option linter.style.header false

/-!
This file formalizes the definitions and propositions in
Articles/IB_Basics.md

The main result is `infraKernelOfEnvironments_continuous`.

It also includes some additional sanity check lemmas.
-/

namespace IB

open ProbabilityTheory MeasureTheory

section CredalSets

open TopologicalSpace

variable {X : Type*}
variable [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

abbrev Δ X [MeasurableSpace X] := ProbabilityMeasure X

/-- We want to define `Δ X` as a metric space.
Mathlib already has that `Δ X` is a metrizable space.
We can therefore pick a metric,
and that metric induces the weak topology.
But beyond that we do not have concrete properties of the metric.
-/
noncomputable local
instance instMetricSpaceDeltaX : MetricSpace (Δ X) :=
  metrizableSpaceMetric (Δ X)


/- sanity check: the topology induced by that metric
is the same as the standard mathlib topology (the weak topology) on `Δ X`.
Note that we need to go through `PseudoMetricSpace` and `UniformSpace`
to get the topology induced by the metric.
-/
noncomputable
example : instMetricSpaceDeltaX.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
  (ProbabilityMeasure.instTopologicalSpace : TopologicalSpace (Δ X))
  := rfl


/-- Lemma (metric of weak convergence):
A sequence of probability measures converges by distance
iff testing with all continuous functions converges.
-/
lemma convergence_iff_weak (μ : ℕ → Δ X) (μ0 : Δ X) :
    Filter.Tendsto (fun n => dist (μ n) μ0) Filter.atTop (nhds 0)
    ↔ ∀ (f : X → ℝ), Continuous f →
    Filter.Tendsto (fun n => ∫ x,  f x ∂(μ n)) Filter.atTop (nhds (∫ x, f x ∂ μ0)) := by
  sorry

/- We want to use a metric on the nonempty compact sets of `X`.
Mathlib actually has a `MetricSpace` instance.
The metric used is the Hausdorff distance.
-/
noncomputable
example : MetricSpace (NonemptyCompacts (Δ X)) :=
  Metric.NonemptyCompacts.instMetricSpace

/- Lemma: compactness of space of probability measures. -/
example : CompactSpace (Δ X) := instCompactSpaceProbabilityMeasure


/-- Defining convexity of a set of probability measures is nontrivial in mathlib.
We convert probability measures to measures to signed measures,
which is a vector space where mathlib can define convexity.
-/
def ProbConvex {X : Type*} [MeasurableSpace X]
  (s : Set (ProbabilityMeasure X)) : Prop :=
  Convex ℝ ((fun x => x.toMeasure.toSignedMeasure) '' s)

/-- an alternative equivalent definition:
using the mathlib convexity definition on measures,
but without an underlying field.
-/
lemma probConvex_iff {X : Type*} [MeasurableSpace X]
    (s : Set (ProbabilityMeasure X)) :
    ProbConvex s ↔ Convex NNReal ((fun x => x.toMeasure) '' s) := by
  sorry

/-- define the type `Credal X` of credal sets over `X` as
nonempty compact sets that are also convex.
Note that because `Δ X` is a compact space, subsets of it are closed
iff they are compact.
-/
def Credal X [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] :=
  { s : NonemptyCompacts (Δ X) // ProbConvex s.carrier }

/-- Lemma: the set of credal sets
with the Hausdorff distance is a metric space.
This instance can be exported.
-/
noncomputable scoped
instance instCredalMetric : MetricSpace (Credal X) := Subtype.metricSpace

namespace Credal

def carrier (s : Credal X) := s.1.carrier

/- confirming that the metric on `Credal X` is the Hausdorff distance.
We do not redefine Hausdorff distance manually.
-/
example (s t : Credal X) :
    dist s t = Metric.hausdorffDist s.carrier t.carrier := rfl


def byClosedConvex (s : Set (Δ X)) (hne : s.Nonempty)
    (hcl : IsClosed s) (hcvx : ProbConvex s) : Credal X :=
    ⟨{ carrier := s, nonempty' := hne,
       isCompact' := IsClosed.isCompact hcl}, hcvx⟩


/- we also want to be able to construct elements of `Credal X`
by using the closed convex hull of a set.
Due to working on the space `Δ X`, we will roll our own definition of `convexHull`.
We will also need a bunch of helper lemmas.
-/

set_option linter.defProp false in
/-- This could have been a lemma, but
for compatibility with the Comparator tool,
lemmas that use `sorry` and are
used by another definition will use def instead of lemma.
It is safe because its type is a `Prop`.
Same with `probConvexHull_convex`, `probConvexHull_nonempty`, `closed_convex_of_convex`
-/
def probConvex_sInter (S : Set (Set (Δ X)))
    (hS : ∀ t ∈ S, ProbConvex t) : ProbConvex (⋂₀ S) := sorry

/-- follows definition of the existing `convexHull` in mathlib -/
def probConvexHull := ClosureOperator.ofCompletePred (@ProbConvex X _) probConvex_sInter

set_option linter.defProp false in
def probConvexHull_convex (s : Set (Δ X)) : ProbConvex (probConvexHull s) := sorry

set_option linter.defProp false in
def probConvexHull_nonempty (s : Set (Δ X))
    (hne : s.Nonempty) : (probConvexHull s).Nonempty := sorry

set_option linter.defProp false in
def probConvex_closure (s : Set (Δ X))
    (hcvx : ProbConvex s) : ProbConvex (closure s) := sorry

/-- Finally: we can construct elements in `Credal X` by taking
the closed convex hull. -/
def byClosedConvexHull (s : Set (Δ X)) (hne : s.Nonempty) : Credal X :=
  byClosedConvex
    (closure (probConvexHull s))
    (closure_nonempty_iff.mpr (probConvexHull_nonempty s hne))
    isClosed_closure
    (probConvex_closure (probConvexHull s) (probConvexHull_convex s))


end Credal

end CredalSets

section InfraKernels

open IB_RL

variable {A O : Type*}
variable [Finite A] [Finite O]

/- we use discrete measurable and topological spaces on A and O -/
variable [MeasurableSpace A] [MeasurableSpace O]
variable [DiscreteMeasurableSpace A] [DiscreteMeasurableSpace O]
variable [TopologicalSpace A] [DiscreteTopology A]
variable [TopologicalSpace O] [DiscreteTopology O]

/- We want to be able to use `Credal (Destiny A O)`.
This requires a bunch of instance work:
MetricSpace, CompactSpace, MeasurableSpace, TopologicalSpace, BorelSpace.
We need to state MetricSpace and TopologicalSpace explicitly here.
-/

/-- Lemma: destinies as a metric space
Mathlib also provides us with `PiNat.metricSpace`,
which can be used as a metric on `Destiny A O`.

As described in the comments on `PiNat.metricSpace`,
the distance is given by `dist x y = (1/2)^n`,
where `n` is the smallest index where `x` and `y` differ,
and the metric is compatible with the product topology.
-/
noncomputable scoped
instance instDestinyMetric : MetricSpace (Destiny A O) := PiNat.metricSpace

/- sanity check:
the topology induced by `PiNat.metricSpace` is the same
as the product topology.
-/
example : instDestinyMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
  (Pi.topologicalSpace : TopologicalSpace (Destiny A O)) := rfl


/-- The space of policies as a topological space.
Mathlib uses the product topology here
-/
noncomputable scoped
instance instPolicyTS : TopologicalSpace (Policy A O) := Pi.topologicalSpace

/- Lemma: The space of destinies is a compact space. -/
example : CompactSpace (Destiny A O) := Function.compactSpace


/-- Definition:
infrakernel generated by a set of environments.
Note that we say infraKernel here despite not yet knowing that the map is continuous
-/
noncomputable
def infraKernelOfEnvironments (E : Set (Environment A O)) (hne : E.Nonempty)
    (π : Policy A O) : Credal (Destiny A O) :=
    Credal.byClosedConvexHull
      ( (fun μ => trajectoryProbMeasure π μ) '' E)
      (Set.Nonempty.image (fun μ ↦ trajectoryProbMeasure π μ) hne)


/-- Proposition 1:
An infrakernel generated by environments is continuous.
-/
theorem infraKernelOfEnvironments_continuous (E : Set (Environment A O)) (hne : E.Nonempty) :
    Continuous (infraKernelOfEnvironments E hne) := by
  sorry


end InfraKernels

end IB

