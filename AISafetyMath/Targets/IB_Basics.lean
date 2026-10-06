module
public import Mathlib

public import AISafetyMath.Targets.IB_RL

set_option linter.style.header false

/-
This file formalizes the definitions and propositions in
Articles/IB_Basics.md

The main results are
- `continuous_of_CCL`
- `exists_ib_optimal_policy`

It also includes some additional sanity check lemmas.
-/

@[expose] public section

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
Mathlib has actually a `MetricSpace` instance.
The metric used is the Hausdorff distance.
-/
noncomputable
example : MetricSpace (NonemptyCompacts (Δ X)) :=
  -- by infer_instance
  NonemptyCompacts.instMetricSpace

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
using a manual definition of a convex set.
-/
lemma probConvex_iff {X : Type*} [MeasurableSpace X]
    (s : Set (ProbabilityMeasure X)) :
    ProbConvex s ↔
      ∀ (x y z : ProbabilityMeasure X) (a b : ENNReal), a + b = 1 →
      a • x.toMeasure + b • y.toMeasure = z.toMeasure → x ∈ s → y ∈ s → z ∈ s := by
  sorry

/-- define the type `Credal X` of credal sets over `X` as
nonempty compact sets that are also convex.
Note that because `Δ X` is a compact space, subsets of it are closed
iff they are compact.
-/
def Credal X [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] :=
  { s : NonemptyCompacts (Δ X) // ProbConvex s.carrier }

/-- Lemma: the set of credal sets with the Hausdorff distance is a metric space.
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

/-- sanity check: confirming that distance on `Credal X`
matches our definition of Hausdorff distance.
-/
lemma dist_is_hausdorff (s t : Credal X) :
    dist s t = max (⨆ (x : s.carrier), ⨅ (y : t.carrier), dist x.1 y.1)
    (⨆ (y : t.carrier), ⨅ (x : s.carrier), dist y.1 x.1) := by
  sorry


def ofClosedConvex (s : Set (Δ X)) (hne : s.Nonempty)
    (hcl : IsClosed s) (hcvx : ProbConvex s) : Credal X :=
    ⟨{ carrier := s, nonempty' := hne,
       isCompact' := IsClosed.isCompact hcl}, hcvx⟩


/- we also want to be able to construct elements of `Credal X`
by using the closed convex hull of a set.
Due to working on the space `Δ X`, we will roll our own definition of `convexHull`.
We will also need a bunch of helper lemmas.
-/

/-- Definition hole for closed convex hull of a set. -/
noncomputable
def closedConvexHull {X : Type*}
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (s : Set (Δ X)) : Set (Δ X) := sorry


/-- Pinning down the definition by its properties:
The closed convex hull of a set `S` is the smallest closed and convex set that contains `S`.
-/
lemma ok_closedConvexHull (s : Set (Δ X)) :
    s ⊆ closedConvexHull s ∧ ProbConvex (closedConvexHull s) ∧ IsClosed (closedConvexHull s)
    ∧ ∀ (t : Set (Δ X)), s ⊆ t → ProbConvex t → IsClosed t → closedConvexHull s ⊆ t
    := by
  sorry


/-- Finally: we can construct elements in `Credal X` by taking
the closed convex hull. -/
def byClosedConvexHull (s : Set (Δ X)) (hne : s.Nonempty) : Credal X :=
  ofClosedConvex
    (closedConvexHull s)
    (hne.mono (ok_closedConvexHull s).1)
    (ok_closedConvexHull s).2.2.1
    (ok_closedConvexHull s).2.1


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

/-- sanity check:
confirming that the metric given by `PiNat.metricSpace`
matches our definition
-/
lemma ok_destinyMetric (h1 h2 : Destiny A O) (t : ℕ)
    (ht_ne : h1 t ≠ h2 t)
    (ht_eq : ∀ s < t, h1 s = h2 s) :
    dist h1 h2 = (2 : ℝ) ^ (- (t : ℝ)) := by
  sorry

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

/-- sanity check: infrakernel generated by a singleton
is `trajectoryProbMeasure`.
-/
lemma infraKernel_singleton (μ : Environment A O) (π : Policy A O) :
    (infraKernelOfEnvironments {μ} (Set.singleton_nonempty μ) π).carrier =
    {trajectoryProbMeasure π μ} := by
  sorry


/-- Definition:
An infrakernel is a crisp causal law if it is generated by some environments.
-/
def IsCrispCausalLaw (Λ : Policy A O → Credal (Destiny A O)) : Prop :=
  ∃ (E : Set (Environment A O)) (hne : E.Nonempty), Λ = infraKernelOfEnvironments E hne

/-- Proposition 1:
Any Crisp Causal Law is continuous.
-/
theorem continuous_of_CCL (Λ : Policy A O → Credal (Destiny A O))
    (h : IsCrispCausalLaw Λ) : Continuous Λ := by
  sorry


end InfraKernels

section MiniMax

variable {X : Type*}
variable [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/--
Infra-Bayesian Expectation:
Given a credal set `Θ` and a loss function `f`,
choose the worst (largest) expectation among `θ ∈ Θ`.
Note that `sSup` has junk value `0` for sets that are unbounded above.
The integral also has a junk value of `0` if not integrable.
These junk values are not a problem if `f` is measurable and bounded.
-/
noncomputable
def expIB (Θ : Credal X) (f : X → ℝ) : ℝ :=
  sSup ((fun θ => ∫ x, f x ∂θ.toMeasure) '' Θ.carrier)


/-- sanity check:
If `f` is bounded and measurable, then it is integrable for all probability measures.
-/
lemma exp_well_defined_of_measurable_bounded (f : X → ℝ)
    (hm : Measurable f)
    (hb1 : BddBelow (Set.range f)) (hb2 : BddAbove (Set.range f))
    (θ : Δ X) :
    Integrable f θ.toMeasure := by
  sorry

/-- sanity check:
If `f` is bounded from above, then `θ ↦ ∫ x, f x ∂θ` is bounded from above.
Thus, `sSup` in `expIB` is bounded above and does not have the `0` junk value
-/
lemma exp_values_bddAbove_of_bddAbove (Θ : Credal X) (f : X → ℝ)
    (hb : BddAbove (Set.range f)) :
    BddAbove ((fun θ => ∫ x, f x ∂θ.toMeasure) '' Θ.carrier) := by
  sorry

/-- sanity check:
If `f` is continuous, then the supremum in `expIB` is attained.
-/
lemma expIB_has_max (Θ : Credal X) (f : X → ℝ)
    (hf : Continuous f) :
    ∃ θ ∈ Θ.carrier, expIB Θ f = ∫ x, f x ∂θ.toMeasure := by
  sorry


/--
Lemma: `expIB` is continuous in `Θ`.
-/
lemma expIB_continuous_in_credal (f : X → ℝ) (hf : Continuous f) :
    Continuous (fun Θ => expIB Θ f) := by
  sorry

end MiniMax

section RLSetting

open IB_RL

variable {A O : Type*}
variable [Finite A] [Finite O]

/- we use discrete measurable and topological spaces on A and O -/
variable [MeasurableSpace A] [MeasurableSpace O]
variable [DiscreteMeasurableSpace A] [DiscreteMeasurableSpace O]
variable [TopologicalSpace A] [DiscreteTopology A]
variable [TopologicalSpace O] [DiscreteTopology O]

section InfraRegret

/- we use a continuous loss function -/
variable (L : Destiny A O → unitInterval)

/-- Definition: expected loss of a policy wrt a CCL -/
noncomputable
def expCCL (Λ : Policy A O → Credal (Destiny A O)) (π : Policy A O) : ℝ :=
  expIB (Λ π) (Subtype.val ∘ L)


/-- sanity check:  `expCCL` has values in `unitInterval` -/
lemma expCCL_mem_unitInterval (Λ : Policy A O → Credal (Destiny A O)) (π : Policy A O) :
    expCCL L Λ π ∈ unitInterval := by
  /- sanity check:  `expCCL` has values in `unitInterval` -/
  sorry


/-- Defining infra-regret.
The notation `⨅` describes the indexed infimum.
Again, using `EReal` because it is a `CompleteLattice` and the infimum
works without junk values in that case.
-/
noncomputable
def infraRegret (Λ : Policy A O → Credal (Destiny A O)) (π : Policy A O) : EReal :=
  (expCCL L Λ π : EReal)
  - ⨅ (π' : Policy A O), (expCCL L Λ π' : EReal)

/-- sanity check:  `infraRegret` has values between `0` and `1`. -/
lemma infraRegret_mem_unitInterval (Λ : Policy A O → Credal (Destiny A O)) (π : Policy A O) :
    infraRegret L Λ π ∈ {a : EReal | 0 ≤ a ∧ a ≤ 1} := by
  sorry


/-- Proposition 2:
The expected loss of a policy wrt a CCL is continuous in policies.
-/
lemma continuous_expCCL (Λ : Policy A O → Credal (Destiny A O))
    (hL : Continuous L) (hCCL : IsCrispCausalLaw Λ) :
    Continuous (expCCL L Λ) := by
  sorry

/-- Definition: Infra-Bayes optimal policy
-/
def IsIBOptimalPolicy {I : Type*}
    [MeasurableSpace I] [DiscreteMeasurableSpace I] (ζ : ProbabilityMeasure I)
    (Λ_fam : I → (Policy A O → Credal (Destiny A O))) : Policy A O → Prop :=
  fun π' => π' ∈ argminSet (fun π =>
    ∫ i, expCCL L (Λ_fam i) π ∂ζ.toMeasure
  )

/- Corollary 1:
Needs `Nonempty A`, otherwise policy space is empty.
 -/
theorem exists_ib_optimal_policy {I : Type*}
    [MeasurableSpace I] [DiscreteMeasurableSpace I] (ζ : ProbabilityMeasure I)
    [Nonempty A]
    (Λ_fam : I → (Policy A O → Credal (Destiny A O)))
    (hL : Continuous L) (hCCL : ∀ i, IsCrispCausalLaw (Λ_fam i)) :
    ∃ π', IsIBOptimalPolicy L ζ Λ_fam π' := by
  sorry

end InfraRegret

section Learnability

/- Loss function now has a `γ` parameter. -/
variable (L : discount → Destiny A O → unitInterval)

/-- Definition: a policy family learns class of CCLs -/
def LearnsCCLClass {I : Type*}
    (Λ_fam : I → Policy A O → Credal (Destiny A O))
    (π_fam : discount → Policy A O) : Prop :=
  ∀ (i : I), Filter.Tendsto
  (fun (γ : discount) => infraRegret (L γ) (Λ_fam i) (π_fam γ)) Filter.atTop (nhds 0)

def NonAnytimeLearnableIB {I : Type*}
    (Λ_fam : I → Policy A O → Credal (Destiny A O)) : Prop :=
  ∃ π_fam, LearnsCCLClass L Λ_fam π_fam


/- Proposition 3 -/
theorem ib_optimal_learns_class {I : Type*}
    [MeasurableSpace I] [DiscreteMeasurableSpace I] (ζ : ProbabilityMeasure I)
    (Λ_fam : I → Policy A O → Credal (Destiny A O))
    (h_learn : NonAnytimeLearnableIB L Λ_fam)
    (h_non_dog : NonDogmaticPrior ζ)
    (π_fam : discount → Policy A O)
    (h_ib_opt : ∀ γ, IsIBOptimalPolicy (L γ) ζ Λ_fam (π_fam γ)) :
    LearnsCCLClass L Λ_fam π_fam := by
  sorry



end Learnability

end RLSetting

end IB
