import Mathlib

set_option linter.style.header false

/-!
This file formalizes the definitions and propositions in
Articles/IB_RL.md

The main results are `exists_optimal_policy` and `bayes_optimal_learns_class`.

It also includes some additional sanity check lemmas.
-/



namespace IB_RL

open ProbabilityTheory MeasureTheory

section Basics

/- introduce actions and observations -/
variable (A O : Type*)

/-- histories are just lists of action-observation pairs.
Oldest appear first in the list.
-/
abbrev History := List (A × O)

/-- destinies are infinite sequences -/
abbrev Destiny := ℕ → (A × O)

/-- helper function. Oldest appear first in the list -/
def initialSegment (h : Destiny A O) (n : ℕ) :
    History A O := List.ofFn (fun (i: Fin n) => h i.1)

/-- Defining momentary loss as functions that map histories to `unitInterval`.
(Mathlib defines `unitInterval : Set ℝ` as `Set.Icc 0 1`)
-/
def MomentaryLoss := History A O → unitInterval

/-- the space for the discount parameter γ, encodes 0 ≤ γ < 1 -/
abbrev discount := Set.Ico (0 : ℝ) 1

-- for defining policies and environments we need (probability) measures on `A` and `O`
variable [MeasurableSpace A] [MeasurableSpace O]

/-- Policy and Environment take turns. The Policy starts.
Each get the full History as input.
-/
def Policy := History A O → ProbabilityMeasure A

def DeterministicPolicy := History A O → A

def Environment := History A O → A → ProbabilityMeasure O

end Basics

section trajMeas

variable {A O : Type*}

/-- defining the total loss on destinies, with γ as a discount factor.
We use `tsum` / `∑'` for the infinite sum.
This would output `0` for series that are not (unconditionally) summable
but this is not a problem for us, see `totalLoss_summable`.
For `t = 0`, the summand is `L` on the empty History
-/
noncomputable def totalLoss (L : MomentaryLoss A O)
    (γ : discount) : Destiny A O → ℝ :=
  fun h => (1 - γ.1) * ∑' (t : ℕ), γ.1 ^ t * L (initialSegment A O h t)

/-- sanity check: the infinite sum exists.
-/
lemma totalLoss_summable (L : MomentaryLoss A O) (γ : discount)
      (h : Destiny A O) : Summable
        (fun t => γ.1 ^ t * L (initialSegment A O h t)) := by
  sorry


/-- sanity check: totalLoss of constant c is c.
Verifies normalization property.
-/
lemma totalLoss_constant (c : unitInterval) (γ : discount)
    (h : Destiny A O) : totalLoss (fun _ => c) γ h = c := by
  sorry


/- We will assume that A and O are finite from now on. -/
variable [Finite A] [Finite O]
variable [MeasurableSpace A] [MeasurableSpace O]
variable [DiscreteMeasurableSpace A] [DiscreteMeasurableSpace O]

/-
Next, we want to define the probability measure on `Destiny A O` which
is induced by a Policy and an Environment.
We want to use `Kernel.trajMeasure` for this (Ionescu-Tulcea approach).
This requires multiple steps.
-/

/-- Define the probability measure for the next step on (A × O) after History `h`.
It is given as the composition product (`Measure.compProd` or `⊗ₘ` in mathlib)
of the Policy measure `π h` on `A` and the Environment `μ h`
interpreted as a `Kernel` of type `A → Measure O`.
-/
noncomputable
def measureAfterHist (π : Policy A O) (μ : Environment A O)
    (h : History A O) : Measure (A × O) :=
  (π h) ⊗ₘ { toFun := fun a => (μ h a).toMeasure, measurable' := Measurable.of_discrete }

/-- sanity check: the first marginal distribution is the Policy measure
-/
lemma measureAfterHist_marginal_fst (π : Policy A O)
    (μ : Environment A O)
    (h : History A O) :
    (measureAfterHist π μ h).fst = (π h).toMeasure := by
  sorry


/-- The resulting measure is a probability measure
-/
local
instance instProbMeasAfterHist (π : Policy A O) (μ : Environment A O) (h : History A O)
    : IsProbabilityMeasure (measureAfterHist π μ h) := by
  have hIMK : IsMarkovKernel
      { toFun := fun a => (μ h a).toMeasure, measurable' := Measurable.of_discrete } :=
    ⟨fun a => (μ h a).2⟩
  exact Measure.instIsProbabilityMeasureProdCompProdOfIsMarkovKernel


/-- helper function to translate from AO-pairs indexed by `Finset.Iic n` to histories
-/
def historyHelper (n : ℕ) : (Finset.Iic n → (A × O)) → History A O :=
  (fun g => List.ofFn
    (fun (i : Fin (n + 1)) => g ⟨i, Finset.mem_Iic.mpr (Fin.is_le i) ⟩))


/-- Definition of transition kernel after time step n.
Depends on previous History.
-/
noncomputable
def transitionKernel (π : Policy A O) (μ : Environment A O) (n : ℕ) :
    Kernel (Finset.Iic n → (A × O)) (A × O) where
      toFun := fun h => measureAfterHist π μ (historyHelper n h)
      measurable' := Measurable.of_discrete



/-- Required for `Kernel.trajMeasure`.
`IsMarkovKernel` means that all images of the kernels are probability measures.
-/
local instance instTransitionMarkovKernel (π : Policy A O) (μ : Environment A O)
    : ∀ n, IsMarkovKernel (transitionKernel π μ n) :=
  fun n => ⟨fun h => instProbMeasAfterHist π μ (historyHelper n h) ⟩

/-- Finally, define the trajectory measure on destinies using `Kernel.trajMeasure`
-/
noncomputable
def trajectoryMeasure (π : Policy A O) (μ : Environment A O) : Measure (Destiny A O) :=
  Kernel.trajMeasure (measureAfterHist π μ List.nil) (transitionKernel π μ)

noncomputable
def trajectoryProbMeasure (π : Policy A O)
    (μ : Environment A O) : ProbabilityMeasure (Destiny A O) :=
  ⟨trajectoryMeasure π μ, Kernel.instIsProbabilityMeasureForallTrajMeasure⟩

/-- sanity check: trajectoryMeasure does the correct thing
on all cylinder sets.
`List.take n` returns the first `n` elements as a new list.
`List.get t` returns element `t` of the list.
-/
lemma trajectoryMeasure_cylinder (π : Policy A O) (μ : Environment A O)
    (h : History A O) :
    (trajectoryMeasure π μ) {d | initialSegment A O d h.length = h}
    = ∏ (t : Fin h.length),
    π (h.take t.1) {(h.get t).1} *
    μ (h.take t.1) (h.get t).1 {(h.get t).2} := by
  sorry


/-- Define the expected total loss.
We will use the integral notation for the expectation wrt a probability measure.
The `∫` / `integral` in mathlib is based on the Bochner integral.
It defaults to `0` if the function is not integrable.
This is not a problem because of `expectedTotalLoss_integrable`
-/
noncomputable
def expectedTotalLoss (L : MomentaryLoss A O) (γ : discount)
    (π : Policy A O) (μ : Environment A O) : ℝ :=
  ∫ h, (totalLoss L γ h) ∂(trajectoryMeasure π μ)


/-- sanity check: the integral exists. -/
lemma expectedTotalLoss_integrable (L : MomentaryLoss A O) (γ : discount)
    (π : Policy A O) (μ : Environment A O)
    : Integrable (totalLoss L γ) (trajectoryMeasure π μ) := by
  sorry

/-- sanity check: the expected total loss is in the unit interval -/
lemma expectedTotalLoss_mem_unitInterval (L : MomentaryLoss A O) (γ : discount)
    (π : Policy A O) (μ : Environment A O)
    : expectedTotalLoss L γ π μ ∈ unitInterval := by
  sorry

/-- sanity check: if the momentary loss a constant `c`,
then the expected total loss is also `c`.
-/
lemma expectedTotalLoss_constant (c : unitInterval) (γ : discount)
    (π : Policy A O) (μ : Environment A O)
    : expectedTotalLoss (fun _ => c) γ π μ = c := by
  sorry




/-- Define the set version of argmin
(Function.argmin does something else).
-/
def argminSet {α : Type*} (f : α → ℝ) : Set α :=
  { a : α | ∀ b, f a ≤ f b}

/-- Define what it means to be an optimal Policy. -/
def IsOptimalPolicy (L : MomentaryLoss A O) (γ : discount)
    (μ : Environment A O) : Policy A O → Prop :=
  fun π' => π' ∈ argminSet (fun π => expectedTotalLoss L γ π μ)

/-- Define whether a `Policy` is equivalent to a `DeterministicPolicy`. -/
def IsPolicyDeterministic (π : Policy A O) : Prop :=
  ∃ (pi_det : DeterministicPolicy A O), ∀ h, π h {pi_det h} = 1

end trajMeas

section Regret

variable {A O : Type*}
variable [Finite A] [Finite O]
variable [MeasurableSpace A] [MeasurableSpace O]
variable [DiscreteMeasurableSpace A] [DiscreteMeasurableSpace O]

variable [Nonempty A] -- so that `Policy A O` is not empty

/-- Proposition 1:
An optimal Policy exists. It can be chosen to be deterministic.
-/
theorem exists_optimal_policy (L : MomentaryLoss A O) (γ : discount) (μ : Environment A O)
    : ∃ π', IsOptimalPolicy L γ μ π'
    ∧ IsPolicyDeterministic π' := by
  sorry


/-- Definition of the regret of a Policy.
Here, ⨅ is notation for the indexed infimum.
We use EReal because it is a CompleteLattice,
and the infimum works without default values there.
-/
noncomputable
def regret (L : MomentaryLoss A O) (γ : discount)
    (π : Policy A O) (μ : Environment A O) : EReal :=
  (expectedTotalLoss L γ π μ : EReal)
  - ⨅ (π': Policy A O), (expectedTotalLoss L γ π' μ : EReal)

/-- sanity check:
in EReal, the infimum over an empty type is `⊤` (+∞).
-/
lemma inf_over_empty_ereal_is_top {X : Type*} [IsEmpty X] (f : X → EReal) :
  ⨅ (x : X), f x = ⊤ := iInf_of_empty f

/-- sanity check:
The regret of an optimal Policy is 0.
-/
lemma regret_of_optimal (L : MomentaryLoss A O) (γ : discount)
    (π : Policy A O) (μ : Environment A O)
    (hopt : IsOptimalPolicy L γ μ π) :
    regret L γ π μ = 0 := by
  sorry


/-- sanity check: the regret is nonnegative. -/
lemma regret_nonneg (L : MomentaryLoss A O) (γ : discount)
    (π : Policy A O) (μ : Environment A O) : 0 ≤ regret L γ π μ := by
  sorry

/-- We say a family of policies (indexed by `γ`) learns a class of environments if
the regret goes to zero as `γ` approaches `1` from below.
On the `discount` set,
we can use `Filter.atTop` to describe that `γ` approaches `1` from below.
The class of environments is indexed by an index type `I`. -/
def LearnsEnvClass (L : MomentaryLoss A O) (I : Type*) (μ_fam : I → Environment A O)
      (π_fam : discount → Policy A O) : Prop :=
    ∀ (i : I), Filter.Tendsto
    (fun (γ : discount) => regret L γ (π_fam γ) (μ_fam i)) Filter.atTop (nhds 0)


/-- sanity check that Filter.atTop over discount behaves as expected:
The identity function converges to 1 over discount as `γ` approaches `1` from below.
-/
lemma discount_atTop :
    Filter.Tendsto (Subtype.val : discount → ℝ) Filter.atTop (nhds 1) := by
  sorry

/-- sanity check: Filter.atTop over discount is not the trivial filter -/
lemma discount_atTop_neBot : (Filter.atTop : Filter discount).NeBot := by
  sorry

/-- A class of environments is non-anytime learnable
if it can be learned by a family of policies. -/
def NonAnytimeLearnable (L : MomentaryLoss A O)
      (I : Type*) (μ_fam : I → Environment A O) : Prop :=
    ∃ π_fam, LearnsEnvClass L I μ_fam π_fam


/-- The article talks about a prior `ζ` over environments.
We will implement this using a family of environments `μ_fam` indexed
by an index type `I`, and then `ζ` is a probability measure `I`
(in the article, ζ gets applied to environments directly).
Again, the `∫` in mathlib returns 0 if the function is not integrable
(or not measurable).
See `bayes_integrand_integrable` below, which guarantees integrability
under assumptions. -/
def IsBayesOptimalPolicy (L : MomentaryLoss A O) (I : Type*)
    (μ_fam : I → Environment A O)
    [MeasurableSpace I] [DiscreteMeasurableSpace I] (ζ : ProbabilityMeasure I)
    (γ : discount) : Policy A O → Prop :=
  fun π' => π' ∈ argminSet (fun π =>
    ∫ i, expectedTotalLoss L γ π (μ_fam i) ∂(ζ.toMeasure)
  )


/-- sanity check: The integral in `IsBayesOptimalPolicy` is well-defined. -/
lemma bayes_integrand_integrable
    (L : MomentaryLoss A O) (I : Type*) (μ_fam : I → Environment A O)
    [MeasurableSpace I] [DiscreteMeasurableSpace I] (ζ : ProbabilityMeasure I)
    (γ : discount) (π : Policy A O) :
    Integrable (fun i => expectedTotalLoss L γ π (μ_fam i)) ζ.toMeasure := by
  sorry

/-- Definition: a non-dogmatic prior -/
def NonDogmaticPrior (I : Type*)
    [MeasurableSpace I] [DiscreteMeasurableSpace I]
    (ζ : ProbabilityMeasure I) : Prop :=
  ∀ (i : I), ζ {i} ≠ 0

/-- Proposition 2:
A bayes-optimal Policy learns an Environment class if the prior is non-dogmatic.
We can leave out the assumption that `I` is countable, because it is already implied by
`NonDogmaticPrior` and `DiscreteMeasurableSpace I`. -/
theorem bayes_optimal_learns_class
    (L : MomentaryLoss A O) (I : Type*) (μ_fam : I → Environment A O)
    [MeasurableSpace I] [DiscreteMeasurableSpace I] (ζ : ProbabilityMeasure I)
    (h_learnable : NonAnytimeLearnable L I μ_fam)
    (h_non_dog : NonDogmaticPrior I ζ)
    (π_fam : discount → Policy A O)
    (h_bayes_optimal : ∀ γ, IsBayesOptimalPolicy L I μ_fam ζ γ (π_fam γ))
    : LearnsEnvClass L I μ_fam π_fam := by
  sorry



end Regret

end IB_RL
