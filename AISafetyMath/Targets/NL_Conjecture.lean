import Mathlib

set_option linter.style.header false

/-!
This file formalizes the definitions and lemma and conjecture in
Articles/NL_Conjecture.md.

The main conjecture is `main_conjecture`.

It also includes some additional sanity check lemmas.
-/

/- We do not use random variables for the formalization,
instead work with probability measures on the value space directly.
The disadvantage of working formally with random variables
is that one would need to make changes to the underlying measure space.
-/


namespace NaturalLatents

open ProbabilityTheory MeasureTheory

section Setup

/- Note that we use `Type` (universe 0) and not `Type*` here.
This makes things a bit easier in case of
`conjecture_refutation`.
Note that every finite type is equivalent to some `Fin n : Type`.
-/
variable {A B C : Type}
variable [Finite A] [Finite B] [Finite C]
variable [MeasurableSpace A] [DiscreteMeasurableSpace A]
variable [MeasurableSpace B] [DiscreteMeasurableSpace B]
variable [MeasurableSpace C] [DiscreteMeasurableSpace C]

/--
Defining the density of the factorized distribution with the fork
B ← A → C
-/
noncomputable
def forkDensity (P : Measure (A × B × C)) (x : A × B × C) : ENNReal
  := P {y | y.1 = x.1}
    * P[{y | y.2.1 = x.2.1} | {y | y.1 = x.1}]
    * P[{y | y.2.2 = x.2.2} | {y | y.1 = x.1}]

/-- Definition hole:
Define a probability distribution.
Later it will be checked in `ok_forkDistr` that it has density `forkDensity`.
-/
noncomputable
def forkDistr (P : ProbabilityMeasure (A × B × C)) : ProbabilityMeasure (A × B × C) :=
  sorry

/-- check that definition is correct
-/
lemma ok_forkDistr (P : ProbabilityMeasure (A × B × C)) (x : A × B × C) :
    (forkDistr P).toMeasure {x} = forkDensity P x := by
  sorry


/--
Defining the density of the factorized distribution with the chain
A → B → C
-/
noncomputable
def chainDensity (P : Measure (A × B × C)) (x : A × B × C) : ENNReal
  := P {y | y.1 = x.1}
    * P[{y | y.2.1 = x.2.1} | {y | y.1 = x.1}]
    * P[{y | y.2.2 = x.2.2} | {y | y.2.1 = x.2.1}]

/-- Definition hole:
Define a probability distribution.
Later it will be checked in `ok_chainDistr` that it has density `chainDensity`.
-/
noncomputable
def chainDistr (P : ProbabilityMeasure (A × B × C)) : ProbabilityMeasure (A × B × C) :=
  sorry

/-- check that definition is correct
-/
lemma ok_chainDistr (P : ProbabilityMeasure (A × B × C)) (x : A × B × C) :
    (chainDistr P).toMeasure {x} = chainDensity P x := by
  sorry


/- some permutation of components stuff -/

/-- swap first two components in a triple
-/
def swapAB : (A × B × C) → (B × A × C) := fun x => (x.2.1,x.1,x.2.2)

def swapBC : (A × B × C) → (A × C × B) := fun x => (x.1,x.2.2,x.2.1)

noncomputable
def swapABProb (P : ProbabilityMeasure (A × B × C)) : ProbabilityMeasure (B × A × C)
  := P.map (f := swapAB) (AEMeasurable.of_discrete)


noncomputable
def swapBCProb (P : ProbabilityMeasure (A × B × C)) : ProbabilityMeasure (A × C × B)
  := P.map (f := swapBC) (AEMeasurable.of_discrete)

noncomputable
def swapACProb (P : ProbabilityMeasure (A × B × C)) : ProbabilityMeasure (C × B × A) :=
  swapBCProb (swapABProb (swapBCProb P))

noncomputable
def getBCProb (P : ProbabilityMeasure (A × B × C)) : ProbabilityMeasure (B × C)
  := ⟨P.1.snd, by
    constructor
    simp only [ProbabilityMeasure.val_eq_to_measure, measure_univ]
  ⟩

noncomputable
def getACProb (P : ProbabilityMeasure (A × B × C)) : ProbabilityMeasure (A × C) :=
  getBCProb (swapABProb P)


noncomputable
def getABProb (P : ProbabilityMeasure (A × B × C)) : ProbabilityMeasure (A × B) :=
  getACProb (swapBCProb P)



/-- sanity check:
fork and chain are equivalent. should be basic conditional probability.
-/
lemma forkDensity_is_chainDensity (P : ProbabilityMeasure (A × B × C)) (x : A × B × C) :
    forkDensity P x = chainDensity (swapABProb P) (swapAB x) := by
  sorry


/-- KL-based approximation error for a fork.
Note that the output of `InformationTheory.klDiv` is an `ENNReal`.
-/
noncomputable
def forkApproxError (P : ProbabilityMeasure (A × B × C)) : ENNReal :=
  InformationTheory.klDiv P.toMeasure (forkDistr P).toMeasure


/-- KL-based approximation error for a chain.
-/
noncomputable
def chainApproxError (P : ProbabilityMeasure (A × B × C)) : ENNReal :=
  InformationTheory.klDiv P.toMeasure (chainDistr P).toMeasure

/-- conditional entropy: of first component, conditioned on the second.
Note that `P.1` is the same as `P.toMeasure`.
While `ENNReal.log 0` is `⊥`, this is not a problem here,
because `0 * ENNReal.log 0 = 0` in `EReal`, see example below.
The `tsum`/`∑'` can be converted to `∑` via `tsum_fintype` and `Fintype.ofFinite`.
-/
noncomputable
def condEntropy (P : ProbabilityMeasure (A × B)) : EReal :=
  - ∑' x, ↑(P.1 {x}) * ENNReal.log (P.1[{y | y.1 = x.1} | {y | y.2 = x.2}])


/- confirming that condEntropy is fine -/
example : (0 : EReal) * ENNReal.log 0 = 0 := by apply zero_mul


/-- sanity check: conditional entropy is nonnegative
-/
lemma condEntropy_nonneg (P : ProbabilityMeasure (A × B)) : condEntropy P ≥ 0 := by
  sorry

/-- sanity check: the conditional entropy is not infinite
-/
lemma condEntropy_lt_top (P : ProbabilityMeasure (A × B)) : condEntropy P < ⊤ := by
  sorry

/-- a non-negative version of `condEntropy`
that lives in `ENNReal`
-/
noncomputable
def condEntropyNN (P : ProbabilityMeasure (A × B)) : ENNReal := (condEntropy P).toENNReal


end Setup

section Latents

variable {X Y L : Type}
variable [Finite X] [Finite Y] [Finite L]

variable [MeasurableSpace X] [DiscreteMeasurableSpace X]
variable [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
variable [MeasurableSpace L] [DiscreteMeasurableSpace L]


/-- Defining an approximate stochastic natural latent:
If P is a probability measure over three finite types,
the latent is the first component.
-/
def IsStochasticNL (P : ProbabilityMeasure (L × X × Y)) (ε : ENNReal) : Prop :=
  ε ≥ forkApproxError P -- X ← L → Y
  ∧ ε ≥ chainApproxError (swapACProb P : ProbabilityMeasure (Y × X × L))  -- Y → X → L,
  ∧ ε ≥ chainApproxError (swapABProb (swapACProb P) : ProbabilityMeasure (X × Y × L))
    -- chain : X → Y → L,


/-- Defining an approximate deterministic natural latent.
-/
def IsDeterministicNL (P : ProbabilityMeasure (L × X × Y)) (ε : ENNReal) : Prop :=
  ε ≥ forkApproxError P -- X ← L → Y
  ∧ ε ≥ condEntropyNN (getABProb P) -- H(L|X)
  ∧ ε ≥ condEntropyNN (getACProb P) -- H(L|Y)


/-- Defining existence of an approximate stochastic natural latent
given a distribution on `X × Y`.
We use `Fin n` for `L` here. This is not a restriction,
as every finite `L` is equivalent to some `Fin n`
-/
def HasStochasticNL (P : ProbabilityMeasure (X × Y)) (ε : ENNReal) : Prop :=
  ∃ (n : ℕ) (Q : ProbabilityMeasure (Fin n × X × Y)),
  IsStochasticNL Q ε ∧ getBCProb Q = P

/-- Defining existence of an approximate deterministic natural latent
given a distribution on `X × Y`
-/
def HasDeterministicNL (P : ProbabilityMeasure (X × Y)) (ε : ENNReal) : Prop :=
  ∃ (n : ℕ) (Q : ProbabilityMeasure (Fin n × X × Y)),
  IsDeterministicNL Q ε ∧ getBCProb Q = P


/-- Theorem (exact case):
If there exists a stochastic natural latent with error 0,
then there exists a deterministic natural latent with error 0.
-/
theorem conjecture_exact_case (P : ProbabilityMeasure (X × Y)) :
    HasStochasticNL P 0 → HasDeterministicNL P 0 := by
  sorry

end Latents

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

/- PICK EXACTLY ONE of proof or disproof: -/

theorem conjecture_solution : MainConjecture := by sorry

theorem conjecture_refutation : ¬MainConjecture := by sorry

/- Not both can be true, otherwise we could conclude `False` from it. 
Both are currently present in the file
so that Comparator can be pointed at either of them.

example : False := conjecture_refutation conjecture_solution
-/

end Conjecture


end NaturalLatents

