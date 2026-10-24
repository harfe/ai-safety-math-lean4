module
public import Mathlib

set_option linter.style.header false

/-!
This file formalizes definitions and lemmas and conjectures
that have to do with maximal lottery lotteries.

This is work in progress and may contain some mistakes.
Comments and descriptions may be lacking.

Source: 
 - https://www.lesswrong.com/s/gnAaZtdwjDBBRpDmw/p/CAKZsP2v7SqqEExz9

The main conjecture is `main_conjecture`.

It also includes some additional sanity check lemmas.
-/

@[expose] public section

namespace MaxLotLot


open ProbabilityTheory MeasureTheory

namespace SymNashGame

/-! 
zero-sum nash games.
-/

variable {D : Type*}
variable [MeasurableSpace D]
variable (f : D × D → ℝ)


def Dominates (A B : ProbabilityMeasure D) : Prop := ∫ x, f x ∂(A.prod B).1 ≥ 0

/-- sanity check -/
lemma integrable_of_meas_bounded (hmeas : Measurable f)
    (hbound : ∃ (cc : ℝ), ∀ x, abs (f x) < cc)
    (A B : ProbabilityMeasure D) :
    Integrable f (A.prod B).1 := by
  sorry


def HasNashEq : Prop := ∃ M, ∀ L, Dominates f M L

theorem exists_nasheq_of_cc_of_zerosum
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [BorelSpace D] [Nonempty D]
    (hcont : Continuous f)
    (hzerosum : ∀ a b, f (a, b) + f (b, a) = 0) : HasNashEq f := by
  sorry


end SymNashGame


variable {C : Type} -- candidates
variable [Finite C] [MeasurableSpace C] [DiscreteMeasurableSpace C]

variable (V : ProbabilityMeasure (C → unitInterval))

namespace MaxLot

/-! For starters, we will consider Maximal Lotteries
(not Maximal Lottery-Lotteries).
-/

/--
probability that A is preferred over B
-/
noncomputable
def prob_prefer (A B : ProbabilityMeasure C) : NNReal :=
  ((A.prod B).prod V) {x | x.2 x.1.1 > x.2 x.1.2 }

lemma prefer_measurable : MeasurableSet
    ({x | x.2 x.1.1 > x.2 x.1.2 } : Set ((C × C) × (C → unitInterval))) := by
  sorry

def Dominates (A B : ProbabilityMeasure C) : Prop :=
  prob_prefer V A B ≥ prob_prefer V B A

/-- existence theorem -/
theorem exists_max_lot [Nonempty C] : ∃ M, ∀ L, Dominates V M L := by
  sorry

end MaxLot

/- We can do a very similar approach for Maximal Lottery-Lotteries now. -/

def prefer_set : Set ((ProbabilityMeasure C × ProbabilityMeasure C) × (C → unitInterval)) :=
  {x | x.1.1[Subtype.val ∘ x.2] > x.1.2[Subtype.val ∘ x.2]}

lemma prefer_measurable : MeasurableSet (prefer_set (C := C)) := by
  sorry

def Dominates (AA BB : ProbabilityMeasure (ProbabilityMeasure C)) : Prop :=
  ((AA.prod BB).prod V) prefer_set ≥ ((BB.prod AA).prod V) prefer_set


section mainConjecture

/-- Defining the main conjecture -/
def MainConjecture : Prop :=
  ∀ {C : Type} [Finite C] [MeasurableSpace C] [DiscreteMeasurableSpace C] [Nonempty C],
  ∀ (V : ProbabilityMeasure (C → unitInterval)),
  ∃ MM, ∀ LL, Dominates V MM LL

theorem solution : MainConjecture := by
  sorry

theorem refutation : ¬ MainConjecture := by
  sorry

end mainConjecture

section finiteVoters

def HasFiniteVoters : Prop := ∃ (S : Set (C → unitInterval)), S.Finite ∧ V S = 1

/-- Weakening of the main conjecture: 
The case of finitely many voters.
-/
def finiteVotersConjecture : Prop :=
  ∀ {C : Type} [Finite C] [MeasurableSpace C] [DiscreteMeasurableSpace C] [Nonempty C],
  ∀ (V : ProbabilityMeasure (C → unitInterval)),
  HasFiniteVoters V → ∃ MM, ∀ LL, Dominates V MM LL

theorem fv_solution : finiteVotersConjecture := by
  sorry

theorem fv_refutation : ¬ finiteVotersConjecture := by
  sorry

/-- Is finiteVotersConjecture enough for MainConjecture?
Maybe there exists an approximation argument.
-/
theorem mc_of_fv : finiteVotersConjecture → MainConjecture := by
  sorry


end finiteVoters

section simplifications

/-- known to be true:
If only finitely many candidate lotteries are allowed,
a solution exists. -/
theorem exists_of_finite_lot (D : Set (ProbabilityMeasure C))
    (hD : D.Finite) (hne : D.Nonempty) :
    ∃ MM, MM D = 1 ∧ ∀ LL, LL D = 1 → Dominates V MM LL := by
  sorry

end simplifications


end MaxLotLot
