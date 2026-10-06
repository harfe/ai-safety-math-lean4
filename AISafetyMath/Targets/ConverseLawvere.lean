module
public import Mathlib

set_option linter.style.header false


/-!
This file formalizes the definitions and lemma and conjecture
related to the converse Lawvere problem

It also includes some additional sanity check lemmas.
-/

@[expose] public section


namespace ConverseLawvere

open Topology

section Basics

variable {X D : Type} [TopologicalSpace X] [TopologicalSpace D]
variable (f : X → X → D)

def ContinuousDiag : Prop := Continuous (fun x => f x x)

def JointlyContinuous : Prop := Continuous f.uncurry

def SurjectivityCondition {X D : Type} [TopologicalSpace X] [TopologicalSpace D]
    (f : X → X → D) : Prop := (∀ (h : C(X, D)), ∃ x, f x = h)

end Basics

/-- Definition:
We say that a topological space D has a Lawvere domain X
if there is a f that is jointly continuous and surjective onto continuous functions
-/
def HasLawvereDomain (D : Type) [TopologicalSpace D] : Prop :=
  ∃ (X : Type) (_ : TopologicalSpace X),
  ∃ (f : X → X → D),
  JointlyContinuous f ∧ SurjectivityCondition f

/-- Definition:
Same as `HasLawvereDomain` but we only require that the diagonal of f is continuous.
-/
def HasLawvereDomainDiag (D : Type) [TopologicalSpace D] : Prop :=
  ∃ (X : Type) (_ : TopologicalSpace X),
  ∃ (f : X → X → D),
  ContinuousDiag f ∧ SurjectivityCondition f

def HasFixedPoints (D : Type) [TopologicalSpace D] : Prop :=
 ∀ (f : C(D, D)), ∃ x, f x = x

/-- sanity check: -/
lemma diag_of_main (D : Type) [TopologicalSpace D] :
    HasLawvereDomain D → HasLawvereDomainDiag D := by
  sorry

theorem lawvereDomDiag_of_fp (D : Type) [TopologicalSpace D] :
    HasFixedPoints D → HasLawvereDomainDiag D := by
  sorry

/-- corollary -/
theorem lawvereDomDiag_unitInterval : HasLawvereDomainDiag unitInterval := by
  sorry

theorem lawvereDomDiag_iff_fp (D : Type) [TopologicalSpace D] :
    HasFixedPoints D ↔ HasLawvereDomainDiag D := by
  sorry

section MainConjecture

def MainConjecture : Prop := HasLawvereDomain unitInterval

theorem conjecture_solution : MainConjecture := by sorry
theorem conjecture_refutation : ¬ MainConjecture := by sorry


end MainConjecture

section Obstacles

theorem not_sigmaCompact (X : Type) [TopologicalSpace X]
    (f : X → X → unitInterval) (hf : JointlyContinuous f ∧ SurjectivityCondition f) :
    ¬ SigmaCompactSpace X := by
  sorry


end Obstacles

end ConverseLawvere
