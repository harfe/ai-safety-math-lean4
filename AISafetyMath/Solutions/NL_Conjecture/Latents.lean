
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import AISafetyMath.Solutions.NL_Conjecture.Setup

/-
Stochastic/deterministic natural-latent predicates and the exact-case theorem
`conjecture_exact_case`, built on top of `Setup.lean`.
-/

namespace NaturalLatents

open ProbabilityTheory MeasureTheory

section Latents

variable {X Y L : Type}
variable [Finite X] [Finite Y] [Finite L]

variable [MeasurableSpace X] [DiscreteMeasurableSpace X]
variable [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
variable [MeasurableSpace L] [DiscreteMeasurableSpace L]

noncomputable local instance instFintypeX : Fintype X := Fintype.ofFinite X
noncomputable local instance instFintypeY : Fintype Y := Fintype.ofFinite Y
noncomputable local instance instFintypeL : Fintype L := Fintype.ofFinite L

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

The mathematical content (construction of the deterministic latent as the
posterior-class of the stochastic latent, and the proof that it satisfies the
three exact conditions) is `conjecture_exact_case_aux` above, ported verbatim
from `prob_5.conjecture_exact_case`. What remains here is a purely mechanical
relabeling step: `conjecture_exact_case_aux` produces a deterministic latent
valued in `X` (not `Fin n`), so we must transport it along the canonical
equivalence `X ≃ Fin (Fintype.card X)` to match the `HasDeterministicNL`
existential, which is fixed to `Fin n`. That transport is `relabelA`, with
invariance of `forkApproxError`/`condEntropyNN`/`getBCProb` supplied by
`isDetLatentAux_relabelA` and `getBCProb_relabelA`. -/
theorem conjecture_exact_case (P : ProbabilityMeasure (X × Y)) :
    HasStochasticNL P 0 → HasDeterministicNL P 0 := by
  rintro ⟨n, Q, hnat, rfl⟩
  obtain ⟨hdet, hmarg⟩ := conjecture_exact_case_aux Q hnat
  -- `detLatent_distr Q : ProbabilityMeasure (X × X × Y)` is an exact deterministic
  -- natural latent with the right marginal; transport its latent coordinate from
  -- `X` to `Fin (Fintype.card X)` via `Fintype.equivFin X` to conclude.
  refine ⟨Fintype.card X, relabelA (Fintype.equivFin X) (detLatent_distr Q),
    isDetLatentAux_relabelA _ _ hdet, ?_⟩
  rw [getBCProb_relabelA, hmarg]

end Latents

end NaturalLatents
