module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option linter.style.header false

/-!
# Lotteries on three candidates

`lot3 a b c` is the lottery `(a, b, c)` on the candidates `(x, y, z) = (0, 1, 2) : Fin 3`.
Used for the test lotteries of the certificate in `Counterexample.lean`.
-/

@[expose] public section

namespace MaxLotLot.Counterexample

open MeasureTheory

/-- The lottery `(a, b, c)` on the candidates `(x, y, z) = (0, 1, 2)`. -/
noncomputable def lot3 (a b c : NNReal) (h : a + b + c = 1) : ProbabilityMeasure (Fin 3) :=
  ⟨(a : ENNReal) • Measure.dirac 0 + (b : ENNReal) • Measure.dirac 1 +
    (c : ENNReal) • Measure.dirac 2, ⟨by simp [← ENNReal.coe_add, h]⟩⟩

@[simp] lemma lot3_real_zero (a b c : NNReal) (h : a + b + c = 1) :
    (lot3 a b c h : Measure (Fin 3)).real {0} = a := by
  simp [lot3, Measure.real]

@[simp] lemma lot3_real_one (a b c : NNReal) (h : a + b + c = 1) :
    (lot3 a b c h : Measure (Fin 3)).real {1} = b := by
  simp [lot3, Measure.real]

@[simp] lemma lot3_real_two (a b c : NNReal) (h : a + b + c = 1) :
    (lot3 a b c h : Measure (Fin 3)).real {2} = c := by
  simp [lot3, Measure.real]

/-- The three probabilities of a lottery on `Fin 3` sum to `1`. -/
lemma real_add_real_add_real (A : ProbabilityMeasure (Fin 3)) :
    (A : Measure (Fin 3)).real {0} + (A : Measure (Fin 3)).real {1} +
      (A : Measure (Fin 3)).real {2} = 1 := by
  rw [← Fin.sum_univ_three (fun i => (A : Measure (Fin 3)).real {i}), sum_measureReal_singleton]
  simp only [Finset.coe_univ, probReal_univ]

end MaxLotLot.Counterexample
