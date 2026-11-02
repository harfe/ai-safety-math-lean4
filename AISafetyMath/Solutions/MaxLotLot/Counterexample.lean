module

public import AISafetyMath.Solutions.MaxLotLot.CounterexampleProfile
public import AISafetyMath.Solutions.MaxLotLot.CounterexampleLotteries

set_option linter.style.header false

/-!
# A finite electorate with no maximal lottery-lottery

The definitions are in `Lotteries.lean`. The counterexample has three candidates
`(x, y, z) = (0, 1, 2) : Fin 3` and four voters with utilities

| voter | `x` | `y` | `z` | weight |
|-------|-----|-----|-----|--------|
| `u₁`  | 1   | 0   | 0   | 10/31  |
| `u₂`  | 1   | 0   | 1   | 10/31  |
| `u₃`  | 0   | 1   | ½   | 10/31  |
| `u₄`  | 0   | 0   | 1   | 1/31   |

(`V` in `CounterexampleProfile.lean`). `not_finiteVotersConjecture`: `V` has no maximal
lottery-lottery. Since `V` is finitely supported, this refutes `finiteVotersConjecture`
(`fv_refutation`) and hence `MainConjecture` (`refutation`).

## Proof

Suppose `M` is maximal. Then `margin V M B ≥ 0` for every lottery `B`, and therefore
`∫ netWinToward V A B P dM(A) ≥ 0` for all lotteries `B` and `P`
(`integral_netWinToward_nonneg_of_forall` in `Margin.lean`): each test `(B, P)` compares a random
`A ∼ M` with `B` moved an infinitesimal step towards `P`. Take the five tests and weights

| `B`             | `P`             | weight |
|-----------------|-----------------|--------|
| `z`             | `z`             | 219    |
| `z`             | `(⅓, ⅔, 0)`     | 12     |
| `p = (½, 0, ½)` | `z`             | 165    |
| `c = (½, ½, 0)` | `(0, ¼, ¾)`     | 17     |
| `x`             | `z`             | 87     |

Their weighted sum `cert A` is `≤ -2/31` at **every** lottery `A` (`cert_le`), so its
`M`-integral is negative, while the weighted sum of the five nonnegative integrals is not.

## Files

* `CounterexampleCertificate.lean`: `certF_le`, the bound on the five tests as an inequality
  between real numbers.
* `CounterexampleLotteries.lean`: `lot3 a b c`, the lottery `(a, b, c)` on `Fin 3`.
* `CounterexampleProfile.lean`: the electorate `V`, and `nwt_eq`, which expresses
  `netWinToward V` through the real-number function of `CounterexampleCertificate.lean`.
* This file: the five tests and the contradiction.

Besides these files, the proof uses only Mathlib, `Lotteries.lean` and `Margin.lean`.
-/

@[expose] public section

namespace MaxLotLot.Counterexample

open MeasureTheory

/-- The vertex `x`. -/
noncomputable def xL : ProbabilityMeasure (Fin 3) := lot3 1 0 0 (by norm_num)
/-- The vertex `z`. -/
noncomputable def zL : ProbabilityMeasure (Fin 3) := lot3 0 0 1 (by norm_num)
/-- The midpoint `p` of the edge `xz`. -/
noncomputable def pL : ProbabilityMeasure (Fin 3) := lot3 (1 / 2) 0 (1 / 2) (by norm_num)
/-- The midpoint `c` of the edge `xy`. -/
noncomputable def cL : ProbabilityMeasure (Fin 3) := lot3 (1 / 2) (1 / 2) 0 (by norm_num)
/-- The target `(⅓, ⅔, 0)` of the test at `z`. -/
noncomputable def P₁ : ProbabilityMeasure (Fin 3) := lot3 (1 / 3) (2 / 3) 0 (by norm_num)
/-- The target `(0, ¼, ¾)` of the test at `c`. -/
noncomputable def P₂ : ProbabilityMeasure (Fin 3) := lot3 0 (1 / 4) (3 / 4) (by norm_num)

/-- The five-test certificate `Σ_j q_j netWinToward V A B_j P_j`. -/
noncomputable def cert (A : ProbabilityMeasure (Fin 3)) : ℝ :=
  219 * netWinToward V A zL zL + 12 * netWinToward V A zL P₁ + 165 * netWinToward V A pL zL +
    17 * netWinToward V A cL P₂ + 87 * netWinToward V A xL zL

lemma thirtyone_mul_cert (A : ProbabilityMeasure (Fin 3)) :
    31 * cert A = certF ((A : Measure (Fin 3)).real {0}) ((A : Measure (Fin 3)).real {1})
      ((A : Measure (Fin 3)).real {2}) := by
  have e : 31 * cert A = 219 * (31 * netWinToward V A zL zL) +
      12 * (31 * netWinToward V A zL P₁) + 165 * (31 * netWinToward V A pL zL) +
      17 * (31 * netWinToward V A cL P₂) + 87 * (31 * netWinToward V A xL zL) := by
    rw [cert]; ring
  rw [e, nwt_eq, nwt_eq, nwt_eq, nwt_eq, nwt_eq, certF]
  simp only [xL, zL, pL, cL, P₁, P₂, lot3_real_zero, lot3_real_one, lot3_real_two]
  norm_num

lemma cert_le (A : ProbabilityMeasure (Fin 3)) : cert A ≤ -2 / 31 := by
  have h := certF_le measureReal_nonneg measureReal_nonneg measureReal_nonneg
    (real_add_real_add_real A)
  rw [← thirtyone_mul_cert] at h
  linarith

lemma integrable_netWinToward (M : ProbabilityMeasure (ProbabilityMeasure (Fin 3)))
    (B P : ProbabilityMeasure (Fin 3)) :
    Integrable (fun A => netWinToward V A B P) (M : Measure (ProbabilityMeasure (Fin 3))) :=
  Integrable.of_bound (measurable_netWinToward V B P).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun A => by
      rw [Real.norm_eq_abs]; exact abs_netWinToward_le V A B P)

/-- `V` has no maximal lottery-lottery, so `finiteVotersConjecture` is false. -/
theorem not_finiteVotersConjecture : ¬ finiteVotersConjecture := by
  intro h
  obtain ⟨M, hM⟩ := h V hasFiniteVoters_V
  have hm : ∀ B, 0 ≤ margin V M B := fun B => margin_nonneg_of_dominates V (hM _)
  have hi := integral_netWinToward_nonneg_of_forall V hm
  have hI := integrable_netWinToward M
  have h1 := (hI zL zL).const_mul 219
  have h2 := (hI zL P₁).const_mul 12
  have h3 := (hI pL zL).const_mul 165
  have h4 := (hI cL P₂).const_mul 17
  have h5 := (hI xL zL).const_mul 87
  have e : ∫ A, cert A ∂(M : Measure (ProbabilityMeasure (Fin 3))) =
      219 * ∫ A, netWinToward V A zL zL ∂(M : Measure (ProbabilityMeasure (Fin 3))) +
      12 * ∫ A, netWinToward V A zL P₁ ∂(M : Measure (ProbabilityMeasure (Fin 3))) +
      165 * ∫ A, netWinToward V A pL zL ∂(M : Measure (ProbabilityMeasure (Fin 3))) +
      17 * ∫ A, netWinToward V A cL P₂ ∂(M : Measure (ProbabilityMeasure (Fin 3))) +
      87 * ∫ A, netWinToward V A xL zL ∂(M : Measure (ProbabilityMeasure (Fin 3))) := by
    simp only [cert]
    rw [integral_add, integral_add, integral_add, integral_add]
    · simp only [integral_const_mul]
    all_goals first | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h1.add h2 |
      exact (h1.add h2).add h3 | exact ((h1.add h2).add h3).add h4
  have hle : ∫ A, cert A ∂(M : Measure (ProbabilityMeasure (Fin 3))) ≤ -2 / 31 := by
    calc ∫ A, cert A ∂(M : Measure (ProbabilityMeasure (Fin 3)))
        ≤ ∫ _, (-2 / 31 : ℝ) ∂(M : Measure (ProbabilityMeasure (Fin 3))) :=
          integral_mono ((((h1.add h2).add h3).add h4).add h5) (integrable_const _) cert_le
      _ = -2 / 31 := by simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  linarith [hi zL zL, hi zL P₁, hi pL zL, hi cL P₂, hi xL zL]

end MaxLotLot.Counterexample

namespace MaxLotLot

theorem fv_refutation : ¬ finiteVotersConjecture := Counterexample.not_finiteVotersConjecture

theorem refutation : ¬ MainConjecture := fun h => fv_refutation fun V _ => h V

end MaxLotLot
