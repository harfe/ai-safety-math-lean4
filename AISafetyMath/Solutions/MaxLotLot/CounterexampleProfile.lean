module

public import AISafetyMath.Solutions.MaxLotLot.Margin
public import AISafetyMath.Solutions.MaxLotLot.CounterexampleCertificate

/-!
# The electorate of the counterexample

`V` is the voter distribution of `Counterexample.lean`: three candidates
`(x, y, z) = (0, 1, 2) : Fin 3` and the four voters `u₁ = (1, 0, 0)`, `u₂ = (1, 0, 1)`,
`u₃ = (0, 1, ½)`, `u₄ = (0, 0, 1)` with weights `(10, 10, 10, 1) / 31`.

* `hasFiniteVoters_V`: `V` is finitely supported.
* `nwt_eq`: `31 · netWinToward V A B P` is `nwt` of `CounterexampleCertificate.lean`, evaluated
  at the probabilities of `A`, `B` and `P`.
-/

@[expose] public section

namespace MaxLotLot.Counterexample

open ProbabilityTheory MeasureTheory

/-- `½` as a point of the unit interval. -/
noncomputable def half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

/-- Voter `u₁ = (1, 0, 0)`. -/
def u₁ : Fin 3 → unitInterval := ![1, 0, 0]
/-- Voter `u₂ = (1, 0, 1)`. -/
def u₂ : Fin 3 → unitInterval := ![1, 0, 1]
/-- Voter `u₃ = (0, 1, ½)`. -/
noncomputable def u₃ : Fin 3 → unitInterval := ![0, 1, half]
/-- Voter `u₄ = (0, 0, 1)`. -/
def u₄ : Fin 3 → unitInterval := ![0, 0, 1]

/-- The unnormalized profile, with total mass `31`. -/
noncomputable def V₀ : Measure (Fin 3 → unitInterval) :=
  (10 : NNReal) • Measure.dirac u₁ + (10 : NNReal) • Measure.dirac u₂ +
    (10 : NNReal) • Measure.dirac u₃ + Measure.dirac u₄

lemma V₀_univ : V₀ Set.univ = 31 := by
  simp [V₀]
  norm_num

instance : IsProbabilityMeasure ((31 : ENNReal)⁻¹ • V₀) := by
  constructor
  rw [smul_apply, V₀_univ, smul_eq_mul, ENNReal.inv_mul_cancel] <;> norm_num

/-- The electorate: voters `u₁, u₂, u₃, u₄` with weights `(10, 10, 10, 1) / 31`. -/
noncomputable def V : ProbabilityMeasure (Fin 3 → unitInterval) :=
  ⟨(31 : ENNReal)⁻¹ • V₀, inferInstance⟩

/-- The indicator of `s` at `u`, as a real number. -/
noncomputable def ind (s : Set (Fin 3 → unitInterval)) (u : Fin 3 → unitInterval) : ℝ :=
  s.indicator 1 u

/-- `V` of any set: the weighted count of the voters in it. -/
lemma V_real (s : Set (Fin 3 → unitInterval)) :
    (V : Measure (Fin 3 → unitInterval)).real s =
      (10 * ind s u₁ + 10 * ind s u₂ + 10 * ind s u₃ + ind s u₄) / 31 := by
  change ((31 : ENNReal)⁻¹ • V₀).real s = _
  rw [measureReal_ennreal_smul_apply, V₀, measureReal_add_apply, measureReal_add_apply,
    measureReal_add_apply]
  simp [Measure.dirac_real_apply, ind]
  ring

lemma hasFiniteVoters_V : HasFiniteVoters V := by
  refine ⟨{u₁, u₂, u₃, u₄}, by simp only [Set.finite_insert, Set.finite_singleton], ?_⟩
  rw [← ProbabilityMeasure.toNNReal_measureReal_eq_coeFn, V_real]
  norm_num [ind]

/-- Net vote of one voter: `tw` of their expected utilities. -/
lemma ind_win_sub_ind_lose (A B P : ProbabilityMeasure (Fin 3)) (u : Fin 3 → unitInterval) :
    ind (winToward A B P) u - ind (loseToward A B P) u =
      tw (A[Subtype.val ∘ u]) (B[Subtype.val ∘ u]) (P[Subtype.val ∘ u]) := by
  simp only [ind, winToward, loseToward, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
  generalize A[Subtype.val ∘ u] = x
  generalize B[Subtype.val ∘ u] = y
  generalize P[Subtype.val ∘ u] = p
  unfold tw
  split_ifs <;> grind

/-- Expected utility on `Fin 3` as a finite sum. -/
lemma eu_eq (A : ProbabilityMeasure (Fin 3)) (u : Fin 3 → unitInterval) :
    A[Subtype.val ∘ u] = ∑ i, (A : Measure (Fin 3)).real {i} * (u i : ℝ) := by
  rw [integral_fintype Integrable.of_finite]
  rfl

/-- The expected utilities of the four voters: `a`, `a + c`, `b + c / 2`, `c`. -/
lemma eu_u₁ (A : ProbabilityMeasure (Fin 3)) :
    A[Subtype.val ∘ u₁] = (A : Measure (Fin 3)).real {0} := by
  simp only [eu_eq, Fin.sum_univ_three, u₁]
  simp only [Fin.isValue, ProbabilityMeasure.measureReal_eq_coe_coeFn, Matrix.cons_val_zero,
      Set.Icc.coe_one, mul_one, Matrix.cons_val_one, Set.Icc.coe_zero, mul_zero, add_zero,
      Matrix.cons_val]

lemma eu_u₂ (A : ProbabilityMeasure (Fin 3)) :
    A[Subtype.val ∘ u₂] = (A : Measure (Fin 3)).real {0} + (A : Measure (Fin 3)).real {2} := by
  simp only [eu_eq, Fin.sum_univ_three, u₂]
  simp only [Fin.isValue, ProbabilityMeasure.measureReal_eq_coe_coeFn, Matrix.cons_val_zero,
      Set.Icc.coe_one, mul_one, Matrix.cons_val_one, Set.Icc.coe_zero, mul_zero, add_zero,
      Matrix.cons_val]

lemma eu_u₃ (A : ProbabilityMeasure (Fin 3)) :
    A[Subtype.val ∘ u₃] = (A : Measure (Fin 3)).real {1} + (A : Measure (Fin 3)).real {2} / 2 := by
  simp only [eu_eq, Fin.sum_univ_three, u₃, half]
  simp only [Fin.isValue, ProbabilityMeasure.measureReal_eq_coe_coeFn, one_div,
      Matrix.cons_val_zero, Set.Icc.coe_zero, mul_zero, Matrix.cons_val_one, Set.Icc.coe_one,
      mul_one, zero_add, Matrix.cons_val, add_right_inj]
  ring

lemma eu_u₄ (A : ProbabilityMeasure (Fin 3)) :
    A[Subtype.val ∘ u₄] = (A : Measure (Fin 3)).real {2} := by
  simp only [eu_eq, Fin.sum_univ_three, u₄]
  simp only [Fin.isValue, ProbabilityMeasure.measureReal_eq_coe_coeFn, Matrix.cons_val_zero,
      Set.Icc.coe_zero, mul_zero, Matrix.cons_val_one, add_zero, Matrix.cons_val, Set.Icc.coe_one,
      mul_one, zero_add]

/-- `netWinToward` for `V`, in units of `1/31` of the vote. -/
theorem nwt_eq (A B P : ProbabilityMeasure (Fin 3)) :
    31 * netWinToward V A B P =
      nwt ((A : Measure (Fin 3)).real {0}) ((A : Measure (Fin 3)).real {1})
        ((A : Measure (Fin 3)).real {2}) ((B : Measure (Fin 3)).real {0})
        ((B : Measure (Fin 3)).real {1}) ((B : Measure (Fin 3)).real {2})
        ((P : Measure (Fin 3)).real {0}) ((P : Measure (Fin 3)).real {1})
        ((P : Measure (Fin 3)).real {2}) := by
  have h := fun u => ind_win_sub_ind_lose A B P u
  rw [netWinToward, V_real, V_real, nwt, ← eu_u₂ A, ← eu_u₂ B, ← eu_u₂ P, ← eu_u₃ A, ← eu_u₃ B,
    ← eu_u₃ P, ← eu_u₁ A, ← eu_u₁ B, ← eu_u₁ P, ← eu_u₄ A, ← eu_u₄ B, ← eu_u₄ P, ← h u₁, ← h u₂,
    ← h u₃, ← h u₄]
  ring

end MaxLotLot.Counterexample
