module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Order.CompletePartialOrder

set_option linter.style.header false

/-!
# Symmetric Nash games

The general symmetric two-player game with payoff `f`, and existence of Nash equilibria.

## Proof outline for `exists_nasheq_of_cc_of_zerosum`

Write `F b := {M | 0 ≤ ∫ a, f (a, b) ∂M}`; we show `⋂ b, F b` is nonempty.

1. `ProbabilityMeasure D` is compact (Mathlib's Prokhorov instance; needs `T2Space D`).
2. Each `F b` is closed (`isClosed_setOf_nonneg_integral`).
3. Finite intersections are nonempty (`exists_finite_witness`), via the finite symmetric
   zero-sum game (`exists_simplex_nonneg`), proved by Hahn–Banach separation.
4. Compactness gives `M ∈ ⋂ b, F b` (`exists_forall_nonneg_integral`).
5. Fubini turns `∀ b` into `∀ L` (`dominates_of_forall_nonneg`).
-/

@[expose] public section

namespace MaxLotLot

open ProbabilityTheory MeasureTheory

namespace SymNashGame

variable {D : Type*}
variable [MeasurableSpace D]
variable (f : D × D → ℝ)

def Dominates (A B : ProbabilityMeasure D) : Prop := ∫ x, f x ∂(A.prod B).1 ≥ 0

/-- sanity check -/
lemma integrable_of_meas_bounded (hmeas : Measurable f)
    (hbound : ∃ (cc : ℝ), ∀ x, abs (f x) < cc)
    (A B : ProbabilityMeasure D) :
    Integrable f (A.prod B).1 := by
  have : IsProbabilityMeasure (A.prod B).1 := (A.prod B).2
  obtain ⟨cc, hcc⟩ := hbound
  exact Integrable.of_bound hmeas.aestronglyMeasurable cc
    (Filter.Eventually.of_forall fun x => (hcc x).le)

def HasNashEq : Prop := ∃ M, ∀ L, Dominates f M L

/-! ### Step 3a: finite symmetric zero-sum games -/

section Finite

variable {ι : Type*} [Fintype ι]

/-- Antisymmetry kills the quadratic form `xᵀ g x`. -/
lemma sum_mul_mul_eq_zero (g : ι → ι → ℝ) (hg : ∀ i j, g i j + g j i = 0) (x : ι → ℝ) :
    ∑ i, ∑ j, x i * x j * g i j = 0 := by
  -- The sum equals its own negative: swap the summation order (`Finset.sum_comm`) and use `hg`.
  have h : ∑ i, ∑ j, x i * x j * g i j = -∑ i, ∑ j, x i * x j * g i j := by
    conv_rhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show g i j = -g j i by linarith [hg i j]]; ring
  linarith

/-- The standard simplex of mixed strategies, as a set of weight vectors. -/
def simplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

lemma convex_simplex : Convex ℝ (simplex ι) := by
  refine fun f hf g hg a b ha hb hab => ⟨fun x => ?_, ?_⟩
  · apply_rules [add_nonneg, mul_nonneg, hf.1, hg.1]
  · simp_rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hf.2, hg.2, mul_one, hab]

lemma isCompact_simplex : IsCompact (simplex ι) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · refine IsClosed.inter (s₁ := {x : ι → ℝ | ∀ i, 0 ≤ x i}) ?_
      (isClosed_eq (f := fun x : ι → ℝ => ∑ i, x i) (by fun_prop) continuous_const)
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun x hx => ?_⟩
    refine mem_closedBall_zero_iff.2 ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hx.1 i), ← hx.2]
    exact Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)

lemma single_mem_simplex [DecidableEq ι] (i : ι) : Pi.single i 1 ∈ simplex ι :=
  ⟨fun j => by by_cases h : j = i <;> simp [h], by simp only [Finset.sum_pi_single',
      Finset.mem_univ, ↓reduceIte]⟩

/-- A finite symmetric zero-sum game has a mixed strategy that weakly beats every pure one.

Proof sketch: let `T x := fun j ↦ ∑ i, x i * g i j`, `s := T '' simplex ι` (compact,
convex) and `t := {y | ∀ j, 0 ≤ y j}` (closed convex cone). If they were disjoint,
`geometric_hahn_banach_compact_closed` gives `ℓ, u, v` with `ℓ < u` on `s`, `u < v`,
`v < ℓ` on `t`. Since `0 ∈ t` and `t` is a cone: `v < 0` and `w j := ℓ (Pi.single j 1) ≥ 0`.
Also `w ≠ 0`, else `ℓ = 0 < u` on `s` contradicts `u < v < ℓ 0 = 0`. Normalising
`w / ∑ w ∈ simplex ι` gives `∑ j, w j * T w j < 0`, contradicting `sum_mul_mul_eq_zero`. -/
theorem exists_simplex_nonneg [Nonempty ι] (g : ι → ι → ℝ) (hg : ∀ i j, g i j + g j i = 0) :
    ∃ x ∈ simplex ι, ∀ j, 0 ≤ ∑ i, x i * g i j := by
  classical
  let T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := Matrix.vecMulLinear (g : Matrix ι ι ℝ)
  have hT : ∀ x j, T x j = ∑ i, x i * g i j := fun x j => rfl
  by_contra hne
  push Not at hne
  have hdisj : Disjoint (T '' simplex ι) {y | ∀ j, 0 ≤ y j} := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ hy
    obtain ⟨j, hj⟩ := hne x hx
    exact (hj.not_ge (hT x j ▸ hy j))
  have htc : Convex ℝ {y : ι → ℝ | ∀ j, 0 ≤ y j} := fun a ha b hb c d hc hd _ j => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hc (ha j)) (mul_nonneg hd (hb j))
  have htcl : IsClosed {y : ι → ℝ | ∀ j, 0 ≤ y j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
  obtain ⟨ℓ, u, v, hs, huv, ht⟩ := geometric_hahn_banach_compact_closed
    (convex_simplex.linear_image T)
    (isCompact_simplex.image (LinearMap.continuous_of_finiteDimensional T))
    htc htcl hdisj
  have hv : v < 0 := by simpa using ht 0 fun _ => le_rfl
  -- `ℓ` is nonnegative on the cone
  have hpos : ∀ y ∈ {y : ι → ℝ | ∀ j, 0 ≤ y j}, 0 ≤ ℓ y := by
    intro y hy
    by_contra hneg
    push Not at hneg
    have hc : 0 < v / ℓ y := div_pos_of_neg_of_neg hv hneg
    have := ht ((v / ℓ y) • y) fun j => by
      simpa using mul_nonneg hc.le (hy j)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at this
    exact lt_irrefl _ this
  set w : ι → ℝ := fun j => ℓ (fun k => if j = k then 1 else 0) with hw_def
  have hℓ : ∀ y, ℓ y = ∑ j, y j * w j := fun y => by
    simpa [smul_eq_mul] using ℓ.toLinearMap.pi_apply_eq_sum_univ y
  have hw : ∀ j, 0 ≤ w j := fun j => hpos _ fun k => by split_ifs <;> norm_num
  have hW : 0 < ∑ j, w j := by
    rcases (Finset.sum_nonneg fun j _ => hw j).lt_or_eq with h | h
    · exact h
    exfalso
    have h0 : ∀ j, w j = 0 := fun j =>
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hw j).1 h.symm j (Finset.mem_univ _)
    obtain ⟨x, hx⟩ : (simplex ι).Nonempty :=
      ⟨_, single_mem_simplex (Classical.arbitrary ι)⟩
    have := hs (T x) ⟨x, hx, rfl⟩
    rw [hℓ] at this
    simp only [h0, mul_zero, Finset.sum_const_zero] at this
    linarith
  set z : ι → ℝ := fun j => w j / ∑ k, w k
  have hz : z ∈ simplex ι := ⟨fun j => div_nonneg (hw j) hW.le, by
    simp only [z, ← Finset.sum_div, div_self hW.ne']⟩
  have hlt := hs (T z) ⟨z, hz, rfl⟩
  have hzero : ℓ (T z) = 0 := by
    have hwz : ∀ j, w j = (∑ k, w k) * z j := fun j => by
      exact (mul_div_cancel₀ _ hW.ne').symm
    generalize ∑ k, w k = W at hwz
    rw [hℓ]
    calc ∑ j, T z j * w j = ∑ i, ∑ j, W * (z i * z j * g i j) := by
          simp_rw [hT, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          conv_lhs => rw [hwz j]
          ring
      _ = 0 := by simp_rw [← Finset.mul_sum]; rw [sum_mul_mul_eq_zero g hg z, mul_zero]
  linarith

end Finite

/-! ### Steps 2–5: the continuous game -/

section Continuous

variable [TopologicalSpace D] [OpensMeasurableSpace D]

/-- Step 3b: transport a finite equilibrium on `u` to the measure `∑ i, x i • δ_i` on `D`.
Handle `u = ∅` separately with any Dirac measure; otherwise apply `exists_simplex_nonneg`
to `g i j := f (i, j)` on `↥u`, then evaluate integrals with `integral_finsetSum_measure`,
`integral_smul_measure` and `integral_dirac'` (measurability from
`Continuous.stronglyMeasurable`). -/
lemma exists_finite_witness [Nonempty D] {f : D × D → ℝ} (hcont : Continuous f)
    (hzerosum : ∀ a b, f (a, b) + f (b, a) = 0) (u : Finset D) :
    ∃ M : ProbabilityMeasure D, ∀ b ∈ u, 0 ≤ ∫ a, f (a, b) ∂M := by
  rcases u.eq_empty_or_nonempty with rfl | hu
  · obtain ⟨d⟩ := ‹Nonempty D›
    exact ⟨⟨Measure.dirac d, inferInstance⟩, by simp only [Finset.notMem_empty,
        ProbabilityMeasure.coe_mk, IsEmpty.forall_iff, implies_true]⟩
  have : Nonempty u := hu.to_subtype
  obtain ⟨x, hx, hxj⟩ := exists_simplex_nonneg (ι := u) (fun i j => f (i.1, j.1))
    fun i j => hzerosum _ _
  let μ : Measure D := ∑ i : u, ENNReal.ofReal (x i) • Measure.dirac i.1
  have hμ : IsProbabilityMeasure μ := ⟨by
    simp only [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hx.1 i, hx.2, ENNReal.ofReal_one]⟩
  refine ⟨⟨μ, hμ⟩, fun b hb => ?_⟩
  have hsm : StronglyMeasurable fun a => f (a, b) := (by fun_prop : Continuous _).stronglyMeasurable
  have key : ∫ a, f (a, b) ∂μ = ∑ i : u, x i * f (i.1, b) := by
    simp only [μ]
    rw [integral_finsetSum_measure fun i _ => (integrable_dirac' hsm enorm_lt_top
      ).smul_measure ENNReal.ofReal_ne_top]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_measure, integral_dirac' _ _ hsm, ENNReal.toReal_ofReal (hx.1 i),
      smul_eq_mul]
  change 0 ≤ ∫ a, f (a, b) ∂μ
  rw [key]
  exact hxj ⟨b, hb⟩

/-- Step 2: `M ↦ ∫ a, f (a, b) ∂M` is continuous, by
`ProbabilityMeasure.continuous_integral_boundedContinuousFunction` applied to
`BoundedContinuousFunction.mkOfCompact ⟨fun a ↦ f (a, b), by fun_prop⟩`. -/
lemma isClosed_setOf_nonneg_integral [CompactSpace D] {f : D × D → ℝ} (hcont : Continuous f)
    (b : D) : IsClosed {M : ProbabilityMeasure D | 0 ≤ ∫ a, f (a, b) ∂M} := by
  exact isClosed_le continuous_const
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (BoundedContinuousFunction.mkOfCompact ⟨fun a ↦ f (a, b), by fun_prop⟩))

/-- Step 4: finite intersection property in the compact space `ProbabilityMeasure D`. -/
lemma exists_forall_nonneg_integral [T2Space D] [CompactSpace D] [BorelSpace D] [Nonempty D]
    {f : D × D → ℝ} (hcont : Continuous f) (hzerosum : ∀ a b, f (a, b) + f (b, a) = 0) :
    ∃ M : ProbabilityMeasure D, ∀ b, 0 ≤ ∫ a, f (a, b) ∂M := by
  obtain ⟨M, -, hM⟩ := isCompact_univ.inter_iInter_nonempty
    (fun b => {M : ProbabilityMeasure D | 0 ≤ ∫ a, f (a, b) ∂M})
    (isClosed_setOf_nonneg_integral hcont) fun u => by
      obtain ⟨M, hM⟩ := exists_finite_witness hcont hzerosum u
      exact ⟨M, Set.mem_univ _, Set.mem_iInter₂.2 hM⟩
  exact ⟨M, Set.mem_iInter.1 hM⟩

end Continuous

/-- Step 5: if `f` is integrable, `integral_prod_symm` rewrites the integral as
`∫ b, ∫ a, f (a, b) ∂M ∂L ≥ 0` (`integral_nonneg`); otherwise it is `0` by `integral_undef`.
No measurability of `f` is needed, which matters since without second countability a
continuous `f` need not be measurable for the product σ-algebra. -/
lemma dominates_of_forall_nonneg {M : ProbabilityMeasure D}
    (hM : ∀ b, 0 ≤ ∫ a, f (a, b) ∂M) (L : ProbabilityMeasure D) : Dominates f M L := by
  unfold Dominates
  by_cases hi : Integrable f (M.prod L).1
  · have hi' : Integrable f ((M : Measure D).prod (L : Measure D)) := hi
    change 0 ≤ ∫ x, f x ∂(M : Measure D).prod (L : Measure D)
    rw [integral_prod_symm f hi']
    exact integral_nonneg fun b => hM b
  · rw [integral_undef hi]

theorem exists_nasheq_of_cc_of_zerosum
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [BorelSpace D] [Nonempty D]
    (hcont : Continuous f)
    (hzerosum : ∀ a b, f (a, b) + f (b, a) = 0) : HasNashEq f := by
  obtain ⟨M, hM⟩ := exists_forall_nonneg_integral hcont hzerosum
  exact ⟨M, dominates_of_forall_nonneg f hM⟩

end SymNashGame

end MaxLotLot
