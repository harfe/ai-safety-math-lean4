module

public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Separation.CompletelyRegular
public import AISafetyMath.Solutions.MaxLotLot.SymNashGame

set_option linter.style.header false

/-!
# Maximal lotteries over candidates `C`

`exists_max_lot`: for every electorate `V` there is a lottery `M` over candidates that dominates
every lottery. This is the symmetric zero-sum game on `C` (with the discrete topology) with payoff
`pairWin V a b - pairWin V b a`, solved by `SymNashGame.exists_nasheq_of_cc_of_zerosum`.
-/

@[expose] public section

namespace MaxLotLot

open ProbabilityTheory MeasureTheory

variable {C : Type} -- candidates
variable [Finite C] [MeasurableSpace C] [DiscreteMeasurableSpace C]

variable (V : ProbabilityMeasure (C → unitInterval))

namespace MaxLot

/-- The probability that a random voter prefers lottery `A` to lottery `B`, comparing a candidate
drawn from `A` with one drawn independently from `B`. -/
noncomputable
def prob_prefer (A B : ProbabilityMeasure C) : NNReal :=
  ((A.prod B).prod V) {x | x.2 x.1.1 > x.2 x.1.2 }

lemma prefer_measurable : MeasurableSet
    ({x | x.2 x.1.1 > x.2 x.1.2 } : Set ((C × C) × (C → unitInterval))) := by
  have hev : ∀ g : (C × C) × (C → unitInterval) → C, Measurable g →
      Measurable (fun x : (C × C) × (C → unitInterval) => x.2 (g x)) := by
    intro g hg
    have : Measurable (fun p : C × ((C × C) × (C → unitInterval)) => p.2.2 p.1) :=
      measurable_from_prod_countable_right (fun c => (measurable_pi_apply c).comp measurable_snd)
    exact this.comp (hg.prodMk measurable_id)
  exact measurableSet_lt (hev _ (by fun_prop)) (hev _ (by fun_prop))

def Dominates (A B : ProbabilityMeasure C) : Prop :=
  prob_prefer V A B ≥ prob_prefer V B A

/-- The probability that a random voter prefers candidate `a` to candidate `b`. -/
noncomputable def pairWin (a b : C) : ℝ :=
  ((V : Measure (C → unitInterval)) {v : C → unitInterval | v a > v b}).toReal

lemma prob_prefer_eq (A B : ProbabilityMeasure C) :
    (prob_prefer V A B : ℝ) =
      ∫ p, pairWin V p.1 p.2 ∂((A : Measure C).prod (B : Measure C)) := by
  unfold prob_prefer pairWin
  rw [ProbabilityMeasure.prod_apply _ _ _ (prefer_measurable)]
  rw [ENNReal.coe_toNNReal_eq_toReal, ProbabilityMeasure.toMeasure_prod,
    integral_toReal]
  · rfl
  · exact (Measurable.aemeasurable (by
      have : Measurable fun p : C × C =>
          (V : Measure (C → unitInterval)) {v | v p.1 > v p.2} := measurable_of_finite _
      exact this))
  · exact Filter.Eventually.of_forall fun p => measure_lt_top _ _

theorem exists_max_lot [Nonempty C] : ∃ M, ∀ L, Dominates V M L := by
  let : TopologicalSpace C := ⊥
  have : DiscreteTopology C := ⟨rfl⟩
  have := Fintype.ofFinite C
  have hnash := SymNashGame.exists_nasheq_of_cc_of_zerosum
    (fun p : C × C => pairWin V p.1 p.2 - pairWin V p.2 p.1)
    (continuous_of_discreteTopology) (fun a b => by ring)
  obtain ⟨M, hM⟩ := hnash
  refine ⟨M, fun L => ?_⟩
  have h := hM L
  unfold SymNashGame.Dominates at h
  have hsw : ∫ p, pairWin V p.2 p.1 ∂((M : Measure C).prod (L : Measure C)) =
      ∫ p, pairWin V p.1 p.2 ∂((L : Measure C).prod (M : Measure C)) :=
    (Measure.measurePreserving_swap (μ := (M : Measure C)) (ν := (L : Measure C))).integral_comp
      MeasurableEquiv.prodComm.measurableEmbedding (fun p : C × C => pairWin V p.1 p.2)
  have hsub : ∫ p, (pairWin V p.1 p.2 - pairWin V p.2 p.1)
      ∂((M : Measure C).prod (L : Measure C)) =
      ∫ p, pairWin V p.1 p.2 ∂((M : Measure C).prod (L : Measure C)) -
      ∫ p, pairWin V p.2 p.1 ∂((M : Measure C).prod (L : Measure C)) :=
    integral_sub (Integrable.of_finite) (Integrable.of_finite)
  have h' : (0 : ℝ) ≤ ∫ p, (pairWin V p.1 p.2 - pairWin V p.2 p.1)
      ∂((M : Measure C).prod (L : Measure C)) := h
  rw [hsub, hsw, ← prob_prefer_eq, ← prob_prefer_eq] at h'
  unfold Dominates
  exact_mod_cast sub_nonneg.mp h'

end MaxLot

end MaxLotLot
