module

public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.UniformSpace.Uniformizable
public import AISafetyMath.Solutions.MaxLotLot.Margin
public import AISafetyMath.Solutions.MaxLotLot.SymNashGame

/-!
# Finitely many lotteries: a maximal lottery-lottery exists

`exists_of_finite_lot`: restricted to a finite set `D` of lotteries, a maximal lottery-lottery
exists. This is the finite symmetric zero-sum game on `D` with payoff
`lotWin V (A, B) - lotWin V (B, A)`, solved by `SymNashGame.exists_forall_nonneg_integral`.
-/

@[expose] public section

namespace MaxLotLot

open ProbabilityTheory MeasureTheory

variable {C : Type} -- candidates
variable [Finite C] [MeasurableSpace C] [DiscreteMeasurableSpace C]

variable (V : ProbabilityMeasure (C → unitInterval))

section simplifications

lemma dominates_of_integral_nonneg (AA BB : ProbabilityMeasure (ProbabilityMeasure C))
    (h : 0 ≤ ∫ p, (lotWin V p - lotWin V (Prod.swap p)) ∂((AA : Measure _).prod (BB : Measure _))) :
    Dominates V AA BB := by
  have hm : Measurable (fun p : ProbabilityMeasure C × ProbabilityMeasure C =>
      lotWin V (Prod.swap p)) := (measurable_lotWin V).comp measurable_swap
  have hi : ∀ g : ProbabilityMeasure C × ProbabilityMeasure C → ℝ, Measurable g →
      (∀ p, |g p| ≤ 1) →
      Integrable g ((AA : Measure _).prod (BB : Measure _)) := fun g hg hb =>
    Integrable.of_bound hg.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun p => by simpa using hb p)
  have hsw : ∫ p, lotWin V (Prod.swap p) ∂((AA : Measure _).prod (BB : Measure _)) =
      ∫ p, lotWin V p ∂((BB : Measure _).prod (AA : Measure _)) :=
    (Measure.measurePreserving_swap (μ := (AA : Measure _)) (ν := (BB : Measure _))).integral_comp
      MeasurableEquiv.prodComm.measurableEmbedding (lotWin V)
  rw [integral_sub (hi _ (measurable_lotWin V) (abs_lotWin_le V))
    (hi _ hm fun p => abs_lotWin_le V _), hsw, ← lotWin_prod, ← lotWin_prod] at h
  unfold Dominates
  exact_mod_cast sub_nonneg.mp h

/-- Singletons are measurable in the Giry σ-algebra on lotteries over a finite candidate set. -/
instance instMeasurableSingletonClassLottery : MeasurableSingletonClass (ProbabilityMeasure C) :=
  ⟨fun A => by
    have : {A} = ⋂ c : C,
        {B : ProbabilityMeasure C | (B : Measure C) {c} = (A : Measure C) {c}} := by
      ext B
      simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
      refine ⟨fun h c => by rw [h], fun h => ?_⟩
      refine Subtype.ext (Measure.ext_iff_singleton.mpr fun c => h c)
    rw [this]
    exact MeasurableSet.iInter fun c =>
      ((Measure.measurable_coe (measurableSet_singleton c)).comp
        measurable_subtypeVal) (measurableSet_singleton _)⟩

/-- `D` with the discrete topology and σ-algebra, independent of the Giry structure. -/
def DT (D : Set (ProbabilityMeasure C)) : Type := D

instance (D : Set (ProbabilityMeasure C)) : TopologicalSpace (DT D) := ⊥
instance (D : Set (ProbabilityMeasure C)) : DiscreteTopology (DT D) := ⟨rfl⟩
instance (D : Set (ProbabilityMeasure C)) : MeasurableSpace (DT D) := ⊤
instance (D : Set (ProbabilityMeasure C)) : BorelSpace (DT D) :=
  ⟨le_antisymm (fun s _ => MeasurableSpace.measurableSet_generateFrom (isOpen_discrete s))
    le_top⟩

theorem exists_of_finite_lot (D : Set (ProbabilityMeasure C)) (hD : D.Finite) (hne : D.Nonempty) :
    ∃ MM, MM D = 1 ∧ ∀ LL, LL D = 1 → Dominates V MM LL := by
  have : Nonempty (DT D) := hne.to_subtype
  have : Finite (DT D) := hD.to_subtype
  let f : DT D × DT D → ℝ := fun p => lotWin V (p.1.val, p.2.val) - lotWin V (p.2.val, p.1.val)
  have hcont : Continuous f := continuous_of_discreteTopology
  obtain ⟨M, hM⟩ := SymNashGame.exists_forall_nonneg_integral hcont (fun a b => by simp [f])
  refine ⟨M.map (fun a : DT D => a.val), ?_, fun LL hLL => ?_⟩
  · have hmeasD : MeasurableSet D := hD.measurableSet
    have h1 : ((M.map (fun a : DT D => a.val) :
        ProbabilityMeasure (ProbabilityMeasure C)) : Measure _) D = 1 := by
      rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply measurable_from_top hmeasD]
      have : (fun a : DT D => a.val) ⁻¹' D = Set.univ := Set.eq_univ_of_forall fun a => a.property
      rw [this]; exact measure_univ
    simp only [ProbabilityMeasure.coeFn_def, h1]
    rfl
  · have hmeasD : MeasurableSet D := hD.measurableSet
    have hLLD : ∀ᵐ B ∂(LL : Measure _), B ∈ D := by
      have h1 : (LL : Measure _) D = 1 := by
        rw [ProbabilityMeasure.coeFn_def] at hLL
        exact (ENNReal.toNNReal_eq_one_iff _).1 hLL
      exact ae_iff.2 ((prob_compl_eq_zero_iff hmeasD).2 h1)
    apply dominates_of_integral_nonneg
    have hint : Integrable (fun p : ProbabilityMeasure C × ProbabilityMeasure C =>
        lotWin V p - lotWin V (Prod.swap p))
        ((M.map (fun a : DT D => a.val) :
          ProbabilityMeasure (ProbabilityMeasure C)).toMeasure.prod (LL : Measure _)) := by
      refine Integrable.of_bound
        (((measurable_lotWin V).sub
          ((measurable_lotWin V).comp measurable_swap)).aestronglyMeasurable) 2
        (Filter.Eventually.of_forall fun p => ?_)
      have := abs_lotWin_le V p
      have := abs_lotWin_le V (Prod.swap p)
      rw [Real.norm_eq_abs]
      calc _ ≤ |lotWin V p| + |lotWin V (Prod.swap p)| := abs_sub _ _
        _ ≤ 2 := by linarith
    rw [integral_prod_symm _ hint]
    refine integral_nonneg_of_ae (hLLD.mono fun B hB => ?_)
    have hmB : Measurable fun A : ProbabilityMeasure C =>
        lotWin V (A, B) - lotWin V (Prod.swap (A, B)) :=
      ((measurable_lotWin V).comp measurable_prodMk_right).sub
        ((measurable_lotWin V).comp (measurable_swap.comp measurable_prodMk_right))
    change 0 ≤ ∫ A, (lotWin V (A, B) - lotWin V (Prod.swap (A, B))) ∂_
    rw [ProbabilityMeasure.toMeasure_map, integral_map measurable_from_top.aemeasurable
      hmB.aestronglyMeasurable]
    exact hM ⟨B, hB⟩

end simplifications

end MaxLotLot
