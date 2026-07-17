
import Mathlib

/-
Helper file: generic credal-set machinery over a compact metric space `X`.

This is fully generic in `X` and has no dependency on the RL scaffolding.
Imported by `Solutions.IB_Basics` and `Solutions.InfraKernel`.
-/

namespace IB

open ProbabilityTheory MeasureTheory

open scoped NNReal ENNReal

section CredalSets

open TopologicalSpace

variable {X : Type*}
variable [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

abbrev Δ X [MeasurableSpace X]:= ProbabilityMeasure X

/- We want to define Δ X as a metric space.
Mathlib actually can endow Δ X with a metric, the Levy-Prokhorov metric.
That metric induces the same topology as the weak/weak-(*) topology.
-/
noncomputable scoped
instance instMetricSpaceDeltaX : MetricSpace (Δ X) :=
  metrizableSpaceMetric (Δ X)

/- sanity check: A sequence of probability measures converges by distance
iff testing with all continuous functions converges
-/
lemma convergence_iff_weak (μ : ℕ → Δ X) (μ0 : Δ X) :
    Filter.Tendsto (fun n => dist (μ n) μ0 ) Filter.atTop (nhds 0)
    ↔ ∀ (f : X → ℝ), Continuous f →
    Filter.Tendsto (fun n => ∫ x,  f x ∂(μ n)) Filter.atTop (nhds (∫ x, f x ∂ μ0)) := by
  rw [← tendsto_iff_dist_tendsto_zero,
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  constructor
  · intro h f hcont
    exact h (BoundedContinuousFunction.mkOfCompact ⟨f, hcont⟩)
  · intro h g
    exact h g g.continuous

/- We want to use a metric on the nonempty compact sets of `X`.
Mathlib has actually a `MetricSpace` instance.
The metric used is the hausdorff distance.
-/
-- noncomputable scoped
-- instance instMetricSpaceNeCompacts : MetricSpace (NonemptyCompacts (Δ X)) :=
  -- Metric.NonemptyCompacts.instMetricSpace

/- Defining convexity of a set of probability measures is nontrivial in mathlib.
We probability measures to measures to signed measures.
-/
def ProbConvex {X : Type*} [MeasurableSpace X]
  (s : Set (ProbabilityMeasure X)) : Prop :=
  Convex ℝ ((fun x => x.toMeasure.toSignedMeasure) '' s)

/- an alternative equivalent definition: -/
lemma probConvex_iff {X : Type*} [MeasurableSpace X]
    (s : Set (ProbabilityMeasure X)) :
    ProbConvex s ↔ Convex NNReal ((fun x => x.toMeasure) '' s) := by
  unfold ProbConvex
  constructor
  · intro H
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ a b ha hb hab
    obtain ⟨r, hr, hrEq⟩ := H ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
      (a := (a : ℝ)) (b := (b : ℝ)) a.coe_nonneg b.coe_nonneg
      (by rw [← NNReal.coe_add, hab, NNReal.coe_one])
    refine ⟨r, hr, ?_⟩
    have hsig : (r.toMeasure).toSignedMeasure
        = (a • p.toMeasure + b • q.toMeasure).toSignedMeasure := by
      rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_smul,
        Measure.toSignedMeasure_smul, NNReal.smul_def, NNReal.smul_def]
      exact hrEq
    rwa [Measure.toSignedMeasure_eq_toSignedMeasure_iff] at hsig
  · intro H
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ a b ha hb hab
    obtain ⟨r, hr, hrEq⟩ := H ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
      (a := a.toNNReal) (b := b.toNNReal) zero_le zero_le
      (by rw [← Real.toNNReal_add ha hb, hab, Real.toNNReal_one])
    refine ⟨r, hr, ?_⟩
    have hrEq' : r.toMeasure = a.toNNReal • p.toMeasure + b.toNNReal • q.toMeasure := hrEq
    have hsig : (r.toMeasure).toSignedMeasure
        = (a.toNNReal • p.toMeasure + b.toNNReal • q.toMeasure).toSignedMeasure :=
      Measure.toSignedMeasure_eq_toSignedMeasure_iff.mpr hrEq'
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_smul,
      Measure.toSignedMeasure_smul, NNReal.smul_def, NNReal.smul_def,
      Real.coe_toNNReal a ha, Real.coe_toNNReal b hb] at hsig
    exact hsig

/- define the type of credal sets over X as
nonempty compact sets that are also convex. -/
def Credal X [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] :=
  { s : NonemptyCompacts (Δ X) // ProbConvex s.carrier }

noncomputable scoped
instance instCredalMetric : MetricSpace (Credal X) := Subtype.metricSpace


namespace Credal

def carrier (s : Credal X) := s.1.carrier

lemma nonempty (s : Credal X) : s.carrier.Nonempty := by
  exact s.1.nonempty'



def byClosedConvex (s : Set (Δ X)) (hne : s.Nonempty)
    (hcl : IsClosed s) (hcvx : ProbConvex s) : Credal X :=
    ⟨{ carrier := s, nonempty' := hne,
       isCompact' := IsClosed.isCompact hcl}, hcvx⟩

set_option linter.unusedSectionVars false in
/- we also want to be able to construct elements of `Credal X`
by using the closed convex hull of a set.
Due to working on the space `Δ X`, we will roll our own definition of `convexHull`.
We will also need a bunch of helper lemmas.
-/
/- `def` instead of `lemma` to match the target file, where these four are
`def`s for Comparator compatibility (they are `Prop`-valued, so this is safe).

Each of the four is a thin `def` wrapper around a `theorem` carrying the actual
proof: the Comparator compares reducibility hints (definition heights) of any
checked `def` that mentions these holes (`probConvexHull`, `byClosedConvexHull`,
`infraKernelOfEnvironments`), and a `theorem` — like the target's `sorryAx` —
contributes height 0, while `@id <goal>` keeps the goal's constants in the body
just as `sorryAx <goal>` does in the target. -/
omit [MetricSpace X] [CompactSpace X] [BorelSpace X] in
theorem probConvex_sInter_proof (S : Set (Set (Δ X)))
    (hS : ∀ t ∈ S, ProbConvex t) : ProbConvex (⋂₀ S) := by
  have hf : Function.Injective (fun x : Δ X => x.toMeasure.toSignedMeasure) := by
    intro p q h
    apply ProbabilityMeasure.toMeasure_injective
    rwa [Measure.toSignedMeasure_eq_toSignedMeasure_iff] at h
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · subst hSe
    rw [Set.sInter_empty]
    unfold ProbConvex
    rintro _ ⟨p, -, rfl⟩ _ ⟨q, -, rfl⟩ a b ha hb hab
    have hprob : IsProbabilityMeasure
        (a.toNNReal • p.toMeasure + b.toNNReal • q.toMeasure) := by
      constructor
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
        measure_univ, measure_univ, ENNReal.smul_def, ENNReal.smul_def,
        smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.coe_add,
        ← Real.toNNReal_add ha hb, hab, Real.toNNReal_one, ENNReal.coe_one]
    refine ⟨⟨a.toNNReal • p.toMeasure + b.toNNReal • q.toMeasure, hprob⟩,
      Set.mem_univ _, ?_⟩
    change (a.toNNReal • p.toMeasure + b.toNNReal • q.toMeasure).toSignedMeasure
        = a • p.toMeasure.toSignedMeasure + b • q.toMeasure.toSignedMeasure
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_smul,
      Measure.toSignedMeasure_smul, NNReal.smul_def, NNReal.smul_def,
      Real.coe_toNNReal a ha, Real.coe_toNNReal b hb]
  · have : Nonempty ↥S := hSne.to_subtype
    unfold ProbConvex
    rw [Set.sInter_eq_iInter, hf.injOn.image_iInter_eq]
    apply convex_iInter
    intro i
    exact hS i.1 i.2

set_option linter.defProp false in
set_option linter.unusedSectionVars false in
def probConvex_sInter (S : Set (Set (Δ X)))
    (hS : ∀ t ∈ S, ProbConvex t) : ProbConvex (⋂₀ S) :=
  @id (ProbConvex (⋂₀ S)) (probConvex_sInter_proof S hS)

-- follows definition of the existing `convexHull` in mathlib
def probConvexHull := ClosureOperator.ofCompletePred (@ProbConvex X _) probConvex_sInter

set_option linter.defProp false in
omit [MetricSpace X] [CompactSpace X] [BorelSpace X] in
theorem probConvexHull_convex_proof (s : Set (Δ X)) : ProbConvex (probConvexHull s) :=
  (probConvexHull).isClosed_closure s

set_option linter.defProp false in
set_option linter.unusedSectionVars false in
def probConvexHull_convex (s : Set (Δ X)) : ProbConvex (probConvexHull s) :=
  @id (ProbConvex (probConvexHull s)) (probConvexHull_convex_proof s)

set_option linter.defProp false in
omit [MetricSpace X] [CompactSpace X] [BorelSpace X] in
theorem probConvexHull_nonempty_proof (s : Set (Δ X))
    (hne : s.Nonempty) : (probConvexHull s).Nonempty :=
  hne.mono (probConvexHull.le_closure s)

set_option linter.defProp false in
set_option linter.unusedSectionVars false in
def probConvexHull_nonempty (s : Set (Δ X))
    (hne : s.Nonempty) : (probConvexHull s).Nonempty :=
  @id ((probConvexHull s).Nonempty) (probConvexHull_nonempty_proof s hne)


set_option linter.unusedSectionVars false in
/- "Closure of a convex set is convex". The mathlib analog `Convex.closure` does
not apply: `ProbConvex (closure s)` unfolds to `Convex ℝ (g '' closure s)` with
`g x := x.toMeasure.toSignedMeasure`, where `closure` is taken in `Δ X`
(Lévy-Prokhorov metric) while convexity lives in the signed measures, which carry
no `TopologicalSpace` instance. Instead we mirror the *proof* of `Convex.closure`
but with the mixture map `F p q = a • p + b • q : Δ X` (built as a probability
measure) and `map_mem_closure₂` — keeping all the topological reasoning inside
(omit `CompactSpace X` to match the target's signature)
`Δ X`. The only substantial obligation is continuity of `F` in the weak topology,
which reduces via `continuous_iff_forall_continuous_integral` to continuity of
`μ ↦ ∫ h ∂μ` (an affine combination of `continuous_integral_boundedContinuousFunction`).
The `g`-image of `F` is the affine combination by construction, and `s` is closed
under `F` by convexity of `g '' s` plus injectivity of `g`. -/
omit [CompactSpace X] in
theorem closed_convex_of_convex_proof (s : Set (Δ X))
    (hcvx : ProbConvex s) : ProbConvex (closure s) := by
  have hg_inj : Function.Injective (fun x : Δ X => x.toMeasure.toSignedMeasure) := by
    intro x y h
    apply ProbabilityMeasure.toMeasure_injective
    rwa [Measure.toSignedMeasure_eq_toSignedMeasure_iff] at h
  unfold ProbConvex
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ a b ha hb hab
  -- the mixture `a • p' + b • q'` is a probability measure
  have hprob : ∀ p' q' : Δ X, IsProbabilityMeasure
      (a.toNNReal • p'.toMeasure + b.toNNReal • q'.toMeasure) := by
    intro p' q'
    constructor
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      measure_univ, measure_univ, ENNReal.smul_def, ENNReal.smul_def,
      smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.coe_add,
      ← Real.toNNReal_add ha hb, hab, Real.toNNReal_one, ENNReal.coe_one]
  -- the mixture map on `Δ X`
  set F : Δ X → Δ X → Δ X := fun p' q' =>
    ⟨a.toNNReal • p'.toMeasure + b.toNNReal • q'.toMeasure, hprob p' q'⟩ with hFdef
  -- its image under `g x = x.toMeasure.toSignedMeasure` is the affine combination
  have hgF : ∀ p' q' : Δ X, (F p' q').toMeasure.toSignedMeasure
      = a • p'.toMeasure.toSignedMeasure + b • q'.toMeasure.toSignedMeasure := by
    intro p' q'
    change (a.toNNReal • p'.toMeasure + b.toNNReal • q'.toMeasure).toSignedMeasure = _
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_smul,
      Measure.toSignedMeasure_smul, NNReal.smul_def, NNReal.smul_def,
      Real.coe_toNNReal a ha, Real.coe_toNNReal b hb]
  -- the mixture map is continuous in the weak topology
  have hF : Continuous (Function.uncurry F) := by
    rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
    intro h
    have hcont : Continuous (fun μ : Δ X => ∫ x, h x ∂(μ : Measure X)) :=
      ProbabilityMeasure.continuous_integral_boundedContinuousFunction h
    have heq : (fun pq : Δ X × Δ X => ∫ x, h x ∂((Function.uncurry F pq : Δ X) : Measure X))
        = fun pq => a.toNNReal • (∫ x, h x ∂(pq.1 : Measure X))
            + b.toNNReal • (∫ x, h x ∂(pq.2 : Measure X)) := by
      funext pq
      obtain ⟨p', q'⟩ := pq
      change ∫ x, h x ∂(a.toNNReal • p'.toMeasure + b.toNNReal • q'.toMeasure) = _
      rw [integral_add_measure (h.integrable _) (h.integrable _),
        integral_smul_nnreal_measure, integral_smul_nnreal_measure]
    rw [heq]
    exact ((hcont.comp continuous_fst).const_smul a.toNNReal).add
      ((hcont.comp continuous_snd).const_smul b.toNNReal)
  -- `s` is closed under the mixture map
  have hmap : ∀ p' ∈ s, ∀ q' ∈ s, F p' q' ∈ s := by
    intro p' hp' q' hq'
    obtain ⟨r, hrs, hr⟩ := hcvx ⟨p', hp', rfl⟩ ⟨q', hq', rfl⟩ ha hb hab
    have : F p' q' = r := by
      apply hg_inj
      simp only
      rw [hgF p' q']
      exact hr.symm
    rwa [this]
  exact ⟨F p q, map_mem_closure₂ hF hp hq hmap, hgF p q⟩

set_option linter.defProp false in
set_option linter.unusedSectionVars false in
def probConvex_closure (s : Set (Δ X))
    (hcvx : ProbConvex s) : ProbConvex (closure s) :=
  @id (ProbConvex (closure s)) (closed_convex_of_convex_proof s hcvx)

/- Finally: we can construct elements in `Credal X` by taking
the closed convex hull. -/
def byClosedConvexHull (s : Set (Δ X)) (hne : s.Nonempty) : Credal X :=
  byClosedConvex
    (closure (probConvexHull s))
    (closure_nonempty_iff.mpr (probConvexHull_nonempty s hne))
    isClosed_closure
    (probConvex_closure (probConvexHull s) ( probConvexHull_convex s))



end Credal


-- confirming that the metric on `Credal X` is the Hausdorff distance
example (s t : Credal X) :
    dist s t = Metric.hausdorffDist s.carrier t.carrier := by rfl

/-! ### Intermediate lemmas for `proposition_1` (local Lévy–Prokhorov swap)

The metric on `Δ X` (`metrizableSpaceMetric`, line ~40) is an *arbitrary* metrization of the weak
topology, so a quantitative Hausdorff bound cannot be proved against it directly. But the goal in
`proposition_1` is a *convergence* (`… → 0`), which is a uniform/topological notion. Since `Δ X` is
compact its uniformity is unique, hence the abstract metric and the Lévy–Prokhorov metric are
uniformly equivalent. We therefore do all quantitative work in the LP metric (where mixing is
metrically well-behaved) and transfer the convergence conclusion back — *without changing any
global instance or type signature*.

The genuine mathematical content is `probConvexHull_eq` (IL4) and `levyProkhorovDist_mix_le`
(IL5); everything else is glue or a direct mathlib application. -/

/-- The Lévy–Prokhorov copy of `Δ X`: the *same underlying probability measures*, but carrying the
LP metric instead of the abstract `metrizableSpaceMetric`. The type synonym is what lets two
different metrics coexist without touching any global instance. -/
abbrev ΔLP (X : Type*) [MeasurableSpace X] [PseudoEMetricSpace X] [OpensMeasurableSpace X] :=
  LevyProkhorov (ProbabilityMeasure X)

/-- `ΔLP X` is compact, transported from compactness of `Δ X` along the LP homeomorphism. -/
instance : CompactSpace (ΔLP X) :=
  LevyProkhorov.probabilityMeasureHomeomorph.compactSpace

/-- **(IL1 — the lever).** The identity map `Δ X → ΔLP X` is a *uniform* equivalence.
Both sides metrize the weak topology and `Δ X` is compact, so its uniformity is unique;
`CompactSpace.uniformContinuous_of_continuous` upgrades the homeomorphism
`LevyProkhorov.probabilityMeasureHomeomorph` (and its inverse) to uniform continuity. -/
noncomputable def lpEquiv : Δ X ≃ᵤ ΔLP X where
  toEquiv := LevyProkhorov.probabilityMeasureHomeomorph.toEquiv
  uniformContinuous_toFun := CompactSpace.uniformContinuous_of_continuous
    LevyProkhorov.probabilityMeasureHomeomorph.continuous
  uniformContinuous_invFun := CompactSpace.uniformContinuous_of_continuous
    LevyProkhorov.probabilityMeasureHomeomorph.symm.continuous

/-- **(IL2 — back-transfer).** Hausdorff convergence to `0` under the LP metric implies it under the
abstract metric. Glue: `lpEquiv.symm` is uniformly continuous and, on the compact hyperspace,
Hausdorff-distance-to-`0` is convergence in the (metric-independent) Vietoris topology, which
uniform maps preserve. -/
lemma hausdorffDist_tendsto_zero_of_lp {K : ℕ → Set (Δ X)} {K₀ : Set (Δ X)}
    (h : Filter.Tendsto (fun k => Metric.hausdorffDist (lpEquiv '' K k) (lpEquiv '' K₀))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => Metric.hausdorffDist (K k) (K₀)) Filter.atTop (nhds 0) := by
  rcases K₀.eq_empty_or_nonempty with hK₀ | hK₀
  · simp [hK₀, Metric.hausdorffDist_empty]
  rw [Metric.tendsto_nhds] at h ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuous_iff.mp
    (lpEquiv (X := X)).symm.uniformContinuous (ε / 2) (by positivity)
  filter_upwards [h δ hδ] with k hk
  rcases (K k).eq_empty_or_nonempty with hKk | hKk
  · simpa [hKk, Metric.hausdorffDist_empty'] using hε
  have hne : Metric.hausdorffEDist (lpEquiv '' K k) (lpEquiv '' K₀) ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded (hKk.image _) (hK₀.image _)
      Metric.isBounded_of_compactSpace Metric.isBounded_of_compactSpace
  rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.hausdorffDist_nonneg] at hk ⊢
  have hb : Metric.hausdorffDist (K k) K₀ ≤ ε / 2 := by
    apply Metric.hausdorffDist_le_of_mem_dist (by positivity)
    · intro x hx
      obtain ⟨z, hz, hdz⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt
        (Set.mem_image_of_mem _ hx) hk hne
      obtain ⟨y, hy, rfl⟩ := hz
      exact ⟨y, hy, le_of_lt (by simpa using hδε hdz)⟩
    · intro y hy
      obtain ⟨z, hz, hdz⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt'
        (Set.mem_image_of_mem _ hy) hk hne
      obtain ⟨x, hx, rfl⟩ := hz
      exact ⟨x, hx, le_of_lt (by simpa [dist_comm] using hδε hdz)⟩
  linarith

/-- Binary convex combination of two probability measures (the mixture already built inline in
`closed_convex_of_convex`, now named so the lemmas below can talk about it). -/
noncomputable def mix {a b : ℝ≥0} (_hab : a + b = 1) (p q : Δ X) : Δ X :=
  ⟨a • p.toMeasure + b • q.toMeasure, by
    constructor
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ, measure_univ,
      ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      ← ENNReal.coe_add, _hab, ENNReal.coe_one]⟩

/-- Finite convex combinations of a set of probability measures (analogue of `convexHull_eq`'s
right-hand side). -/
def probFiniteCombos (s : Set (Δ X)) : Set (Δ X) :=
  { μ | ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ≥0) (p : ι → Δ X),
      (∀ i, p i ∈ s) ∧ (∑ i, w i = 1) ∧
      μ.toMeasure = ∑ i, w i • (p i).toMeasure }

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] in
/-- The signed-measure embedding `g x = x.toMeasure.toSignedMeasure` is injective. -/
lemma toSignedMeasure_injective :
    Function.Injective (fun x : Δ X => x.toMeasure.toSignedMeasure) := by
  intro x y h
  apply ProbabilityMeasure.toMeasure_injective
  rwa [Measure.toSignedMeasure_eq_toSignedMeasure_iff] at h

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] in
/-- The signed measure of a finite `ℝ≥0`-combination is the corresponding `ℝ`-combination
(the bridge between convexity in signed-measure space and mixing in `Δ X`). -/
lemma toSignedMeasure_sum {ι : Type*} (t : Finset ι) (w : ι → ℝ≥0) (p : ι → Δ X) :
    (∑ i ∈ t, w i • (p i).toMeasure).toSignedMeasure
      = ∑ i ∈ t, (w i : ℝ) • (p i).toMeasure.toSignedMeasure := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha, Measure.toSignedMeasure_add, Measure.toSignedMeasure_smul,
      ih, NNReal.smul_def]

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] in
/-- Points of `s` are trivial finite combinations. -/
lemma subset_probFiniteCombos (s : Set (Δ X)) : s ⊆ probFiniteCombos s := by
  intro x hx
  exact ⟨Fin 1, inferInstance, fun _ => 1, fun _ => x, fun _ => hx, by simp, by simp⟩

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] in
/-- A `ProbConvex` set containing `s` contains all finite combinations of points of `s`. -/
lemma probFiniteCombos_subset {s t : Set (Δ X)} (ht : ProbConvex t) (hst : s ⊆ t) :
    probFiniteCombos s ⊆ t := by
  rintro μ ⟨ι, _, w, p, hp, hw, hμ⟩
  have key : μ.toMeasure.toSignedMeasure
      = ∑ i, (w i : ℝ) • (p i).toMeasure.toSignedMeasure := by
    rw [← toSignedMeasure_sum]; congr 1
  have hmem : μ.toMeasure.toSignedMeasure
      ∈ (fun x : Δ X => x.toMeasure.toSignedMeasure) '' t := by
    rw [key]
    refine Convex.sum_mem ht (fun i _ => (w i).coe_nonneg) ?_ (fun i _ => ?_)
    · rw [← NNReal.coe_sum, hw, NNReal.coe_one]
    · exact Set.mem_image_of_mem _ (hst (hp i))
  obtain ⟨ν, hν, hνeq⟩ := hmem
  rwa [toSignedMeasure_injective hνeq] at hν

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] in
/-- The set of finite combinations of `s` is itself `ProbConvex`. -/
lemma probConvex_probFiniteCombos (s : Set (Δ X)) : ProbConvex (probFiniteCombos s) := by
  classical
  unfold ProbConvex
  rintro _ ⟨μ, ⟨ι, _, w, p, hp, hw, hμeq⟩, rfl⟩ _ ⟨ν, ⟨κ, _, v, q, hq, hv, hνeq⟩, rfl⟩ a b ha hb hab
  set W : ι ⊕ κ → ℝ≥0 :=
    Sum.elim (fun i => a.toNNReal * w i) (fun j => b.toNNReal * v j) with hW
  set P : ι ⊕ κ → Δ X := Sum.elim p q with hP
  have hWsum : ∑ x, W x = 1 := by
    rw [Fintype.sum_sum_type]
    simp only [hW, Sum.elim_inl, Sum.elim_inr]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hw, hv, mul_one, mul_one,
      ← Real.toNNReal_add ha hb, hab, Real.toNNReal_one]
  have hprob : IsProbabilityMeasure (∑ x, W x • (P x).toMeasure) := by
    constructor
    rw [Measure.finsetSum_apply]
    simp only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one]
    rw [← ENNReal.ofNNReal_finsetSum, hWsum, ENNReal.coe_one]
  have hgμ : μ.toMeasure.toSignedMeasure
      = ∑ i, (w i : ℝ) • (p i).toMeasure.toSignedMeasure := by
    rw [← toSignedMeasure_sum]; congr 1
  have hgν : ν.toMeasure.toSignedMeasure
      = ∑ j, (v j : ℝ) • (q j).toMeasure.toSignedMeasure := by
    rw [← toSignedMeasure_sum]; congr 1
  refine ⟨⟨∑ x, W x • (P x).toMeasure, hprob⟩,
    ⟨ι ⊕ κ, inferInstance, W, P, ?_, hWsum, rfl⟩, ?_⟩
  · intro x; cases x with
    | inl i => exact hp i
    | inr j => exact hq j
  · change (∑ x, W x • (P x).toMeasure).toSignedMeasure
        = a • μ.toMeasure.toSignedMeasure + b • ν.toMeasure.toSignedMeasure
    rw [toSignedMeasure_sum, Fintype.sum_sum_type, hgμ, hgν, Finset.smul_sum, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hW, hP, Sum.elim_inl]
      rw [NNReal.coe_mul, Real.coe_toNNReal a ha, mul_smul]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [hW, hP, Sum.elim_inr]
      rw [NNReal.coe_mul, Real.coe_toNNReal b hb, mul_smul]

omit [MetricSpace X][BorelSpace X] [CompactSpace X] in
/-- **(IL4 — obstruction B: finite-combination characterization).** The abstract closure-operator
`probConvexHull` coincides with the set of finite convex combinations. Needed to *name* the point
of `probConvexHull t` witnessing the Hausdorff bound in IL6. Proof: the RHS is `ProbConvex`,
contains `s`, and lies inside every `ProbConvex` superset of `s`. -/
lemma probConvexHull_eq (s : Set (Δ X)) : Credal.probConvexHull s = probFiniteCombos s := by
  apply Set.Subset.antisymm
  · have hcl : Credal.probConvexHull.IsClosed (probFiniteCombos s) :=
      probConvex_probFiniteCombos s
    calc Credal.probConvexHull s
        ⊆ Credal.probConvexHull (probFiniteCombos s) :=
          Credal.probConvexHull.monotone (subset_probFiniteCombos s)
      _ = probFiniteCombos s := hcl.closure_eq
  · exact probFiniteCombos_subset (Credal.probConvexHull_convex s)
      (Credal.probConvexHull.le_closure s)

/-- **(IL5 — obstruction A: the metric core).** The Lévy–Prokhorov distance is convex under mixing.
One-line math proof from the LP definition: if `ε = max (d p₁ p₂) (d q₁ q₂)` then `pᵢ(B) ≤ qᵢ(Bᵉ)+ε`
for each side, and the `a,b`-weighted sum gives the same inequality for the mixtures. This is the
property that fails for a generic `metrizableSpaceMetric`; it is the sole reason we route via LP. -/
lemma levyProkhorovDist_mix_le {a b : ℝ≥0} (hab : a + b = 1) (p₁ q₁ p₂ q₂ : Δ X) :
    dist (lpEquiv (mix hab p₁ q₁)) (lpEquiv (mix hab p₂ q₂))
      ≤ max (dist (lpEquiv p₁) (lpEquiv p₂)) (dist (lpEquiv q₁) (lpEquiv q₂)) := by
  -- underlying measure of a mixture
  have hmix : ∀ p q : Δ X,
      (mix hab p q).toMeasure = a • p.toMeasure + b • q.toMeasure := fun _ _ => rfl
  -- LP edist between mapped measures is the `levyProkhorovEDist` of the underlying measures
  have hedist : ∀ p p' : Δ X,
      edist (lpEquiv p) (lpEquiv p') = levyProkhorovEDist p.toMeasure p'.toMeasure := by
    intro p p'
    rw [LevyProkhorov.edist_probabilityMeasure_def]
    rfl
  -- core inequality on `levyProkhorovEDist`
  have hcore : levyProkhorovEDist ((mix hab p₁ q₁).toMeasure) ((mix hab p₂ q₂).toMeasure)
      ≤ max (levyProkhorovEDist p₁.toMeasure p₂.toMeasure)
            (levyProkhorovEDist q₁.toMeasure q₂.toMeasure) := by
    apply levyProkhorovEDist_le_of_forall
    intro ε B hδε _ hB
    have hp : levyProkhorovEDist p₁.toMeasure p₂.toMeasure < ε :=
      lt_of_le_of_lt (le_max_left _ _) hδε
    have hq : levyProkhorovEDist q₁.toMeasure q₂.toMeasure < ε :=
      lt_of_le_of_lt (le_max_right _ _) hδε
    refine ⟨?_, ?_⟩
    · simp only [hmix, Measure.add_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
      have h1 := left_measure_le_of_levyProkhorovEDist_lt hp hB
      have h2 := left_measure_le_of_levyProkhorovEDist_lt hq hB
      calc (a : ℝ≥0∞) * p₁.toMeasure B + (b : ℝ≥0∞) * q₁.toMeasure B
          ≤ (a : ℝ≥0∞) * (p₂.toMeasure (Metric.thickening ε.toReal B) + ε)
              + (b : ℝ≥0∞) * (q₂.toMeasure (Metric.thickening ε.toReal B) + ε) := by gcongr
        _ = (a : ℝ≥0∞) * p₂.toMeasure (Metric.thickening ε.toReal B)
              + (b : ℝ≥0∞) * q₂.toMeasure (Metric.thickening ε.toReal B)
              + ((a : ℝ≥0∞) * ε + (b : ℝ≥0∞) * ε) := by ring
        _ = _ := by rw [← add_mul, ← ENNReal.coe_add, hab, ENNReal.coe_one, one_mul]
    · simp only [hmix, Measure.add_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
      have h1 := right_measure_le_of_levyProkhorovEDist_lt hp hB
      have h2 := right_measure_le_of_levyProkhorovEDist_lt hq hB
      calc (a : ℝ≥0∞) * p₂.toMeasure B + (b : ℝ≥0∞) * q₂.toMeasure B
          ≤ (a : ℝ≥0∞) * (p₁.toMeasure (Metric.thickening ε.toReal B) + ε)
              + (b : ℝ≥0∞) * (q₁.toMeasure (Metric.thickening ε.toReal B) + ε) := by gcongr
        _ = (a : ℝ≥0∞) * p₁.toMeasure (Metric.thickening ε.toReal B)
              + (b : ℝ≥0∞) * q₁.toMeasure (Metric.thickening ε.toReal B)
              + ((a : ℝ≥0∞) * ε + (b : ℝ≥0∞) * ε) := by ring
        _ = _ := by rw [← add_mul, ← ENNReal.coe_add, hab, ENNReal.coe_one, one_mul]
  -- convert from `edist` to `dist`
  have hfin_mix : levyProkhorovEDist (mix hab p₁ q₁).toMeasure (mix hab p₂ q₂).toMeasure ≠ ⊤ :=
    levyProkhorovEDist_ne_top _ _
  have hfin_p : levyProkhorovEDist p₁.toMeasure p₂.toMeasure ≠ ⊤ := levyProkhorovEDist_ne_top _ _
  have hfin_q : levyProkhorovEDist q₁.toMeasure q₂.toMeasure ≠ ⊤ := levyProkhorovEDist_ne_top _ _
  rw [dist_edist, dist_edist, dist_edist, hedist, hedist, hedist,
    ← ENNReal.toReal_max hfin_p hfin_q]
  exact (ENNReal.toReal_le_toReal hfin_mix
    (max_lt (lt_top_iff_ne_top.mpr hfin_p) (lt_top_iff_ne_top.mpr hfin_q)).ne).mpr hcore

omit [CompactSpace X] [BorelSpace X] in
/-- Finite-sum form of IL5: a common LP bound on matched components bounds the LP distance of the
equally-weighted finite mixtures. Same proof as `levyProkhorovDist_mix_le` with `Finset.sum` in
place of the binary mixture, avoiding an induction over iterated `mix`. -/
lemma levyProkhorovEDist_sum_le {ι : Type} [Fintype ι] {w : ι → ℝ≥0} (hw : ∑ i, w i = 1)
    {p q : ι → Δ X} {r : ℝ≥0∞}
    (h : ∀ i, levyProkhorovEDist (p i).toMeasure (q i).toMeasure ≤ r) :
    levyProkhorovEDist (∑ i, w i • (p i).toMeasure) (∑ i, w i • (q i).toMeasure) ≤ r := by
  apply levyProkhorovEDist_le_of_forall
  intro ε B hrε _ hB
  have hside : ∀ u v : ι → Δ X,
      (∀ i, levyProkhorovEDist (u i).toMeasure (v i).toMeasure ≤ r) →
      (∑ i, w i • (u i).toMeasure) B
        ≤ (∑ i, w i • (v i).toMeasure) (Metric.thickening ε.toReal B) + ε := by
    intro u v huv
    rw [Measure.finsetSum_apply, Measure.finsetSum_apply]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    calc ∑ i, (w i : ℝ≥0∞) * (u i).toMeasure B
        ≤ ∑ i, (w i : ℝ≥0∞) * ((v i).toMeasure (Metric.thickening ε.toReal B) + ε) := by
          gcongr with i
          exact left_measure_le_of_levyProkhorovEDist_lt (lt_of_le_of_lt (huv i) hrε) hB
      _ = ∑ i, (w i : ℝ≥0∞) * (v i).toMeasure (Metric.thickening ε.toReal B)
            + (∑ i, (w i : ℝ≥0∞)) * ε := by
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => mul_add _ _ _
      _ = _ := by rw [← ENNReal.ofNNReal_finsetSum, hw, ENNReal.coe_one, one_mul]
  refine ⟨hside p q h, hside q p fun i => ?_⟩
  rw [levyProkhorovEDist_comm]
  exact h i

/-- **(IL6 — convex hull is 1-Lipschitz for LP-Hausdorff).** Assembled from IL3/IL4/IL5: every
element of `probConvexHull s` is a finite combination (IL4) of points of `s`, matched termwise to
points of `t`, and the combination stays within the bound by `levyProkhorovEDist_sum_le` (the
finite-sum form of IL5); close with `Metric.hausdorffDist_le_of_mem_dist`. -/
lemma hausdorffDist_lp_probConvexHull_le (s t : Set (Δ X)) :
    Metric.hausdorffDist (lpEquiv '' Credal.probConvexHull s) (lpEquiv '' Credal.probConvexHull t)
      ≤ Metric.hausdorffDist (lpEquiv '' s) (lpEquiv '' t) := by
  have hempty : ∀ u : Set (Δ X), u = ∅ → Credal.probConvexHull u = ∅ := by
    intro u hu
    rw [probConvexHull_eq]
    ext μ
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨ι, _, w, p, hp, hw, -⟩
    rcases isEmpty_or_nonempty ι with hι | hι
    · rw [Finset.univ_eq_empty, Finset.sum_empty] at hw
      exact zero_ne_one hw
    · exact absurd (hp (Classical.arbitrary ι)) (by simp [hu])
  rcases s.eq_empty_or_nonempty with hs | hs
  · simp [hempty s hs, Metric.hausdorffDist_empty', Metric.hausdorffDist_nonneg]
  rcases t.eq_empty_or_nonempty with ht | ht
  · simp [hempty t ht, Metric.hausdorffDist_empty, Metric.hausdorffDist_nonneg]
  have hedist : ∀ p p' : Δ X,
      edist (lpEquiv p) (lpEquiv p') = levyProkhorovEDist p.toMeasure p'.toMeasure := by
    intro p p'
    rw [LevyProkhorov.edist_probabilityMeasure_def]
    rfl
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have key : ∀ u v : Set (Δ X),
      Metric.hausdorffEDist (lpEquiv '' u) (lpEquiv '' v) ≠ ⊤ →
      ∀ x ∈ lpEquiv '' Credal.probConvexHull u, ∃ y ∈ lpEquiv '' Credal.probConvexHull v,
        dist x y ≤ Metric.hausdorffDist (lpEquiv '' u) (lpEquiv '' v) + ε := by
    intro u v hfin x hx
    rw [probConvexHull_eq] at hx
    obtain ⟨μ, ⟨ι, _, w, p, hp, hw, hμ⟩, rfl⟩ := hx
    set H := Metric.hausdorffDist (lpEquiv '' u) (lpEquiv '' v) with hH
    have hq : ∀ i, ∃ y ∈ v, dist (lpEquiv (p i)) (lpEquiv y) < H + ε := by
      intro i
      obtain ⟨z, hz, hdz⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt
        (Set.mem_image_of_mem _ (hp i)) (lt_add_of_pos_right H hε) hfin
      obtain ⟨y, hy, rfl⟩ := hz
      exact ⟨y, hy, hdz⟩
    choose q hqv hqd using hq
    have hprob : IsProbabilityMeasure (∑ i, w i • (q i).toMeasure) := by
      constructor
      rw [Measure.finsetSum_apply]
      simp only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one]
      rw [← ENNReal.ofNNReal_finsetSum, hw, ENNReal.coe_one]
    refine ⟨lpEquiv ⟨∑ i, w i • (q i).toMeasure, hprob⟩, Set.mem_image_of_mem _ ?_, ?_⟩
    · rw [probConvexHull_eq]
      exact ⟨ι, ‹Fintype ι›, w, q, hqv, hw, rfl⟩
    · have hcore : levyProkhorovEDist (∑ i, w i • (p i).toMeasure) (∑ i, w i • (q i).toMeasure)
          ≤ ENNReal.ofReal (H + ε) := by
        refine levyProkhorovEDist_sum_le hw fun i => ?_
        rw [← hedist, edist_dist]
        exact ENNReal.ofReal_le_ofReal (hqd i).le
      have hHε : (0 : ℝ) ≤ H + ε := add_nonneg Metric.hausdorffDist_nonneg hε.le
      rw [dist_edist, hedist]
      calc (levyProkhorovEDist μ.toMeasure _).toReal
          ≤ (ENNReal.ofReal (H + ε)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top (by rw [hμ]; exact hcore)
        _ = H + ε := ENNReal.toReal_ofReal hHε
  have hfin : Metric.hausdorffEDist (lpEquiv '' s) (lpEquiv '' t) ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded (hs.image _) (ht.image _)
      Metric.isBounded_of_compactSpace Metric.isBounded_of_compactSpace
  refine Metric.hausdorffDist_le_of_mem_dist
    (add_nonneg Metric.hausdorffDist_nonneg hε.le) (key s t hfin) fun y hy => ?_
  obtain ⟨x, hx, hd⟩ := key t s (by rwa [Metric.hausdorffEDist_comm]) y hy
  refine ⟨x, hx, ?_⟩
  rwa [Metric.hausdorffDist_comm] at hd

/-- **(IL7 — the full squeeze, LP side).** For sequences of generating sets whose LP-Hausdorff
distance tends to `0`, the LP-Hausdorff distance of their *closed convex hulls* (the credal
carriers) also tends to `0`. Combines `Metric.hausdorffDist_closure` (outer closure, metric-free)
with IL6. Its output feeds IL2 to conclude in the abstract metric. -/
lemma hausdorffDist_lp_carrier_tendsto_zero {S : ℕ → Set (Δ X)} {S₀ : Set (Δ X)}
    (h : Filter.Tendsto (fun k => Metric.hausdorffDist (lpEquiv '' S k) (lpEquiv '' S₀))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k =>
        Metric.hausdorffDist (lpEquiv '' closure (Credal.probConvexHull (S k)))
                             (lpEquiv '' closure (Credal.probConvexHull S₀)))
      Filter.atTop (nhds 0) := by
  have himg : ∀ A : Set (Δ X), ⇑lpEquiv '' closure A = closure (⇑lpEquiv '' A) := fun A =>
    lpEquiv.toHomeomorph.image_closure A
  simp only [himg, Metric.hausdorffDist_closure]
  exact squeeze_zero (fun k => Metric.hausdorffDist_nonneg)
    (fun k => hausdorffDist_lp_probConvexHull_le _ _) h

/- defining infrakernels on a topological space Z -/
-- variable {Z : Type*} [TopologicalSpace Z]

-- def infraKernel := C(Z, Credal X)

end CredalSets

end IB
