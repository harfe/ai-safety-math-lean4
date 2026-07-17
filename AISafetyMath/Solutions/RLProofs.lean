import Mathlib
import AISafetyMath.Solutions.TrajectoryMeasure

/-
Helper file (part 2 of the RL development): the two main propositions.

Definitions (`Policy`, `trajectoryMeasure`, `expectedTotalLoss`, …) come from
`Solutions.TrajectoryMeasure` (implicit `{A O}`, target notation).

Imported (together with `TrajectoryMeasure`) by `Solutions.IB_RL`.
-/

open ProbabilityTheory MeasureTheory

open scoped NNReal ENNReal

namespace IB_RL

section Existence

variable {A O : Type*}
variable [Finite A] [Finite O]
variable [MeasurableSpace A] [MeasurableSpace O]
variable [DiscreteMeasurableSpace A] [DiscreteMeasurableSpace O]
variable [Nonempty A]
variable [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
variable [TopologicalSpace O] [DiscreteTopology O] [BorelSpace O]

/- The finite sums over the (finite) action set `A` only need a `Fintype` structure inside
proofs; derive it from `Finite` so the statements stay `Finite`-parametrised. -/
noncomputable local instance : Fintype A := Fintype.ofFinite A
noncomputable local instance : Fintype O := Fintype.ofFinite O

instance : Nonempty (ProbabilityMeasure A) :=
  ⟨⟨Measure.dirac (Classical.arbitrary A), inferInstance⟩⟩
instance : Nonempty (Policy A O) := Pi.instNonempty

omit [Finite A] [Finite O] [MeasurableSpace A] [MeasurableSpace O]
  [DiscreteMeasurableSpace A] [DiscreteMeasurableSpace O] [Nonempty A] [BorelSpace A]
  [BorelSpace O] in
lemma totalLoss_continuous (L : MomentaryLoss A O) (γ : discount) :
    Continuous (fun h : ℕ → A × O => totalLoss L γ h) := by
  unfold totalLoss
  refine Continuous.mul continuous_const ?_
  refine continuous_tsum (u := fun t => γ.1 ^ t) ?_
    (summable_geometric_of_lt_one γ.2.1 γ.2.2) ?_
  · -- each summand is locally constant: it factors through the first `t` coordinates,
    -- a finite product of discrete spaces (hence discrete), so it is continuous.
    intro t
    refine Continuous.mul continuous_const ?_
    have h1 : Continuous (fun h : ℕ → A × O => (fun i : Fin t => h i.1)) :=
      continuous_pi (fun i => continuous_apply i.1)
    exact (continuous_of_discreteTopology
      (f := fun v : Fin t → A × O => ((L (List.ofFn v) : Set.Icc (0 : ℝ) 1) : ℝ))).comp h1
  · -- uniform bound by the geometric series, since `0 ≤ L ≤ 1` and `0 ≤ γ`.
    intro t h
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg γ.2.1 t),
      abs_of_nonneg (L (initialSegment A O h t)).2.1]
    calc γ.1 ^ t * (L (initialSegment A O h t)).1
        ≤ γ.1 ^ t * 1 :=
          mul_le_mul_of_nonneg_left (L (initialSegment A O h t)).2.2 (pow_nonneg γ.2.1 t)
      _ = γ.1 ^ t := mul_one _

omit [Nonempty A] in
lemma expectedTotalLoss_continuous
    (L : MomentaryLoss A O) (γ : discount) (μ : Environment A O) :
    Continuous (fun π : Policy A O => expectedTotalLoss L γ π μ) := by
  -- Package the bounded continuous `totalLoss` (step (a) + compactness of `ℕ → A × O`).
  let f : BoundedContinuousFunction (ℕ → A × O) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨_, totalLoss_continuous L γ⟩
  -- Integrating `f` is weakly continuous in the measure; precompose with the law map (step (c)).
  exact (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp
    (trajectoryMeasure_continuous μ)

/- Lower semicontinuity is all the minimisation in `optimal_policy_exists` needs; it is a
direct downcast of the continuity in step (d). -/
omit [Nonempty A] in
lemma expectedTotalLoss_lowerSemicontinuous
    (L : MomentaryLoss A O) (γ : discount) (μ : Environment A O) :
    LowerSemicontinuous (fun π : Policy A O => expectedTotalLoss L γ π μ) :=
  (expectedTotalLoss_continuous L γ μ).lowerSemicontinuous

/- The first half of Proposition 1: an optimal Policy exists (possibly stochastic). -/
theorem optimal_policy_exists (L : MomentaryLoss A O) (γ : discount)
    (μ : Environment A O) :
    ∃ π', IsOptimalPolicy L γ μ π' := by
  obtain ⟨π', _, hmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn Set.univ_nonempty isCompact_univ
      ((expectedTotalLoss_lowerSemicontinuous L γ μ).lowerSemicontinuousOn Set.univ)
  exact ⟨π', fun b => isMinOn_iff.mp hmin b (Set.mem_univ b)⟩

/- ===========================================================================
Second half of Proposition 1: determinism.

CRUX (`exists_deterministic_le`): every Policy is matched or beaten by a deterministic one.
This is the finite-action "determinisation" fact. Intended proof route:
  * `π ↦ expectedTotalLoss` is affine in each coordinate `π h` (the trajectory law is
    multilinear in the per-History action distributions);
  * an affine function on the simplex `ProbabilityMeasure A` (finite `A`) attains its min at a
    vertex, i.e. a Dirac — so each stochastic choice can be pushed to a deterministic one
    without increasing the loss;
  * assemble over all histories (the set of deterministic policies is closed, hence compact,
    in the Policy space, so a deterministic minimiser exists with value ≤ that of `π`).
Once the crux is in hand, `optimal_deterministic_policy_exists` is pure plumbing.
=========================================================================== -/

omit [Nonempty A] [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
  [TopologicalSpace O] [DiscreteTopology O] [BorelSpace O] in
open Classical in
/-- SINGLE-STEP AFFINENESS (foundation of the crux). The one-step measure
`measureAfterHist … π … h` is the `π h₀ {a}`-barycentre of its Dirac substitutions. For `h ≠ h₀`
the substitution does not touch coordinate `h`, and the weights sum to `1`; for `h = h₀` this is the
linearity of `compProd` in its first (finite-`A`) argument. -/
lemma measureAfterHist_barycentric (μ : Environment A O) (π : Policy A O) (h₀ h : History A O) :
    measureAfterHist π μ h
      = ∑ a : A, ((π h₀ {a} : ℝ≥0) : ℝ≥0∞) •
          measureAfterHist (Function.update π h₀ ⟨Measure.dirac a, inferInstance⟩) μ h := by
  -- Singleton-mass formula for any Policy `p`: factor the compProd over `{a'} ×ˢ {o'}`.
  have key : ∀ (p : Policy A O) (a' : A) (o' : O),
      measureAfterHist p μ h {(a', o')}
        = ((μ h a' : Measure O) {o'}) * ((p h {a'} : ℝ≥0) : ℝ≥0∞) := by
    intro p a' o'
    haveI hk : IsMarkovKernel
        ({ toFun := fun a => (μ h a).toMeasure,
           measurable' := Measurable.of_discrete } : Kernel A O) :=
      ⟨fun a => (μ h a).2⟩
    have hprod : ({(a', o')} : Set (A × O)) = {a'} ×ˢ {o'} := by
      ext ⟨a, o⟩; simp [Prod.ext_iff]
    rw [measureAfterHist, hprod,
      Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
      MeasureTheory.lintegral_singleton, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    rfl
  -- The weights `π h₀ {a}` sum to `1` (probability measure on finite `A`).
  have hwsum : ∑ a : A, ((π h₀ {a} : ℝ≥0) : ℝ≥0∞) = 1 := by
    simp_rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    rw [← MeasureTheory.measure_biUnion_finset (fun a _ b _ hab => Set.disjoint_singleton.mpr hab)
      (fun _ _ => measurableSet_singleton _),
      (by ext x; simp : (⋃ a ∈ (Finset.univ : Finset A), ({a} : Set A)) = Set.univ)]
    exact measure_univ
  apply Measure.ext_of_singleton
  rintro ⟨a', o'⟩
  rw [Measure.finsetSum_apply, key π a' o']
  -- Pull the (Policy-independent) Environment factor `μ h a' {o'}` out of the finite sum.
  have hfac : ∀ x : A,
      (((π h₀ {x} : ℝ≥0) : ℝ≥0∞) • measureAfterHist
          (Function.update π h₀ ⟨Measure.dirac x, inferInstance⟩) μ h) {(a', o')}
        = ((μ h a' : Measure O) {o'}) * (((π h₀ {x} : ℝ≥0) : ℝ≥0∞) *
            (((Function.update π h₀ ⟨Measure.dirac x, inferInstance⟩) h {a'} : ℝ≥0) : ℝ≥0∞)) := by
    intro x
    rw [Measure.smul_apply, key _ a' o', smul_eq_mul]; ring
  simp_rw [hfac, ← Finset.mul_sum]
  congr 1
  by_cases hh : h = h₀
  · -- At the touched coordinate the substitution makes `π h₀ = δ x`, so only `x = a'` survives.
    subst hh
    have hd : ∀ x : A,
        (((Function.update π h ⟨Measure.dirac x, inferInstance⟩ h) {a'} : ℝ≥0) : ℝ≥0∞)
          = if x = a' then 1 else 0 := by
      intro x
      rw [Function.update_self, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      change (Measure.dirac x) {a'} = if x = a' then 1 else 0
      rw [MeasureTheory.Measure.dirac_apply' _ (measurableSet_singleton a')]
      simp [Set.indicator_apply]
    simp_rw [hd, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ a' (fun x => ((π h {x} : ℝ≥0) : ℝ≥0∞))]
    simp
  · -- Away from `h₀`, the substitution leaves `π h` untouched; factor it out and use `hwsum`.
    simp_rw [Function.update_of_ne hh, ← Finset.sum_mul, hwsum, one_mul]

open Classical in
set_option linter.unusedSectionVars false in
omit [Nonempty A] [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
  [TopologicalSpace O] [DiscreteTopology O] [BorelSpace O] in
/-- Updating the Policy at a single History `h₀` leaves the one-step measure at every *other*
History untouched. -/
lemma measureAfterHist_update_of_ne (μ : Environment A O) (π : Policy A O) (h₀ h : History A O)
    (a : A) (hh : h ≠ h₀) :
    measureAfterHist (Function.update π h₀ ⟨Measure.dirac a, inferInstance⟩) μ h
      = measureAfterHist π μ h := by
  rw [measureAfterHist, measureAfterHist, Function.update_of_ne hh]

omit [Nonempty A] [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
  [TopologicalSpace O] [DiscreteTopology O] [BorelSpace O] in
/-- Singleton mass of the horizon-`0` marginal: a single one-step measure from the empty History. -/
lemma traj_marginal_singleton_zero (μ : Environment A O) (π : Policy A O)
    (ω : (i : Finset.Iic 0) → A × O) :
    ((trajectoryMeasure π μ).map (Preorder.frestrictLe 0)) {ω}
      = (measureAfterHist π μ List.nil) {ω ⟨0, Finset.mem_Iic.mpr le_rfl⟩} := by
  rw [trajectoryMeasure, Kernel.trajMeasure,
    Measure.map_comp _ _ (Preorder.measurable_frestrictLe _),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp,
    Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, MeasurableEquiv.piUnique_symm_apply]
  have huniq : (⟨0, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic 0)
      = (default : Finset.Iic 0) := Subsingleton.elim _ _
  constructor
  · intro hx; rw [← hx, huniq, uniqueElim_default]
  · intro hx; funext i
    rw [show i = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ from
      Subtype.ext (Nat.le_zero.mp (Finset.mem_Iic.mp i.2)), huniq, uniqueElim_default, hx, huniq]

omit [Nonempty A] [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
  [TopologicalSpace O] [DiscreteTopology O] [BorelSpace O] in
/-- Singleton mass of the horizon-`(k+1)` marginal: the horizon-`k` marginal mass times the
one-step measure at the realized length-`(k+1)` History (the Ionescu–Tulcea recursion). -/
lemma traj_marginal_singleton_succ (μ : Environment A O) (π : Policy A O) (k : ℕ)
    (ω : (i : Finset.Iic (k + 1)) → A × O) :
    ((trajectoryMeasure π μ).map (Preorder.frestrictLe (k + 1))) {ω}
      = ((trajectoryMeasure π μ).map (Preorder.frestrictLe k))
          {Preorder.frestrictLe₂ (π := fun _ => A × O) (Nat.le_succ k) ω}
        * (measureAfterHist π μ (historyHelper k
            (Preorder.frestrictLe₂ (π := fun _ => A × O) (Nat.le_succ k) ω)))
            {ω ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩} := by
  have hrec := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => A × O) (μ₀ := measureAfterHist π μ List.nil)
    (κ := transitionKernel π μ) (a := k)
  have hset : (Preorder.frestrictLe (π := fun _ => A × O) (k + 1)) ⁻¹' {ω}
      = (fun x : ℕ → A × O => (Preorder.frestrictLe k x, x (k + 1))) ⁻¹'
          ({Preorder.frestrictLe₂ (π := fun _ => A × O) (Nat.le_succ k) ω}
            ×ˢ {ω ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩}) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod]
    constructor
    · intro hx
      refine ⟨?_, by rw [← hx]; rfl⟩
      rw [← Preorder.frestrictLe₂_comp_frestrictLe (π := fun _ => A × O) (Nat.le_succ k)]
      simp only [Function.comp_apply, hx]
    · rintro ⟨h1, h2⟩
      funext i
      rcases eq_or_lt_of_le (Finset.mem_Iic.mp i.2) with hi | hi
      · rw [show i = ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩ from Subtype.ext hi]; exact h2
      · have := congrFun h1 ⟨i.1, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp hi)⟩
        simpa only [Preorder.frestrictLe_apply, Preorder.frestrictLe₂_apply] using this
  rw [trajectoryMeasure,
    Measure.map_apply (Preorder.measurable_frestrictLe _) (measurableSet_singleton _), hset,
    ← Measure.map_apply (by fun_prop) (MeasurableSet.prod (measurableSet_singleton _)
      (measurableSet_singleton _)), ← hrec,
    Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
    MeasureTheory.lintegral_singleton, mul_comm]
  rfl

open Classical in
omit [Nonempty A] [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
  [TopologicalSpace O] [DiscreteTopology O] [BorelSpace O] in
/-- Below the horizon `|h₀|`, updating the Policy at `h₀` does not change any finite marginal:
the first `n + 1` realized histories all have length `≤ n < |h₀|`, so none of them is `h₀`. -/
lemma traj_marginal_inert (μ : Environment A O) (π : Policy A O) (h₀ : History A O) (a : A) :
    ∀ n, n < h₀.length → ∀ ω : (i : Finset.Iic n) → A × O,
      ((trajectoryMeasure (Function.update π h₀ ⟨Measure.dirac a, inferInstance⟩) μ).map
          (Preorder.frestrictLe n)) {ω}
        = ((trajectoryMeasure π μ).map (Preorder.frestrictLe n)) {ω} := by
  intro n
  induction n with
  | zero =>
    intro hn ω
    rw [traj_marginal_singleton_zero, traj_marginal_singleton_zero,
      measureAfterHist_update_of_ne μ π h₀ List.nil a (by rintro rfl; simp at hn)]
  | succ k ih =>
    intro hn ω
    have hHk : (historyHelper k
        (Preorder.frestrictLe₂ (π := fun _ => A × O) (Nat.le_succ k) ω)) ≠ h₀ := by
      intro heq
      have : (historyHelper k
          (Preorder.frestrictLe₂ (π := fun _ => A × O) (Nat.le_succ k) ω)).length = h₀.length := by
        rw [heq]
      simp only [historyHelper, List.length_ofFn] at this
      omega
    rw [traj_marginal_singleton_succ, traj_marginal_singleton_succ,
      ih (by omega) _, measureAfterHist_update_of_ne μ π h₀ _ a hHk]

open Classical in
omit [Nonempty A] [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
  [TopologicalSpace O] [DiscreteTopology O] [BorelSpace O] in
/-- The barycentric identity at the level of every finite-horizon marginal (singleton masses), by
induction on the horizon. Along any trajectory the History of length `|h₀|` is realized at exactly
one step, so `π h₀` enters the marginal-mass product in at most one factor: at the step where the
realized History *is* `h₀` (`hcase`) the one-step measure is barycentric while the lower marginal is
inert (`traj_marginal_inert`); at every other step the one-step measure is inert
(`measureAfterHist_update_of_ne`) and the lower marginal recurses. -/
lemma traj_marginal_barycentric (μ : Environment A O) (π : Policy A O) (h₀ : History A O) :
    ∀ n, ∀ ω : (i : Finset.Iic n) → A × O,
      ((trajectoryMeasure π μ).map (Preorder.frestrictLe n)) {ω}
        = ∑ a : A, ((π h₀ {a} : ℝ≥0) : ℝ≥0∞) *
            ((trajectoryMeasure (Function.update π h₀ ⟨Measure.dirac a, inferInstance⟩) μ).map
                (Preorder.frestrictLe n)) {ω} := by
  intro n
  induction n with
  | zero =>
    intro ω
    rw [traj_marginal_singleton_zero, measureAfterHist_barycentric μ π h₀ List.nil,
      Measure.finsetSum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Measure.smul_apply, smul_eq_mul, traj_marginal_singleton_zero]
  | succ k ih =>
    intro ω
    simp only [traj_marginal_singleton_succ]
    set ω' := Preorder.frestrictLe₂ (π := fun _ => A × O) (Nat.le_succ k) ω with hω'def
    set Hk := historyHelper k ω' with hHkdef
    set z := ω ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩ with hzdef
    by_cases hcase : Hk = h₀
    · -- Touched step: the lower marginal is inert and the one-step measure is barycentric.
      have hlen : k < h₀.length := by
        rw [← hcase, hHkdef]; simp [historyHelper, List.length_ofFn]
      have hge : ∀ a : A,
          ((trajectoryMeasure (Function.update π h₀ ⟨Measure.dirac a, inferInstance⟩) μ).map
              (Preorder.frestrictLe k)) {ω'}
            = ((trajectoryMeasure π μ).map (Preorder.frestrictLe k)) {ω'} :=
        fun a => traj_marginal_inert μ π h₀ a k hlen ω'
      have hbar : (measureAfterHist π μ Hk) {z}
          = ∑ a : A, ((π h₀ {a} : ℝ≥0) : ℝ≥0∞) *
              (measureAfterHist (Function.update π h₀ ⟨Measure.dirac a, inferInstance⟩) μ Hk)
                {z} := by
        rw [measureAfterHist_barycentric μ π h₀ Hk, Measure.finsetSum_apply]
        exact Finset.sum_congr rfl (fun a _ => by rw [Measure.smul_apply, smul_eq_mul])
      rw [hbar, Finset.mul_sum]
      simp_rw [hge]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    · -- Untouched step: the one-step measure is inert, recurse on the lower marginal.
      have hmah : ∀ a : A,
          (measureAfterHist (Function.update π h₀ ⟨Measure.dirac a, inferInstance⟩) μ Hk) {z}
            = (measureAfterHist π μ Hk) {z} :=
        fun a => by rw [measureAfterHist_update_of_ne μ π h₀ Hk a hcase]
      simp_rw [hmah, ← mul_assoc]
      rw [← Finset.sum_mul, ← ih ω']

open Classical in
omit [Nonempty A] [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
  [TopologicalSpace O] [DiscreteTopology O] [BorelSpace O] in
/-- MEASURE-LEVEL AFFINENESS. The trajectory law is the `π h₀`-barycentre of the laws obtained by
replacing the single coordinate `π h₀` with each Dirac `δ a`. The coordinate `π h₀` enters the
Ionescu–Tulcea construction only through the one-step measure `measureAfterHist` at the *single*
History `h₀` (where it appears linearly, via `compProd`, as established by
`measureAfterHist_barycentric`), and `A` is finite, so the whole law is affine in that coordinate
— i.e. a finite `π h₀ {a}`-weighted mixture of the Dirac-substituted laws.

PROOF (lift the single-step identity through the projective limit):
  * `traj π` and the mixture `ν` are both the projective limit of the same family (the marginals
    of `traj π`): a measure on `ℕ → A × O` is determined by its `frestrictLe n` pushforwards
    (`IsProjectiveLimit.unique`).
  * Their `frestrictLe n` marginals agree by `traj_marginal_barycentric` — the singleton-mass
    barycentric identity proved by induction on the horizon (`measureAfterHist_barycentric`
    applied to the unique step realizing `h₀`, with `traj_marginal_inert` /
    `measureAfterHist_update_of_ne` collapsing the others).
Everything downstream (`expectedTotalLoss_barycentric` and the determinism argument) follows. -/
lemma trajectoryMeasure_barycentric (μ : Environment A O) (π : Policy A O) (h₀ : History A O) :
    trajectoryMeasure π μ
      = ∑ a : A, ((π h₀ {a} : ℝ≥0) : ℝ≥0∞) •
          trajectoryMeasure (Function.update π h₀ ⟨Measure.dirac a, inferInstance⟩) μ := by
  classical
  set ν : Measure (ℕ → A × O) := ∑ a : A, ((π h₀ {a} : ℝ≥0) : ℝ≥0∞) •
    trajectoryMeasure (Function.update π h₀ ⟨Measure.dirac a, inferInstance⟩) μ with hν
  -- Each finite marginal of `traj π` is a probability measure, so the induced projective family is.
  haveI hprob : ∀ n, IsProbabilityMeasure
      ((trajectoryMeasure π μ).map (Preorder.frestrictLe n)) :=
    fun n => Measure.isProbabilityMeasure_map (Preorder.measurable_frestrictLe n).aemeasurable
  -- The marginal sequence is projective (nested restrictions agree).
  have hproj : ∀ a b : ℕ, ∀ hab : a ≤ b,
      ((trajectoryMeasure π μ).map (Preorder.frestrictLe b)).map
          (Preorder.frestrictLe₂ (π := fun _ => A × O) hab)
        = (trajectoryMeasure π μ).map (Preorder.frestrictLe a) := by
    intro a b hab
    rw [Measure.map_map (by fun_prop) (by fun_prop),
      ← Preorder.frestrictLe₂_comp_frestrictLe (π := fun _ => A × O) hab]
  have hPfam : MeasureTheory.IsProjectiveMeasureFamily
      (MeasureTheory.inducedFamily
        (fun n => (trajectoryMeasure π μ).map (Preorder.frestrictLe n))) :=
    MeasureTheory.isProjectiveMeasureFamily_inducedFamily _ (fun a b hab => hproj a b hab)
  -- `traj π` is the projective limit of its own marginals.
  have hlimπ : MeasureTheory.IsProjectiveLimit (trajectoryMeasure π μ)
      (MeasureTheory.inducedFamily
        (fun n => (trajectoryMeasure π μ).map (Preorder.frestrictLe n))) := by
    rw [MeasureTheory.isProjectiveLimit_nat_iff' hPfam _ 0]
    intro n _
    rw [MeasureTheory.inducedFamily_Iic]
  -- So is `ν`: its marginals equal those of `traj π` by the marginal barycentric identity.
  have hlimν : MeasureTheory.IsProjectiveLimit ν
      (MeasureTheory.inducedFamily
        (fun n => (trajectoryMeasure π μ).map (Preorder.frestrictLe n))) := by
    rw [MeasureTheory.isProjectiveLimit_nat_iff' hPfam _ 0]
    intro n _
    rw [MeasureTheory.inducedFamily_Iic]
    apply Measure.ext_of_singleton
    intro ω
    have hLHS : (ν.map (Preorder.frestrictLe n)) {ω}
        = ∑ a : A, ((π h₀ {a} : ℝ≥0) : ℝ≥0∞) *
            ((trajectoryMeasure (Function.update π h₀ ⟨Measure.dirac a, inferInstance⟩) μ).map
                (Preorder.frestrictLe n)) {ω} := by
      rw [Measure.map_apply (Preorder.measurable_frestrictLe n) (measurableSet_singleton _), hν,
        Measure.finsetSum_apply]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Measure.smul_apply, smul_eq_mul,
        Measure.map_apply (Preorder.measurable_frestrictLe n) (measurableSet_singleton _)]
    rw [hLHS]
    exact (traj_marginal_barycentric μ π h₀ n ω).symm
  haveI : ∀ i : Finset ℕ, IsFiniteMeasure
      (MeasureTheory.inducedFamily
        (fun n => (trajectoryMeasure π μ).map (Preorder.frestrictLe n)) i) := by
    intro i; rw [MeasureTheory.inducedFamily]; infer_instance
  exact hlimπ.unique hlimν

open Classical in
omit [Nonempty A] [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
  [TopologicalSpace O] [DiscreteTopology O] [BorelSpace O] in
/-- AFFINENESS (the measure-theoretic heart). `expectedTotalLoss` at `π` is the `π h₀`-weighted
average of its values at the policies obtained by replacing the single coordinate `π h₀` with a
Dirac. This barycentric identity *is* affineness in the coordinate `π h₀`: it holds because `π h₀`
enters the trajectory law only through the one-step measure `measureAfterHist` at History `h₀`
(via `compProd`), in which it appears linearly, and `A` is finite so the mixture is a finite sum.
Given the measure-level statement (`trajectoryMeasure_barycentric`), this is integral-linearity:
the integral of `totalLoss` against a finite weighted sum of measures distributes. -/
lemma expectedTotalLoss_barycentric (L : MomentaryLoss A O) (γ : discount)
    (μ : Environment A O) (π : Policy A O) (h₀ : History A O) :
    expectedTotalLoss L γ π μ
      = ∑ a : A, ((π h₀ {a} : ℝ≥0) : ℝ) *
          expectedTotalLoss L γ
            (Function.update π h₀ ⟨Measure.dirac a, inferInstance⟩) μ := by
  -- Spell the goal with the `ℕ → A × O` integral binder (defeq-unfolding `expectedTotalLoss`
  -- and the `Destiny` synonym), so the measure-space instances stay consistent under `rw`.
  change ∫ h : ℕ → A × O, totalLoss L γ h ∂trajectoryMeasure π μ
      = ∑ a : A, ((π h₀ {a} : ℝ≥0) : ℝ) *
          ∫ h : ℕ → A × O, totalLoss L γ h
            ∂trajectoryMeasure (Function.update π h₀ ⟨Measure.dirac a, inferInstance⟩) μ
  -- `totalLoss` is integrable against each scaled law (a finite measure): direct when the weight
  -- is positive, trivial when it is `0` (the measure collapses to `0`).
  have hint : ∀ a : A, Integrable (fun h : ℕ → A × O => totalLoss L γ h)
      (((π h₀ {a} : ℝ≥0) : ℝ≥0∞) •
        trajectoryMeasure (Function.update π h₀ ⟨Measure.dirac a, inferInstance⟩) μ) := by
    intro a
    rcases eq_or_ne ((π h₀ {a} : ℝ≥0) : ℝ≥0∞) 0 with h0 | h0
    · rw [h0, zero_smul]; exact integrable_zero_measure
    · exact (integrable_smul_measure h0 (by simp)).mpr
        (expectedTotalLoss_integrable L γ _ μ)
  rw [trajectoryMeasure_barycentric μ π h₀,
    integral_finsetSum_measure (fun a _ => hint a)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul]

open Classical in
omit [TopologicalSpace O] [DiscreteTopology O] [BorelSpace O] in
/-- CRUX (single-coordinate). At any *one* History `h₀` the Policy can be replaced by a Dirac on a
best action there — `Function.update π h₀ (δ a)` — without increasing the expected loss. Immediate
from `expectedTotalLoss_barycentric`: the right-hand side is a convex combination (weights
`π h₀ {a} ≥ 0` summing to `1`), hence is `≥` its least term, so some Dirac value is `≤` it. -/
lemma exists_dirac_improvement (L : MomentaryLoss A O) (γ : discount)
    (μ : Environment A O) (π : Policy A O) (h₀ : History A O) :
    ∃ a : A, expectedTotalLoss L γ
        (Function.update π h₀ ⟨Measure.dirac a, inferInstance⟩) μ
      ≤ expectedTotalLoss L γ π μ := by
  classical
  -- The weights `π h₀ {a}` are nonnegative and sum to `1` (it is a probability measure).
  have hwsum : ∑ a : A, ((π h₀ {a} : ℝ≥0) : ℝ) = 1 := by
    have hcast : ∀ a : A, ((π h₀ {a} : ℝ≥0) : ℝ) = (π h₀ : Measure A).real {a} := by
      intro a
      rw [MeasureTheory.measureReal_def,
        ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_toReal]
    simp_rw [hcast]
    rw [MeasureTheory.sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  -- Pick a best action; the barycentric average is `≥` its least term.
  obtain ⟨a₀, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset A)
    (fun a => expectedTotalLoss L γ
      (Function.update π h₀ ⟨Measure.dirac a, inferInstance⟩) μ) Finset.univ_nonempty
  refine ⟨a₀, ?_⟩
  rw [expectedTotalLoss_barycentric L γ μ π h₀]
  calc expectedTotalLoss L γ (Function.update π h₀ ⟨Measure.dirac a₀, inferInstance⟩) μ
      = ∑ a : A, ((π h₀ {a} : ℝ≥0) : ℝ) *
          expectedTotalLoss L γ
            (Function.update π h₀ ⟨Measure.dirac a₀, inferInstance⟩) μ := by
        rw [← Finset.sum_mul, hwsum, one_mul]
    _ ≤ ∑ a : A, ((π h₀ {a} : ℝ≥0) : ℝ) *
          expectedTotalLoss L γ
            (Function.update π h₀ ⟨Measure.dirac a, inferInstance⟩) μ :=
        Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (hmin a (Finset.mem_univ a)) (NNReal.coe_nonneg _)

/-- Determinisation (CRUX assembly): every Policy is matched or improved by a deterministic Policy.
Enumerate the countably-many histories `h₀, h₁, …` and greedily determinise coordinate-by-coordinate
with `exists_dirac_improvement`, each step a `Function.update` that leaves earlier (already-Dirac)
coordinates untouched and does not increase the loss. Each coordinate is fixed after finitely many
steps, so the iterates converge *pointwise* — i.e. in the product topology — to a fully
deterministic Policy `πd`; continuity (`expectedTotalLoss_continuous`) then gives
`F πd = lim F(iterate) ≤ F π`. (No tightness/tail bound or compactness needed: pointwise convergence
plus continuity suffices.) -/
lemma exists_deterministic_le (L : MomentaryLoss A O) (γ : discount)
    (μ : Environment A O) (π : Policy A O) :
    ∃ πd : Policy A O, IsPolicyDeterministic πd ∧
      expectedTotalLoss L γ πd μ ≤ expectedTotalLoss L γ π μ := by
  classical
  haveI : Nonempty (History A O) := ⟨[]⟩
  haveI : Countable (History A O) := inferInstanceAs (Countable (List (A × O)))
  -- Enumerate the (countably-many) histories.
  obtain ⟨e, he⟩ := exists_surjective_nat (History A O)
  -- One greedy determinisation step: replace `p` at History `h` by a best Dirac.
  set g : History A O → Policy A O → Policy A O := fun h p =>
    Function.update p h
      ⟨Measure.dirac (Classical.choose (exists_dirac_improvement L γ μ p h)), inferInstance⟩
    with hg
  -- The descent sequence: at step `n` determinise `e n`, but only at its *first* occurrence.
  set seq : ℕ → Policy A O := fun n => Nat.rec (motive := fun _ => Policy A O) π
    (fun k p => if e k ∉ Finset.image e (Finset.range k) then g (e k) p else p) n with hseq
  have hseqS : ∀ n, seq (n + 1)
      = if e n ∉ Finset.image e (Finset.range n) then g (e n) (seq n) else seq n :=
    fun n => rfl
  have hseq0 : seq 0 = π := rfl
  -- Make `seq`/`g` opaque: keep only their equational lemmas, so defeq never re-unfolds `Nat.rec`.
  clear_value seq g
  -- Each step does not increase the loss.
  have hstep_le : ∀ n, expectedTotalLoss L γ (seq (n + 1)) μ
      ≤ expectedTotalLoss L γ (seq n) μ := by
    intro n
    rw [hseqS]
    split_ifs with hfresh
    · exact le_refl _
    · rw [hg]
      exact Classical.choose_spec (exists_dirac_improvement L γ μ (seq n) (e n))
  -- Hence every iterate is `≤` the start.
  have hle_start : ∀ n, expectedTotalLoss L γ (seq n) μ
      ≤ expectedTotalLoss L γ π μ := by
    intro n
    induction n with
    | zero => exact le_of_eq (by rw [hseq0])
    | succ k ih => exact le_trans (hstep_le k) ih
  -- First index that hits each History.
  set N : History A O → ℕ := fun h => Nat.find (he h) with hN
  have hNspec : ∀ h, e (N h) = h := fun h => Nat.find_spec (he h)
  have hNmin : ∀ h, ∀ m < N h, e m ≠ h := fun h m hm => Nat.find_min (he h) hm
  -- The limiting determinised Policy.
  set πd : Policy A O := fun h => seq (N h + 1) h with hπd
  -- Past step `N h`, coordinate `h` is frozen at `πd h`.
  have hstab : ∀ h, ∀ n, N h + 1 ≤ n → seq n h = πd h := by
    intro h n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      have hstep : seq (m + 1) h = seq m h := by
        rw [hseqS]
        split_ifs with hfresh
        · rfl
        · have hem : e m ≠ h := by
            intro hcontra
            apply hfresh
            rw [hcontra, ← hNspec h]
            exact Finset.mem_image_of_mem e (Finset.mem_range.mpr (by omega))
          simp only [hg]
          rw [Function.update_of_ne (Ne.symm hem)]
      rw [hstep, ih]
  -- The frozen value is a Dirac, so `πd` is deterministic.
  have hdir : ∀ h, πd h = ⟨Measure.dirac
      (Classical.choose (exists_dirac_improvement L γ μ (seq (N h)) h)), inferInstance⟩ := by
    intro h
    have hπdh : πd h = seq (N h + 1) h := rfl
    rw [hπdh, hseqS]
    have hfresh : e (N h) ∉ Finset.image e (Finset.range (N h)) := by
      rw [hNspec h]
      intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨m, hmrange, hem⟩ := hmem
      exact hNmin h m (Finset.mem_range.mp hmrange) hem
    rw [if_pos hfresh]
    simp only [hg]
    rw [hNspec h, Function.update_self]
  refine ⟨πd, ⟨fun h => Classical.choose (exists_dirac_improvement L γ μ (seq (N h)) h),
    fun h => ?_⟩, ?_⟩
  · -- `πd h` puts mass `1` on its Dirac point.
    rw [hdir h, ← ENNReal.coe_eq_one, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_singleton _)
  · -- Value: continuity + pointwise convergence of the iterates.
    have hseqtend : Filter.Tendsto seq Filter.atTop (nhds πd) := by
      refine tendsto_pi_nhds.mpr fun h => ?_
      exact tendsto_atTop_of_eventually_const (i₀ := N h + 1) fun n hn => hstab h n hn
    have htend : Filter.Tendsto (fun n => expectedTotalLoss L γ (seq n) μ)
        Filter.atTop (nhds (expectedTotalLoss L γ πd μ)) :=
      ((expectedTotalLoss_continuous L γ μ).tendsto πd).comp hseqtend
    exact le_of_tendsto htend (Filter.Eventually.of_forall hle_start)

/-- The determinism conjunct of Proposition 1: an optimal Policy can be chosen deterministic.
Combines existence (`optimal_policy_exists`) with determinisation (`exists_deterministic_le`). -/
lemma optimal_deterministic_policy_exists (L : MomentaryLoss A O) (γ : discount)
    (μ : Environment A O) :
    ∃ π', IsOptimalPolicy L γ μ π' ∧ IsPolicyDeterministic π' := by
  obtain ⟨π, hπ⟩ := optimal_policy_exists L γ μ
  obtain ⟨πd, hdet, hle⟩ := exists_deterministic_le L γ μ π
  refine ⟨πd, ?_, hdet⟩
  intro b
  exact le_trans hle (hπ b)

end Existence

section Regret

variable {A O : Type*}
variable [Finite A] [Finite O]
variable [MeasurableSpace A] [MeasurableSpace O]
variable [DiscreteMeasurableSpace A] [DiscreteMeasurableSpace O]
variable [Nonempty A]

/- Proposition 1:
An optimal Policy exists. It can be chosen to be deterministic.
Transported from `optimal_deterministic_policy_exists` by equipping the finite,
discrete-measurable `A`, `O` with their canonical discrete topology (`BorelSpace`
is then automatic). -/
theorem exists_optimal_policy (L : MomentaryLoss A O) (γ : discount) (μ : Environment A O)
    : ∃ π', IsOptimalPolicy L γ μ π'
    ∧ IsPolicyDeterministic π' := by
  letI : TopologicalSpace A := ⊥
  letI : TopologicalSpace O := ⊥
  haveI : DiscreteTopology A := ⟨rfl⟩
  haveI : DiscreteTopology O := ⟨rfl⟩
  haveI : BorelSpace A := DiscreteMeasurableSpace.toBorelSpace
  haveI : BorelSpace O := DiscreteMeasurableSpace.toBorelSpace
  exact optimal_deterministic_policy_exists L γ μ

/- The article talks about an optimal Policy.
As there might be more than one such Policy,
we use `Classical.choose` to pick one. -/
noncomputable
def best_policy (L : MomentaryLoss A O) (γ : discount)
    (μ : Environment A O) : Policy A O := Classical.choose (exists_optimal_policy L γ μ)

/- Definition of the regret of a Policy.
Here, ⨅ is notation for the indexed infimum.
We use EReal so that the infimum always exists (definition verbatim from the target). -/
noncomputable
def regret (L : MomentaryLoss A O) (γ : discount)
  (π : Policy A O) (μ : Environment A O) : EReal :=
    (expectedTotalLoss L γ π μ : EReal)
    - ⨅ (π': Policy A O), (expectedTotalLoss L γ π' μ : EReal)

/- sanity check:
in EReal, the infimum Π over an empty type is ⊤ -/
lemma inf_over_empty_ereal_is_top {X : Type*} [IsEmpty X] (f : X → EReal) :
  ⨅ (x : X), f x = ⊤ := iInf_of_empty f

/- In `regret`, the infimum is taken in `ℝ` (the coercion to `EReal` is applied to the
whole infimum). It is attained by `best_policy` (via `exists_optimal_policy`), so it is
the loss of the best Policy. `ℝ` is only conditionally complete, so we need the range to
be bounded below (by `0`) and nonempty (from `Nonempty A`) for the `ciInf` lemmas. -/
lemma iInf_expected_total_loss_eq (L : MomentaryLoss A O) (γ : discount)
    (μ : Environment A O) :
    ⨅ (π' : Policy A O), expectedTotalLoss L γ π' μ
      = expectedTotalLoss L γ (best_policy L γ μ) μ :=
  le_antisymm
    (ciInf_le ⟨0, by rintro x ⟨π', rfl⟩
                     exact (expectedTotalLoss_mem_unitInterval L γ π' μ).1⟩ _)
    (le_ciInf fun π' => (Classical.choose_spec (exists_optimal_policy L γ μ)).1 π')

/- The real-valued regret against the chosen best Policy. The machinery below is
developed for this quantity and transported to `regret` via `regret_eq_coe_regretR`. -/
noncomputable
def regretR (L : MomentaryLoss A O) (γ : discount)
  (π : Policy A O) (μ : Environment A O) : ℝ :=
  expectedTotalLoss L γ π μ - expectedTotalLoss L γ (best_policy L γ μ) μ

/- `regret` is the coercion of the real-valued regret: the infimum is attained,
and the subtraction of two (finite) reals in `EReal` is the real subtraction. -/
lemma regret_eq_coe_regretR (L : MomentaryLoss A O) (γ : discount)
    (π : Policy A O) (μ : Environment A O) :
    regret L γ π μ = ((regretR L γ π μ : ℝ) : EReal) := by
  rw [regret, regretR, EReal.coe_sub]
  congr 1
  exact le_antisymm (iInf_le _ (best_policy L γ μ))
    (le_iInf fun π' => EReal.coe_le_coe_iff.mpr
      ((Classical.choose_spec (exists_optimal_policy L γ μ)).1 π'))

/- the real-valued regret is nonnegative -/
lemma regretR_nonneg (L : MomentaryLoss A O) (γ : discount)
    (π : Policy A O) (μ : Environment A O) : regretR L γ π μ ≥ 0 := by
  rw [regretR, ge_iff_le, sub_nonneg]
  exact (Classical.choose_spec (exists_optimal_policy L γ μ)).1 π

/- sanity check:
The regret of an optimal Policy is 0
-/
lemma regret_of_optimal (L : MomentaryLoss A O) (γ : discount)
    (π : Policy A O) (μ : Environment A O)
    (hopt : IsOptimalPolicy L γ μ π) :
    regret L γ π μ = 0 := by
  have hR : regretR L γ π μ = 0 :=
    sub_eq_zero_of_eq (le_antisymm (hopt (best_policy L γ μ))
      ((Classical.choose_spec (exists_optimal_policy L γ μ)).1 π))
  rw [regret_eq_coe_regretR, hR, EReal.coe_zero]

/- sanity check: the regret is nonnegative. -/
lemma regret_nonneg (L : MomentaryLoss A O) (γ : discount)
    (π : Policy A O) (μ : Environment A O) : 0 ≤ regret L γ π μ := by
  rw [regret_eq_coe_regretR]
  exact_mod_cast regretR_nonneg L γ π μ

/- We say a family of policies (indexed by `γ`) learns a class of environments if
the regret goes to zero as `γ` approaches `1` from below. -/
def LearnsEnvClass (L : MomentaryLoss A O) (I : Type*) (μ_fam : I → Environment A O)
    (π_fam : discount → Policy A O) :=
    ∀ (i : I), Filter.Tendsto
    (fun (γ : discount) => regret L γ (π_fam γ) (μ_fam i)) Filter.atTop (nhds 0)

/- The real-valued analogue of `LearnsEnvClass`, used by the Bayes machinery below. -/
def learnsEnvClassR (L : MomentaryLoss A O) (I : Type*) (μ_fam : I → Environment A O)
    (π_fam : discount → Policy A O) :=
    ∀ (i : I), Filter.Tendsto
    (fun (γ : discount) => regretR L γ (π_fam γ) (μ_fam i)) Filter.atTop (nhds 0)

/- The two notions agree: `ℝ → EReal` is a topological embedding, so `EReal`-convergence
of the coerced regret to `0 = ((0 : ℝ) : EReal)` is convergence of the real regret. -/
lemma learnsEnvClass_iff (L : MomentaryLoss A O) (I : Type*)
    (μ_fam : I → Environment A O) (π_fam : discount → Policy A O) :
    LearnsEnvClass L I μ_fam π_fam ↔ learnsEnvClassR L I μ_fam π_fam := by
  unfold LearnsEnvClass learnsEnvClassR
  refine forall_congr' fun i => ?_
  simp_rw [regret_eq_coe_regretR, ← EReal.coe_zero]
  exact EReal.tendsto_coe

/- sanity check that Filter.atTop over discount behaves as expected:
The identity function converges to 1 over discount as `γ` approaches `1` from below -/
lemma discount_atTop :
    Filter.Tendsto (Subtype.val : discount → ℝ) Filter.atTop (nhds 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_atTop]
  refine ⟨⟨max 0 (1 - ε / 2), ?_⟩, ?_⟩
  · rw [Set.mem_Ico]
    exact ⟨le_max_left _ _, max_lt (by norm_num) (by linarith)⟩
  · intro x hx
    have hxval : max 0 (1 - ε / 2) ≤ x.1 := hx
    have hx1 : x.1 < 1 := x.2.2
    have h2 : 1 - ε / 2 ≤ x.1 := le_trans (le_max_right _ _) hxval
    rw [Real.dist_eq, abs_of_nonpos (by linarith), neg_sub]
    linarith

/- sanity check: Filter.atTop over discount is not the trivial filter -/
lemma discount_atTop_neBot : (Filter.atTop : Filter discount).NeBot :=
  inferInstance

/- A class of environments is non-anytime learnable
if it can be learned by a family of policies. -/
def NonAnytimeLearnable (L : MomentaryLoss A O)
    (I : Type*) (μ_fam : I → Environment A O) :=
    ∃ π_fam, LearnsEnvClass L I μ_fam π_fam

/- The article talks about a prior `ζ` over environments, implemented as a
probability measure over an index type `I`. -/
def IsBayesOptimalPolicy (L : MomentaryLoss A O) (I : Type*)
  (μ_fam : I → Environment A O)
  [MeasurableSpace I] [DiscreteMeasurableSpace I] (ζ : ProbabilityMeasure I)
  (γ : discount) : Policy A O -> Prop :=
  fun π' => π' ∈ argminSet (fun π =>
    ∫ i, expectedTotalLoss L γ π (μ_fam i) ∂(ζ.toMeasure)
  )

/- sanity check: The integral in `IsBayesOptimalPolicy` is well-defined. -/
set_option linter.unusedSectionVars false in
lemma bayes_integrand_integrable
    (L : MomentaryLoss A O) (I : Type*) (μ_fam : I → Environment A O)
    [MeasurableSpace I] [DiscreteMeasurableSpace I] (ζ : ProbabilityMeasure I)
    (γ : discount) (π : Policy A O) :
    Integrable (fun i => expectedTotalLoss L γ π (μ_fam i)) ζ.toMeasure := by
  have hbound : ∀ i, ‖expectedTotalLoss L γ π (μ_fam i)‖ ≤ 1 := by
    intro i
    have hmem := Set.mem_Icc.mp (expectedTotalLoss_mem_unitInterval L γ π (μ_fam i))
    rw [Real.norm_eq_abs, abs_of_nonneg hmem.1]
    exact hmem.2
  exact Integrable.mono' (integrable_const (μ := ζ.toMeasure) 1)
    Measurable.of_discrete.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

/- Definition: a non-dogmatic prior -/
def NonDogmaticPrior (I : Type*)
  [MeasurableSpace I] [DiscreteMeasurableSpace I] (ζ : ProbabilityMeasure I) :
  Prop := ∀ (i : I), ζ {i} ≠ 0

/- Together with `regretR_nonneg`, the real regret lives in `[0, 1]`. -/
lemma regretR_le_one (L : MomentaryLoss A O) (γ : discount)
    (π : Policy A O) (μ : Environment A O) :
    regretR L γ π μ ≤ 1 := by
  unfold regretR
  have h1 := (expectedTotalLoss_mem_unitInterval L γ π μ).2
  have h2 := (expectedTotalLoss_mem_unitInterval L γ (best_policy L γ μ) μ).1
  linarith

/- Step 1 prerequisite: the π-independent term in the regret integral is integrable. -/
lemma best_loss_integrable (L : MomentaryLoss A O) (γ : discount)
    (I : Type*) (μ_fam : I → Environment A O)
    [MeasurableSpace I] [DiscreteMeasurableSpace I] (ζ : ProbabilityMeasure I) :
    Integrable (fun i => expectedTotalLoss L γ (best_policy L γ (μ_fam i)) (μ_fam i))
      ζ.toMeasure := by
  refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const 1)
    Measurable.of_discrete.aestronglyMeasurable (Filter.Eventually.of_forall fun i => ?_)
  have h := expectedTotalLoss_mem_unitInterval L γ (best_policy L γ (μ_fam i)) (μ_fam i)
  rw [Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2

/- Difference of two integrable functions. -/
lemma regretR_integrable (L : MomentaryLoss A O) (γ : discount)
    (I : Type*) (μ_fam : I → Environment A O)
    [MeasurableSpace I] [DiscreteMeasurableSpace I] (ζ : ProbabilityMeasure I)
    (π : Policy A O) :
    Integrable (fun i => regretR L γ π (μ_fam i)) ζ.toMeasure := by
  exact (bayes_integrand_integrable L I μ_fam ζ γ π).sub (best_loss_integrable L γ I μ_fam ζ)

/- Step 1: Bayes regret is Bayes loss minus a π-independent constant. -/
lemma integral_regretR_eq (L : MomentaryLoss A O) (γ : discount)
    (I : Type*) (μ_fam : I → Environment A O)
    [MeasurableSpace I] [DiscreteMeasurableSpace I] (ζ : ProbabilityMeasure I)
    (π : Policy A O) :
    ∫ i, regretR L γ π (μ_fam i) ∂ζ.toMeasure
      = (∫ i, expectedTotalLoss L γ π (μ_fam i) ∂ζ.toMeasure)
        - ∫ i, expectedTotalLoss L γ (best_policy L γ (μ_fam i)) (μ_fam i) ∂ζ.toMeasure := by
  exact MeasureTheory.integral_sub (bayes_integrand_integrable L I μ_fam ζ γ π)
    (best_loss_integrable L γ I μ_fam ζ)

/- Step 1: a Bayes-optimal Policy minimizes Bayes regret. -/
lemma bayes_optimal_integral_regretR_le (L : MomentaryLoss A O) (γ : discount)
    (I : Type*) (μ_fam : I → Environment A O)
    [MeasurableSpace I] [DiscreteMeasurableSpace I] (ζ : ProbabilityMeasure I)
    {π' : Policy A O} (h_opt : IsBayesOptimalPolicy L I μ_fam ζ γ π')
    (π : Policy A O) :
    ∫ i, regretR L γ π' (μ_fam i) ∂ζ.toMeasure
      ≤ ∫ i, regretR L γ π (μ_fam i) ∂ζ.toMeasure := by
  rw [integral_regretR_eq, integral_regretR_eq]
  exact sub_le_sub_right (h_opt π) _

/- Step 2a: `atTop` on `discount` is countably generated. -/
instance discount_atTop_isCountablyGenerated :
    (Filter.atTop : Filter discount).IsCountablyGenerated := by
  infer_instance

/- Step 2b: dominated convergence along `atTop : Filter discount`. -/
lemma integral_regret_tendsto_zero (L : MomentaryLoss A O)
    (I : Type*) (μ_fam : I → Environment A O)
    [MeasurableSpace I] [DiscreteMeasurableSpace I] (ζ : ProbabilityMeasure I)
    (π_fam : discount → Policy A O)
    (h_learns : learnsEnvClassR L I μ_fam π_fam) :
    Filter.Tendsto (fun γ : discount => ∫ i, regretR L γ (π_fam γ) (μ_fam i) ∂ζ.toMeasure)
      Filter.atTop (nhds 0) := by
  have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := ζ.toMeasure)
    (F := fun (γ : discount) i => regretR L γ (π_fam γ) (μ_fam i)) (f := fun _ => (0 : ℝ))
    (bound := fun _ => 1)
    (Filter.Eventually.of_forall fun γ => Measurable.of_discrete.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun γ => Filter.Eventually.of_forall fun i => by
      rw [Real.norm_eq_abs, abs_of_nonneg (regretR_nonneg L γ (π_fam γ) (μ_fam i))]
      exact regretR_le_one L γ (π_fam γ) (μ_fam i))
    (MeasureTheory.integrable_const 1)
    (Filter.Eventually.of_forall fun i => h_learns i)
  simpa using h

/- Step 3: Markov-type bound extracting one Environment. -/
lemma mass_mul_regretR_le_integral (L : MomentaryLoss A O) (γ : discount)
    (I : Type*) (μ_fam : I → Environment A O)
    [MeasurableSpace I] [DiscreteMeasurableSpace I] (ζ : ProbabilityMeasure I)
    (π : Policy A O) (i : I) :
    (ζ {i} : ℝ) * regretR L γ π (μ_fam i)
      ≤ ∫ j, regretR L γ π (μ_fam j) ∂ζ.toMeasure := by
  have h := MeasureTheory.setIntegral_le_integral (s := {i})
    (regretR_integrable L γ I μ_fam ζ π)
    (Filter.Eventually.of_forall fun j => regretR_nonneg L γ π (μ_fam j))
  simpa [MeasureTheory.integral_singleton, mul_comm, NNReal.smul_def,
    ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using h

/- Generic squeeze finishing the main theorem. -/
lemma tendsto_zero_of_nonneg_of_mul_le {ι : Type*} {l : Filter ι} {f g : ι → ℝ} {c : ℝ}
    (hc : 0 < c) (hf : ∀ x, 0 ≤ f x) (hfg : ∀ x, c * f x ≤ g x)
    (hg : Filter.Tendsto g l (nhds 0)) :
    Filter.Tendsto f l (nhds 0) := by
  exact squeeze_zero (g := fun x => g x / c) hf
    (fun x => (le_div_iff₀ hc).mpr (by linarith [hfg x])) (by simpa using hg.div_const c)

/- Proposition 2, for the real-valued regret: the whole quantitative argument. -/
theorem bayes_optimal_learns_classR
    (L : MomentaryLoss A O) (I : Type*) (μ_fam : I → Environment A O)
    [MeasurableSpace I] [DiscreteMeasurableSpace I] (ζ : ProbabilityMeasure I)
    (h_learnable : ∃ π_fam', learnsEnvClassR L I μ_fam π_fam')
    (h_non_dog : NonDogmaticPrior I ζ)
    (π_fam : discount → Policy A O)
    (h_bayes_optimal : ∀ γ, IsBayesOptimalPolicy L I μ_fam ζ γ (π_fam γ))
    : learnsEnvClassR L I μ_fam π_fam := by
  intro i
  obtain ⟨π_fam', h_learns⟩ := h_learnable
  have hg : Filter.Tendsto (fun γ : discount => ∫ j, regretR L γ (π_fam γ) (μ_fam j) ∂ζ.toMeasure)
      Filter.atTop (nhds 0) :=
    squeeze_zero
      (fun γ => MeasureTheory.integral_nonneg fun j => regretR_nonneg L γ (π_fam γ) (μ_fam j))
      (fun γ => bayes_optimal_integral_regretR_le L γ I μ_fam ζ (h_bayes_optimal γ) (π_fam' γ))
      (integral_regret_tendsto_zero L I μ_fam ζ π_fam' h_learns)
  have hc : (0 : ℝ) < (ζ {i} : ℝ) := by
    have h0 : 0 < ζ {i} := pos_iff_ne_zero.mpr (h_non_dog i)
    exact_mod_cast h0
  exact tendsto_zero_of_nonneg_of_mul_le hc
    (fun γ => regretR_nonneg L γ (π_fam γ) (μ_fam i))
    (fun γ => mass_mul_regretR_le_integral L γ I μ_fam ζ (π_fam γ) i)
    hg

/- Proposition 2:
A bayes-optimal Policy learns an Environment class if the prior is non-dogmatic.
Transported from the real-valued version through `learnsEnvClass_iff`. -/
theorem bayes_optimal_learns_class
    (L : MomentaryLoss A O) (I : Type*) (μ_fam : I → Environment A O)
    [MeasurableSpace I] [DiscreteMeasurableSpace I] (ζ : ProbabilityMeasure I)
    (h_learnable : NonAnytimeLearnable L I μ_fam)
    (h_non_dog : NonDogmaticPrior I ζ)
    (π_fam : discount → Policy A O)
    (h_bayes_optimal : ∀ γ, IsBayesOptimalPolicy L I μ_fam ζ γ (π_fam γ))
    : LearnsEnvClass L I μ_fam π_fam := by
  rw [learnsEnvClass_iff]
  obtain ⟨π_fam', h_learns⟩ := h_learnable
  exact bayes_optimal_learns_classR L I μ_fam ζ
    ⟨π_fam', (learnsEnvClass_iff L I μ_fam π_fam').mp h_learns⟩
    h_non_dog π_fam h_bayes_optimal

end Regret

end IB_RL
