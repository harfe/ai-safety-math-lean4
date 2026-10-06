module
public import AISafetyMath.Solutions.NL_Conjecture.DLorell.Main
public import AISafetyMath.Solutions.NL_Conjecture.Conjecture

/-!
# Bridge lemmas: `stoch_to_det` ↔ `NaturalLatents`

DRAFT — sorry-stubbed skeletons, not proofs.

Connects `stoch_to_det.T_le_Cstar` (real-valued PMFs, `Latent p`, bits via
`Real.logb 2`) to `NaturalLatents.MainConjecture` (`ProbabilityMeasure`,
`ENNReal`-valued KL/entropy quantities, nats).

The files under `NL_Conjecture/DLorell/` are from
https://github.com/DLorell/stoch_to_det, © the original authors; the glue
code connecting them to `NaturalLatents` in this file is original.
-/

@[expose] public section

namespace NaturalLatents.Bridge

open stoch_to_det MeasureTheory ProbabilityTheory

variable {X Y : Type} [Finite X] [Finite Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [DiscreteMeasurableSpace X] [DiscreteMeasurableSpace Y]

noncomputable local instance instFintypeX : Fintype X := Fintype.ofFinite X
noncomputable local instance instFintypeY : Fintype Y := Fintype.ofFinite Y
noncomputable local instance instDecEqX : DecidableEq X := Classical.decEq X
noncomputable local instance instDecEqY : DecidableEq Y := Classical.decEq Y

/-- §1. A `ProbabilityMeasure` on a finite discrete-measurable type induces a
real-valued PMF in `stoch_to_det`'s sense. -/
noncomputable def pmfOfMeasure (P : ProbabilityMeasure (X × Y)) : X × Y → ℝ :=
  fun z => (P.toMeasure {z}).toReal

theorem pmfOfMeasure_isPMF (P : ProbabilityMeasure (X × Y)) :
    stoch_to_det.IsPMF (pmfOfMeasure P) := by
  refine ⟨fun z => ENNReal.toReal_nonneg, ?_⟩
  unfold stoch_to_det.mass pmfOfMeasure
  have h := MeasureTheory.sum_measureReal_singleton (μ := P.toMeasure)
    (Finset.univ : Finset (X × Y))
  simp only [Finset.coe_univ, Measure.real] at h
  rw [h]
  simp only [measure_univ, ENNReal.toReal_one]

/-- §2. Conversely, a `stoch_to_det` PMF induces a `ProbabilityMeasure`. -/
noncomputable def measureOfPMF {p : X × Y → ℝ} (hp : stoch_to_det.IsPMF p) :
    ProbabilityMeasure (X × Y) :=
  have hsum : ∑ z, ENNReal.ofReal (p z) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => hp.nonneg z),
      show ∑ z, p z = mass p from rfl, hp.total, ENNReal.ofReal_one]
  ⟨(PMF.ofFintype (fun z => ENNReal.ofReal (p z)) hsum).toMeasure,
    PMF.toMeasure.isProbabilityMeasure _⟩

/-- The atoms of `measureOfPMF hp` carry mass `ENNReal.ofReal (p z)`. -/
theorem measureOfPMF_singleton {p : X × Y → ℝ} (hp : stoch_to_det.IsPMF p) (z : X × Y) :
    (measureOfPMF hp).toMeasure {z} = ENNReal.ofReal (p z) := by
  simp only [measureOfPMF, ProbabilityMeasure.coe_mk]
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton z), PMF.ofFintype_apply]

theorem pmfOfMeasure_measureOfPMF {p : X × Y → ℝ} (hp : stoch_to_det.IsPMF p) :
    pmfOfMeasure (measureOfPMF hp) = p := by
  funext z
  rw [pmfOfMeasure, measureOfPMF_singleton hp z, ENNReal.toReal_ofReal (hp.nonneg z)]

theorem measureOfPMF_pmfOfMeasure (P : ProbabilityMeasure (X × Y)) :
    measureOfPMF (pmfOfMeasure_isPMF P) = P := by
  apply ProbabilityMeasure.toMeasure_injective
  apply MeasureTheory.Measure.ext_of_singleton
  intro z
  simp only [measureOfPMF, ProbabilityMeasure.coe_mk]
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton z), PMF.ofFintype_apply]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

/-- §3. Unit conversion: nats (`Real.log`, `ENNReal`) to bits (`Real.logb 2`, `ℝ`). -/
noncomputable def natsToBits (x : ENNReal) : ℝ := x.toReal / Real.log 2

/-- Pushing `pmfOfMeasure P` forward along `f` computes the measure of the fiber. -/
theorem push_pmfOfMeasure {γ : Type} [DecidableEq γ] (P : ProbabilityMeasure (X × Y))
    (f : X × Y → γ) (c : γ) :
    stoch_to_det.push f (pmfOfMeasure P) c = (P.toMeasure {y | f y = c}).toReal := by
  have h := MeasureTheory.sum_measureReal_singleton (μ := P.toMeasure)
    (Finset.univ.filter (fun z : X × Y => f z = c))
  simp only [Measure.real] at h
  simp only [stoch_to_det.push, pmfOfMeasure]
  rw [h]
  congr 2
  ext z
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]

/-- `push` along the identity (written as `fun w => (w.1, w.2)`) is the identity. -/
theorem push_prod_mk (P : ProbabilityMeasure (X × Y)) :
    stoch_to_det.push (fun w : X × Y => (w.1, w.2)) (pmfOfMeasure P) = pmfOfMeasure P := by
  funext c
  rw [push_pmfOfMeasure]
  simp only [pmfOfMeasure]
  congr 2

omit [Finite X] [Finite Y] [DiscreteMeasurableSpace X] [DiscreteMeasurableSpace Y] in
/-- Each singleton has at most the mass of its `Y`-fiber. -/
theorem pmfOfMeasure_le_marginal (P : ProbabilityMeasure (X × Y)) (z : X × Y) :
    pmfOfMeasure P z ≤ (P.toMeasure {y : X × Y | y.2 = z.2}).toReal :=
  ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (by intro y hy; simp only [Set.mem_singleton_iff] at hy; simp [hy]))

/-- §4c, real side: `condH` for the two coordinate projections of `pmfOfMeasure P`. -/
theorem condH_pmfOfMeasure (P : ProbabilityMeasure (X × Y)) :
    stoch_to_det.condH (fun w : X × Y => w.1) (fun w => w.2) (pmfOfMeasure P) =
      ∑ z, pmfOfMeasure P z *
        lg ((P.toMeasure {y : X × Y | y.2 = z.2}).toReal / pmfOfMeasure P z) := by
  have hm := pmfOfMeasure_isPMF P
  have hmass2 : stoch_to_det.mass (stoch_to_det.push (fun w : X × Y => w.2) (pmfOfMeasure P)) = 1 :=
    by rw [stoch_to_det.mass_push]; exact hm.total
  -- the marginal term, re-indexed over `X × Y` by fibers
  have hfib : ∑ b : Y, (P.toMeasure {y : X × Y | y.2 = b}).toReal *
        lg (1 / (P.toMeasure {y : X × Y | y.2 = b}).toReal) =
      ∑ z : X × Y, pmfOfMeasure P z *
        lg (1 / (P.toMeasure {y : X × Y | y.2 = z.2}).toReal) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun z : X × Y => z.2)
      (fun z => pmfOfMeasure P z * lg (1 / (P.toMeasure {y : X × Y | y.2 = z.2}).toReal))]
    refine Finset.sum_congr rfl fun b _ => ?_
    nth_rewrite 1 [← push_pmfOfMeasure P (fun w : X × Y => w.2) b]
    rw [stoch_to_det.push, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [(Finset.mem_filter.mp hz).2]
  rw [stoch_to_det.condH, stoch_to_det.Hvar, stoch_to_det.Hvar, push_prod_mk, stoch_to_det.H,
    stoch_to_det.H, hm.total, hmass2]
  simp only [push_pmfOfMeasure]
  rw [hfib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  rcases eq_or_lt_of_le (ENNReal.toReal_nonneg (a := P.toMeasure {z})) with h0 | hpos
  · simp only [pmfOfMeasure, ← h0, zero_mul, sub_zero]
  · have hu : (0 : ℝ) < pmfOfMeasure P z := hpos
    have hv : (0 : ℝ) < (P.toMeasure {y : X × Y | y.2 = z.2}).toReal :=
      lt_of_lt_of_le hu (pmfOfMeasure_le_marginal P z)
    rw [← mul_sub]
    congr 1
    rw [lg_eq_log_div, lg_eq_log_div, lg_eq_log_div, Real.log_div hv.ne' hu.ne', one_div, one_div,
      Real.log_inv, Real.log_inv]
    ring

private lemma ereal_coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, ((f i : ℝ) : EReal) := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, EReal.coe_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, EReal.coe_add, ih]

/-- §4c, `ENNReal` side: each summand of `condEntropy` in real form. -/
theorem condEntropy_term (P : ProbabilityMeasure (X × Y)) (x : X × Y) :
    (↑(P.1 {x}) * ENNReal.log (P.1[{y : X × Y | y.1 = x.1} | {y : X × Y | y.2 = x.2}]) : EReal) =
      ((-(pmfOfMeasure P x *
        Real.log ((P.toMeasure {y : X × Y | y.2 = x.2}).toReal / pmfOfMeasure P x)) : ℝ)
          : EReal) := by
  have : IsProbabilityMeasure (P.1 : Measure (X × Y)) := P.2
  have hinter : {y : X × Y | y.2 = x.2} ∩ {y : X × Y | y.1 = x.1} = {x} := by
    ext y; simp [Prod.ext_iff, and_comm]
  have hmarg : P.toMeasure {y : X × Y | y.2 = x.2} = P.1 {y : X × Y | y.2 = x.2} := rfl
  have hpm : pmfOfMeasure P x = (P.1 {x}).toReal := rfl
  rw [ProbabilityTheory.cond_apply .of_discrete, hinter, hmarg, hpm]
  rcases eq_or_ne (P.1 {x}) 0 with h0 | h0
  · rw [h0]
    simp only [EReal.coe_ennreal_zero, ProbabilityMeasure.val_eq_to_measure, mul_zero,
        ENNReal.log_zero, zero_mul, ENNReal.toReal_zero, div_zero, Real.log_zero, neg_zero,
        EReal.coe_zero]
  · have hvne : P.1 {y : X × Y | y.2 = x.2} ≠ 0 := by
      refine fun h => h0 (le_zero_iff.mp (h ▸ measure_mono ?_))
      intro y hy; simp only [Set.mem_singleton_iff] at hy; simp [hy]
    have hne : (P.1 {y : X × Y | y.2 = x.2})⁻¹ * P.1 {x} ≠ 0 :=
      mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) h0
    have htop : (P.1 {y : X × Y | y.2 = x.2})⁻¹ * P.1 {x} ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hvne) (measure_ne_top _ _)
    rw [ENNReal.log_pos_real hne htop, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ← EReal.coe_ennreal_toReal (measure_ne_top _ _), ← EReal.coe_mul, EReal.coe_eq_coe_iff]
    have hu : (0 : ℝ) < (P.1 {x}).toReal :=
      ENNReal.toReal_pos h0 (measure_ne_top _ _)
    have hv : (0 : ℝ) < (P.1 {y : X × Y | y.2 = x.2}).toReal :=
      lt_of_lt_of_le hu (pmfOfMeasure_le_marginal P x)
    rw [Real.log_mul (by positivity) hu.ne', Real.log_inv, Real.log_div hv.ne' hu.ne']
    ring

/-- §4c, `ENNReal` side: `condEntropy` as a real number. -/
theorem condEntropy_eq_coe (P : ProbabilityMeasure (X × Y)) :
    condEntropy P = ((∑ z : X × Y, pmfOfMeasure P z *
      Real.log ((P.toMeasure {y : X × Y | y.2 = z.2}).toReal / pmfOfMeasure P z) : ℝ) : EReal) := by
  rw [condEntropy_eq_sum]
  rw [Finset.sum_congr rfl fun x _ => condEntropy_term P x]
  rw [← ereal_coe_sum, Finset.sum_neg_distrib, EReal.coe_neg, neg_neg]

section Atomic

variable {Z : Type} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

omit [Finite X] [Finite Y] [DiscreteMeasurableSpace X] [DiscreteMeasurableSpace Y] in
/-- The real-valued pmf attached to a `ProbabilityMeasure` on a finite space with
measurable singletons. Agrees with `pmfOfMeasure` by definition. -/
theorem pmfOfMeasure_eq_atomic (P : ProbabilityMeasure (X × Y)) :
    pmfOfMeasure P = fun z => (P.toMeasure {z}).toReal := rfl

/-- Generic version of `pmfOfMeasure_isPMF` for an arbitrary finite atomic space. -/
theorem atomic_isPMF (P : ProbabilityMeasure Z) :
    stoch_to_det.IsPMF (fun z => (P.toMeasure {z}).toReal) := by
  refine ⟨fun z => ENNReal.toReal_nonneg, ?_⟩
  unfold stoch_to_det.mass
  have h := MeasureTheory.sum_measureReal_singleton (μ := P.toMeasure) (Finset.univ : Finset Z)
  simp only [Finset.coe_univ, Measure.real] at h
  rw [h]
  simp only [measure_univ, ENNReal.toReal_one]

/-- Generic version of `push_pmfOfMeasure`. -/
theorem push_atomic {γ : Type} [DecidableEq γ] (P : ProbabilityMeasure Z) (f : Z → γ) (c : γ) :
    stoch_to_det.push f (fun z => (P.toMeasure {z}).toReal) c =
      (P.toMeasure {y | f y = c}).toReal := by
  have h := MeasureTheory.sum_measureReal_singleton (μ := P.toMeasure)
    (Finset.univ.filter (fun z : Z => f z = c))
  simp only [Measure.real] at h
  simp only [stoch_to_det.push]
  rw [h]
  congr 2
  ext z
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]

omit [MeasurableSingletonClass Z] in
/-- Re-indexing a `push`-weighted sum over the fibers of `f`. -/
theorem sum_push_atomic {γ : Type} [Fintype γ] [DecidableEq γ] (P : ProbabilityMeasure Z)
    (f : Z → γ) (g : γ → ℝ) :
    ∑ c, stoch_to_det.push f (fun z => (P.toMeasure {z}).toReal) c * g c =
      ∑ z, (P.toMeasure {z}).toReal * g (f z) := by
  rw [← Finset.sum_fiberwise Finset.univ f (fun z => (P.toMeasure {z}).toReal * g (f z))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [stoch_to_det.push, Finset.sum_mul]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [(Finset.mem_filter.mp hz).2]

/-- `Hvar` of a variable `f`, written as a sum over the underlying space. -/
theorem Hvar_atomic {γ : Type} [Fintype γ] [DecidableEq γ] (P : ProbabilityMeasure Z)
    (f : Z → γ) :
    stoch_to_det.Hvar f (fun z => (P.toMeasure {z}).toReal) =
      ∑ z, (P.toMeasure {z}).toReal * lg (1 / (P.toMeasure {y | f y = f z}).toReal) := by
  have hmass : stoch_to_det.mass (stoch_to_det.push f (fun z => (P.toMeasure {z}).toReal)) = 1 := by
    rw [stoch_to_det.mass_push]; exact (atomic_isPMF P).total
  rw [stoch_to_det.Hvar, stoch_to_det.H, hmass]
  rw [sum_push_atomic P f (fun c => lg (1 / stoch_to_det.push f
    (fun z => (P.toMeasure {z}).toReal) c))]
  exact Finset.sum_congr rfl fun z _ => by rw [push_atomic]

omit [Fintype Z] in
/-- On a space with measurable singletons, the Radon–Nikodym derivative at an atom
satisfies `(∂μ/∂ν) z * ν {z} = μ {z}`. -/
theorem rnDeriv_mul_singleton (μ ν : Measure Z) [SigmaFinite μ] [SigmaFinite ν]
    (hac : μ ≪ ν) (z : Z) : μ.rnDeriv ν z * ν {z} = μ {z} := by
  conv_rhs => rw [← Measure.withDensity_rnDeriv_eq μ ν hac]
  rw [withDensity_apply _ (measurableSet_singleton z),
    lintegral_singleton' (μ.measurable_rnDeriv ν)]

omit [Fintype Z] in
/-- On a finite atomic space, absolute continuity is a pointwise condition on atoms. -/
theorem absolutelyContinuous_of_singleton [Finite Z] (μ ν : Measure Z)
    (h : ∀ z, ν {z} = 0 → μ {z} = 0) : μ ≪ ν := by
  classical
  have := Fintype.ofFinite Z
  intro s hs
  have hset : μ s = ∑ z ∈ s.toFinset, μ {z} := by
    rw [MeasureTheory.sum_measure_singleton]
    congr 1
    simp only [Set.coe_toFinset]
  rw [hset]
  refine Finset.sum_eq_zero fun z hz => h z (measure_mono_null ?_ hs)
  simpa using Set.mem_toFinset.mp hz

/-- The KL divergence between two probability measures on a finite atomic space, as a
real-valued sum. The `hac` hypothesis makes the usual `0 · log(0/0) = 0` convention
automatic. -/
theorem klDiv_toReal_eq_sum (μ ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) :
    (InformationTheory.klDiv μ ν).toReal =
      ∑ z, (μ {z}).toReal * Real.log ((μ {z}).toReal / (ν {z}).toReal) := by
  rw [InformationTheory.toReal_klDiv_of_measure_eq hac (by simp only [measure_univ]),
    integral_fintype MeasureTheory.Integrable.of_finite]
  refine Finset.sum_congr rfl fun z _ => ?_
  rcases eq_or_ne (ν {z}) 0 with h0 | h0
  · have hμ0 : μ {z} = 0 := hac (by simpa using h0)
    simp [Measure.real, hμ0]
  · have hd : μ.rnDeriv ν z = μ {z} / ν {z} := by
      rw [ENNReal.eq_div_iff h0 (measure_ne_top _ _), mul_comm]
      exact rnDeriv_mul_singleton μ ν hac z
    simp only [llr_def, Measure.real, smul_eq_mul, hd, ENNReal.toReal_div]

end Atomic

section ForkChain

variable {A B C : Type} [Finite A] [Finite B] [Finite C]
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  [DiscreteMeasurableSpace A] [DiscreteMeasurableSpace B] [DiscreteMeasurableSpace C]

omit [Finite A] [Finite B] [Finite C] [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [DiscreteMeasurableSpace A] [DiscreteMeasurableSpace B]
  [DiscreteMeasurableSpace C] in
/-- A singleton is contained in each of its "marginal" sets. -/
private theorem singleton_subset (x : A × B × C) (s : Set (A × B × C)) (hx : x ∈ s) :
    ({x} : Set (A × B × C)) ⊆ s := by
  intro y hy; simp only [Set.mem_singleton_iff] at hy; exact hy ▸ hx

/-- The fork reference density at an atom of positive mass. -/
theorem forkDistr_singleton (P : ProbabilityMeasure (A × B × C)) (x : A × B × C)
    (hx : P.toMeasure {x} ≠ 0) :
    (forkDistr P).toMeasure {x} =
      P.toMeasure {y : A × B × C | y.1 = x.1 ∧ y.2.1 = x.2.1} *
        P.toMeasure {y : A × B × C | y.1 = x.1 ∧ y.2.2 = x.2.2} /
        P.toMeasure {y : A × B × C | y.1 = x.1} := by
  have hA : P.toMeasure {y : A × B × C | y.1 = x.1} ≠ 0 := fun h =>
    hx (le_zero_iff.mp (h ▸ measure_mono (singleton_subset x _ rfl)))
  have hint1 : {y : A × B × C | y.1 = x.1} ∩ {y : A × B × C | y.2.1 = x.2.1} =
      {y : A × B × C | y.1 = x.1 ∧ y.2.1 = x.2.1} := rfl
  have hint2 : {y : A × B × C | y.1 = x.1} ∩ {y : A × B × C | y.2.2 = x.2.2} =
      {y : A × B × C | y.1 = x.1 ∧ y.2.2 = x.2.2} := rfl
  rw [ok_forkDistr, forkDensity, cond_apply .of_discrete, cond_apply .of_discrete, hint1, hint2,
    ENNReal.div_eq_inv_mul]
  rw [show P.toMeasure {y : A × B × C | y.1 = x.1} *
      ((P.toMeasure {y : A × B × C | y.1 = x.1})⁻¹ *
        P.toMeasure {y : A × B × C | y.1 = x.1 ∧ y.2.1 = x.2.1}) *
      ((P.toMeasure {y : A × B × C | y.1 = x.1})⁻¹ *
        P.toMeasure {y : A × B × C | y.1 = x.1 ∧ y.2.2 = x.2.2}) =
      (P.toMeasure {y : A × B × C | y.1 = x.1} *
        (P.toMeasure {y : A × B × C | y.1 = x.1})⁻¹) *
      ((P.toMeasure {y : A × B × C | y.1 = x.1})⁻¹ *
        (P.toMeasure {y : A × B × C | y.1 = x.1 ∧ y.2.1 = x.2.1} *
          P.toMeasure {y : A × B × C | y.1 = x.1 ∧ y.2.2 = x.2.2})) by ring,
    ENNReal.mul_inv_cancel hA (measure_ne_top _ _), one_mul]

/-- The chain reference density at an atom of positive mass. -/
theorem chainDistr_singleton (P : ProbabilityMeasure (A × B × C)) (x : A × B × C)
    (hx : P.toMeasure {x} ≠ 0) :
    (chainDistr P).toMeasure {x} =
      P.toMeasure {y : A × B × C | y.1 = x.1 ∧ y.2.1 = x.2.1} *
        P.toMeasure {y : A × B × C | y.2.1 = x.2.1 ∧ y.2.2 = x.2.2} /
        P.toMeasure {y : A × B × C | y.2.1 = x.2.1} := by
  have hA : P.toMeasure {y : A × B × C | y.1 = x.1} ≠ 0 := fun h =>
    hx (le_zero_iff.mp (h ▸ measure_mono (singleton_subset x _ rfl)))
  have hint1 : {y : A × B × C | y.1 = x.1} ∩ {y : A × B × C | y.2.1 = x.2.1} =
      {y : A × B × C | y.1 = x.1 ∧ y.2.1 = x.2.1} := rfl
  have hint2 : {y : A × B × C | y.2.1 = x.2.1} ∩ {y : A × B × C | y.2.2 = x.2.2} =
      {y : A × B × C | y.2.1 = x.2.1 ∧ y.2.2 = x.2.2} := rfl
  rw [ok_chainDistr, chainDensity, cond_apply .of_discrete, cond_apply .of_discrete, hint1, hint2,
    ENNReal.div_eq_inv_mul]
  rw [show P.toMeasure {y : A × B × C | y.1 = x.1} *
      ((P.toMeasure {y : A × B × C | y.1 = x.1})⁻¹ *
        P.toMeasure {y : A × B × C | y.1 = x.1 ∧ y.2.1 = x.2.1}) *
      ((P.toMeasure {y : A × B × C | y.2.1 = x.2.1})⁻¹ *
        P.toMeasure {y : A × B × C | y.2.1 = x.2.1 ∧ y.2.2 = x.2.2}) =
      (P.toMeasure {y : A × B × C | y.1 = x.1} *
        (P.toMeasure {y : A × B × C | y.1 = x.1})⁻¹) *
      ((P.toMeasure {y : A × B × C | y.2.1 = x.2.1})⁻¹ *
        (P.toMeasure {y : A × B × C | y.1 = x.1 ∧ y.2.1 = x.2.1} *
          P.toMeasure {y : A × B × C | y.2.1 = x.2.1 ∧ y.2.2 = x.2.2})) by ring,
    ENNReal.mul_inv_cancel hA (measure_ne_top _ _), one_mul]

/-- Every distribution on a finite discrete space is absolutely continuous with respect
to its own fork reference measure. -/
theorem absolutelyContinuous_forkDistr (P : ProbabilityMeasure (A × B × C)) :
    P.toMeasure ≪ (forkDistr P).toMeasure := by
  refine absolutelyContinuous_of_singleton _ _ fun x h => ?_
  by_contra hx
  have hAB : P.toMeasure {y : A × B × C | y.1 = x.1 ∧ y.2.1 = x.2.1} ≠ 0 := fun h' =>
    hx (le_zero_iff.mp (h' ▸ measure_mono (singleton_subset x _ ⟨rfl, rfl⟩)))
  have hAC : P.toMeasure {y : A × B × C | y.1 = x.1 ∧ y.2.2 = x.2.2} ≠ 0 := fun h' =>
    hx (le_zero_iff.mp (h' ▸ measure_mono (singleton_subset x _ ⟨rfl, rfl⟩)))
  rw [forkDistr_singleton P x hx, ENNReal.div_eq_zero_iff] at h
  rcases h with h | h
  · exact (mul_ne_zero hAB hAC) h
  · exact (measure_ne_top _ _) h

/-- Every distribution on a finite discrete space is absolutely continuous with respect
to its own chain reference measure. -/
theorem absolutelyContinuous_chainDistr (P : ProbabilityMeasure (A × B × C)) :
    P.toMeasure ≪ (chainDistr P).toMeasure := by
  refine absolutelyContinuous_of_singleton _ _ fun x h => ?_
  by_contra hx
  have hAB : P.toMeasure {y : A × B × C | y.1 = x.1 ∧ y.2.1 = x.2.1} ≠ 0 := fun h' =>
    hx (le_zero_iff.mp (h' ▸ measure_mono (singleton_subset x _ ⟨rfl, rfl⟩)))
  have hBC : P.toMeasure {y : A × B × C | y.2.1 = x.2.1 ∧ y.2.2 = x.2.2} ≠ 0 := fun h' =>
    hx (le_zero_iff.mp (h' ▸ measure_mono (singleton_subset x _ ⟨rfl, rfl⟩)))
  rw [chainDistr_singleton P x hx, ENNReal.div_eq_zero_iff] at h
  rcases h with h | h
  · exact (mul_ne_zero hAB hBC) h
  · exact (measure_ne_top _ _) h

/-- `forkApproxError` is finite on a finite discrete space. -/
theorem forkApproxError_ne_top (P : ProbabilityMeasure (A × B × C)) :
    forkApproxError P ≠ ⊤ :=
  InformationTheory.klDiv_ne_top (absolutelyContinuous_forkDistr P)
    (MeasureTheory.Integrable.of_finite)

/-- `chainApproxError` is finite on a finite discrete space. -/
theorem chainApproxError_ne_top (P : ProbabilityMeasure (A × B × C)) :
    chainApproxError P ≠ ⊤ :=
  InformationTheory.klDiv_ne_top (absolutelyContinuous_chainDistr P)
    (MeasureTheory.Integrable.of_finite)

/-- `swapABProb` moves atoms along `swapAB`. -/
theorem swapABProb_singleton (P : ProbabilityMeasure (A × B × C)) (w : A × B × C) :
    (swapABProb P).toMeasure {swapAB w} = P.toMeasure {w} := by
  have hpre : (swapAB ⁻¹' ({swapAB w} : Set (B × A × C))) = ({w} : Set (A × B × C)) := by
    ext y; simp only [Set.mem_preimage, Set.mem_singleton_iff, swapAB, Prod.ext_iff]; tauto
  rw [← hpre]
  exact P.map_apply' AEMeasurable.of_discrete MeasurableSet.of_discrete

/-- `swapBCProb` moves atoms along `swapBC`. -/
theorem swapBCProb_singleton (P : ProbabilityMeasure (A × B × C)) (w : A × B × C) :
    (swapBCProb P).toMeasure {swapBC w} = P.toMeasure {w} := by
  have hpre : (swapBC ⁻¹' ({swapBC w} : Set (A × C × B))) = ({w} : Set (A × B × C)) := by
    ext y; simp only [Set.mem_preimage, Set.mem_singleton_iff, swapBC, Prod.ext_iff]; tauto
  rw [← hpre]
  exact P.map_apply' AEMeasurable.of_discrete MeasurableSet.of_discrete

/-- `swapACProb` reverses the three coordinates of an atom. -/
theorem swapACProb_singleton (P : ProbabilityMeasure (A × B × C)) (w : A × B × C) :
    (swapACProb P).toMeasure {(w.2.2, w.2.1, w.1)} = P.toMeasure {w} := by
  rw [swapACProb, show ((w.2.2, w.2.1, w.1) : C × B × A) = swapBC (swapAB (swapBC w)) from rfl,
    swapBCProb_singleton, swapABProb_singleton, swapBCProb_singleton]

end ForkChain

/-- §4a. `forkApproxError` (KL divergence, nats) is the conditional mutual
information `I(B;C∣A)` (bits), up to the nats→bits factor. Core identity
underlying `isNatLatentAux`'s fork condition:
`klDiv P (forkDistr P) = log 2 · I(B;C∣A)`. -/
theorem forkApproxError_eq_condMI {A B C : Type} [Finite A] [Finite B] [Finite C]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [DiscreteMeasurableSpace A] [DiscreteMeasurableSpace B] [DiscreteMeasurableSpace C]
    (P : ProbabilityMeasure (A × B × C)) :
    haveI : Fintype A := Fintype.ofFinite A
    haveI : Fintype B := Fintype.ofFinite B
    haveI : Fintype C := Fintype.ofFinite C
    haveI : DecidableEq A := Classical.decEq A
    haveI : DecidableEq B := Classical.decEq B
    haveI : DecidableEq C := Classical.decEq C
    natsToBits (forkApproxError P) =
      stoch_to_det.condMI (fun w : A × B × C => w.2.1) (fun w => w.2.2) (fun w => w.1)
        (pmfOfMeasure (P : ProbabilityMeasure (A × (B × C)))) := by
  classical
  let _ : Fintype A := Fintype.ofFinite A
  let _ : Fintype B := Fintype.ofFinite B
  let _ : Fintype C := Fintype.ofFinite C
  have : IsProbabilityMeasure (P.toMeasure) := P.2
  have : IsProbabilityMeasure ((forkDistr P).toMeasure) := (forkDistr P).2
  -- the three "marginal" sets attached to a point, and the containment `{x} ⊆ ·`
  have hsubA : ∀ x : A × B × C, ({x} : Set (A × B × C)) ⊆ {y | y.1 = x.1} := by
    intro x y hy; simp only [Set.mem_singleton_iff] at hy; simp [hy]
  have hsubAB : ∀ x : A × B × C,
      ({x} : Set (A × B × C)) ⊆ {y | y.1 = x.1 ∧ y.2.1 = x.2.1} := by
    intro x y hy; simp only [Set.mem_singleton_iff] at hy; simp [hy]
  have hsubAC : ∀ x : A × B × C,
      ({x} : Set (A × B × C)) ⊆ {y | y.1 = x.1 ∧ y.2.2 = x.2.2} := by
    intro x y hy; simp only [Set.mem_singleton_iff] at hy; simp [hy]
  -- the density of `forkDistr P` at an atom of positive mass, and absolute continuity
  have hfork := forkDistr_singleton P
  have hac := absolutelyContinuous_forkDistr P
  -- set identities matching the `condMI` variables
  have hset1 : ∀ x : A × B × C, {y : A × B × C | (y.2.1, y.1) = (x.2.1, x.1)} =
      {y : A × B × C | y.1 = x.1 ∧ y.2.1 = x.2.1} := by
    intro x; ext y; simp only [Set.mem_ofPred_eq, Prod.mk.injEq]; tauto
  have hset2 : ∀ x : A × B × C, {y : A × B × C | (y.2.2, y.1) = (x.2.2, x.1)} =
      {y : A × B × C | y.1 = x.1 ∧ y.2.2 = x.2.2} := by
    intro x; ext y; simp only [Set.mem_ofPred_eq, Prod.mk.injEq]; tauto
  have hset3 : ∀ x : A × B × C, {y : A × B × C | (y.2.1, y.2.2, y.1) = (x.2.1, x.2.2, x.1)} =
      ({x} : Set (A × B × C)) := by
    intro x; ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.ext_iff]
    tauto
  rw [natsToBits, forkApproxError, klDiv_toReal_eq_sum _ _ hac]
  simp only [pmfOfMeasure_eq_atomic, stoch_to_det.condMI]
  rw [Hvar_atomic, Hvar_atomic, Hvar_atomic, Hvar_atomic, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [hset1, hset2, hset3]
  rcases eq_or_lt_of_le (ENNReal.toReal_nonneg (a := P.toMeasure {x})) with h0 | hpos
  · rw [← h0]; ring
  have hx : P.toMeasure {x} ≠ 0 := by
    intro h; rw [h] at hpos; simp only [ENNReal.toReal_zero, lt_self_iff_false] at hpos
  have hA : (0 : ℝ) < (P.toMeasure {y : A × B × C | y.1 = x.1}).toReal :=
    lt_of_lt_of_le hpos (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (hsubA x)))
  have hAB : (0 : ℝ) <
      (P.toMeasure {y : A × B × C | y.1 = x.1 ∧ y.2.1 = x.2.1}).toReal :=
    lt_of_lt_of_le hpos (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (hsubAB x)))
  have hAC : (0 : ℝ) <
      (P.toMeasure {y : A × B × C | y.1 = x.1 ∧ y.2.2 = x.2.2}).toReal :=
    lt_of_lt_of_le hpos (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (hsubAC x)))
  rw [hfork x hx, ENNReal.toReal_div, ENNReal.toReal_mul]
  rw [lg_eq_log_div, lg_eq_log_div, lg_eq_log_div, lg_eq_log_div]
  rw [Real.log_div hpos.ne' (by positivity), Real.log_div (by positivity) hA.ne',
    Real.log_mul hAB.ne' hAC.ne']
  simp only [one_div, Real.log_inv]
  ring

/-- §4b. `chainApproxError` (KL divergence, nats) is likewise a conditional
mutual information (bits), via the chain-rule identity for KL divergence
against a Markov-chain reference measure. -/
theorem chainApproxError_eq_condMI {A B C : Type} [Finite A] [Finite B] [Finite C]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [DiscreteMeasurableSpace A] [DiscreteMeasurableSpace B] [DiscreteMeasurableSpace C]
    (P : ProbabilityMeasure (A × B × C)) :
    haveI : Fintype A := Fintype.ofFinite A
    haveI : Fintype B := Fintype.ofFinite B
    haveI : Fintype C := Fintype.ofFinite C
    haveI : DecidableEq A := Classical.decEq A
    haveI : DecidableEq B := Classical.decEq B
    haveI : DecidableEq C := Classical.decEq C
    natsToBits (chainApproxError P) =
      stoch_to_det.condMI (fun w : A × B × C => w.1) (fun w => w.2.2) (fun w => w.2.1)
        (pmfOfMeasure (P : ProbabilityMeasure (A × (B × C)))) := by
  classical
  let _ : Fintype A := Fintype.ofFinite A
  let _ : Fintype B := Fintype.ofFinite B
  let _ : Fintype C := Fintype.ofFinite C
  have : IsProbabilityMeasure (P.toMeasure) := P.2
  have : IsProbabilityMeasure ((chainDistr P).toMeasure) := (chainDistr P).2
  -- the "marginal" sets attached to a point, and the containment `{x} ⊆ ·`
  have hsubA : ∀ x : A × B × C, ({x} : Set (A × B × C)) ⊆ {y | y.1 = x.1} := by
    intro x y hy; simp only [Set.mem_singleton_iff] at hy; simp [hy]
  have hsubB : ∀ x : A × B × C, ({x} : Set (A × B × C)) ⊆ {y | y.2.1 = x.2.1} := by
    intro x y hy; simp only [Set.mem_singleton_iff] at hy; simp [hy]
  have hsubAB : ∀ x : A × B × C,
      ({x} : Set (A × B × C)) ⊆ {y | y.1 = x.1 ∧ y.2.1 = x.2.1} := by
    intro x y hy; simp only [Set.mem_singleton_iff] at hy; simp [hy]
  have hsubBC : ∀ x : A × B × C,
      ({x} : Set (A × B × C)) ⊆ {y | y.2.1 = x.2.1 ∧ y.2.2 = x.2.2} := by
    intro x y hy; simp only [Set.mem_singleton_iff] at hy; simp [hy]
  -- the density of `chainDistr P` at an atom of positive mass, and absolute continuity
  have hchain := chainDistr_singleton P
  have hac := absolutelyContinuous_chainDistr P
  -- set identities matching the `condMI` variables
  have hset1 : ∀ x : A × B × C, {y : A × B × C | (y.1, y.2.1) = (x.1, x.2.1)} =
      {y : A × B × C | y.1 = x.1 ∧ y.2.1 = x.2.1} := by
    intro x; ext y; simp only [Set.mem_ofPred_eq, Prod.mk.injEq]
  have hset2 : ∀ x : A × B × C, {y : A × B × C | (y.2.2, y.2.1) = (x.2.2, x.2.1)} =
      {y : A × B × C | y.2.1 = x.2.1 ∧ y.2.2 = x.2.2} := by
    intro x; ext y; simp only [Set.mem_ofPred_eq, Prod.mk.injEq]; tauto
  have hset3 : ∀ x : A × B × C, {y : A × B × C | (y.1, y.2.2, y.2.1) = (x.1, x.2.2, x.2.1)} =
      ({x} : Set (A × B × C)) := by
    intro x; ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.ext_iff]
    tauto
  rw [natsToBits, chainApproxError, klDiv_toReal_eq_sum _ _ hac]
  simp only [pmfOfMeasure_eq_atomic, stoch_to_det.condMI]
  rw [Hvar_atomic, Hvar_atomic, Hvar_atomic, Hvar_atomic, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [hset1, hset2, hset3]
  rcases eq_or_lt_of_le (ENNReal.toReal_nonneg (a := P.toMeasure {x})) with h0 | hpos
  · rw [← h0]; ring
  have hx : P.toMeasure {x} ≠ 0 := by
    intro h; rw [h] at hpos; simp only [ENNReal.toReal_zero, lt_self_iff_false] at hpos
  have hB : (0 : ℝ) < (P.toMeasure {y : A × B × C | y.2.1 = x.2.1}).toReal :=
    lt_of_lt_of_le hpos (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (hsubB x)))
  have hAB : (0 : ℝ) <
      (P.toMeasure {y : A × B × C | y.1 = x.1 ∧ y.2.1 = x.2.1}).toReal :=
    lt_of_lt_of_le hpos (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (hsubAB x)))
  have hBC : (0 : ℝ) <
      (P.toMeasure {y : A × B × C | y.2.1 = x.2.1 ∧ y.2.2 = x.2.2}).toReal :=
    lt_of_lt_of_le hpos (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (hsubBC x)))
  rw [hchain x hx, ENNReal.toReal_div, ENNReal.toReal_mul]
  rw [lg_eq_log_div, lg_eq_log_div, lg_eq_log_div, lg_eq_log_div]
  rw [Real.log_div hpos.ne' (by positivity), Real.log_div (by positivity) hB.ne',
    Real.log_mul hAB.ne' hBC.ne']
  simp only [one_div, Real.log_inv]
  ring

section ApproxErrorOfReal

variable {A B C : Type} [Finite A] [Finite B] [Finite C]
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  [DiscreteMeasurableSpace A] [DiscreteMeasurableSpace B] [DiscreteMeasurableSpace C]

/-- §4a, `ENNReal` form: `forkApproxError` is `log 2` times a conditional mutual
information in bits. -/
theorem forkApproxError_eq_ofReal (P : ProbabilityMeasure (A × B × C)) :
    haveI : Fintype A := Fintype.ofFinite A
    haveI : Fintype B := Fintype.ofFinite B
    haveI : Fintype C := Fintype.ofFinite C
    haveI : DecidableEq A := Classical.decEq A
    haveI : DecidableEq B := Classical.decEq B
    haveI : DecidableEq C := Classical.decEq C
    forkApproxError P = ENNReal.ofReal
      (stoch_to_det.condMI (fun w : A × B × C => w.2.1) (fun w => w.2.2) (fun w => w.1)
        (pmfOfMeasure (P : ProbabilityMeasure (A × (B × C)))) * Real.log 2) := by
  have h := forkApproxError_eq_condMI P
  rw [natsToBits, div_eq_iff (Real.log_pos (by norm_num)).ne'] at h
  rw [← ENNReal.ofReal_toReal (forkApproxError_ne_top P), h]

/-- §4b, `ENNReal` form: `chainApproxError` is `log 2` times a conditional mutual
information in bits. -/
theorem chainApproxError_eq_ofReal (P : ProbabilityMeasure (A × B × C)) :
    haveI : Fintype A := Fintype.ofFinite A
    haveI : Fintype B := Fintype.ofFinite B
    haveI : Fintype C := Fintype.ofFinite C
    haveI : DecidableEq A := Classical.decEq A
    haveI : DecidableEq B := Classical.decEq B
    haveI : DecidableEq C := Classical.decEq C
    chainApproxError P = ENNReal.ofReal
      (stoch_to_det.condMI (fun w : A × B × C => w.1) (fun w => w.2.2) (fun w => w.2.1)
        (pmfOfMeasure (P : ProbabilityMeasure (A × (B × C)))) * Real.log 2) := by
  have h := chainApproxError_eq_condMI P
  rw [natsToBits, div_eq_iff (Real.log_pos (by norm_num)).ne'] at h
  rw [← ENNReal.ofReal_toReal (chainApproxError_ne_top P), h]

end ApproxErrorOfReal

/-- §4c. `condEntropyNN` (nats) is `condH` (bits), up to the nats→bits factor. -/
theorem condEntropyNN_eq_condH {A B : Type} [Finite A] [Finite B]
    [MeasurableSpace A] [MeasurableSpace B]
    [DiscreteMeasurableSpace A] [DiscreteMeasurableSpace B]
    (P : ProbabilityMeasure (A × B)) :
    haveI : Fintype A := Fintype.ofFinite A
    haveI : Fintype B := Fintype.ofFinite B
    haveI : DecidableEq A := Classical.decEq A
    haveI : DecidableEq B := Classical.decEq B
    natsToBits (condEntropyNN P) =
      stoch_to_det.condH (fun w : A × B => w.1) (fun w => w.2) (pmfOfMeasure P) := by
  have hcoe := condEntropy_eq_coe P
  have hSnn : (0 : ℝ) ≤ ∑ z : A × B, pmfOfMeasure P z *
      Real.log ((P.toMeasure {y : A × B | y.2 = z.2}).toReal / pmfOfMeasure P z) := by
    have h := condEntropy_nonneg P
    rw [ge_iff_le, hcoe] at h
    exact_mod_cast h
  rw [condH_pmfOfMeasure P, natsToBits, condEntropyNN, hcoe,
    EReal.toENNReal_of_ne_top (by simp only [ne_eq, EReal.coe_ne_top, not_false_eq_true]),
    EReal.toReal_coe, ENNReal.toReal_ofReal hSnn, Finset.sum_div]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [lg_eq_log_div, mul_div_assoc]

/-- §4c, `ENNReal` form: `condEntropyNN` is `log 2` times a conditional entropy in bits. -/
theorem condEntropyNN_eq_ofReal {A B : Type} [Finite A] [Finite B] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [MeasurableSpace A] [MeasurableSpace B]
    [DiscreteMeasurableSpace A] [DiscreteMeasurableSpace B]
    (P : ProbabilityMeasure (A × B)) :
    condEntropyNN P = ENNReal.ofReal
      (stoch_to_det.condH (fun w : A × B => w.1) (fun w => w.2) (pmfOfMeasure P) * Real.log 2) := by
  have hne : condEntropyNN P ≠ ⊤ := by
    rw [condEntropyNN, condEntropy_eq_coe]; simp only [ne_eq, EReal.coe_ne_top, not_false_eq_true,
        EReal.toENNReal_of_ne_top, EReal.toReal_coe, ENNReal.ofReal_ne_top]
  have h := condEntropyNN_eq_condH P
  rw [Subsingleton.elim (Fintype.ofFinite A) (inferInstanceAs (Fintype A)),
    Subsingleton.elim (Fintype.ofFinite B) (inferInstanceAs (Fintype B)),
    Subsingleton.elim (Classical.decEq A) (inferInstanceAs (DecidableEq A)),
    Subsingleton.elim (Classical.decEq B) (inferInstanceAs (DecidableEq B))] at h
  rw [natsToBits, div_eq_iff (Real.log_pos (by norm_num)).ne'] at h
  rw [← ENNReal.ofReal_toReal hne, h]

section Marginals

variable {A B C : Type} [Finite A] [Finite B] [Finite C]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  [DiscreteMeasurableSpace A] [DiscreteMeasurableSpace B] [DiscreteMeasurableSpace C]

omit [DecidableEq C] in
/-- The `(A, B)`-marginal pmf of `Q` is the pushforward of `Q`'s pmf along `(w.1, w.2.1)`. -/
theorem pmfOfMeasure_getABProb (Q : ProbabilityMeasure (A × B × C)) :
    pmfOfMeasure (getABProb Q) =
      stoch_to_det.push (fun w : A × B × C => (w.1, w.2.1))
        (pmfOfMeasure (Q : ProbabilityMeasure (A × (B × C)))) := by
  funext z
  obtain ⟨a, b⟩ := z
  rw [show pmfOfMeasure (Q : ProbabilityMeasure (A × (B × C))) =
        fun w => (Q.toMeasure {w}).toReal from rfl,
    push_atomic, pmfOfMeasure]
  refine congrArg ENNReal.toReal ((getABProb_singleton Q a b).trans ?_)
  rw [massAB]
  congr 1
  ext y
  simp [Prod.ext_iff]

omit [DecidableEq B] in
/-- The `(A, C)`-marginal pmf of `Q` is the pushforward of `Q`'s pmf along `(w.1, w.2.2)`. -/
theorem pmfOfMeasure_getACProb (Q : ProbabilityMeasure (A × B × C)) :
    pmfOfMeasure (getACProb Q) =
      stoch_to_det.push (fun w : A × B × C => (w.1, w.2.2))
        (pmfOfMeasure (Q : ProbabilityMeasure (A × (B × C)))) := by
  funext z
  obtain ⟨a, c⟩ := z
  rw [show pmfOfMeasure (Q : ProbabilityMeasure (A × (B × C))) =
        fun w => (Q.toMeasure {w}).toReal from rfl,
    push_atomic, pmfOfMeasure]
  refine congrArg ENNReal.toReal ((getACProb_singleton Q a c).trans ?_)
  rw [massAC]
  congr 1
  ext y
  simp [Prod.ext_iff]

omit [DecidableEq A] in
/-- The `(B, C)`-marginal pmf of `Q` is the pushforward of `Q`'s pmf along `(w.2.1, w.2.2)`. -/
theorem pmfOfMeasure_getBCProb (Q : ProbabilityMeasure (A × B × C)) :
    pmfOfMeasure (getBCProb Q) =
      stoch_to_det.push (fun w : A × B × C => (w.2.1, w.2.2))
        (pmfOfMeasure (Q : ProbabilityMeasure (A × (B × C)))) := by
  funext z
  obtain ⟨b, c⟩ := z
  rw [show pmfOfMeasure (Q : ProbabilityMeasure (A × (B × C))) =
        fun w => (Q.toMeasure {w}).toReal from rfl,
    push_atomic, pmfOfMeasure]
  refine congrArg ENNReal.toReal ((getBCProb_singleton Q b c).trans ?_)
  rw [massBC]
  congr 1
  ext y
  simp [Prod.ext_iff]

end Marginals

section Relabel

open stoch_to_det

variable {α α' γ γ' δ δ' κ κ' : Type} [Fintype α] [Fintype α']
  [Fintype γ] [DecidableEq γ] [Fintype γ'] [DecidableEq γ']
  [Fintype δ] [DecidableEq δ] [Fintype δ'] [DecidableEq δ']
  [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

omit [Fintype γ] in
/-- Relabelling the sample space by an equivalence commutes with `push`. -/
theorem push_reindex (e : α ≃ α') (m : α → ℝ) (f : α' → γ) :
    stoch_to_det.push f (fun a' => m (e.symm a')) = stoch_to_det.push (fun a => f (e a)) m := by
  funext c
  simp only [stoch_to_det.push, Finset.sum_filter]
  rw [← Equiv.sum_comp e (fun a' => if f a' = c then m (e.symm a') else 0)]
  exact Finset.sum_congr rfl fun a _ => by simp only [Equiv.symm_apply_apply]

/-- Relabelling the sample space by an equivalence preserves `Hvar`. -/
theorem Hvar_reindex (e : α ≃ α') (m : α → ℝ) (f : α' → γ) :
    stoch_to_det.Hvar f (fun a' => m (e.symm a')) = stoch_to_det.Hvar (fun a => f (e a)) m := by
  unfold stoch_to_det.Hvar
  rw [push_reindex]

/-- Relabelling the sample space by an equivalence preserves `condMI`. -/
theorem condMI_reindex (e : α ≃ α') (m : α → ℝ) (f : α' → γ) (g : α' → δ) (h : α' → κ) :
    stoch_to_det.condMI f g h (fun a' => m (e.symm a')) =
      stoch_to_det.condMI (fun a => f (e a)) (fun a => g (e a)) (fun a => h (e a)) m := by
  unfold stoch_to_det.condMI
  rw [Hvar_reindex e m (fun a' => (f a', h a')), Hvar_reindex e m (fun a' => (g a', h a')),
    Hvar_reindex e m (fun a' => (f a', g a', h a')), Hvar_reindex e m h]

/-- `I(f ; g ∣ h)` is symmetric in its first two arguments. -/
theorem condMI_comm {m : α → ℝ} (hm : stoch_to_det.IsPMF m) (f : α → γ) (g : α → δ)
    (h : α → κ) : stoch_to_det.condMI f g h m = stoch_to_det.condMI g f h m := by
  have hswap : stoch_to_det.Hvar (fun a => (f a, g a, h a)) m =
      stoch_to_det.Hvar (fun a => (g a, f a, h a)) m := by
    simpa only [Equiv.coe_fn_mk] using (stoch_to_det.Hvar_equiv hm (fun a => (g a, f a, h a))
      (⟨fun w => (w.2.1, w.1, w.2.2), fun w => (w.2.1, w.1, w.2.2), fun _ => rfl, fun _ => rfl⟩ :
        δ × γ × κ ≃ γ × δ × κ))
  unfold stoch_to_det.condMI
  rw [hswap]
  ring

/-- Re-encoding the conditioning argument of `condMI` by an equivalence. -/
theorem condMI_equiv₃ {m : α → ℝ} (hm : stoch_to_det.IsPMF m) (f : α → γ) (g : α → δ)
    (h : α → κ) (e : κ ≃ κ') :
    stoch_to_det.condMI f g (fun a => e (h a)) m = stoch_to_det.condMI f g h m := by
  have h1 : stoch_to_det.Hvar (fun a => (f a, e (h a))) m =
      stoch_to_det.Hvar (fun a => (f a, h a)) m :=
    stoch_to_det.Hvar_equiv hm (fun a => (f a, h a)) ((Equiv.refl γ).prodCongr e)
  have h2 : stoch_to_det.Hvar (fun a => (g a, e (h a))) m =
      stoch_to_det.Hvar (fun a => (g a, h a)) m :=
    stoch_to_det.Hvar_equiv hm (fun a => (g a, h a)) ((Equiv.refl δ).prodCongr e)
  have h3 : stoch_to_det.Hvar (fun a => (f a, g a, e (h a))) m =
      stoch_to_det.Hvar (fun a => (f a, g a, h a)) m :=
    stoch_to_det.Hvar_equiv hm (fun a => (f a, g a, h a))
      ((Equiv.refl γ).prodCongr ((Equiv.refl δ).prodCongr e))
  have h4 : stoch_to_det.Hvar (fun a => e (h a)) m = stoch_to_det.Hvar h m :=
    stoch_to_det.Hvar_equiv hm h e
  unfold stoch_to_det.condMI
  rw [h1, h2, h3, h4]

/-- `Hvar` of a pushforward is `Hvar` of the composite variable. -/
theorem Hvar_push (F : α → κ) (m : α → ℝ) (f : κ → γ) :
    stoch_to_det.Hvar f (stoch_to_det.push F m) = stoch_to_det.Hvar (fun a => f (F a)) m := by
  unfold stoch_to_det.Hvar
  rw [stoch_to_det.push_push]
  rfl

/-- `condH` of a pushforward is `condH` of the composite variables. -/
theorem condH_push (F : α → κ) (m : α → ℝ) (f : κ → γ) (g : κ → δ) :
    stoch_to_det.condH f g (stoch_to_det.push F m) =
      stoch_to_det.condH (fun a => f (F a)) (fun a => g (F a)) m := by
  unfold stoch_to_det.condH
  rw [Hvar_push F m (fun w => (f w, g w)), Hvar_push F m g]

/-- Relabelling the sample space by an equivalence preserves `condH`. -/
theorem condH_reindex (e : α ≃ α') (m : α → ℝ) (f : α' → γ) (g : α' → δ) :
    stoch_to_det.condH f g (fun a' => m (e.symm a')) =
      stoch_to_det.condH (fun a => f (e a)) (fun a => g (e a)) m := by
  unfold stoch_to_det.condH
  rw [Hvar_reindex e m (fun a' => (f a', g a')), Hvar_reindex e m g]

/-- Re-encoding the first argument of `condH` by an equivalence. -/
theorem condH_equiv₁ {m : α → ℝ} (hm : stoch_to_det.IsPMF m) (f : α → γ) (g : α → δ)
    (e : γ ≃ γ') : stoch_to_det.condH (fun a => e (f a)) g m = stoch_to_det.condH f g m := by
  unfold stoch_to_det.condH
  congr 1
  simpa using stoch_to_det.Hvar_equiv hm (fun a => (f a, g a)) (e.prodCongr (Equiv.refl δ))

/-- Conditional entropy is nonnegative. -/
theorem condH_nonneg {m : α → ℝ} (hm : stoch_to_det.IsPMF m) (f : α → γ) (g : α → δ) :
    0 ≤ stoch_to_det.condH f g m :=
  sub_nonneg.mpr (by
    simpa [Function.comp_def] using
      stoch_to_det.Hvar_comp_le hm (fun a => (f a, g a)) (Prod.snd : γ × δ → δ))

end Relabel

/-- `IsPMF` does not depend on the chosen `Fintype` instance. -/
theorem isPMF_cast {S : Type} (i₁ i₂ : Fintype S) {f : S → ℝ}
    (h : @stoch_to_det.IsPMF S i₁ f) : @stoch_to_det.IsPMF S i₂ f := by
  rw [Subsingleton.elim i₂ i₁]; exact h

/-- §6. Converse: a `HasStochasticNL ε` witness produces a `Latent p` with
`score ≤ 3 * natsToBits ε` — the factor `3` because `HasStochasticNL` bounds
each of the three conditional-MI terms by `ε` individually, while
`Latent.score` sums them.

The hypothesis `ε ≠ ⊤` is necessary: `HasStochasticNL P ⊤` holds trivially for
every `P` (a constant `Fin 1` latent satisfies all three bounds vacuously), but
`natsToBits ⊤ = 0`, so at `ε = ⊤` the conclusion would demand an *unconditional*
exact (zero-error) latent for every finite joint `p`, which is false in general
(e.g. a 3-point joint with no exact common-information latent). `§8`/`MainConjecture`
does not need this case: its own `ε = ⊤` case is trivial via `HasDeterministicNL _ ⊤`
directly (see `Conjecture.lean`'s `MainConjecture` docstring). -/
theorem latent_of_hasStochasticNL {P : ProbabilityMeasure (X × Y)} {ε : ENNReal}
    (hε : ε ≠ ⊤) (h : NaturalLatents.HasStochasticNL P ε) :
    ∃ V : stoch_to_det.Latent (pmfOfMeasure P), V.score ≤ 3 * natsToBits ε := by
  classical
  obtain ⟨n, Q, ⟨hfork, hchain1, hchain2⟩, hmarg⟩ := h
  set q : Fin n × X × Y → ℝ := pmfOfMeasure Q with hq_def
  have hq : stoch_to_det.IsPMF q := isPMF_cast _ _ (pmfOfMeasure_isPMF Q)
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hp : stoch_to_det.IsPMF (pmfOfMeasure P) := pmfOfMeasure_isPMF P
  -- the three score terms, each bounded by `natsToBits ε`
  have hb1 : stoch_to_det.condMI (fun w : Fin n × X × Y => w.2.1) (fun w => w.2.2)
      (fun w => w.1) q ≤ natsToBits ε := by
    rw [forkApproxError_eq_ofReal] at hfork
    rw [Subsingleton.elim (Fintype.ofFinite (Fin n)) (inferInstanceAs (Fintype (Fin n))),
      Subsingleton.elim (Fintype.ofFinite X) (inferInstanceAs (Fintype X)),
      Subsingleton.elim (Fintype.ofFinite Y) (inferInstanceAs (Fintype Y)),
      Subsingleton.elim (Classical.decEq (Fin n)) (inferInstanceAs (DecidableEq (Fin n))),
      Subsingleton.elim (Classical.decEq X) (inferInstanceAs (DecidableEq X)),
      Subsingleton.elim (Classical.decEq Y) (inferInstanceAs (DecidableEq Y))] at hfork
    rw [← hq_def, ge_iff_le] at hfork
    exact (le_div_iff₀ hlog).mpr ((ENNReal.ofReal_le_iff_le_toReal hε).mp hfork)
  have hb3 : stoch_to_det.condMI (fun w : Fin n × X × Y => w.1) (fun w => w.2.2)
      (fun w => w.2.1) q ≤ natsToBits ε := by
    rw [chainApproxError_eq_ofReal] at hchain1
    rw [Subsingleton.elim (Fintype.ofFinite Y) (inferInstanceAs (Fintype Y)),
      Subsingleton.elim (Fintype.ofFinite X) (inferInstanceAs (Fintype X)),
      Subsingleton.elim (Fintype.ofFinite (Fin n)) (inferInstanceAs (Fintype (Fin n))),
      Subsingleton.elim (Classical.decEq Y) (inferInstanceAs (DecidableEq Y)),
      Subsingleton.elim (Classical.decEq X) (inferInstanceAs (DecidableEq X)),
      Subsingleton.elim (Classical.decEq (Fin n))
        (inferInstanceAs (DecidableEq (Fin n)))] at hchain1
    rw [ge_iff_le] at hchain1
    let e : Fin n × X × Y ≃ Y × X × Fin n :=
      { toFun := fun w => (w.2.2, w.2.1, w.1)
        invFun := fun z => (z.2.2, z.2.1, z.1)
        left_inv := fun w => by simp only [Prod.mk.eta]
        right_inv := fun z => by simp only [Prod.mk.eta] }
    have hR : pmfOfMeasure (swapACProb Q) = fun z : Y × X × Fin n => q (e.symm z) := by
      funext z; obtain ⟨y, x, l⟩ := z
      rw [pmfOfMeasure, swapACProb_singleton Q (l, x, y)]; rfl
    rw [hR] at hchain1
    have hk : stoch_to_det.condMI (fun w : Y × X × Fin n => w.1) (fun w => w.2.2)
        (fun w => w.2.1) (fun z => q (e.symm z)) =
        stoch_to_det.condMI (fun w : Fin n × X × Y => w.1) (fun w => w.2.2) (fun w => w.2.1) q := by
      have hred := condMI_reindex e q (fun w : Y × X × Fin n => w.1) (fun w => w.2.2)
        (fun w => w.2.1)
      exact hred.trans (condMI_comm hq (fun w : Fin n × X × Y => w.2.2) (fun w => w.1)
        (fun w => w.2.1))
    rw [hk] at hchain1
    exact (le_div_iff₀ hlog).mpr ((ENNReal.ofReal_le_iff_le_toReal hε).mp hchain1)
  have hb2 : stoch_to_det.condMI (fun w : Fin n × X × Y => w.1) (fun w => w.2.1)
      (fun w => w.2.2) q ≤ natsToBits ε := by
    rw [chainApproxError_eq_ofReal] at hchain2
    rw [Subsingleton.elim (Fintype.ofFinite X) (inferInstanceAs (Fintype X)),
      Subsingleton.elim (Fintype.ofFinite Y) (inferInstanceAs (Fintype Y)),
      Subsingleton.elim (Fintype.ofFinite (Fin n)) (inferInstanceAs (Fintype (Fin n))),
      Subsingleton.elim (Classical.decEq X) (inferInstanceAs (DecidableEq X)),
      Subsingleton.elim (Classical.decEq Y) (inferInstanceAs (DecidableEq Y)),
      Subsingleton.elim (Classical.decEq (Fin n))
        (inferInstanceAs (DecidableEq (Fin n)))] at hchain2
    rw [ge_iff_le] at hchain2
    let e : Fin n × X × Y ≃ X × Y × Fin n :=
      { toFun := fun w => (w.2.1, w.2.2, w.1)
        invFun := fun z => (z.2.2, z.1, z.2.1)
        left_inv := fun w => by simp only [Prod.mk.eta]
        right_inv := fun z => by simp only [Prod.mk.eta] }
    have hS : pmfOfMeasure (swapABProb (swapACProb Q)) = fun z : X × Y × Fin n => q (e.symm z) := by
      funext z; obtain ⟨x, y, l⟩ := z
      have h1 := swapABProb_singleton (swapACProb Q) (y, x, l)
      simp only [swapAB] at h1
      rw [pmfOfMeasure, h1, swapACProb_singleton Q (l, x, y)]; rfl
    rw [hS] at hchain2
    have hk : stoch_to_det.condMI (fun w : X × Y × Fin n => w.1) (fun w => w.2.2)
        (fun w => w.2.1) (fun z => q (e.symm z)) =
        stoch_to_det.condMI (fun w : Fin n × X × Y => w.1) (fun w => w.2.1) (fun w => w.2.2) q := by
      have hred := condMI_reindex e q (fun w : X × Y × Fin n => w.1) (fun w => w.2.2)
        (fun w => w.2.1)
      exact hred.trans (condMI_comm hq (fun w : Fin n × X × Y => w.2.1) (fun w => w.1)
        (fun w => w.2.2))
    rw [hk] at hchain2
    exact (le_div_iff₀ hlog).mpr ((ENNReal.ofReal_le_iff_le_toReal hε).mp hchain2)
  -- build the latent `V` on index `Fin n`, with `V.joint = q`
  set prior : Fin n → ℝ := fun v => ∑ z : X × Y, q (v, z) with hprior_def
  have hprior_nonneg : ∀ v, 0 ≤ prior v := fun v => Finset.sum_nonneg fun z _ => hq.nonneg _
  have hprior_total : ∑ v, prior v = 1 := by
    have htot : stoch_to_det.mass q = 1 := hq.total
    rw [stoch_to_det.mass, Fintype.sum_prod_type] at htot
    exact htot
  set comp : Fin n → (X × Y → ℝ) :=
    fun v z => if prior v = 0 then pmfOfMeasure P z else q (v, z) / prior v with hcomp_def
  have hjoint : ∀ v z, prior v * comp v z = q (v, z) := by
    intro v z
    by_cases hv : prior v = 0
    · have hz0 : q (v, z) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun z (_ : z ∈ Finset.univ) => hq.nonneg (v, z)).mp
          hv z (Finset.mem_univ z)
      simp [hcomp_def, hv, hz0]
    · rw [hcomp_def]
      simp only [ite_eq_right hv]
      field_simp
  have hcomp_isPMF : ∀ v, stoch_to_det.IsPMF (comp v) := by
    intro v
    by_cases hv : prior v = 0
    · refine ⟨fun z => by simp [hcomp_def, hv, hp.nonneg], ?_⟩
      show stoch_to_det.mass (comp v) = 1
      simp only [stoch_to_det.mass, hcomp_def, ite_eq_left hv]
      exact hp.total
    · have hvpos : 0 < prior v := lt_of_le_of_ne (hprior_nonneg v) (Ne.symm hv)
      refine ⟨fun z => ?_, ?_⟩
      · simp only [hcomp_def, ite_eq_right hv]
        exact div_nonneg (hq.nonneg _) hvpos.le
      · show stoch_to_det.mass (comp v) = 1
        simp only [stoch_to_det.mass, hcomp_def, ite_eq_right hv, ← Finset.sum_div]
        exact div_self hv
  have hmix : ∀ z, ∑ v, prior v * comp v z = pmfOfMeasure P z := by
    intro z
    simp_rw [hjoint]
    have hBC : pmfOfMeasure (getBCProb Q) =
        stoch_to_det.push (fun w : Fin n × X × Y => (w.2.1, w.2.2)) q := pmfOfMeasure_getBCProb Q
    rw [hmarg] at hBC
    rw [hBC, stoch_to_det.push]
    have hset : (Finset.univ.filter (fun w : Fin n × X × Y => (w.2.1, w.2.2) = z)) =
        Finset.univ.image (fun v : Fin n => (v, z)) := by
      ext w; simp [Prod.ext_iff, eq_comm]
    rw [hset, Finset.sum_image (by intro a _ b _ h; simpa using h)]
  let V : stoch_to_det.Latent (pmfOfMeasure P) :=
    ⟨Fin n, inferInstance, inferInstance, prior, comp, ⟨hprior_nonneg, hprior_total⟩,
      hcomp_isPMF, hmix⟩
  have hVjoint : V.joint = q := by
    funext w
    obtain ⟨v, z⟩ := w
    exact hjoint v z
  refine ⟨V, ?_⟩
  change stoch_to_det.condMI (fun w : Fin n × X × Y => w.2.1) (fun w => w.2.2) (fun w => w.1)
      V.joint +
    stoch_to_det.condMI (fun w : Fin n × X × Y => w.1) (fun w => w.2.1) (fun w => w.2.2) V.joint +
    stoch_to_det.condMI (fun w : Fin n × X × Y => w.1) (fun w => w.2.2) (fun w => w.2.1) V.joint ≤
      3 * natsToBits ε
  rw [hVjoint]
  nlinarith only [hb1, hb2, hb3]

/-- §7. A deterministic `Latent p` with bounded `DScore` produces a
`HasDeterministicNL` witness, dually to §5. -/
theorem hasDeterministicNL_of_detLatent {p : X × Y → ℝ} (hp : stoch_to_det.IsPMF p)
    (V : stoch_to_det.Latent p) (_hdet : V.IsDet) :
    NaturalLatents.HasDeterministicNL (measureOfPMF hp)
      (ENNReal.ofReal (V.DScore * Real.log 2)) := by
  classical
  set n := Fintype.card V.ι with hn
  let e : V.ι ≃ Fin n := Fintype.equivFin V.ι
  let E : V.ι × (X × Y) ≃ Fin n × (X × Y) := e.prodCongr (Equiv.refl (X × Y))
  let q : Fin n × (X × Y) → ℝ := fun w => V.joint (E.symm w)
  have hq : stoch_to_det.IsPMF q := by
    refine ⟨fun w => V.joint_isPMF.nonneg _, ?_⟩
    rw [stoch_to_det.mass, ← Equiv.sum_comp E q]
    simpa [q, stoch_to_det.mass] using V.joint_isPMF.total
  have hq2 : ∀ i : Fintype (Fin n × (X × Y)), @stoch_to_det.IsPMF _ i q :=
    fun i => isPMF_cast _ i hq
  have hjoint : ∀ i : Fintype (V.ι × (X × Y)), @stoch_to_det.IsPMF _ i V.joint :=
    fun i => isPMF_cast _ i V.joint_isPMF
  have hDScore : V.DScore =
      stoch_to_det.condMI (fun w : V.ι × X × Y => w.2.1) (fun w => w.2.2) (fun w => w.1) V.joint +
      stoch_to_det.condH (fun w : V.ι × X × Y => w.1) (fun w => w.2.1) V.joint +
      stoch_to_det.condH (fun w : V.ι × X × Y => w.1) (fun w => w.2.2) V.joint := rfl
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hn1 : 0 ≤ stoch_to_det.condMI (fun w : V.ι × X × Y => w.2.1) (fun w => w.2.2)
      (fun w => w.1) V.joint := stoch_to_det.condMI_nonneg (hjoint _) _ _ _
  have hn2 : 0 ≤ stoch_to_det.condH (fun w : V.ι × X × Y => w.1) (fun w => w.2.1) V.joint :=
    condH_nonneg (hjoint _) _ _
  have hn3 : 0 ≤ stoch_to_det.condH (fun w : V.ι × X × Y => w.1) (fun w => w.2.2) V.joint :=
    condH_nonneg (hjoint _) _ _
  refine ⟨n, measureOfPMF (hq2 _), ⟨?_, ?_, ?_⟩, ?_⟩
  -- fork condition: `I(X ; Y ∣ V)`
  · rw [forkApproxError_eq_ofReal, pmfOfMeasure_measureOfPMF]
    convert_to ENNReal.ofReal (V.DScore * Real.log 2) ≥
      ENNReal.ofReal (stoch_to_det.condMI (fun w : Fin n × X × Y => w.2.1) (fun w => w.2.2)
        (fun w => w.1) q * Real.log 2)
    · congr!
    have hk : stoch_to_det.condMI (fun w : Fin n × X × Y => w.2.1) (fun w => w.2.2)
        (fun w => w.1) q =
        stoch_to_det.condMI (fun w : V.ι × X × Y => w.2.1) (fun w => w.2.2) (fun w => w.1)
          V.joint := by
      rw [show q = fun w => V.joint (E.symm w) from rfl, condMI_reindex E V.joint]
      exact condMI_equiv₃ (hjoint _) _ _ _ e
    rw [ge_iff_le, hk, hDScore]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  -- `H(L ∣ X)`
  · rw [condEntropyNN_eq_ofReal]
    convert_to ENNReal.ofReal (V.DScore * Real.log 2) ≥
      ENNReal.ofReal (stoch_to_det.condH (fun w : Fin n × X × Y => w.1) (fun w => w.2.1) q *
        Real.log 2)
    · congr! 1
      rw [pmfOfMeasure_getABProb, pmfOfMeasure_measureOfPMF, condH_push]
    have hk : stoch_to_det.condH (fun w : Fin n × X × Y => w.1) (fun w => w.2.1) q =
        stoch_to_det.condH (fun w : V.ι × X × Y => w.1) (fun w => w.2.1) V.joint := by
      rw [show q = fun w => V.joint (E.symm w) from rfl, condH_reindex E V.joint]
      exact condH_equiv₁ (hjoint _) _ _ e
    rw [ge_iff_le, hk, hDScore]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  -- `H(L ∣ Y)`
  · rw [condEntropyNN_eq_ofReal]
    convert_to ENNReal.ofReal (V.DScore * Real.log 2) ≥
      ENNReal.ofReal (stoch_to_det.condH (fun w : Fin n × X × Y => w.1) (fun w => w.2.2) q *
        Real.log 2)
    · congr! 1
      rw [pmfOfMeasure_getACProb, pmfOfMeasure_measureOfPMF, condH_push]
    have hk : stoch_to_det.condH (fun w : Fin n × X × Y => w.1) (fun w => w.2.2) q =
        stoch_to_det.condH (fun w : V.ι × X × Y => w.1) (fun w => w.2.2) V.joint := by
      rw [show q = fun w => V.joint (E.symm w) from rfl, condH_reindex E V.joint]
      exact condH_equiv₁ (hjoint _) _ _ e
    rw [ge_iff_le, hk, hDScore]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  -- the `(X, Y)`-marginal of the transported joint law is `p`
  · apply ProbabilityMeasure.toMeasure_injective
    refine MeasureTheory.Measure.ext_of_singleton fun z => ?_
    have hset : (Prod.snd ⁻¹' ({z} : Set (X × Y)) : Set (Fin n × X × Y)) =
        ↑((Finset.univ : Finset (Fin n)).image (fun l => (l, z))) := by
      ext w; simp [Prod.ext_iff, eq_comm]
    have h1 : (getBCProb (measureOfPMF (hq2 _))).toMeasure {z} =
        ∑ l : Fin n, ENNReal.ofReal (q (l, z)) := by
      change ((measureOfPMF (hq2 _)).toMeasure.snd) {z} = _
      rw [MeasureTheory.Measure.snd_apply (measurableSet_singleton z), hset,
        ← MeasureTheory.sum_measure_singleton,
        Finset.sum_image (by intro a _ b _ h; simpa using h)]
      exact Finset.sum_congr rfl fun l _ => measureOfPMF_singleton _ _
    rw [h1, measureOfPMF_singleton hp z,
      ← ENNReal.ofReal_sum_of_nonneg (fun l _ => hq.nonneg _)]
    congr 1
    rw [← V.mixture z, ← Equiv.sum_comp e (fun l => q (l, z))]
    exact Finset.sum_congr rfl fun u _ => by simp [q, E, stoch_to_det.Latent.joint]

/-- §8. Glue: `MainConjecture`, assembled from `T_le_Cstar` via §6/§7. `cc`
absorbs the `3` (sum-vs-each-term, §6); `stoch_to_det`'s `H`/`score`/`DScore` are
already bit-valued (`Entropy.lean`'s `H` uses `lg = Real.logb 2`), so the
nats/bits `Real.log 2` factor is consumed converting `W.DScore` (bits) to the
nats-valued `ε` (see `hkey` below), not baked into `cc`. -/
theorem mainConjecture_of_T_le_Cstar : NaturalLatents.MainConjecture := by
  have hC : 0 < stoch_to_det.Cstar := stoch_to_det.Cstar_pos
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(stoch_to_det.Cstar * 3).toNNReal, Real.toNNReal_pos.mpr (by positivity), ?_⟩
  intro X Y _ _ _ _ _ _ P ε h
  by_cases hε : ε = ⊤
  · subst hε
    have htopmul : (((stoch_to_det.Cstar * 3).toNNReal : ENNReal)) * (⊤ : ENNReal) = ⊤ :=
      ENNReal.mul_top (by
        simp only [ne_eq, ENNReal.coe_eq_zero, Real.toNNReal_eq_zero, not_le]
        positivity)
    rw [htopmul]
    have hq : stoch_to_det.IsPMF (fun w : Fin 1 × X × Y => pmfOfMeasure P w.2) := by
      refine ⟨fun w => (pmfOfMeasure_isPMF P).nonneg w.2, ?_⟩
      show mass (fun w : Fin 1 × X × Y => pmfOfMeasure P w.2) = 1
      unfold stoch_to_det.mass
      rw [Fintype.sum_prod_type, Fin.sum_univ_one]
      exact (pmfOfMeasure_isPMF P).total
    refine ⟨1, measureOfPMF (isPMF_cast _ _ hq), ⟨le_top, le_top, le_top⟩, ?_⟩
    apply ProbabilityMeasure.toMeasure_injective
    refine MeasureTheory.Measure.ext_of_singleton fun z => ?_
    have hset : (Prod.snd ⁻¹' ({z} : Set (X × Y)) : Set (Fin 1 × X × Y)) =
        ↑((Finset.univ : Finset (Fin 1)).image (fun l => (l, z))) := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_image, Finset.coe_univ,
        Set.image_univ, Set.mem_range]
      constructor
      · intro hw; exact ⟨w.1, by simp [Prod.ext_iff, hw]⟩
      · rintro ⟨l, hl⟩; rw [← hl]
    have h1 : (getBCProb (measureOfPMF (isPMF_cast _ _ hq))).toMeasure {z} =
        ∑ _l : Fin 1, ENNReal.ofReal (pmfOfMeasure P z) := by
      change ((measureOfPMF (isPMF_cast _ _ hq)).toMeasure.snd) {z} = _
      rw [MeasureTheory.Measure.snd_apply (measurableSet_singleton z), hset,
        ← MeasureTheory.sum_measure_singleton,
        Finset.sum_image (by intro a _ b _ h; simpa using h)]
      exact Finset.sum_congr rfl fun l _ => measureOfPMF_singleton (isPMF_cast _ _ hq) (l, z)
    rw [h1, Fin.sum_univ_one, pmfOfMeasure, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  · obtain ⟨V, hVscore⟩ := latent_of_hasStochasticNL hε h
    have hp : stoch_to_det.IsPMF (pmfOfMeasure P) := pmfOfMeasure_isPMF P
    have htau : stoch_to_det.tau (pmfOfMeasure P) ≤ V.score := stoch_to_det.tau_le_score V
    have hTle : stoch_to_det.T (pmfOfMeasure P) ≤
        stoch_to_det.Cstar * stoch_to_det.tau (pmfOfMeasure P) := stoch_to_det.T_le_Cstar hp
    obtain ⟨W, hWdet, hWTscore⟩ := stoch_to_det.exists_T_optimal_latent hp
    have hWbound : W.score ≤ stoch_to_det.Cstar * (3 * natsToBits ε) := by
      rw [hWTscore]
      calc stoch_to_det.T (pmfOfMeasure P)
          ≤ stoch_to_det.Cstar * stoch_to_det.tau (pmfOfMeasure P) := hTle
        _ ≤ stoch_to_det.Cstar * V.score := by nlinarith [htau]
        _ ≤ stoch_to_det.Cstar * (3 * natsToBits ε) := by nlinarith [hVscore]
    have hWDScore : W.DScore = W.score := stoch_to_det.Latent.DScore_eq_score_of_isDet hp W hWdet
    have hkey : W.DScore * Real.log 2 ≤ stoch_to_det.Cstar * 3 * ε.toReal := by
      rw [hWDScore]
      unfold natsToBits at hWbound
      have hlog' := hlog.ne'
      have : W.score * Real.log 2 ≤ stoch_to_det.Cstar * (3 * (ε.toReal / Real.log 2)) *
          Real.log 2 := by nlinarith [hWbound, hlog]
      calc W.score * Real.log 2 ≤ stoch_to_det.Cstar * (3 * (ε.toReal / Real.log 2)) * Real.log 2 :=
            this
        _ = stoch_to_det.Cstar * 3 * ε.toReal := by field_simp
    have hbound : ENNReal.ofReal (W.DScore * Real.log 2) ≤
        (stoch_to_det.Cstar * 3).toNNReal * ε := by
      calc ENNReal.ofReal (W.DScore * Real.log 2)
          ≤ ENNReal.ofReal (stoch_to_det.Cstar * 3 * ε.toReal) := ENNReal.ofReal_le_ofReal hkey
        _ = ENNReal.ofReal (stoch_to_det.Cstar * 3) * ENNReal.ofReal ε.toReal :=
            ENNReal.ofReal_mul (by positivity)
        _ = (stoch_to_det.Cstar * 3).toNNReal * ε := by
            rw [ENNReal.ofReal_toReal hε]; rfl
    have hdet := hasDeterministicNL_of_detLatent hp W hWdet
    rw [measureOfPMF_pmfOfMeasure] at hdet
    obtain ⟨n, Q, ⟨h1, h2, h3⟩, hQ⟩ := hdet
    exact ⟨n, Q, ⟨h1.trans hbound, h2.trans hbound, h3.trans hbound⟩, hQ⟩

end NaturalLatents.Bridge

/-- `Conjecture.lean`'s `conjecture_solution` slot, discharged by `§8`. Stated here
(rather than in `Conjecture.lean`) since that file is imported by `Bridge.lean` and
cannot import it back. -/
theorem NaturalLatents.conjecture_solution : NaturalLatents.MainConjecture :=
  NaturalLatents.Bridge.mainConjecture_of_T_le_Cstar
