module

public import AISafetyMath.Solutions.ConverseLawvere.Basics

/-!
`not_sigmaCompact`: a witness of `MainConjecture` cannot live on a σ-compact space (no separation
axioms needed).

The sections `f x` are equicontinuous on each compact `K n` of a compact covering
(`eventually_forall_dist_lt`). If some continuous `g : X → I` were not locally constant at `y₀`,
pick `y n → y₀` with `g (y n) ≠ g y₀` and `f x` moving by `< 2⁻⁽ⁿ⁺¹⁾` on `K n` between `y n`
and `y₀`; the single map `ψ ∘ g` with `ψ t = ∑ 2⁻⁽ⁿ⁺¹⁾ min 1 (|t - g y₀| / |g (y n) - g y₀|)`
then moves by `≥ 2⁻⁽ⁿ⁺¹⁾` for every `n`, so it is no section `f x`
(`isLocallyConstant_of_surjectivityCondition`). Thus `x ↦ f x y` has finite range on each `K n`,
hence countable range, yet hits every point of the uncountable `I`.
-/

@[expose] public section

namespace ConverseLawvere

open Topology unitInterval Filter

/-- The sections `f x` are equicontinuous on compact sets of indices `x`. -/
theorem eventually_forall_dist_lt {X : Type} [TopologicalSpace X] (f : X → X → I)
    (hf : JointlyContinuous f) {K : Set X} (hK : IsCompact K) (y₀ : X) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 y₀, ∀ x ∈ K, dist (f x y) (f x y₀) < ε := by
  refine hK.eventually_forall_of_forall_eventually fun x _ => ?_
  have hc : Continuous fun z : X × X => dist (f z.2 z.1) (f z.2 y₀) :=
    continuous_dist.comp ((hf.comp continuous_swap).prodMk
      (hf.comp (continuous_snd.prodMk continuous_const)))
  have h0 : (fun z : X × X => dist (f z.2 z.1) (f z.2 y₀)) (y₀, x) < ε := by
    simpa only [dist_self] using hε
  exact hc.continuousAt.eventually (gt_mem_nhds h0)

/-- On a σ-compact space carrying a witness of `HasLawvereDomain unitInterval`, every continuous
map `X → I` is locally constant. -/
theorem isLocallyConstant_of_surjectivityCondition {X : Type} [TopologicalSpace X]
    [SigmaCompactSpace X]
    (f : X → X → I) (hf : JointlyContinuous f) (hcov : SurjectivityCondition f) (g : C(X, I)) :
    IsLocallyConstant g := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y₀
  by_contra hne
  rw [Filter.not_eventually] at hne
  set ε : ℕ → ℝ := fun n => 1 / 2 / 2 ^ n
  have εpos (n : ℕ) : 0 < ε n := by positivity
  have hsum : HasSum ε 1 := hasSum_geometric_two' 1
  have hy (n : ℕ) : ∃ y, g y ≠ g y₀ ∧
      ∀ x ∈ compactCovering X n, dist (f x y) (f x y₀) < ε n :=
    (hne.and_eventually
      (eventually_forall_dist_lt f hf (isCompact_compactCovering X n) y₀ (εpos n))).exists
  choose y hyne hyd using hy
  set a : ℝ := (g y₀ : ℝ)
  set d : ℕ → ℝ := fun n => |(g (y n) : ℝ) - a|
  have dpos (n : ℕ) : 0 < d n :=
    abs_pos.mpr (sub_ne_zero.mpr fun h => hyne n (Subtype.ext h))
  have hterm (t : ℝ) (n : ℕ) :
      0 ≤ ε n * min 1 (|t - a| / d n) ∧ ε n * min 1 (|t - a| / d n) ≤ ε n := by
    have h0 : 0 ≤ min 1 (|t - a| / d n) := le_min zero_le_one (by have := dpos n; positivity)
    exact ⟨mul_nonneg (εpos n).le h0, mul_le_of_le_one_right (εpos n).le (min_le_left _ _)⟩
  have hsumm (t : ℝ) : Summable fun n => ε n * min 1 (|t - a| / d n) :=
    Summable.of_nonneg_of_le (fun n => (hterm t n).1) (fun n => (hterm t n).2) hsum.summable
  let ψ : ℝ → ℝ := fun t => ∑' n, ε n * min 1 (|t - a| / d n)
  have hψc : Continuous ψ := by
    refine continuous_tsum (fun n => by fun_prop (disch := exact (dpos n).ne')) hsum.summable
      fun n t => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hterm t n).1]
    exact (hterm t n).2
  have hψ0 (t : ℝ) : 0 ≤ ψ t := tsum_nonneg fun n => (hterm t n).1
  have hψ1 (t : ℝ) : ψ t ≤ 1 :=
    hsum.tsum_eq ▸ Summable.tsum_le_tsum (fun n => (hterm t n).2) (hsumm t) hsum.summable
  let h : C(X, I) := ⟨fun z => ⟨ψ (g z), hψ0 _, hψ1 _⟩,
    (hψc.comp (continuous_subtype_val.comp g.continuous)).subtype_mk _⟩
  obtain ⟨x, hx⟩ := hcov h
  obtain ⟨n, hn⟩ := exists_mem_compactCovering x
  have hlt := hyd n x hn
  rw [hx] at hlt
  have hA : ψ a = 0 := by simp [ψ]
  have hB : ε n ≤ ψ (g (y n)) := by
    have hle := (hsumm (g (y n))).le_tsum n fun m _ => (hterm _ m).1
    have : ε n * min 1 (|(g (y n) : ℝ) - a| / d n) = ε n := by
      have hdn : |(g (y n) : ℝ) - a| = d n := rfl
      rw [hdn, div_self (dpos n).ne', min_self, mul_one]
    rwa [this] at hle
  rw [Subtype.dist_eq, Real.dist_eq] at hlt
  change |ψ (g (y n)) - ψ a| < ε n at hlt
  rw [hA, sub_zero, abs_of_nonneg (hψ0 _)] at hlt
  exact absurd hB (not_le.mpr hlt)

/-- A witness of `HasLawvereDomain unitInterval` on a σ-compact space cannot exist. -/
theorem not_sigmaCompactSpace {X : Type} [TopologicalSpace X] [SigmaCompactSpace X]
    (f : X → X → I) (hf : JointlyContinuous f) (hcov : SurjectivityCondition f) : False := by
  obtain ⟨y₀⟩ : Nonempty X := ⟨(hcov (ContinuousMap.const X 0)).choose⟩
  -- The continuous map `x ↦ f x y₀` hits every point of `I`, but has countable range.
  let g : C(X, I) := ⟨fun x => f x y₀, hf.comp (continuous_id.prodMk continuous_const)⟩
  have hsurj : Set.range g = Set.univ := by
    refine Set.eq_univ_of_forall fun c => ?_
    obtain ⟨x, hx⟩ := hcov (ContinuousMap.const X c)
    exact ⟨x, congrFun hx y₀⟩
  have hloc := isLocallyConstant_of_surjectivityCondition f hf hcov g
  have hcount : (Set.range g).Countable := by
    rw [← Set.image_univ, ← iUnion_compactCovering, Set.image_iUnion]
    refine Set.countable_iUnion fun n => Set.Finite.countable ?_
    have : CompactSpace (compactCovering X n) :=
      isCompact_iff_compactSpace.mp (isCompact_compactCovering X n)
    rw [Set.image_eq_range]
    exact (hloc.comp_continuous continuous_subtype_val).range_finite
  rw [hsurj] at hcount
  have himg := hcount.image (Subtype.val : I → ℝ)
  rw [Set.image_univ, Subtype.range_coe] at himg
  exact absurd (Cardinal.Real.Icc_countable_iff.mp himg) (by norm_num)

section Obstacles

theorem not_sigmaCompact (X : Type) [TopologicalSpace X]
    (f : X → X → unitInterval) (hf : JointlyContinuous f ∧ SurjectivityCondition f) :
    ¬ SigmaCompactSpace X :=
  fun _ => not_sigmaCompactSpace f hf.1 hf.2

end Obstacles

end ConverseLawvere
