module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.DiracProba
public import AISafetyMath.Solutions.MaxLotLot.Lotteries

set_option linter.style.header false

/-!
# Margins, mixtures and one-sided tests

Fix an electorate `V` on a finite candidate set `C`.

* `lotWin V (A, B)`: the probability that a random voter prefers lottery `A` to lottery `B`.
* `netWin V A B = lotWin V (A, B) - lotWin V (B, A)`, and the *margin*
  `margin V M B = ∫ netWin V A B dM(A)` of a lottery-lottery `M` against a lottery `B`.
  If `M` is maximal then `margin V M B ≥ 0` for every `B`, since `M` dominates the point mass at
  `B` (`margin_nonneg_of_dominates`).
* `mix t B P`: the lottery `(1 - t) B + t P`.
* `netWinToward V A B P`: the net vote share of `A` against `B` moved an infinitesimal step
  towards `P`, i.e. the limit of `netWin V A (mix t B P)` as `t ↓ 0` (`tendsto_netWin_mix`).
  Voters who are indifferent between `A` and `B` break the tie according to whether they prefer
  `B` or `P`. By dominated convergence, a lottery-lottery with nonnegative margin against every
  lottery also has nonnegative `netWinToward`-integral against every `(B, P)`
  (`integral_netWinToward_nonneg_of_forall`).
-/

@[expose] public section

namespace MaxLotLot

open ProbabilityTheory MeasureTheory Topology Filter

/-! ### The margin of a lottery-lottery against a lottery -/

section Margin

variable {C : Type} [Finite C] [MeasurableSpace C] [DiscreteMeasurableSpace C]
variable (V : ProbabilityMeasure (C → unitInterval))

/-- The probability that a random voter prefers lottery `p.1` to lottery `p.2`. -/
noncomputable def lotWin (p : ProbabilityMeasure C × ProbabilityMeasure C) : ℝ :=
  ((V : Measure (C → unitInterval)) (Prod.mk p ⁻¹' prefer_set)).toReal

lemma measurable_lotWin : Measurable (lotWin V (C := C)) :=
  (measurable_measure_prodMk_left (ν := (V : Measure (C → unitInterval)))
    (prefer_measurable (C := C))).ennreal_toReal

omit [Finite C] [DiscreteMeasurableSpace C] in
lemma abs_lotWin_le (p : ProbabilityMeasure C × ProbabilityMeasure C) : |lotWin V p| ≤ 1 := by
  unfold lotWin
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

lemma lotWin_prod (AA BB : ProbabilityMeasure (ProbabilityMeasure C)) :
    (((AA.prod BB).prod V) prefer_set : ℝ) =
      ∫ p, lotWin V p ∂((AA : Measure _).prod (BB : Measure _)) := by
  unfold lotWin
  rw [ProbabilityMeasure.prod_apply _ _ _ prefer_measurable, ENNReal.coe_toNNReal_eq_toReal,
    ProbabilityMeasure.toMeasure_prod, integral_toReal]
  · exact (measurable_measure_prodMk_left (ν := (V : Measure (C → unitInterval)))
      (prefer_measurable (C := C))).aemeasurable
  · exact Filter.Eventually.of_forall fun p => measure_lt_top _ _

lemma measurableSet_win (p : ProbabilityMeasure C × ProbabilityMeasure C) :
    MeasurableSet {u : C → unitInterval | p.1[Subtype.val ∘ u] > p.2[Subtype.val ∘ u]} :=
  measurable_prodMk_left (prefer_measurable (C := C))

/-- The integrand of `margin`: the net vote share of `A` against `B`. -/
noncomputable def netWin (A B : ProbabilityMeasure C) : ℝ := lotWin V (A, B) - lotWin V (B, A)

/-- The margin of `M` against `B`: the expected net vote share of `A ∼ M` against `B`. -/
noncomputable def margin (M : ProbabilityMeasure (ProbabilityMeasure C))
    (B : ProbabilityMeasure C) : ℝ :=
  ∫ A, netWin V A B ∂(M : Measure (ProbabilityMeasure C))

lemma measurable_netWin_left (B : ProbabilityMeasure C) : Measurable fun A => netWin V A B :=
  ((measurable_lotWin V).comp measurable_prodMk_right).sub
    ((measurable_lotWin V).comp measurable_prodMk_left)

omit [Finite C] [DiscreteMeasurableSpace C] in
lemma lotWin_nonneg (p : ProbabilityMeasure C × ProbabilityMeasure C) : 0 ≤ lotWin V p :=
  ENNReal.toReal_nonneg

omit [Finite C] [DiscreteMeasurableSpace C] in
lemma abs_netWin_le (A B : ProbabilityMeasure C) : |netWin V A B| ≤ 1 := by
  have h1 := abs_lotWin_le V (A, B)
  have h2 := abs_lotWin_le V (B, A)
  have h3 := lotWin_nonneg V (A, B)
  have h4 := lotWin_nonneg V (B, A)
  rw [abs_of_nonneg h3] at h1
  rw [abs_of_nonneg h4] at h2
  rw [netWin, abs_le]; constructor <;> linarith

/-- Domination of a point mass gives a nonnegative margin. -/
lemma margin_nonneg_of_dominates {MM : ProbabilityMeasure (ProbabilityMeasure C)}
    {B : ProbabilityMeasure C} (h : Dominates V MM (diracProba B)) : 0 ≤ margin V MM B := by
  unfold Dominates at h
  have h' : (((MM.prod (diracProba B)).prod V) prefer_set : ℝ) ≥
      (((diracProba B).prod MM).prod V) prefer_set := by exact_mod_cast h
  rw [lotWin_prod, lotWin_prod] at h'
  have hm1 : Measurable fun A : ProbabilityMeasure C => lotWin V (A, B) :=
    (measurable_lotWin V).comp measurable_prodMk_right
  have hm2 : Measurable fun A : ProbabilityMeasure C => lotWin V (B, A) :=
    (measurable_lotWin V).comp measurable_prodMk_left
  have e1 : ∫ p, lotWin V p ∂((MM : Measure (ProbabilityMeasure C)).prod
      (diracProba B : Measure (ProbabilityMeasure C))) =
      ∫ A, lotWin V (A, B) ∂(MM : Measure (ProbabilityMeasure C)) := by
    change ∫ p, lotWin V p ∂((MM : Measure (ProbabilityMeasure C)).prod (Measure.dirac B)) = _
    rw [Measure.prod_dirac, integral_map measurable_prodMk_right.aemeasurable
      (measurable_lotWin V).aestronglyMeasurable]
  have e2 : ∫ p, lotWin V p ∂((diracProba B : Measure (ProbabilityMeasure C)).prod
      (MM : Measure (ProbabilityMeasure C))) =
      ∫ A, lotWin V (B, A) ∂(MM : Measure (ProbabilityMeasure C)) := by
    change ∫ p, lotWin V p ∂((Measure.dirac B).prod (MM : Measure (ProbabilityMeasure C))) = _
    rw [Measure.dirac_prod, integral_map measurable_prodMk_left.aemeasurable
      (measurable_lotWin V).aestronglyMeasurable]
  rw [e1, e2] at h'
  have hb : ∀ q, |lotWin V q| ≤ 1 := abs_lotWin_le V
  unfold margin netWin
  rw [integral_sub (Integrable.of_bound hm1.aestronglyMeasurable 1
      (Eventually.of_forall fun A => by rw [Real.norm_eq_abs]; exact hb _))
    (Integrable.of_bound hm2.aestronglyMeasurable 1
      (Eventually.of_forall fun A => by rw [Real.norm_eq_abs]; exact hb _))]
  linarith

end Margin

/-! ### Mixtures of two lotteries -/

section Mix

variable {C : Type} [Finite C] [MeasurableSpace C] [DiscreteMeasurableSpace C]

/-- The lottery `(1 - t) B + t P`. -/
noncomputable def mix (t : unitInterval) (B P : ProbabilityMeasure C) : ProbabilityMeasure C :=
  ⟨ENNReal.ofReal (1 - t) • (B : Measure C) + ENNReal.ofReal t • (P : Measure C), by
    constructor
    simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (by linarith [t.2.2]) t.2.1]
    simp only [sub_add_cancel, ENNReal.ofReal_one]⟩

lemma integral_mix (t : unitInterval) (B P : ProbabilityMeasure C) (f : C → ℝ) :
    ∫ c, f c ∂(mix t B P : Measure C) =
      (1 - t) * ∫ c, f c ∂(B : Measure C) + t * ∫ c, f c ∂(P : Measure C) := by
  have := Fintype.ofFinite C
  change ∫ c, f c ∂(ENNReal.ofReal (1 - t) • (B : Measure C) + ENNReal.ofReal t • (P : Measure C))
    = _
  rw [integral_add_measure (Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top)
    (Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure,
    integral_smul_measure, ENNReal.toReal_ofReal (by linarith [t.2.2]),
    ENNReal.toReal_ofReal t.2.1, smul_eq_mul, smul_eq_mul]

end Mix

/-! ### Directional limits: moving `B` an infinitesimal step towards `P` -/

section Toward

variable {C : Type} [Finite C] [MeasurableSpace C] [DiscreteMeasurableSpace C]
variable (V : ProbabilityMeasure (C → unitInterval))

/-- Voters who prefer `A` to `B⁺`, where `B⁺` is `B` moved an infinitesimal step towards `P`:
they prefer `A` to `B`, or they are tied between `A` and `B` and prefer `B` to `P`. -/
def winToward (A B P : ProbabilityMeasure C) : Set (C → unitInterval) :=
  {u | B[Subtype.val ∘ u] < A[Subtype.val ∘ u] ∨
    (A[Subtype.val ∘ u] = B[Subtype.val ∘ u] ∧ P[Subtype.val ∘ u] < B[Subtype.val ∘ u])}

/-- Voters who prefer `B⁺` to `A`. -/
def loseToward (A B P : ProbabilityMeasure C) : Set (C → unitInterval) :=
  {u | A[Subtype.val ∘ u] < B[Subtype.val ∘ u] ∨
    (A[Subtype.val ∘ u] = B[Subtype.val ∘ u] ∧ B[Subtype.val ∘ u] < P[Subtype.val ∘ u])}

/-- The net vote share of `A` against `B⁺` (the one-sided limit of `netWin V A ((1-t)B + tP)` as
`t ↓ 0`, `tendsto_netWin_mix`). -/
noncomputable def netWinToward (A B P : ProbabilityMeasure C) : ℝ :=
  (V : Measure (C → unitInterval)).real (winToward A B P) -
    (V : Measure (C → unitInterval)).real (loseToward A B P)

lemma measurable_eu (A : ProbabilityMeasure C) :
    Measurable fun u : C → unitInterval => A[Subtype.val ∘ u] :=
  measurable_integral_eval (A := fun _ => A) measurable_const measurable_id

lemma measurableSet_winToward (A B P : ProbabilityMeasure C) :
    MeasurableSet (winToward A B P) :=
  (measurableSet_lt (measurable_eu B) (measurable_eu A)).union
    ((measurableSet_eq_fun (measurable_eu A) (measurable_eu B)).inter
      (measurableSet_lt (measurable_eu P) (measurable_eu B)))

lemma measurableSet_loseToward (A B P : ProbabilityMeasure C) :
    MeasurableSet (loseToward A B P) :=
  (measurableSet_lt (measurable_eu A) (measurable_eu B)).union
    ((measurableSet_eq_fun (measurable_eu A) (measurable_eu B)).inter
      (measurableSet_lt (measurable_eu B) (measurable_eu P)))

/-- Real-number core: `(1-t) b + t p < a` stabilizes as `t ↓ 0`. -/
lemma eventually_mix_lt_iff {a b p : ℝ} {t : ℕ → ℝ} (ht0 : ∀ n, 0 < t n)
    (htlim : Tendsto t atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ((1 - t n) * b + t n * p < a ↔ (b < a ∨ (a = b ∧ p < b))) := by
  have hx : Tendsto (fun n => (1 - t n) * b + t n * p) atTop (𝓝 b) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub htlim).mul
      (tendsto_const_nhds (x := b)) |>.add (htlim.mul (tendsto_const_nhds (x := p)))
  rcases lt_trichotomy a b with h | h | h
  · filter_upwards [hx.eventually (lt_mem_nhds h)] with n hn
    constructor
    · intro h'; linarith
    · rintro (h' | ⟨h', -⟩) <;> linarith
  · subst h
    refine Eventually.of_forall fun n => ?_
    have e : (1 - t n) * a + t n * p = a + t n * (p - a) := by ring
    rw [e]
    have := ht0 n
    constructor
    · intro h'; right; refine ⟨rfl, ?_⟩; by_contra hc; push Not at hc; nlinarith
    · rintro (h' | ⟨-, h'⟩)
      · linarith
      · nlinarith
  · filter_upwards [hx.eventually (gt_mem_nhds h)] with n hn
    exact ⟨fun _ => Or.inl h, fun _ => hn⟩

lemma eventually_lt_mix_iff {a b p : ℝ} {t : ℕ → ℝ} (ht0 : ∀ n, 0 < t n)
    (htlim : Tendsto t atTop (𝓝 0)) :
    ∀ᶠ n in atTop, (a < (1 - t n) * b + t n * p ↔ (a < b ∨ (a = b ∧ b < p))) := by
  have := eventually_mix_lt_iff (a := -a) (b := -b) (p := -p) ht0 htlim
  filter_upwards [this] with n hn
  have e : (1 - t n) * -b + t n * -p = -((1 - t n) * b + t n * p) := by ring
  rw [e, neg_lt_neg_iff] at hn
  rw [hn]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · left; linarith
    · right; exact ⟨by linarith, by linarith⟩
  · rintro (h | ⟨h1, h2⟩)
    · left; linarith
    · right; exact ⟨by linarith, by linarith⟩

/-- Along `t_n ↓ 0`, `netWin V A ((1 - t_n) B + t_n P) → netWinToward V A B P`, for every `A`. -/
lemma tendsto_netWin_mix (A B P : ProbabilityMeasure C) {t : ℕ → unitInterval}
    (ht0 : ∀ n, 0 < (t n : ℝ)) (htlim : Tendsto (fun n => (t n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => netWin V A (mix (t n) B P)) atTop (𝓝 (netWinToward V A B P)) := by
  have hdom : ∀ (s : ℕ → Set (C → unitInterval)) (s₀ : Set (C → unitInterval)),
      (∀ n, MeasurableSet (s n)) → MeasurableSet s₀ →
      (∀ u, ∀ᶠ n in atTop, (u ∈ s n ↔ u ∈ s₀)) →
      Tendsto (fun n => (V : Measure (C → unitInterval)).real (s n)) atTop
        (𝓝 ((V : Measure (C → unitInterval)).real s₀)) := by
    intro s s₀ hs hs₀ hev
    classical
    simp_rw [← integral_indicator_one (hs _), ← integral_indicator_one hs₀]
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
      (Eventually.of_forall fun n => (measurable_const.indicator (hs n)).aestronglyMeasurable)
      (Eventually.of_forall fun n => Eventually.of_forall fun u => ?_) (integrable_const 1)
      (ae_of_all _ fun u => ?_)
    · rw [Real.norm_eq_abs, Set.indicator_apply]
      split_ifs <;> simp only [Pi.one_apply, abs_one, abs_zero, zero_le_one, Std.le_refl]
    · refine tendsto_const_nhds.congr' ((hev u).mono fun n hn => ?_)
      by_cases h : u ∈ s₀
      · simp [h, hn.2 h]
      · simp [h, mt hn.1 h]
  have h1 : Tendsto (fun n => lotWin V (A, mix (t n) B P)) atTop
      (𝓝 ((V : Measure (C → unitInterval)).real (winToward A B P))) := by
    refine hdom _ _ (fun n => measurableSet_win (A, mix (t n) B P))
      (measurableSet_winToward A B P) fun u => ?_
    filter_upwards [eventually_mix_lt_iff (a := A[Subtype.val ∘ u]) (b := B[Subtype.val ∘ u])
      (p := P[Subtype.val ∘ u]) ht0 htlim] with n hn
    change (A[Subtype.val ∘ u] > (mix (t n) B P)[Subtype.val ∘ u]) ↔ _
    rw [integral_mix, gt_iff_lt, hn]
    rfl
  have h2 : Tendsto (fun n => lotWin V (mix (t n) B P, A)) atTop
      (𝓝 ((V : Measure (C → unitInterval)).real (loseToward A B P))) := by
    refine hdom _ _ (fun n => measurableSet_win (mix (t n) B P, A))
      (measurableSet_loseToward A B P) fun u => ?_
    filter_upwards [eventually_lt_mix_iff (a := A[Subtype.val ∘ u]) (b := B[Subtype.val ∘ u])
      (p := P[Subtype.val ∘ u]) ht0 htlim] with n hn
    change ((mix (t n) B P)[Subtype.val ∘ u] > A[Subtype.val ∘ u]) ↔ _
    rw [integral_mix, gt_iff_lt, hn]
    rfl
  exact h1.sub h2

omit [Finite C] [DiscreteMeasurableSpace C] in
lemma abs_netWinToward_le (A B P : ProbabilityMeasure C) : |netWinToward V A B P| ≤ 1 := by
  have h1 : (V : Measure (C → unitInterval)).real (winToward A B P) ≤ 1 := measureReal_le_one
  have h2 : (V : Measure (C → unitInterval)).real (loseToward A B P) ≤ 1 := measureReal_le_one
  have h3 := measureReal_nonneg (μ := (V : Measure (C → unitInterval))) (s := winToward A B P)
  have h4 := measureReal_nonneg (μ := (V : Measure (C → unitInterval))) (s := loseToward A B P)
  rw [netWinToward, abs_le]; constructor <;> linarith

/-- A sequence `t n ↓ 0` in the unit interval with every `t n > 0`. -/
lemma exists_seq_pos_tendsto_zero : ∃ t : ℕ → unitInterval,
    (∀ n, 0 < (t n : ℝ)) ∧ Tendsto (fun n => (t n : ℝ)) atTop (𝓝 0) := by
  let t : ℕ → unitInterval := fun n => ⟨1 / ((n : ℝ) + 2), by positivity, by
    rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]⟩
  have ht0 : ∀ n, 0 < (t n : ℝ) := fun n => by simp only [t]; positivity
  exact ⟨t, ht0, squeeze_zero (fun n => (ht0 n).le)
    (fun n => show 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) from
      one_div_le_one_div_of_le (by positivity) (by linarith))
    tendsto_one_div_add_atTop_nhds_zero_nat⟩

/-- `A ↦ netWinToward V A B P` is measurable (a pointwise limit of measurable functions). -/
lemma measurable_netWinToward (B P : ProbabilityMeasure C) :
    Measurable fun A => netWinToward V A B P := by
  obtain ⟨t, ht0, htlim⟩ := exists_seq_pos_tendsto_zero
  exact measurable_of_tendsto_metrizable (fun n => measurable_netWin_left V (mix (t n) B P))
    (tendsto_pi_nhds.2 fun A => tendsto_netWin_mix V A B P ht0 htlim)

/-- If `M` has nonnegative margin against every lottery, then also against every `B` moved an
infinitesimal step towards `P`: the margins against `mix t B P` converge to the
`netWinToward`-integral as `t ↓ 0`. -/
theorem integral_netWinToward_nonneg_of_forall {M : ProbabilityMeasure (ProbabilityMeasure C)}
    (hM : ∀ B, 0 ≤ margin V M B) (B P : ProbabilityMeasure C) :
    0 ≤ ∫ A, netWinToward V A B P ∂(M : Measure (ProbabilityMeasure C)) := by
  obtain ⟨t, ht0, htlim⟩ := exists_seq_pos_tendsto_zero
  have hconv : Tendsto (fun n => margin V M (mix (t n) B P)) atTop
      (𝓝 (∫ A, netWinToward V A B P ∂(M : Measure (ProbabilityMeasure C)))) :=
    tendsto_integral_of_dominated_convergence (fun _ => 1)
      (fun n => (measurable_netWin_left V _).aestronglyMeasurable) (integrable_const 1)
      (fun n => ae_of_all _ fun A => by rw [Real.norm_eq_abs]; exact abs_netWin_le V _ _)
      (ae_of_all _ fun A => tendsto_netWin_mix V A B P ht0 htlim)
  exact ge_of_tendsto' hconv fun n => hM _

end Toward

end MaxLotLot
