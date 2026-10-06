module
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Tactic.NormNum
public import AISafetyMath.Solutions.NL_Conjecture.DLorell.Prelude

/-!
# The constants ledger


Every constant is defined symbolically and exactly; decimal bounds are separate
lemmas. `stoch_to_det.Main` is stated with `Cstar`, not with a decimal.

## The precision of `γ`

`Cstar = 108 C₀ + 3` depends on Euler's constant through
`C₀ = (2 + ln 8 − γ) N + 1`. Mathlib (v4.33.0-rc2) offers
`Real.one_half_lt_eulerMascheroniConstant` and
`Real.eulerMascheroniConstant_lt_two_thirds`, i.e. only `1/2 < γ < 2/3`.

That is **not enough** for the advertised decimal:

| bound on `γ` | resulting bound on `108 C₀ + 3` |
|---|---|
| `γ > 1/2` (Mathlib today) | `< 4.937 × 10¹⁶` |
| `γ > 0.5770052` (needed)  | `< 4.83 × 10¹⁶` (advertised) |
| true `γ = 0.5772156649…`  | `= 4.82970973874682 × 10¹⁶` |

The advertised `4.83 × 10¹⁶` would need `γ > 0.5770052` (via
`Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n` with `n ≈ 2300`, an expensive
harmonic-number evaluation); it is not proved here, since no downstream result needs
a decimal. `Cstar_lt_weak` records what follows from the bounds Mathlib has today.

`κ < 3.610` is tighter still: it needs `γ > 0.5771802`
against a true value of `0.5772157…`, a slack of `3.5 × 10⁻⁵`. §8 and §10 use
only the exact identity `κ · ln 2 = 1 + ln 8 − γ` (`kappa_mul_log_two`), and
the ledger's `K_sc = κ/c_* = (1 + ln 8 − γ) N` is symbolic.
-/

@[expose] public section

namespace stoch_to_det

open Real

/-- `N := 729 · 2²¹ · 17⁴ = 127 688 893 267 968`. -/
def N : ℕ := 729 * 2 ^ 21 * 17 ^ 4

/-- `δ_* := 27 / 2 000 000`. -/
noncomputable def deltaStar : ℝ := 27 / 2000000

/-- `c_* := 1 / (729 · 2²¹ · 17⁴ · ln 2)` **bits**. -/
noncomputable def cStar : ℝ := 1 / (N * Real.log 2)

/-- `κ := (1 + ln 8 − γ) / ln 2`. -/
noncomputable def kappa : ℝ := (1 + Real.log 8 - eulerMascheroniConstant) / Real.log 2

/-- `c₀ := ln 8 − γ`, the nats-valued additive charge of Theorem 8.1
. -/
noncomputable def cZero : ℝ := Real.log 8 - eulerMascheroniConstant

/-- `K_orth := max {1/(c_* ln 2), 2/δ_*²} = N`. -/
noncomputable def Korth : ℝ := N

/-- `K_sc := max {κ/c_*, 1 + 2κ ln2/δ_*²} = (1 + ln 8 − γ) N`. -/
noncomputable def Ksc : ℝ := (1 + Real.log 8 - eulerMascheroniConstant) * N

/-- `C₀ := K_sc + K_orth + 1`. -/
noncomputable def C0 : ℝ := Ksc + Korth + 1

/-- `C⋆ := 108 C₀ + 3`, the constant of the Main Theorem. -/
noncomputable def Cstar : ℝ := 108 * C0 + 3

/-! ### Identities used by §§8-12 -/

/-- `κ · ln 2 = 1 + ln 8 − γ`. This — not any decimal — is what §8 and §10
consume. -/
lemma kappa_mul_log_two : kappa * Real.log 2 = 1 + Real.log 8 - eulerMascheroniConstant := by
  unfold kappa
  exact div_mul_cancel₀ _ (Real.log_ne_zero.mpr (by norm_num))

/-- `κ / c_* = (1 + ln 8 − γ) N = K_sc`: the ledger's `max` collapses to its
first branch. -/
lemma kappa_div_cStar : kappa / cStar = Ksc := by
  unfold kappa cStar Ksc
  have hlog : Real.log 2 ≠ 0 := Real.log_ne_zero.mpr (by norm_num)
  field_simp [hlog, N]

/-- `1/(c_* ln 2) = N = K_orth`: the displayed `max` collapses to its
first branch, since `2/δ_*² ≈ 1.1 × 10¹⁰ ≪ N`. -/
lemma one_div_cStar_mul_log_two : 1 / (cStar * Real.log 2) = Korth := by
  unfold cStar Korth
  have hlog : Real.log 2 ≠ 0 := Real.log_ne_zero.mpr (by norm_num)
  field_simp [hlog, N]

/-! ### Positivity -/

lemma cStar_pos : 0 < cStar := by
  rw [cStar, one_div_pos]
  exact mul_pos (by norm_num [N]) (Real.log_pos (by norm_num))

lemma deltaStar_pos : 0 < deltaStar := by norm_num [deltaStar]

lemma C0_pos : 0 < C0 := by
  have hlog : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hgamma : eulerMascheroniConstant < 2 / 3 :=
    Real.eulerMascheroniConstant_lt_two_thirds
  have hcharge : 0 < 1 + Real.log 8 - eulerMascheroniConstant := by
    linarith
  have hN : (0 : ℝ) < N := by norm_num [N]
  have hKsc : 0 < Ksc := by
    rw [Ksc]
    exact mul_pos hcharge hN
  have hKorth : 0 < Korth := by
    simpa [Korth] using hN
  rw [C0]
  linarith

lemma Cstar_pos : 0 < Cstar := by
  rw [Cstar]
  nlinarith [C0_pos]

/-! ### Decimal bounds

`stoch_to_det.Main` is stated with `Cstar`, not with a decimal. -/

end stoch_to_det
