module
public import AISafetyMath.Solutions.NL_Conjecture.DLorell.Connected
public import AISafetyMath.Solutions.NL_Conjecture.DLorell.Envelope
public import AISafetyMath.Solutions.NL_Conjecture.DLorell.SeedConstant
public import AISafetyMath.Solutions.NL_Conjecture.DLorell.Race

/-!
# §12. The universal cell-defect bound and the Main Theorem


## Structure

`stoch_to_det.T_le_Cstar` rests on exactly two statements:

1. `stoch_to_det.Connected.reduce_to_connected` — §3, entirely finite;
2. `T_le_Cstar_connected` — §§4-11, the connected case.

The whole continuous tier (`stoch_to_det.Seed`, `stoch_to_det.Quotient`,
`stoch_to_det.Scalar`, `stoch_to_det.Cone`,
`stoch_to_det.SeedConstant`) is reached only through the second, with three
available constant assemblies.

## The chain of Theorem 12.1

```
R_cell ≤ 3 I(A;Z ∣ ε,L₀) ≤ 3 H(A ∣ ε,L₀)          (I ≤ H)
       ≤ 3C₀[M + I(V;Z ∣ L₀)]                      (Thm 11.1)
       ≤ 3C₀[3M + Q⁽²⁾] ≤ 9C₀(M + Q⁽²⁾)            (Lem 5.6(d))
𝒟_w   ≤ R_cell + b_Z                               (Thm 5.7)
       ≤ 9C₀M + 9C₀Q⁽²⁾ + b_Z
       ≤ 9C₀M + (54C₀+1) b_Z                       (Lem 5.6(c): Q⁽²⁾ ≤ 6b_Z)
       ≤ 9C₀M + (108C₀+2) B                        (Lem 5.3: b_Z ≤ 2B)
       ≤ (108C₀+2) τ                               (τ = M + B)
T      ≤ (108C₀+3) τ                               (Cor 4.4)
```

## Constants: three routes, same lemmas

| Theorem | Constant | Difference |
|---|---|---|
| `T_le_Cstar` | `108C₀+3 < 4.94×10¹⁶` (`Cstar_lt_weak`) | baseline assembly |
| `T_le_CstarSharp` | `12C₀+3 < 5.37×10¹⁵` | uses `I(V;Z∣L₀) ≤ 2b_Z` (Lem 5.4), no co-info detour |
| `T_le_Cstar_sharpest` | `6C₀+3 < 2.69×10¹⁵` | adds the single-replica form of Thm 11.1 |

All three run on the same lemmas; only the assembly differs.
-/

@[expose] public section

namespace stoch_to_det

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

private theorem main_M_nonneg {p : α × β → ℝ} (D : SeedSetup p) : 0 ≤ D.M := by
  exact condMI_nonneg D.L.joint_isPMF
    (fun q => q.2.1) (fun q => q.2.2) (fun q => q.1)

private theorem main_Bq_nonneg {p : α × β → ℝ} (D : SeedSetup p) : 0 ≤ D.Bq := by
  unfold SeedSetup.Bq
  exact add_nonneg
    (condMI_nonneg D.L.joint_isPMF
      (fun q => q.1) (fun q => q.2.1) (fun q => q.2.2))
    (condMI_nonneg D.L.joint_isPMF
      (fun q => q.1) (fun q => q.2.2) (fun q => q.2.1))

/-- **Theorem 12.1** (universal ungated cell-defect bound,
*gumbel-cell-defect-universal*):
`𝒟_w(p,L) ≤ (108 C₀ + 2) τ(p)` for connected support. -/
theorem Dwdefect_le {p : α × β → ℝ} (D : SeedSetup p)
    (K : Clustering D) (R : RaceQuantities D K) :
    Dwdefect D ≤ (108 * C0 + 2) * tau p := by
  let pairI := condMI (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2)
    (fun u => u.1) (replicaLaw D)
  have hC0 : 0 ≤ C0 := C0_pos.le
  have hM := main_M_nonneg D
  have hB := main_Bq_nonneg D
  have hRseed : Rcell D ≤ 3 * C0 * (D.M + pairI) := by
    calc
      Rcell D ≤ 3 * R.winnerEntropy := R.rcell_le
      _ ≤ 3 * (C0 * (D.M + pairI)) :=
        mul_le_mul_of_nonneg_left (seed_constant R) (by norm_num)
      _ = 3 * C0 * (D.M + pairI) := by ring
  have hpair : D.M + pairI ≤ 3 * D.M + Q2 D := by
    dsimp [pairI]
    linarith [pair_le_Q2_add_two_M D]
  have hR : Rcell D ≤ 3 * C0 * (3 * D.M + Q2 D) :=
    hRseed.trans (mul_le_mul_of_nonneg_left hpair (mul_nonneg (by norm_num) hC0))
  have hQ : (3 * C0) * Q2 D ≤ (3 * C0) * (6 * bZ D) :=
    mul_le_mul_of_nonneg_left (Q2_le_six_bZ D)
      (mul_nonneg (by norm_num) hC0)
  have hcoef : 0 ≤ 18 * C0 + 1 := by nlinarith
  have hb := mul_le_mul_of_nonneg_left (bZ_le_two_Bq D) hcoef
  rw [D.tau_eq_M_add_Bq]
  calc
    Dwdefect D ≤ Rcell D + bZ D := Dwdefect_le_Rcell_add_bZ D
    _ ≤ 3 * C0 * (3 * D.M + Q2 D) + bZ D := by
      simpa [add_comm] using add_le_add_right hR (bZ D)
    _ ≤ 9 * C0 * D.M + (18 * C0 + 1) * bZ D := by
      nlinarith
    _ ≤ 9 * C0 * D.M + (36 * C0 + 2) * D.Bq := by
      nlinarith
    _ ≤ (108 * C0 + 2) * (D.M + D.Bq) := by
      nlinarith [mul_nonneg hC0 hM, mul_nonneg hC0 hB]

/-- **The connected case.** This is the single statement
`T_le_Cstar` consumes from §§4-11. -/
theorem T_le_Cstar_connected {p : α × β → ℝ} (hp : IsPMF p)
    (hconn : IsConnected (support p)) :
    T p ≤ Cstar * tau p := by
  obtain ⟨D⟩ := exists_seedSetup hp hconn
  obtain ⟨K⟩ := exists_clustering D
  obtain ⟨R⟩ := exists_raceQuantities D K
  have hT := T_le_of_Dwdefect_le D (integrable_winnerScore D) (Dwdefect_le D K R)
  rw [Cstar]
  convert hT using 1 ; ring

/-- **Theorem 12.2 (Main Theorem, stoch_to_det)**.

For every finite law `p` on a finite product alphabet,
`T(p) ≤ C⋆ · τ(p)` with `C⋆ = 108 C₀ + 3`.

The constant is universal: it depends on no alphabet, no support size, no
prior, and no number of latent values. -/
theorem T_le_Cstar {p : α × β → ℝ} (hp : IsPMF p) : T p ≤ Cstar * tau p :=
  reduce_to_connected Cstar (fun _q hq hconn => T_le_Cstar_connected hq hconn) p hp

end stoch_to_det
