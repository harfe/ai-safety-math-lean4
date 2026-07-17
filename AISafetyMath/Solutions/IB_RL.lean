
import Mathlib

import AISafetyMath.Solutions.TrajectoryMeasure
import AISafetyMath.Solutions.RLProofs

/-
This file formalizes the definitions and propositions in
Articles/IB_RL.md

The main results are `exists_optimal_policy` and `bayes_optimal_learns_class`.
It also includes a number of sanity-check lemmas.

To keep this file readable, the definitions and the (often long) proofs live in
two helper files in this directory, which this file simply re-exposes:

* `AISafetyMath.Solutions.TrajectoryMeasure` — the basic definitions (`History`,
  `Destiny`, `Policy`, `Environment`, `totalLoss`, `trajectoryMeasure`,
  `expectedTotalLoss`, …), the Ionescu–Tulcea trajectory-measure construction and
  its sanity checks, and the μ-uniform Lévy–Prokhorov continuity of the trajectory
  law in the Policy (`trajectoryMeasure_continuous`).

* `AISafetyMath.Solutions.RLProofs` — Proposition 1 (`exists_optimal_policy`: an
  optimal, indeed deterministic, Policy exists) via the barycentric determinisation
  argument, and Proposition 2 (`bayes_optimal_learns_class`) together with the regret
  machinery (`regret`, `LearnsEnvClass`, `IsBayesOptimalPolicy`, …). The
  `EReal`-valued `regret` (loss of `π` minus the infimum of losses over all policies,
  as in the target) is related to the real-valued workhorse `regretR` (difference to
  `best_policy`) via `regret_eq_coe_regretR`, since the infimum is attained.

All names live in the `IB_RL` namespace, exactly as in `Targets/IB_RL.lean`.
-/
