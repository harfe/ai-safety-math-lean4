module

public import AISafetyMath.Solutions.NL_Conjecture.Setup
public import AISafetyMath.Solutions.NL_Conjecture.Latents
public import AISafetyMath.Solutions.NL_Conjecture.Conjecture
public import AISafetyMath.Solutions.NL_Conjecture.Bridge


/-!
This file solves `AISafetyMath/Targets/NL_Conjecture.lean`.

The main definition is `MainConjecture`.

The development is split across `AISafetyMath/Solutions/NL_Conjecture/`:
* `Setup.lean`      — fork/chain densities, natural- and deterministic-latent
                       predicates on `A × B × C`, and `conjecture_exact_case_aux`.
* `Latents.lean`     — `IsStochasticNL`/`IsDeterministicNL`/`HasStochasticNL`/
                       `HasDeterministicNL` and `conjecture_exact_case`.
* `Conjecture.lean`  — `MainConjecture` and the proof/refutation slots.
* `Bridge.lean`      — connects `Conjecture.lean` to the real-valued `stoch_to_det`
                       development and proves `NaturalLatents.conjecture_solution`.

This file just re-exports all of the above under `AISafetyMath.Solutions.NL_Conjecture`.
-/

@[expose] public section
