module

public import AISafetyMath.Solutions.ConverseLawvere.Basics
public import AISafetyMath.Solutions.ConverseLawvere.SigmaCompact

/-!
This file solves `AISafetyMath/Targets/ConverseLawvere.lean` minus the main conjecture
(`compconfigs/ConverseLawvere_without_conjecture.json`).

The solution consists of exactly the files imported here:
* `Basics.lean`       — the target's definitions, `diag_of_main`, `lawvereDomDiag_of_fp`,
                        `lawvereDomDiag_unitInterval`, `lawvereDomDiag_iff_fp`.
* `SigmaCompact.lean` — `not_sigmaCompact`.

`MainConjecture` (`conjecture_solution` / `conjecture_refutation`) is Garrabrant's open problem.
Exploratory work on it, not needed for the comparator, lives in `ConverseLawvere/Exploratory/`
(start from `Exploratory/Obstructions.md`).
-/
