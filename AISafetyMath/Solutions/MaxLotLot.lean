module

public import AISafetyMath.Solutions.MaxLotLot.MaxLot
public import AISafetyMath.Solutions.MaxLotLot.FiniteLot
public import AISafetyMath.Solutions.MaxLotLot.Counterexample

/-!
# Maximal lottery-lotteries: solution

## The counterexample

These six files import only Mathlib and each other, and can be read on their own; start from
`Counterexample.lean`.

* `Lotteries`   — lotteries, lottery-lotteries, `Dominates`, and the statements `MainConjecture`,
  `HasFiniteVoters`, `finiteVotersConjecture`.
* `Margin`      — `lotWin`, `netWin`, `margin`, mixtures `mix t B P`, and the one-sided tests
  `netWinToward` with `integral_netWinToward_nonneg_of_forall`.
* `CounterexampleCertificate` — `certF_le`: the five-test certificate is `≤ -2` on the whole
  simplex, as a statement about real numbers.
* `CounterexampleLotteries`, `CounterexampleProfile` — lotteries on three candidates, the
  electorate `Counterexample.V`, and `Counterexample.nwt_eq`: `netWinToward` for `V` is the `nwt`
  of `CounterexampleCertificate`.
* `Counterexample` — **`fv_refutation`** and **`refutation`**: `Counterexample.V` has no maximal
  lottery-lottery.

## The rest of the solution

* `SymNashGame` — symmetric Nash games and their equilibria.
* `MaxLot`      — maximal lotteries over candidates.
* `FiniteLot`   — `exists_of_finite_lot`: with finitely many lotteries, a maximal lottery-lottery
  exists.

## Not stated here

* `solution` and `fv_solution` are false: their negations are `refutation` and `fv_refutation`.
* `mc_of_fv` holds vacuously, since `finiteVotersConjecture` is false.
* `no_nasheq_discontinuous` is not proved.
-/
