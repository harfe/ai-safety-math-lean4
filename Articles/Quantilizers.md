---
title: Quantilizers
---

## Article

Throughout this article,
Let $A$ be a finite set of actions,
$U : A\to [0,1]$ be a utility function,
and $\gamma \in \Delta A$ be a prior over actions.

**Definition (sorted action function)**:
A function $f : [0,1]\to A$ is called a sorted action function
if $f$ is measurable, 
$U\circ f$ is non-decreasing,
and
$$ \mu(\{x\in[0,1]\mid f(x) = a\}) = \gamma(\{a\}), $$
where $\mu$ is the Lebesgue measure on $[0,1]$.

**Lemma (existence of sorted action function)**:
There exists a finite action function.

Note that there can be multiple sorted action functions.
For the remainder, we just pick a fixed one.

**Definition (quantilizer)**:
Let $q\in(0,1]$.
A $q$-quantilizer picks a uniformly random $x\in[1-q,1]$
and then returns $f(x)$.
We will write $Q_{U,\gamma,q,f}\in\Delta A$ for the corresponding distribution over actions.


**Lemma (cost bound on quantilizers)**:
Let $q\in(0,1]$.
Let $c:A\to \mathbb{R}_{\ge0}$ be a cost function such that
$\mathbb{E}_{a\sim\gamma}[c(a)] \le 1$.
Then 
$\mathbb{E}_{a\sim Q_{U,\gamma,q,f}}[c(a)] \le 1/q$.

**Definition (conservative cost constraint)**:
Let $p\in\Delta A$ and $t>1$ be given.
We say that $p$ satisfies the conservative cost constraint
for threshold $t$ if
for all cost functions $c : A\to\mathbb{R}_{\ge0}$
the implication
$$
\mathbb{E}_{a\sim\gamma}[c(a)] \le 1
\implies
\mathbb{E}_{a\sim p}[c(a)] \le t
$$
holds.

**Theorem (quantilizer optimality)**:
Let $t>1$ be given.
We choose $q = 1/t$.
Then the $q$-quantilizer $Q_{U,\gamma,q,f}$
satisfies the conservative cost constraint with threshold $t$,
and, among all $p\in\Delta A$ satisfying the constraint, 
maximizes $\mathbb{E}_p[U]$.


## Commentary and source material

The article roughly follows 
https://intelligence.org/files/QuantilizersSaferAlternative.pdf
until Theorem 1.

That article maps actions to a distribution over outcomes,
and then considers the expected utility of each action.
Instead, we take a shortcut by directly assigning a (deterministic) utility to each action.


*Observation*: The construction is not easily extendable to infinite A.
The best action is given by $f(1)$ (due to monotonicity), but
if A is infinite there might not be a best action.

