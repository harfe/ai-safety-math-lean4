---
title: Reinforcement learning for understanding Infrabayesianism
---

## Article

Let $A$ and $O$ be finite sets.
The set $A$ is the set of actions and $O$ is the set of observations.
Throughout this article $\gamma\in[0,1)$ is a discount factor.
The notation $\Delta X$ refers to the set of
probability measures on a topological space $X$ 
(using the Borel-$\sigma$-algebra).

**Definition (histories)**:
The set $(A\times O)^*$ denotes finite sequences of action-observation pairs
and its elements are called histories.

**Definition (destinies)**:
The set $(A\times O)^\omega$ denotes infinite sequences of action-observation pairs
and its elements are called destinies.

**Definition (momentary loss function)**:
A momentary loss function is a function $L:(A\times O)^*\to[0,1]$.

**Definition (total loss function)**:
Given a momentary loss function $L$ and a discount factor $\gamma\in[0,1)$,
the total loss $L^\gamma: (A\times O)^\omega\to[0,1]$ is defined by
$$L^\gamma((a_t,o_t)_{t=0}^\infty) = (1-\gamma) \sum_{t=0}^\infty \gamma^t L((a_0,o_0,\ldots,a_{t-1},o_{t-1})).$$

**Definition (policy)**:
A policy is a function of type $(A\times O)^*\to\Delta A$.
A deterministic policy is a function of type $(A\times O)^*\to A$.

**Definition (environment)**:
An environment is a function of type 
$(A\times O)^*\times A\to\Delta O$.


**Definition (probability distribution on destinies induced by a policy and environment)**:
If $\pi$ is a policy and $\mu$ is an environment,
then we define the probability distribution $\mu^\pi \in 
\Delta ((A\times O)^\omega)$
as the unique probability distribution that satisfies
$$\mu^\pi\left(\{(a_t,o_t)_{t=0}^l\} \times (A\times O)^\omega\right) =
\prod_{t=0}^l \pi(a_t | a_0, o_0, \ldots, a_{t-1}, o_{t-1}) \mu(o_t|a_0,o_0,\ldots,a_t)$$
for all cylinder sets $\left\{(a_t,o_t)_{t=0}^l\right\} \times (A\times O)^\omega$.
This is the distribution over destinies that results when 
the probability of actions and observations
at each step are given by $\pi$ and $\mu$.

**Definition (expected total loss)**:
Given a total loss function $L^\gamma$,
the expected total loss of a policy $\pi$ in an environment $\mu$
is given by $\mathbb{E}_{h\sim\mu^\pi}\left[L^\gamma(h)\right]$.


**Proposition 1 (existence of optimal policy)**:
Assume that $A$ and $O$ are finite and that $A$ is nonempty.
Then, for any given environment $\mu$ there exists
an optimal policy $\pi$ that minimizes
$\mathbb{E}_{h\sim\mu^\pi}\left[L^\gamma(h)\right]$.
That policy can be chosen to be deterministic.

**Definition (regret)**:
Given an environment $\mu$ and a total loss function $L^\gamma$,
the regret of a policy $\pi$ is defined by
$$\text{Reg}(\pi,\mu,L^\gamma) :=
\mathbb{E}_{h\sim\mu^\pi}\left[L^\gamma(h)\right] - 
\inf_{\pi' \in \Pi}
\mathbb{E}_{h\sim\mu^{\pi'}}\left[L^\gamma(h)\right],$$
where $\Pi$ is the set of policies.

**Definition (non-anytime learnable)**:
Let $I$ be an index set.
A class $\{\mu_i\}_{i\in I}$ of environments is said to be
non-anytime learnable if there exists a family of policies 
$\{\pi^\gamma\}_{\gamma\in[0,1)}$
such that
$\lim_{\gamma\nearrow 1} \text{Reg}(\pi^\gamma,\mu_i,L^\gamma) = 0$
holds for all $i\in I$.
In that case, we say that 
$\{\pi^\gamma\}_{\gamma\in[0,1)}$ learns the class 
$\{\mu_i\}_{i\in I}$.

**Definition (Bayes-optimal policy)**:
Let $\zeta$ be a probability distribution
over a countable class $\{\mu_i\}_{i\in I}$ of environments.
We call $\zeta$ a prior in this context.
Let $L^\gamma$ be a total loss function.
A policy $\pi^*_\zeta$ is said to be Bayes-optimal if it minimizes
$\pi\mapsto
\mathbb{E}_{\mu\sim\zeta} \left[\mathbb{E}_{h\sim\mu^\pi}\left[L^\gamma(h)\right]\right]$.

**Definition (non-dogmatic prior)**:
Let $\zeta$ be a probability distribution 
over a countable class $\{\mu_i\}_{i\in I}$ of environments.
We call $\zeta$ non-dogmatic prior if $\zeta(\{\mu_i\})>0$ for all $i\in I$.


**Proposition 2 (Bayes-optimal policy learns class)**:
Let $\zeta$ be a non-dogmatic prior
with respect to the countable class $\{\mu_i\}_{i\in I}$ of environments.
If the class $\{\mu_i\}_{i\in I}$ is non-anytime learnable,
then the family $\{\pi^{*,\gamma}_\zeta\}_{\gamma\in[0,1)}$
(where $\pi^{*,\gamma}_\zeta$ is the Bayes-optimal policy for $L^\gamma$ and $\zeta$)
learns the class $\{\mu_i\}_{i\in I}$.

## Commentary and source material

The article roughly follows
"An Introduction to Reinforcement Learning for Understanding Infra-Bayesianism"
from https://www.lesswrong.com/s/n7qFxakSnxGuvmYAX/p/gd4ALPL9nSyTgzccz
until Proposition 2.

It also takes the comments under that post into account,
which leads to some minor differences to the LessWrong post.

Bayes-optimal policies were only defined for a countable class of environments here,
so that we do not need to add conditions on measurability.


