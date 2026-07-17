---
title: Are (Approximately) Deterministic Natural Latents All You Need?
---

## Main Article

Throughout this article, $A$, $B$, $C$, $X$, $Y$, $L$ are finite sets.
In the context of a distribution $Q$ over $A\times B\times C$,
and an element $a\in A$, we sometimes
denote the event $\{(x,y,z)\in A\times B\times C \mid x = a\}$
simply by $a$ itself.
Similar notations can be used for $b\in B$ or $c\in C$
in that context.
This will allow us to write things like $Q(c\mid a)$ or $Q(b)$
for certain conditionals or marginals.
The KL-divergence and conditional entropy use nats, not bits.

**Definition (fork factorized distribution)**:
If $Q$ is a distribution over the cartesian product of $A$, $B$, $C$ (in any order),
then the fork factorized distribution $Q_{B\leftarrow A\rightarrow C}$
is a distribution over the same space as $Q$,
and is defined by
$$Q_{B\leftarrow A\rightarrow C}(a,b,c) = Q(a)Q(b\mid a)Q(c\mid a)$$
(or $Q_{B\leftarrow A\rightarrow C}(a,b,c) = 0$ if $Q(a)=0$)
for all $a\in A$, $b\in B$, $c\in C$.

**Definition (chain factorized distribution)**:
If $Q$ is a distribution over the cartesian product of $A$, $B$, $C$ (in any order),
then the chain factorized distribution $Q_{A\rightarrow B\rightarrow C}$
is a distribution over the same space as $Q$,
and is defined by
$$Q_{A\rightarrow B\rightarrow C}(a,b,c) = Q(a)Q(b\mid a)Q(c\mid b)$$
(or $Q_{A\rightarrow B\rightarrow C}(a,b,c) = 0$ 
if $Q(a)=0$ or $Q(b)=0$)
for all $a\in A$, $b\in B$, $c\in C$.

**Definition (stochastic natural latent error)**:
Let $X$, $Y$, $L$ be finite sets, 
$Q$ be a probability distribution on
$L\times X\times Y$, and $\varepsilon\ge0$.
Then we say that $Q$ has a stochastic natural latent error of at most $\varepsilon$ if
the following three conditions hold:
$$\varepsilon \ge D_{KL}(Q \parallel Q_{X\leftarrow L \rightarrow Y}) $$

$$\varepsilon \ge D_{KL}(Q \parallel Q_{Y\rightarrow X \rightarrow L}) $$

$$\varepsilon \ge D_{KL}(Q \parallel Q_{X\rightarrow Y \rightarrow L}) $$

Here, $D_{KL}$ denotes the KL-divergence.

**Definition (deterministic natural latent error)**:
Let $X$, $Y$, $L$ be finite sets, 
$Q$ be a probability distribution on
$L\times X\times Y$, and $\varepsilon\ge0$.
Then we say that $Q$ has deterministic natural latent error of at most $\varepsilon$ if
the following three conditions hold:
$$\varepsilon \ge D_{KL}(Q \parallel Q_{X\leftarrow L \rightarrow Y}) $$
$$\varepsilon \ge H_Q(L\mid X) $$
$$\varepsilon \ge H_Q(L\mid Y) $$
Here, 
$H_Q(L\mid X) = -\sum_{l,x}Q(l,x)\log Q(l\mid x)$
denotes the 
conditional entropy of $L$ given $X$ under distribution $Q$.

**Definition (existence of stochastic natural latent)**:
Given $\varepsilon\ge0$ and 
a distribution $P$ on $X\times Y$ (with $X$, $Y$ finite sets),
we say there exists a stochastic natural latent of $P$ 
with approximation error $\varepsilon$,
if there exists a finite set $L$ and a probability distribution $Q$ on $L\times X\times Y$,
such that the marginal of $Q$ on $X\times Y$ is $P$,
and $Q$ has stochastic natural latent error of at most $\varepsilon$.

**Definition (existence of deterministic natural latent)**:
Given $\varepsilon\ge0$ and 
a distribution $P$ on $X\times Y$ (with $X$, $Y$ finite sets),
we say there exists a deterministic natural latent of $P$ 
with approximation error $\varepsilon$,
if there exists a finite set $L$ and a probability distribution $Q$ on $L\times X\times Y$,
such that the marginal of $Q$ on $X\times Y$ is $P$,
and $Q$ has deterministic natural latent error of at most $\varepsilon$.

**Theorem (exact case)**:
Let $X$, $Y$ be finite sets and $P$ be a probability distribution on $X\times Y$.
If there exists a stochastic natural latent of $P$ 
with approximation error $0$,
then there exists a deterministic natural latent of $P$  
with approximation error $0$.


**Conjecture**:
Let $X$, $Y$ be finite sets and $P$ be a probability distribution on $X\times Y$, and let $\varepsilon\ge0$.
If there exists a stochastic natural latent of $P$ 
with approximation error $\varepsilon$,
then there exists a deterministic natural latent of $P$  
with approximation error $c\varepsilon$,
where $c>0$ is a global constant 
independent of $X$, $Y$, $P$, $\varepsilon$.


## Commentary and source material

The article roughly follows
"$500 Bounty Problem: Are (Approximately) Deterministic Natural Latents All You Need?" from
https://www.lesswrong.com/posts/e9KwDDdAxborNSuCd/usd500-bounty-problem-are-approximately-deterministic.

There are some differences to the LessWrong article:
- We restrict ourselves to finite value spaces
- We talk in probability distributions rather than random variables.
- We allow any global linear bound, and not just linear bounds with small constants.


