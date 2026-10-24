---
title: Logical Induction
---

**Definition (sentences)**:
We start out with a nonempty set of so-called prime sentences.
A sentence is any expression that (recursively) combines prime sentences
via logical $`\land`$, $`\lor`$, $`\lnot`$ operators.
We commonly write $`\mathcal{S}`$ for the set of all sentences.

We assume that prime sentences come with an injective encoding over some finite alphabet.
Sentences can then be encoded naturally by adding symbols for $`\land`$, $`\lor`$, $`\lnot`$
and a prefix symbol for atoms.

**Definition (world)**:
A world is any truth assignment $`\mathbb{W}:\mathcal{S}\to\mathbb{B}`$,
where $`\mathbb{B}=\{0,1\}`$ is the set of boolean values
(with $`0`$ meaning false and $`1`$ meaning true).

**Definition (propositionally consistent)**:
A world $`\mathbb{W}:\mathcal{S}\to\mathbb B`$ is called propositionally consistent if
$`\mathbb{W}(\phi\land\psi) = \mathbb{W}(\phi)\land\mathbb{W}(\psi)`$,
$`\mathbb{W}(\phi\lor\psi) = \mathbb{W}(\phi)\lor\mathbb{W}(\psi)`$,
and $`\mathbb{W}(\lnot\phi) = \lnot\mathbb{W}(\phi)`$.

Given a set $`D`$ of sentences, we define $`\mathcal{PC}(D)`$ to be the set of all
propositionally consistent worlds $`\mathbb{W}`$ where 
$`\mathbb{W}(\phi)=1`$ for all $`\phi\in D`$.


**Definition (efficiently computable)**:
A sequence $`(x_n)_{n\in\mathbb N_0}`$ is called efficiently computable if
there is a computable function that outputs $`x_n`$ on input $`n`$
with runtime polynomial in $`n`$ (i.e., with $`n`$ encoded in unary).

**Definition (belief state)**:
A belief state is a map 
$`\mathbb{P}:\mathcal{S}\to\mathbb{Q}\cap[0,1]`$
with finite support.

**Definition (valuation sequence)**:
A valuation sequence 
$`\mathbb V`$ is a sequence $`(\mathbb V_i)_{i\in\mathbb N_0}`$ of 
valuations $`\mathbb V_i:\mathcal S\to[0,1]`$.

**Definition (market)**:
A market is a computable sequence
$`(\mathbb{P}_i)_{i\in\mathbb N_0}`$ of pricings
$`\mathbb{P}_i:\mathcal{S}\to\mathbb{Q}\cap[0,1]`$.
Here, computable means that the map 
$`(s, i)\mapsto \mathbb P_i(s)`$ is computable.

**Definition (deductive process)**:
A deductive process is a computable sequence
$`(D_i)_{i\in\mathbb N_0}`$ of finite sets of sentences,
with $`D_{i}\subseteq D_{i+1}`$ for all $`i\in\mathbb N_0`$.
Here, computable means that on input $`n`$ the 
output is the concrete finite list of sentences.

**Definition (valuation feature)**:
A valuation feature $`\alpha : [0,1]^{\mathbb N_0\times\mathcal{S}}\to\mathbb R`$
of rank $`n`$ is a continuous function from valuation sequences to $`\mathbb R`$
that only depends on valuations $`\mathbb V_i`$ with $`0\le i \le n`$.
The set of all valuation features of rank $`n`$ is denoted by $`\mathcal{F}_n`$.
The topology used on $`[0,1]^{\mathbb N_0\times\mathcal{S}}`$ is the product topology.

**Definition (price feature)**:
For each $`\phi\in\mathcal S`$ and $`n\in \mathbb N_0`$,
we define a price feature 
$`\phi^{*n}\in\mathcal{F}_n`$
by the formula $`\phi^{*n}(\mathbb V) = \mathbb V_n(\phi)`$,
where $`\mathbb V`$ is a valuation sequence.

**Definition (expressible features)**:
An expressible feature is a valuation feature expressible by an
algebraic expression built from price features $`\phi^{*n}`$ 
(for any $`\phi\in\mathcal S`$, $`n\in\mathbb N_0`$),
rational numbers,
addition, multiplication, $`\max(\cdot,\cdot)`$, and $`\max(1,\cdot)^{-1}`$
(called "safe reciprocation").

**Note (encoding of expressible features)**:
Expressible features will be encoded as a program as follows:
each line can be a price feature, rational number,
or can be an addition/multiplication/maximum/safe reciprocation
of expressible features described by earlier lines.
The final line describes the expressible feature
that the entire program encodes.
This encoding allows for deduplication and more efficiency
compared to a standard encoding.

**Definition (day-n trading strategy)**:
For $`n\in\mathbb N_0`$, a trading strategy $`T_n`$ for day $`n`$
is a tuple of distinct sentences $`(\phi_1,\ldots,\phi_k)`$
together with a tuple of expressible features $`(\xi_1,\ldots,\xi_k)`$
(for some $`k\in\mathbb N_0`$),
where the expressible features are valuation features of rank at most $`n`$.

For such a trading strategy $`T_n`$ and any sentence $`\phi\in\mathcal S`$,
we define the coefficients $`T_n[\phi]\in\mathcal{F}_n`$ via
$`T_n[\phi]=\xi_i`$ if $`\phi=\phi_i`$ for some $`i=1,\ldots,k`$,
and $`T_n[\phi]=0`$ otherwise.
Additionally, we define the cash term
```math
T_n[1] := -\sum_{i=1}^k\xi_i\phi_i^{*n} \in\mathcal{F}_n.
```

The encoding of trading strategies is done in a natural way,
with the encoding for its expressible features described above.

**Definition (trader)**:
A trader is a sequence $`(T_n)_{n\in\mathbb N_0}`$, where each
$`T_n`$ is a trading strategy for day $`n`$.

**Definition (value of holdings of a trader)**:
Given a world $`\mathbb W`$,
the value of holdings of a trader $`T=(T_n)_{n\in\mathbb N_0}`$
interacting with a valuation sequence $`\mathbb V`$
until day $`k\in\mathbb N_0`$ is given by
```math
\mathrm{Val}(\mathbb W, T, \mathbb V, k)
:= \sum_{\phi\in\mathcal S}
\mathbb W(\phi) \cdot \sum_{i=0}^k T_i[\phi](\mathbb V)
+ \sum_{i=0}^k T_i[1](\mathbb V).
```

**Definition (trader exploits)**:
A trader $`T`$ is said to exploit a valuation sequence $`\mathbb V`$ 
relative to a deductive process 
$`(D_n)_{n\in\mathbb N_0}`$ 
if the set
```math
\big\{\mathrm{Val}(\mathbb W, T, \mathbb V, n) 
\mid n \in \mathbb N_0, \mathbb W \in \mathcal{PC}(D_n)\big\}
```
is bounded below but not bounded above.

**Definition (logical inductor)**:
A market is a logical inductor over a deductive process $`D`$ 
if it cannot be exploited by an efficiently computable trader $`T`$
relative to $`D`$.

**Theorem (existence of logical inductor)**:
For any deductive process $`D`$, there exists a market $`\mathbb P`$ 
that is a logical inductor over $`D`$.

Additionally, $`\mathbb P_i`$ is a belief state for each $`i`$.
If it is also decidable whether a word is a valid encoding of some prime sentence,
then the concrete finite list of sentences where $`\mathbb P_i`$
is supported can be computed from $`i`$.


## Commentary and source material

The article follows section 3 of "Logical Induction" from https://arxiv.org/pdf/1609.03543.

The circuit encoding of expressible features can be found in Appendix A.2 of Logical Induction.

There are some minor differences:
 - Trading days start at `0`, not `1`.
 - a belief state is not defined as being computable, because it is already
   computable due to having finite support.
 - The order of some of the definitions is different
