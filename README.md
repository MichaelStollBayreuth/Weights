# Weights

Formalization in Lean4 of some results in [*Minimization of hypersurfaces*](https://arxiv.org/abs/2110.04625) by A.-S. Elsenhans and myself.

## Contents

The paper introduces the notion of a *weight* on forms of degree $d$
in $n+1$ variables, which is simply an $(n+1)$-tuple of natural numbers.
We index the entries from $0$ to $n$. See `Weight`.

We can then compare weights in the following way. We first define $J_{n,d}$
to be the Set of $(n+1)$-tuples of natural numbers whose sum is $d$ (`Weight.testvecs n d`).
Then to a weight $w$, we associate the map $f_w \colon J_{n,d} \to \mathbb{Z}\_{\ge 0}$
given by sending $a \in J_{n,d}$ to
$$\max\Bigl\\{0, \Bigl\lfloor\frac{d \, \Sigma w}{n+1}\Bigr\rfloor - \langle a, w \rangle\Bigr\\}$$
(where $\Sigma w$ denotes the sum of the entries of $w$). See `Weight.f`.

Then we say that a weight $w$ *dominates* another weight $w'$ if $f_w \le f_{w'}$
point-wise. In this file, we write `w ≤d w'` for this relation. `≤d` is a pre-order
on the set of weights, but not a (partial) order. For example, a weight $w$
and $w + k \mathbf{1}$ dominate each other for each natural number $k$.
We can therefore restrict to weights whose minimal entry is zero.

We say that a weight $w$ that is (weakly) increasing and such that $w_0 = 0$
is *normalized* (`Weight.normalized`). We show that if a normalized weight $w$ dominates
some weight $w'$, then it also dominates the increasing permutation of $w'$
(`Weight.dom_of_dom_perm`). So up to permutations, it suffices to consider
only normalized weights.

We say that a set $S$ of normalized weights is *complete* if every normalized
weight is dominated by an element of $S$ (`Weight.complete_set`). We say that a complete
set of weights is *minimal* if it is minimal with respect to inclusion among complete sets
(`Weight.minimal_complete_set`). This is equivalent to saying that when $w$ and $w'$ are
in $S$ and $w$ dominates $w'$, then $w = w'$.

The first main result of this project is that there is a *unique* minimal complete set
of weights, which is given by the set `M n d` of all normalized weights that are minimal
elements with respect to domination within the set of all normalized weights.
See `Weight.M_is_minimal` and `Weight.M_is_unique`.

We show in addition that the entries of nonzero elements of `M n d` are coprime
(`Weight.gcd_eq_one_of_in_M`) and that `M n 1` consists of the single
element $(0,1,\ldots,1)$ (`Weight.w1_unique`).

The second main result is a proof of Theorem 1.6 in the paper, which says that
in the case $n = 2$, the weights in a minimal complete set of normalized weights
have entries bounded by the degree $d$. See `Weight.dom_by_max_le_d`.
(Currently, only the case when $d$ is divisible by 3 is complete.)