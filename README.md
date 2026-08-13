# general_stoch_to_det

[![Lean verification](https://github.com/satchlj/general_stoch_to_det/actions/workflows/lean.yml/badge.svg)](https://github.com/satchlj/general_stoch_to_det/actions/workflows/lean.yml)

A Lean 4 proof that, for every finite distribution on $n \ge 3$ variables,
the best deterministic auxiliary variable is within an explicit factor of the
best stochastic auxiliary variable. The factor depends on $n$, but **not** on
the size of the alphabet.

## The result in one sentence

Let

$$
X=(X_1,\ldots,X_n) \sim p
$$

take values in $A^n$, where $A$ is any finite alphabet and $n \ge 3$. A
stochastic auxiliary variable $V$ has score

$$
\begin{aligned}
S(V)
&= \mathrm{TC}(X\mid V) \\
&\quad + \sum_{i=1}^n I(V;X_i\mid X_{-i}),
\end{aligned}
$$

where $X_{-i}$ means all coordinates except $X_i$, and

$$
\mathrm{TC}(X\mid V)
= \sum_{i=1}^n H(X_i\mid V)-H(X\mid V)
$$

is conditional total correlation.

There are two optimization problems:

- $\tau_n(p)$ is the infimum of $S(V)$ over all finite stochastic auxiliaries
  coupled to $X$.
- $T_n(p)$ is the minimum of the same score over hard auxiliaries
  $\Gamma=\Gamma(X)$—ordinary deterministic functions of the observed tuple.

The main theorem is

$$
\boxed{T_n(p)\le\bigl(1+1036(n+1)n(n-2)\bigr)\cdot\tau_n(p)}
\qquad(n\ge3).
$$

In particular,

$$
T_3(p)\le 12433\cdot\tau_3(p).
$$

The constant is uniform over the alphabet $A$, the distribution $p$, and the
alphabet of the stochastic auxiliary. The theorem is finite: $A$ and every
auxiliary alphabet are finite.

## What this means

The stochastic optimization may use a genuinely randomized $V$ given $X$.
The deterministic optimization must choose one fixed summary $\Gamma(X)$.
The theorem says that randomization cannot beat every deterministic summary
by more than the displayed alphabet-independent factor.

The hard part is that the two sides optimize over different witness classes.
It is not enough to compare a preselected $V$ with a preselected $\Gamma$; the
proof must start from an optimal stochastic witness and manufacture a single
deterministic witness without paying for the size of any alphabet.

## Proof idea

The formal proof has five conceptual steps.

### 1. Choose an optimal soft witness

Finite-dimensional envelope arguments give a finite stochastic auxiliary $C$
with $S(C)=\tau_n(p)$.

### 2. Resample its posterior

Given $X$, draw two independent copies $C_0,C_1$ from the posterior law of
$C$. Define the replica defect

$$
D=I(C_1;X\mid C_0).
$$

Optimality of $C$, together with a multivariate Shannon inequality, gives

$$
D\le n(n-2)S(C).
$$

### 3. Use the certified two-variable theorem

Apply the bound $T\le517\tau$ to the pair $(X,C_0)$ with stochastic auxiliary
$C_1$. The relevant two-variable stochastic score is exactly $2D$.

### 4. Remove the posterior randomness

Represent $C_0$ as a function of $X$ and an independent finite random table.
Averaging and then fixing one table produces a genuine hard code $\Gamma(X)$
satisfying

$$
\begin{aligned}
I(C;X\mid\Gamma)+H(\Gamma\mid C)
&\le (2\cdot517+2)D \\
&=1036D.
\end{aligned}
$$

### 5. Harden the multivariate score

A direct entropy ledger proves

$$
\begin{aligned}
S(\Gamma)
&\le S(C) \\
&\quad +(n+1)\bigl(I(C;X\mid\Gamma)+H(\Gamma\mid C)\bigr).
\end{aligned}
$$

Substituting the two preceding bounds and $S(C)=\tau_n(p)$ gives the stated
coefficient.

## Machine-checked statement

The public Lean declaration is
[`stoch_to_det.general_stoch_to_det`](stoch_to_det/MainTheorems.lean):

```lean
theorem general_stoch_to_det (hp : IsPMF p) (hn : 3 <= n) :
    nT (fun i => coordinateView (alpha := alpha) i)
        (fun i => coordinateDeletionView (alpha := alpha) i) p <=
      (1 + ((n : Real) + 1) * 1036 * (n : Real) * ((n : Real) - 2)) *
        nTau (fun i => coordinateView (alpha := alpha) i)
          (fun i => coordinateDeletionView (alpha := alpha) i) p
```

The specialization
[`stoch_to_det.general_stoch_to_det_three`](stoch_to_det/MainTheorems.lean)
states the $12433$ bound directly.

## Verify it

Install [Elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/satchlj/general_stoch_to_det.git
cd general_stoch_to_det
./verify.sh
```

The first run may download the pinned Lean toolchain and Mathlib dependencies.
The verifier:

1. rejects unfinished or disallowed Lean constructs;
2. builds the complete library;
3. checks transitively that the public declarations contain no `sorryAx`; and
4. checks their complete axiom dependencies.

The expected axiom set is exactly Lean and Mathlib's standard

```text
[propext, Classical.choice, Quot.sound]
```

GitHub Actions runs the same verification on every push and pull request.

## Where the proof lives

| File | Role |
| --- | --- |
| [`MainTheorems.lean`](stoch_to_det/MainTheorems.lean) | Short public theorem statements |
| [`NVarAlphabetFree.lean`](stoch_to_det/NVarAlphabetFree.lean) | Final all-$n$ assembly |
| [`NVarReplicaBound.lean`](stoch_to_det/NVarReplicaBound.lean) | Alphabet-free replica-defect bound |
| [`NVarPosteriorCompression.lean`](stoch_to_det/NVarPosteriorCompression.lean) | Two-variable compression, random-table representation, and seed fixing |
| [`NVarHardening.lean`](stoch_to_det/NVarHardening.lean) | Converts one-sided approximation error into the hard score |
| [`Final517.lean`](stoch_to_det/Final517.lean) | Certified two-variable bound $T\le517\tau$ |
| [`Verify.lean`](Verify.lean) | Kernel-level public theorem audit |
| [`verify.sh`](verify.sh) | One-command source, build, and axiom check |

The other Lean files are the exact transitive proof dependencies. Exploratory
files and abandoned proof routes are intentionally not included.

## Provenance and license

This development builds on David Lorell's
[`stoch_to_det`](https://github.com/DLorell/stoch_to_det) repository. The
two-variable $517$ endpoint is from
[PR #3](https://github.com/DLorell/stoch_to_det/pull/3). Module names in the
`stoch_to_det` namespace are preserved so the inherited definitions and proof
chain remain easy to compare with upstream.

See [`NOTICE.md`](NOTICE.md) for exact revisions and checksums. The repository
is licensed under Apache 2.0; see [`LICENSE`](LICENSE).
