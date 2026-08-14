# general_stoch_to_det

[![Lean verification](https://github.com/satchlj/general_stoch_to_det/actions/workflows/lean.yml/badge.svg)](https://github.com/satchlj/general_stoch_to_det/actions/workflows/lean.yml)

A Lean 4 proof that a good stochastic natural latent can be replaced by a
deterministic natural latent, with an explicit loss depending only on the
number of variables and the deletion budget—not on any alphabet size.

## The theorem

Fix a finite joint law for

$$
X=(X_1,\ldots,X_n), \qquad n\ge 3,
$$

and choose a deletion budget $1\le m\le n-1$. For a set $D$ of $m$ coordinates,
$X_D$ denotes the deleted block and $X_{-D}$ the surviving coordinates.

For any finite latent $W$, define its separation error by

$$
\mathrm{TC}(X\mid W)
=\sum_{i=1}^{n}H(X_i\mid W)-H(X\mid W).
$$

A stochastic latent $Y$ may be coupled to $X$ in any way. Its redundancy
error is

$$
r^m_{\mathrm{sto}}(Y)
=\max_{\lvert D\rvert=m} I(Y;X_D\mid X_{-D}).
$$

A deterministic latent is a hard code $Z=\Gamma(X)$ with finite output
alphabet. Its redundancy error is instead

$$
r^m_{\mathrm{det}}(Z)
=\max_{\lvert D\rvert=m} H(Z\mid X_{-D}).
$$

These are genuinely different objectives. Define

$$
\tau_m(p)
=\inf_Y\left[\mathrm{TC}(X\mid Y)+r^m_{\mathrm{sto}}(Y)\right]
$$

and

$$
T_m(p)
=\inf_{Z=\Gamma(X)}
\left[\mathrm{TC}(X\mid Z)+r^m_{\mathrm{det}}(Z)\right].
$$

The certified theorem proves, simultaneously for every $1\le m\le n-1$,

$$
T_m(p)\le C(n,m)\tau_m(p),
$$

where

$$
C(n,m)
=\binom{n}{m}
\left[
1+194\left(n+\binom{n}{m}+1\right)
\left(n^2(n-2)+1\right)
\right].
$$

The coefficient is intentionally coarse. Its important feature is that it is
independent of the alphabet of $X$, the alphabet of $Y$, and the law $p$.

## Meaning

The stochastic optimization can randomize $Y$ after observing $X$. The
deterministic optimization must choose one ordinary function $\Gamma(X)$.
The theorem says that randomization cannot improve the combined natural-latent
error by more than the displayed alphabet-free factor.

The Lean definition of $T_m$ uses one fixed finite codomain large enough to
encode every partition of the finite state space of $X$. A recoding argument
shows that this loses no deterministic candidate: it is equivalent to ranging
over all finite hard codes $\Gamma(X)$.

## Proof idea

The proof first replaces each maximum by a sum over the
$\binom{n}{m}$ deletion sets. This sum objective has a finite optimal
stochastic latent $C$.

Two independent posterior copies of $C$ given $X$ produce a replica defect
$b$. Optimality of $C$, the previously certified all-$n$ replica inequality,
and conditional-information monotonicity give

$$
b\le\left(n^2(n-2)+1\right)S_m(C),
$$

where $S_m$ is the summed stochastic score.

The certified two-variable theorem and a finite random-table construction then
produce a genuine hard code $\Gamma(X)$ with

$$
I(C;X\mid\Gamma)+H(\Gamma\mid C)\le194b.
$$

The number $194=2\cdot96+2$ is centralized in
`NVarTwoVariableInput.oneSidedFactor`. The multivariate proof refers only to
that definition, so a future two-variable improvement is isolated to the
small adapter module rather than repeated throughout the proof.

A general entropy ledger transfers this approximation into the summed hard
score. Finally,

$$
\max_D a_D\le\sum_D a_D
\le\binom{n}{m}\max_D a_D
$$

converts the summed theorem back to the requested max-redundancy objectives.

## Machine-checked statement

The stable public declaration is
[`stoch_to_det.general_stoch_to_det_all_deletions`](stoch_to_det/MainTheorems.lean).
Its conclusion is

```lean
deletionMaxT (m := m) p <=
  (Nat.choose n m : Real) *
    (1 + ((n : Real) + (Nat.choose n m : Real) + 1) *
      NVarTwoVariableInput.oneSidedFactor *
      (((n : Real) ^ 2 * ((n : Real) - 2)) + 1)) *
    deletionMaxTau (m := m) p
```

under the hypotheses `IsPMF p`, `3 <= n`, `1 <= m`, and `m < n`.

The earlier coordinate-sum theorem remains available as
[`stoch_to_det.general_stoch_to_det`](stoch_to_det/MainTheorems.lean) for
backward compatibility. It is not used to identify the deterministic and
stochastic redundancy errors above.

## Verify it

Install [Elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/satchlj/general_stoch_to_det.git
cd general_stoch_to_det
lake exe cache get
./verify.sh
```

The Mathlib cache command avoids rebuilding upstream dependencies when a
matching binary cache is available. The verifier then:

1. rejects unfinished or disallowed Lean constructs;
2. builds the complete public library;
3. checks the all-deletion theorem and its key intermediate lemmas with
   `assert_no_sorry`; and
4. checks the complete axiom dependencies of the public declarations.

The expected axiom set is exactly

```text
[propext, Classical.choice, Quot.sound]
```

GitHub Actions runs the same verification on every push and pull request.

## Proof map

| File | Role |
| --- | --- |
| [`MainTheorems.lean`](stoch_to_det/MainTheorems.lean) | Short, stable public theorem statements |
| [`NVarAllDeletion.lean`](stoch_to_det/NVarAllDeletion.lean) | Arbitrary deletion sets, summed score, max score, and final all-deletion theorem |
| [`NVarReplicaBound.lean`](stoch_to_det/NVarReplicaBound.lean) | Alphabet-free replica-defect inequality |
| [`NVarTwoVariableInput.lean`](stoch_to_det/NVarTwoVariableInput.lean) | Single adapter for the certified two-variable factor and derived one-sided factor |
| [`NVarPosteriorCompression.lean`](stoch_to_det/NVarPosteriorCompression.lean) | Two-variable compression, posterior sampling, and seed fixing |
| [`NVarHardening.lean`](stoch_to_det/NVarHardening.lean) | Converts approximation errors into a deterministic hard score |
| [`SharedRace.lean`](stoch_to_det/SharedRace.lean) | Certified `T <= 96 * tau` endpoint used by posterior compression |
| [`Ledger96.lean`](stoch_to_det/Ledger96.lean) | Calibrated two-variable ledger beneath the shared-race endpoint |
| [`VerifyAllDeletion.lean`](VerifyAllDeletion.lean) | Dedicated no-`sorry` and axiom audit for the all-deletion theorem |
| [`Verify.lean`](Verify.lean) | Audit of the stable public declarations |
| [`verify.sh`](verify.sh) | One-command source, build, and kernel audit |

Exploratory files and abandoned proof routes are intentionally not included.

## Provenance and license

This development builds on David Lorell's
[`stoch_to_det`](https://github.com/DLorell/stoch_to_det) repository. The
two-variable endpoint used here comes from
[PR #5](https://github.com/DLorell/stoch_to_det/pull/5).

See [`NOTICE.md`](NOTICE.md) for exact revisions and checksums. The repository
is licensed under Apache 2.0; see [`LICENSE`](LICENSE).
