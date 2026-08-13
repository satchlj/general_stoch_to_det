# Provenance

This repository contains a standalone Lean formalization assembled from two
layers:

1. The finite-information and two-variable stochastic-to-deterministic
   development from [DLorell/stoch_to_det](https://github.com/DLorell/stoch_to_det),
   including the `T_le_517` endpoint from
   [pull request #3](https://github.com/DLorell/stoch_to_det/pull/3), head commit
   `ced09a4ccac361668a4aaecdfaebea9f664eae5b`.
2. The multivariate posterior-replica, hardening, posterior-compression, and
   final alphabet-independent assembly modules whose public endpoint is
   `stoch_to_det.general_stoch_to_det`.

For auditability, the imported `stoch_to_det/Final517.lean` has SHA-256 digest

```text
4d25365dd4622d091a939e7ea0397ac41d9bea86167c0349105e1831a4cb00ca
```

which matches that file at the head of pull request #3.

The Lean namespace and inherited module names remain `stoch_to_det` so that
the formal definitions can be compared directly with upstream. The repository
and Lake package are named `general_stoch_to_det` to identify the multivariate
extension.

The source is distributed under the Apache License 2.0 in [`LICENSE`](LICENSE).
