# Provenance

This repository contains a standalone Lean formalization assembled from two
layers:

1. The finite-information and two-variable stochastic-to-deterministic
   development from [DLorell/stoch_to_det](https://github.com/DLorell/stoch_to_det),
   including the `T_le_270` endpoint from
   [pull request #4](https://github.com/DLorell/stoch_to_det/pull/4), head commit
   `f77c6ffac9208949e72bac0ac0e9567cdca3cc15`.
2. The multivariate posterior-replica, hardening, posterior-compression, and
   final alphabet-independent assembly modules whose public endpoint is
   `stoch_to_det.general_stoch_to_det`.

For auditability, the imported `stoch_to_det/Ledger270.lean` has SHA-256 digest

```text
5c9cbf74bd9d33c3bece735b7ca49b838a0f944a5a426eb2ec6364af475fef1e
```

which matches that file at the head of pull request #4. Its complete
34-module Lean dependency closure is copied byte-for-byte from that commit;
the multivariate modules form the separate second layer described above.

The Lean namespace and inherited module names remain `stoch_to_det` so that
the formal definitions can be compared directly with upstream. The repository
and Lake package are named `general_stoch_to_det` to identify the multivariate
extension.

The source is distributed under the Apache License 2.0 in [`LICENSE`](LICENSE).
