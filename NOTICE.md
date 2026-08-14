# Provenance

This repository contains a standalone Lean formalization assembled from two
layers:

1. The finite-information and two-variable stochastic-to-deterministic
   development from [DLorell/stoch_to_det](https://github.com/DLorell/stoch_to_det),
   including the `T_le_96` endpoint from
   [pull request #5](https://github.com/DLorell/stoch_to_det/pull/5), head commit
   `36d6cd22cb70c36fce6b864a4be78b3d876cfce5`.
2. The multivariate posterior-replica, hardening, posterior-compression, and
   alphabet-independent assembly modules. Their max-redundancy natural-latent
   endpoint for every deletion budget is
   `stoch_to_det.general_stoch_to_det_all_deletions`; the earlier
   coordinate-sum endpoint remains available as
   `stoch_to_det.general_stoch_to_det`.

For auditability, the imported `stoch_to_det/SharedRace.lean` has SHA-256 digest

```text
6d8e9000eb51b67245f645a1386ad6a9b983b05a3590f49dff7e41d5368435eb
```

which matches that file at the head of pull request #5. The pull request's
standalone Lean dependency closure is copied from that commit. The sole
build-only adjustment retains the equivalent precise imports in
`stoch_to_det/PhiBounds.lean` instead of its umbrella `import Mathlib`; the
multivariate modules form the separate second layer described above.

The Lean namespace and inherited module names remain `stoch_to_det` so that
the formal definitions can be compared directly with upstream. The repository
and Lake package are named `general_stoch_to_det` to identify the multivariate
extension.

The source is distributed under the Apache License 2.0 in [`LICENSE`](LICENSE).
