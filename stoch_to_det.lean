import stoch_to_det.MainTheorems

/-!
# general_stoch_to_det — root module

The public endpoint `stoch_to_det.general_stoch_to_det_all_deletions` proves
an alphabet-size-independent natural-latent stochastic-to-deterministic
comparison for every finite coordinate law, every `n >= 3`, and every
deletion budget `1 <= m < n`.

The imported two-variable input is `stoch_to_det.T_le_96`. Its contribution
to the multivariate proof is isolated in
`stoch_to_det.NVarTwoVariableInput`, where the one-sided bridge factor is
defined as `2 * 96 + 2 = 194`.
-/
