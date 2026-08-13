import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Prelude: conventions for the stoch_to_det formalization


## Units

Information quantities are in **bits** unless explicitly marked *nats*.
Here `lg = Real.logb 2`, while nats-valued statements carry `_nats` in the
name and use `Real.log`. The exact ledger of bit-valued constants
(`c_* = 1/(N ln 2)`, `κ = (1 + ln 8 − γ)/ln 2`, `C₀`, `108C₀+3`) is reproduced
in `stoch_to_det.Constants`.

## The `0 · log 0 = 0` convention

We use `𝖧(m) := ∑ m log(|m|/m)` with the convention `0 log 0 := 0`.
In Lean this convention is automatic: `Real.log 0 = 0` and `x / 0 = 0`, so
`m a * lg (mass m / m a)` evaluates to `0` when `m a = 0`, with no `if`-guard
and no side condition.

The same junk values make a statement vacuously true for malformed inputs, so
the hypotheses `IsFinMeas` / `IsPMF` are carried explicitly throughout.
-/

namespace stoch_to_det

open scoped BigOperators

/-- Base-2 logarithm. All information quantities in this development are in
**bits** unless the name says `_nats`. -/
noncomputable abbrev lg (x : ℝ) : ℝ := Real.logb 2 x

@[simp] lemma lg_zero : lg 0 = 0 := by simp [lg]

@[simp] lemma lg_one : lg 1 = 0 := by simp [lg]

/-- Conversion factor between the two unit systems: `lg x = Real.log x / Real.log 2`. -/
lemma lg_eq_log_div (x : ℝ) : lg x = Real.log x / Real.log 2 := rfl

end stoch_to_det
