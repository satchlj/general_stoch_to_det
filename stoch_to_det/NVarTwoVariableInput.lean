import stoch_to_det.SharedRace

/-!
# Two-variable input to the multivariate bridge

This is the only multivariate module that names the currently certified
two-variable endpoint.  Future improvements should update `certifiedFactor`
and `T_le_certifiedFactor`; the posterior-compression and multivariate layers
depend only on the derived `oneSidedFactor`.
-/

namespace stoch_to_det
namespace NVarTwoVariableInput

universe u

/-- The multiplicative factor in the imported two-variable theorem. -/
noncomputable def certifiedFactor : Real := 96

/-- Stable adapter from the imported endpoint to the multivariate layer. -/
theorem T_le_certifiedFactor
    {alpha : Type u} {beta : Type*}
    [Fintype alpha] [Fintype beta] [DecidableEq alpha] [DecidableEq beta]
    {p : alpha × beta -> Real} (hp : IsPMF p) :
    T p <= certifiedFactor * tau p := by
  simpa [certifiedFactor] using T_le_96 hp

/-- One-sided posterior compression pays twice the two-variable factor and
two additional replica-defect units in the bridge ledger. -/
noncomputable def oneSidedFactor : Real := 2 * certifiedFactor + 2

theorem certifiedFactor_eq : certifiedFactor = 96 := rfl

theorem oneSidedFactor_eq : oneSidedFactor = 194 := by
  norm_num [oneSidedFactor, certifiedFactor]

theorem oneSidedFactor_nonneg : 0 <= oneSidedFactor := by
  rw [oneSidedFactor_eq]
  norm_num

end NVarTwoVariableInput
end stoch_to_det
