import stoch_to_det.NVarAlphabetFree

/-!
# Public theorems

This module gives short, stable names to the multivariate endpoint and its
three-coordinate specialization. The proof itself is assembled in
`stoch_to_det.NVarAlphabetFree`.
-/

namespace stoch_to_det

variable {n : Nat} {alpha : Type} [Fintype alpha] [DecidableEq alpha]
  [Inhabited alpha]
variable {p : (Fin n -> alpha) -> Real}

/-- **General stochastic-to-deterministic bound.** For every finite law on
`alpha^n` with `n >= 3`, the optimal hard score is at most
`1 + 542 * (n+1) * n * (n-2)` times the optimal stochastic score. The
coefficient is independent of `alpha` and `p`. -/
theorem general_stoch_to_det (hp : IsPMF p) (hn : 3 <= n) :
    nT (fun i => coordinateView (alpha := alpha) i)
        (fun i => coordinateDeletionView (alpha := alpha) i) p <=
      (1 + ((n : Real) + 1) * 542 * (n : Real) * ((n : Real) - 2)) *
        nTau (fun i => coordinateView (alpha := alpha) i)
          (fun i => coordinateDeletionView (alpha := alpha) i) p :=
  NVarAlphabetFree.nT_le_alphabetFree hp hn

/-- The concrete three-coordinate specialization of
`general_stoch_to_det`. -/
theorem general_stoch_to_det_three
    {p : (Fin 3 -> alpha) -> Real} (hp : IsPMF p) :
    nT (fun i => coordinateView (alpha := alpha) i)
        (fun i => coordinateDeletionView (alpha := alpha) i) p <=
      6505 *
        nTau (fun i => coordinateView (alpha := alpha) i)
          (fun i => coordinateDeletionView (alpha := alpha) i) p := by
  have h :=
    general_stoch_to_det (n := 3) hp (by norm_num : 3 <= (3 : Nat))
  norm_num at h
  exact h

end stoch_to_det
