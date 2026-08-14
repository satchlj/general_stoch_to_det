import stoch_to_det.NVarAllDeletion

/-!
# Public theorems

This module gives short, stable names to the natural-latent theorem for every
deletion budget, the earlier coordinate-sum endpoint, and its three-coordinate
specialization.
-/

namespace stoch_to_det

variable {n : Nat} {alpha : Type} [Fintype alpha] [DecidableEq alpha]
  [Inhabited alpha]
variable {p : (Fin n -> alpha) -> Real}

/-- **Natural-latent stochastic-to-deterministic bound.** For every finite law
on `alpha^n`, every `n >= 3`, and every deletion budget `1 <= m < n`, the
optimal deterministic max-redundancy score is at most the displayed
alphabet-free factor times the optimal stochastic max-redundancy score.

Here `deletionMaxT` minimizes
`TC(X | Gamma) + max_{|D|=m} H(Gamma | X_{-D})` over hard codes
`Gamma = Gamma(X)`, while `deletionMaxTau` takes the infimum of
`TC(X | Y) + max_{|D|=m} I(Y; X_D | X_{-D})` over finite stochastic
auxiliaries `Y`. -/
theorem general_stoch_to_det_all_deletions {m : Nat}
    (hp : IsPMF p) (hn : 3 <= n) (hm1 : 1 <= m) (hmn : m < n) :
    letI : Nonempty (DeletionSet n m) := deletionSet_nonempty (Nat.le_of_lt hmn)
    deletionMaxT (m := m) p <=
      (Nat.choose n m : Real) *
        (1 + ((n : Real) + (Nat.choose n m : Real) + 1) * 542 *
          (((n : Real) ^ 2 * ((n : Real) - 2)) + 1)) *
        deletionMaxTau (m := m) p := by
  letI : Nonempty (DeletionSet n m) :=
    deletionSet_nonempty (Nat.le_of_lt hmn)
  rw [← deletionMaxConstant_eq_choose n m]
  exact deletionMaxT_le_alphabetFree_for_range hp hn hm1 hmn

/-- **Coordinate-sum stochastic-to-deterministic bound.** For every finite law
on `alpha^n` with `n >= 3`, the earlier coordinate-sum hard score is at most
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
