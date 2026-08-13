import stoch_to_det.NVarReplicaCoordinate

/-!
# The coordinate defect bound for an optimal finite latent

This file instantiates the alphabet-free Shannon certificate on the two
conditionally independent posterior replicas of an optimal latent.
-/

namespace stoch_to_det

open Finset

namespace NLatent

variable {n : Nat} {alpha : Type} [Fintype alpha] [DecidableEq alpha]
  [Inhabited alpha]
variable {p : (Fin n -> alpha) -> Real}

private theorem replica_coordinateScore_first (V : NLatent p) :
    ReplicaCoordinate.coordinateScore V.replicaLaw (fun u => u.2)
        (fun u => u.1.1) =
      V.score (fun i => coordinateView (alpha := alpha) i)
        (fun i => coordinateDeletionView (alpha := alpha) i) := by
  unfold ReplicaCoordinate.coordinateScore NLatent.score
  simp only [coordinateView, coordinateDeletionView]
  have hsingle :
      (∑ i, condH (fun u : (V.ι × V.ι) × (Fin n -> alpha) => u.2 i)
          (fun u => u.1.1) V.replicaLaw) =
        ∑ i, condH (fun w : V.ι × (Fin n -> alpha) => w.2 i)
          (fun w => w.1) V.joint := by
    apply Finset.sum_congr rfl
    intro i _
    exact V.replica_condH_first (fun x => x i)
  have hfull :
      condH (fun u : (V.ι × V.ι) × (Fin n -> alpha) => u.2)
          (fun u => u.1.1) V.replicaLaw =
        condH (fun w : V.ι × (Fin n -> alpha) => w.2)
          (fun w => w.1) V.joint :=
    V.replica_condH_first (fun x => x)
  have hred :
      (∑ i, condMI (fun u : (V.ι × V.ι) × (Fin n -> alpha) => u.1.1)
          (fun u => u.2 i) (fun u => maskDelete i u.2) V.replicaLaw) =
        ∑ i, condMI (fun w : V.ι × (Fin n -> alpha) => w.1)
          (fun w => w.2 i) (fun w => maskDelete i w.2) V.joint := by
    apply Finset.sum_congr rfl
    intro i _
    exact V.replica_condMI_first (fun x => x i) (maskDelete i)
  rw [hsingle, hfull, hred]

private theorem replica_coordinateScore_symm (V : NLatent p) :
    ReplicaCoordinate.coordinateScore V.replicaLaw (fun u => u.2)
        (fun u => u.1.1) =
      ReplicaCoordinate.coordinateScore V.replicaLaw (fun u => u.2)
        (fun u => u.1.2) := by
  let X : ((V.ι × V.ι) × (Fin n -> alpha)) -> (Fin n -> alpha) := fun u => u.2
  let A : ((V.ι × V.ι) × (Fin n -> alpha)) -> V.ι := fun u => u.1.1
  let B : ((V.ι × V.ι) × (Fin n -> alpha)) -> V.ι := fun u => u.1.2
  have hH (i : Fin n) :
      condH (fun u => X u i) B V.replicaLaw =
        condH (fun u => X u i) A V.replicaLaw := by
    have h := FiniteInfo.condH_comp_equiv_eq_of_invariant V.replicaLaw
      V.replicaSwap V.replicaLaw_swap_equiv (fun u => X u i) A
    simpa [X, A, B, NLatent.replicaSwap, Function.comp_def] using h
  have hHX : condH X B V.replicaLaw = condH X A V.replicaLaw := by
    have h := FiniteInfo.condH_comp_equiv_eq_of_invariant V.replicaLaw
      V.replicaSwap V.replicaLaw_swap_equiv X A
    simpa [X, A, B, NLatent.replicaSwap, Function.comp_def] using h
  have hMI (i : Fin n) :
      condMI B (fun u => X u i) (fun u => maskDelete i (X u)) V.replicaLaw =
        condMI A (fun u => X u i) (fun u => maskDelete i (X u)) V.replicaLaw := by
    have h := FiniteInfo.condMI_comp_equiv_eq_of_invariant V.replicaLaw
      V.replicaSwap V.replicaLaw_swap_equiv A (fun u => X u i)
        (fun u => maskDelete i (X u))
    simpa [X, A, B, NLatent.replicaSwap, Function.comp_def] using h
  unfold ReplicaCoordinate.coordinateScore
  dsimp only [X, A, B] at hH hHX hMI
  simp_rw [hH, hMI]
  rw [hHX]

private theorem replica_coordinateCross_symm (V : NLatent p) :
    ReplicaCoordinate.coordinateCross V.replicaLaw (fun u => u.2)
        (fun u => u.1.1) (fun u => u.1.2) =
      ReplicaCoordinate.coordinateCross V.replicaLaw (fun u => u.2)
        (fun u => u.1.2) (fun u => u.1.1) := by
  let X : ((V.ι × V.ι) × (Fin n -> alpha)) -> (Fin n -> alpha) := fun u => u.2
  let A : ((V.ι × V.ι) × (Fin n -> alpha)) -> V.ι := fun u => u.1.1
  let B : ((V.ι × V.ι) × (Fin n -> alpha)) -> V.ι := fun u => u.1.2
  have hdelete (i : Fin n) :
      condMI B (fun u => maskDelete i (X u)) (fun u => (A u, X u i))
          V.replicaLaw =
        condMI A (fun u => maskDelete i (X u)) (fun u => (B u, X u i))
          V.replicaLaw := by
    have h := FiniteInfo.condMI_comp_equiv_eq_of_invariant V.replicaLaw
      V.replicaSwap V.replicaLaw_swap_equiv A
        (fun u => maskDelete i (X u)) (fun u => (B u, X u i))
    simpa [X, A, B, NLatent.replicaSwap, Function.comp_def] using h
  have hsingle (i : Fin n) :
      condMI B (fun u => X u i) (fun u => (A u, maskDelete i (X u)))
          V.replicaLaw =
        condMI A (fun u => X u i) (fun u => (B u, maskDelete i (X u)))
          V.replicaLaw := by
    have h := FiniteInfo.condMI_comp_equiv_eq_of_invariant V.replicaLaw
      V.replicaSwap V.replicaLaw_swap_equiv A (fun u => X u i)
        (fun u => (B u, maskDelete i (X u)))
    simpa [X, A, B, NLatent.replicaSwap, Function.comp_def] using h
  unfold ReplicaCoordinate.coordinateCross
  dsimp only [X, A, B] at hdelete hsingle
  simp_rw [hdelete, hsingle]

/-- The collapsed Shannon certificate, specialized to posterior replicas. -/
theorem replica_coordinateCross_le_score (V : NLatent p) (hn : 3 <= n) :
    ReplicaCoordinate.coordinateCross V.replicaLaw (fun u => u.2)
        (fun u => u.1.1) (fun u => u.1.2) <=
      (n : Real) * ((n : Real) - 2) *
        V.score (fun i => coordinateView (alpha := alpha) i)
          (fun i => coordinateDeletionView (alpha := alpha) i) := by
  have h := ReplicaCoordinate.coordinateCross_le_mul_coordinateScore hn
    V.replicaLaw_isPMF (fun u => u.2) (fun u => u.1.1) (fun u => u.1.2)
    V.replica_markov V.replica_coordinateScore_symm
      V.replica_coordinateCross_symm
  rw [V.replica_coordinateScore_first] at h
  exact h

private theorem replicaDefect_swap (V : NLatent p) :
    condMI (fun u : (V.ι × V.ι) × (Fin n -> alpha) => u.1.1)
        (fun u => u.2) (fun u => u.1.2) V.replicaLaw =
      V.replicaDefect := by
  have h := FiniteInfo.condMI_comp_equiv_eq_of_invariant V.replicaLaw
    V.replicaSwap V.replicaLaw_swap_equiv
    (fun u : (V.ι × V.ι) × (Fin n -> alpha) => u.1.2)
    (fun u => u.2) (fun u => u.1.1)
  simpa [NLatent.replicaDefect, NLatent.replicaSwap, Function.comp_def] using h

private theorem replicaViewInformation_swap (V : NLatent p) :
    (∑ i, (condMI
        (fun u : (V.ι × V.ι) × (Fin n -> alpha) => u.1.1)
        (fun u => u.2 i) (fun u => u.1.2) V.replicaLaw +
      condMI (fun u => u.1.1) (fun u => maskDelete i u.2)
        (fun u => u.1.2) V.replicaLaw)) =
      V.replicaViewInformation
        (fun i => coordinateView (alpha := alpha) i)
        (fun i => coordinateDeletionView (alpha := alpha) i) := by
  have hsingle (i : Fin n) :
      condMI (fun u : (V.ι × V.ι) × (Fin n -> alpha) => u.1.1)
          (fun u => u.2 i) (fun u => u.1.2) V.replicaLaw =
        condMI (fun u => u.1.2) (fun u => u.2 i)
          (fun u => u.1.1) V.replicaLaw := by
    have h := FiniteInfo.condMI_comp_equiv_eq_of_invariant V.replicaLaw
      V.replicaSwap V.replicaLaw_swap_equiv
      (fun u : (V.ι × V.ι) × (Fin n -> alpha) => u.1.2)
      (fun u => u.2 i) (fun u => u.1.1)
    simpa [NLatent.replicaSwap, Function.comp_def] using h
  have hdelete (i : Fin n) :
      condMI (fun u : (V.ι × V.ι) × (Fin n -> alpha) => u.1.1)
          (fun u => maskDelete i u.2) (fun u => u.1.2) V.replicaLaw =
        condMI (fun u => u.1.2) (fun u => maskDelete i u.2)
          (fun u => u.1.1) V.replicaLaw := by
    have h := FiniteInfo.condMI_comp_equiv_eq_of_invariant V.replicaLaw
      V.replicaSwap V.replicaLaw_swap_equiv
      (fun u : (V.ι × V.ι) × (Fin n -> alpha) => u.1.2)
      (fun u => maskDelete i u.2) (fun u => u.1.1)
    simpa [NLatent.replicaSwap, Function.comp_def] using h
  unfold replicaViewInformation
  simp only [coordinateView, coordinateDeletionView]
  apply Finset.sum_congr rfl
  intro i _
  rw [hsingle i, hdelete i]

/-- Exact bridge between the cross-information certificate and the posterior
resampling budget. -/
theorem replica_coordinateCross_eq (V : NLatent p) :
    ReplicaCoordinate.coordinateCross V.replicaLaw (fun u => u.2)
        (fun u => u.1.1) (fun u => u.1.2) =
      2 * (n : Real) * V.replicaDefect -
        V.replicaViewInformation
          (fun i => coordinateView (alpha := alpha) i)
          (fun i => coordinateDeletionView (alpha := alpha) i) := by
  let X : ((V.ι × V.ι) × (Fin n -> alpha)) -> (Fin n -> alpha) := fun u => u.2
  let A : ((V.ι × V.ι) × (Fin n -> alpha)) -> V.ι := fun u => u.1.1
  let B : ((V.ι × V.ι) × (Fin n -> alpha)) -> V.ι := fun u => u.1.2
  have hdef : condMI A X B V.replicaLaw = V.replicaDefect := by
    simpa [X, A, B] using V.replicaDefect_swap
  have hterm (i : Fin n) :
      condMI A (fun u => maskDelete i (X u)) (fun u => (B u, X u i))
          V.replicaLaw +
        condMI A (fun u => X u i) (fun u => (B u, maskDelete i (X u)))
          V.replicaLaw =
        2 * V.replicaDefect -
          (condMI A (fun u => X u i) B V.replicaLaw +
            condMI A (fun u => maskDelete i (X u)) B V.replicaLaw) := by
    have hpair1 := FiniteInfo.condMI_pair_right V.replicaLaw_isPMF A
      (fun u => X u i) (fun u => maskDelete i (X u)) B
    have hrecode1 := FiniteInfo.condMI_comp_right_eq_of_injective
      V.replicaLaw_isPMF A X B
      (fun x : Fin n -> alpha => (x i, maskDelete i x))
      (coordinate_pair_injective (alpha := alpha) i)
    have hinj_swap : Function.Injective
        (fun x : Fin n -> alpha => (maskDelete i x, x i)) := by
      intro x y hxy
      apply coordinate_pair_injective (alpha := alpha) i
      exact Prod.ext (congrArg Prod.snd hxy) (congrArg Prod.fst hxy)
    have hpair2 := FiniteInfo.condMI_pair_right V.replicaLaw_isPMF A
      (fun u => maskDelete i (X u)) (fun u => X u i) B
    have hrecode2 := FiniteInfo.condMI_comp_right_eq_of_injective
      V.replicaLaw_isPMF A X B
      (fun x : Fin n -> alpha => (maskDelete i x, x i)) hinj_swap
    dsimp only [X, A, B] at hpair1 hrecode1 hpair2 hrecode2 hdef ⊢
    linarith
  unfold ReplicaCoordinate.coordinateCross
  change (∑ i, (condMI A (fun u => maskDelete i (X u))
      (fun u => (B u, X u i)) V.replicaLaw +
    condMI A (fun u => X u i) (fun u => (B u, maskDelete i (X u)))
      V.replicaLaw)) = _
  rw [show (∑ i, (condMI A (fun u => maskDelete i (X u))
        (fun u => (B u, X u i)) V.replicaLaw +
      condMI A (fun u => X u i) (fun u => (B u, maskDelete i (X u)))
        V.replicaLaw)) =
      ∑ i, (2 * V.replicaDefect -
        (condMI A (fun u => X u i) B V.replicaLaw +
          condMI A (fun u => maskDelete i (X u)) B V.replicaLaw)) by
        apply Finset.sum_congr rfl
        intro i _
        exact hterm i]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hview := V.replicaViewInformation_swap
  change (∑ i, (condMI A (fun u => X u i) B V.replicaLaw +
      condMI A (fun u => maskDelete i (X u)) B V.replicaLaw)) =
        V.replicaViewInformation
          (fun i => coordinateView (alpha := alpha) i)
          (fun i => coordinateDeletionView (alpha := alpha) i) at hview
  rw [hview]
  ring

/-- Alphabet-free posterior-replica defect bound for an optimal coordinate
latent.  The deliberately division-free coefficient is convenient for the
final hardening argument. -/
theorem replicaDefect_le_score_of_optimal (V : NLatent p) (hn : 3 <= n)
    (hoptimal :
      V.score (fun i => coordinateView (alpha := alpha) i)
          (fun i => coordinateDeletionView (alpha := alpha) i) =
        nTau (fun i => coordinateView (alpha := alpha) i)
          (fun i => coordinateDeletionView (alpha := alpha) i) p) :
    V.replicaDefect <=
      (n : Real) * ((n : Real) - 2) *
        V.score (fun i => coordinateView (alpha := alpha) i)
          (fun i => coordinateDeletionView (alpha := alpha) i) := by
  have hresample := V.replicaViewInformation_le_of_optimal
    (fun i => coordinateView (alpha := alpha) i)
    (fun i => coordinateDeletionView (alpha := alpha) i)
    (fun i => coordinate_pair_injective (alpha := alpha) i)
    (coordinate_tuple_injective (alpha := alpha)) hoptimal
  have hcross := V.replica_coordinateCross_le_score hn
  have hid := V.replica_coordinateCross_eq
  have hb : 0 <= V.replicaDefect :=
    condMI_nonneg V.replicaLaw_isPMF
      (fun u => u.1.2) (fun u => u.2) (fun u => u.1.1)
  have hnR : (3 : Real) <= (n : Real) := by exact_mod_cast hn
  nlinarith

end NLatent

end stoch_to_det
