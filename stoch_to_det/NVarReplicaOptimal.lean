import stoch_to_det.NVarBounds
import stoch_to_det.NVarReplica
import stoch_to_det.Functionals

/-!
# The posterior-resampling inequality from optimality

The paper proof obtained the view-resampling inequality from a common-contact
dual certificate.  For the averaged inequality actually needed by the replica
budget, the duality layer can be avoided: adjoining a posterior replica is an
admissible refinement of an optimal latent, so its score cannot decrease.
The score chain rule is exactly the desired resampling inequality.
-/

namespace stoch_to_det

open Finset

variable {Omega : Type} [Fintype Omega] [DecidableEq Omega]
variable {p : Omega -> Real}
variable {n : Nat} {kappa gamma : Fin n -> Type}
  [forall i, Fintype (kappa i)] [forall i, DecidableEq (kappa i)]
  [forall i, Fintype (gamma i)] [forall i, DecidableEq (gamma i)]

namespace NLatent

variable (V : NLatent p)
variable (f : forall i, Omega -> kappa i) (g : forall i, Omega -> gamma i)

/-- `I(C₁;X | C₀)` under the posterior-replica coupling. -/
noncomputable def replicaDefect : Real :=
  condMI (fun u : (V.ι × V.ι) × Omega => u.1.2) (fun u => u.2)
    (fun u => u.1.1) V.replicaLaw

/-- The sum of the singleton/deletion information exposed by the second
replica after the first replica is known. -/
noncomputable def replicaViewInformation : Real :=
  ∑ i, (condMI (fun u : (V.ι × V.ι) × Omega => u.1.2)
      (fun u => f i u.2) (fun u => u.1.1) V.replicaLaw +
    condMI (fun u : (V.ι × V.ι) × Omega => u.1.2)
      (fun u => g i u.2) (fun u => u.1.1) V.replicaLaw)

/-- Exact score increment when the posterior replica is adjoined to the
latent label. -/
theorem replicaRefinement_score_sub
    (hinj : forall i, Function.Injective (fun x => (f i x, g i x))) :
    V.replicaRefinement.score f g - V.score f g =
      ((n : Real) + 1) * V.replicaDefect - V.replicaViewInformation f g := by
  let R := V.replicaLaw
  let A : (V.ι × V.ι) × Omega -> V.ι := fun u => u.1.1
  let B : (V.ι × V.ι) × Omega -> V.ι := fun u => u.1.2
  let X : (V.ι × V.ι) × Omega -> Omega := fun u => u.2
  have hXfirst : condH X A R =
      condH (fun w : V.ι × Omega => w.2) (fun w => w.1) V.joint := by
    simpa [R, A, X] using V.replica_condH_first (fun x : Omega => x)
  have hVscore : V.score f g =
      ((∑ i, condH (fun u => f i (X u)) A R) - condH X A R) +
        ∑ i, condMI A (fun u => f i (X u)) (fun u => g i (X u)) R := by
    unfold NLatent.score
    dsimp only [R, A, X]
    simp_rw [V.replica_condH_first]
    simp_rw [V.replica_condMI_first]
    rw [hXfirst]
  have hWscore : V.replicaRefinement.score f g =
      ((∑ i, condH (fun u => f i (X u)) (fun u => (A u, B u)) R) -
          condH X (fun u => (A u, B u)) R) +
        ∑ i, condMI (fun u => (A u, B u)) (fun u => f i (X u))
          (fun u => g i (X u)) R := by
    unfold NLatent.score
    rw [V.replicaRefinement_joint_eq]
    rfl
  have hcond_i (i : Fin n) :
      condH (fun u => f i (X u)) (fun u => (A u, B u)) R -
          condH (fun u => f i (X u)) A R =
        -condMI B (fun u => f i (X u)) A R := by
    have hswap := FiniteInfo.condH_equiv_cond V.replicaLaw_isPMF
      (fun u => f i (X u)) (fun u => (B u, A u))
      (Equiv.prodComm V.ι V.ι)
    change condH (fun u => f i (X u)) (fun u => (A u, B u)) R =
      condH (fun u => f i (X u)) (fun u => (B u, A u)) R at hswap
    have hchain := condMI_eq_condH_sub_pair V.replicaLaw_isPMF
      (fun u => f i (X u)) B A
    have hcomm := FiniteInfo.condMI_comm V.replicaLaw_isPMF
      (fun u => f i (X u)) B A
    rw [hswap]
    linarith [hchain, hcomm]
  have hcond_X :
      condH X (fun u => (A u, B u)) R - condH X A R =
        -V.replicaDefect := by
    have hswap := FiniteInfo.condH_equiv_cond V.replicaLaw_isPMF X
      (fun u => (B u, A u)) (Equiv.prodComm V.ι V.ι)
    change condH X (fun u => (A u, B u)) R =
      condH X (fun u => (B u, A u)) R at hswap
    have hchain := condMI_eq_condH_sub_pair V.replicaLaw_isPMF X B A
    have hcomm := FiniteInfo.condMI_comm V.replicaLaw_isPMF X B A
    dsimp only [replicaDefect, R, A, B, X] at hcomm ⊢
    rw [hswap]
    linarith
  have hred_i (i : Fin n) :
      condMI (fun u => (A u, B u)) (fun u => f i (X u))
          (fun u => g i (X u)) R -
        condMI A (fun u => f i (X u)) (fun u => g i (X u)) R =
      V.replicaDefect - condMI B (fun u => g i (X u)) A R := by
    have hleft := FiniteInfo.condMI_pair_left V.replicaLaw_isPMF A B
      (fun u => f i (X u)) (fun u => g i (X u))
    have hcondSwap := FiniteInfo.condMI_equiv_cond V.replicaLaw_isPMF B
      (fun u => f i (X u)) (fun u => (g i (X u), A u))
      (Equiv.prodComm (gamma i) V.ι)
    change condMI B (fun u => f i (X u)) (fun u => (A u, g i (X u))) R =
      condMI B (fun u => f i (X u)) (fun u => (g i (X u), A u)) R at hcondSwap
    have hpair := FiniteInfo.condMI_pair_right V.replicaLaw_isPMF B
      (fun u => g i (X u)) (fun u => f i (X u)) A
    have hgf_inj : Function.Injective (fun x => (g i x, f i x)) := by
      intro x y hxy
      apply hinj i
      apply Prod.ext
      · exact congrArg Prod.snd hxy
      · exact congrArg Prod.fst hxy
    have hrecode := FiniteInfo.condMI_comp_right_eq_of_injective
      V.replicaLaw_isPMF B X A (fun x => (g i x, f i x)) hgf_inj
    dsimp only [replicaDefect, R, A, B, X] at hrecode ⊢
    rw [← hcondSwap] at hleft
    linarith
  rw [hWscore, hVscore]
  unfold replicaViewInformation
  rw [Finset.sum_add_distrib]
  dsimp only [R, A, B, X]
  have hsum_cond :
      (∑ i, condH (fun u => f i u.2) (fun u => (u.1.1, u.1.2)) V.replicaLaw) -
          ∑ i, condH (fun u => f i u.2) (fun u => u.1.1) V.replicaLaw =
        -∑ i, condMI (fun u => u.1.2) (fun u => f i u.2)
          (fun u => u.1.1) V.replicaLaw := by
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ i, (condH (fun u => f i u.2) (fun u => (u.1.1, u.1.2)) V.replicaLaw -
          condH (fun u => f i u.2) (fun u => u.1.1) V.replicaLaw)) =
          ∑ i, -condMI (fun u => u.1.2) (fun u => f i u.2)
            (fun u => u.1.1) V.replicaLaw := by
            apply Finset.sum_congr rfl
            intro i _
            simpa [R, A, B, X] using hcond_i i
      _ = -∑ i, condMI (fun u => u.1.2) (fun u => f i u.2)
          (fun u => u.1.1) V.replicaLaw := by rw [Finset.sum_neg_distrib]
  have hsum_red :
      (∑ i, condMI (fun u => (u.1.1, u.1.2)) (fun u => f i u.2)
          (fun u => g i u.2) V.replicaLaw) -
        ∑ i, condMI (fun u => u.1.1) (fun u => f i u.2)
          (fun u => g i u.2) V.replicaLaw =
      (n : Real) * V.replicaDefect -
        ∑ i, condMI (fun u => u.1.2) (fun u => g i u.2)
          (fun u => u.1.1) V.replicaLaw := by
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ i, (condMI (fun u => (u.1.1, u.1.2)) (fun u => f i u.2)
          (fun u => g i u.2) V.replicaLaw -
        condMI (fun u => u.1.1) (fun u => f i u.2)
          (fun u => g i u.2) V.replicaLaw)) =
        ∑ i, (V.replicaDefect -
          condMI (fun u => u.1.2) (fun u => g i u.2)
            (fun u => u.1.1) V.replicaLaw) := by
              apply Finset.sum_congr rfl
              intro i _
              simpa [R, A, B, X] using hred_i i
      _ = (n : Real) * V.replicaDefect -
          ∑ i, condMI (fun u => u.1.2) (fun u => g i u.2)
            (fun u => u.1.1) V.replicaLaw := by
              rw [Finset.sum_sub_distrib, Finset.sum_const,
                Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith

/-- The averaged contact/resampling inequality follows solely from optimality
of the latent. -/
theorem replicaViewInformation_le_of_optimal [Nonempty Omega]
    (hinj : forall i, Function.Injective (fun x => (f i x, g i x)))
    (htup : Function.Injective (tupleView f))
    (hoptimal : V.score f g = nTau f g p) :
    V.replicaViewInformation f g <= ((n : Real) + 1) * V.replicaDefect := by
  have hbdd : BddBelow (Set.range fun W : NLatent p => W.score f g) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨W, rfl⟩
    exact NLatent.score_nonneg W hinj htup
  have hmin : V.score f g <= V.replicaRefinement.score f g := by
    rw [hoptimal]
    unfold nTau
    exact ciInf_le hbdd V.replicaRefinement
  have hdiff := V.replicaRefinement_score_sub f g hinj
  linarith

end NLatent

end stoch_to_det
