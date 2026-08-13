import stoch_to_det.NVarReplicaBound

/-!
# Hardening a finite multivariate latent

A hard code is compared to an arbitrary stochastic latent through the two
one-sided errors `I(C;X | Gamma)` and `H(Gamma | C)`.  The coefficient is
independent of every alphabet.
-/

namespace stoch_to_det

open Finset

namespace FiniteInfo

lemma condH_nonneg
    {Z F K : Type*} [Fintype Z] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]
    {m : Z -> Real} (hm : IsPMF m) (f : Z -> F) (h : Z -> K) :
    0 <= condH f h m := by
  have hmono := Hvar_comp_le hm (fun z => (f z, h z)) Prod.snd
  change Hvar h m <= Hvar (fun z => (f z, h z)) m at hmono
  unfold condH
  linarith

lemma condH_pair_condition_le
    {Z F G K : Type*} [Fintype Z] [Fintype F] [Fintype G] [Fintype K]
    [DecidableEq F] [DecidableEq G] [DecidableEq K]
    {m : Z -> Real} (hm : IsPMF m) (f : Z -> F) (g : Z -> G) (h : Z -> K) :
    condH f (fun z => (g z, h z)) m <= condH f h m := by
  have hmi := condMI_nonneg hm f g h
  have hchain := condMI_eq_condH_sub_pair hm f g h
  linarith

lemma condMI_le_condH_left
    {Z F G K : Type*} [Fintype Z] [Fintype F] [Fintype G] [Fintype K]
    [DecidableEq F] [DecidableEq G] [DecidableEq K]
    {m : Z -> Real} (hm : IsPMF m) (f : Z -> F) (g : Z -> G) (h : Z -> K) :
    condMI f g h m <= condH f h m := by
  have hchain := condMI_eq_condH_sub_pair hm f g h
  have hnonneg := condH_nonneg hm f (fun z => (g z, h z))
  linarith

lemma condH_function_of_condition_zero
    {Z F K : Type*} [Fintype Z] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]
    {m : Z -> Real} (hm : IsPMF m) (f : Z -> F) (h : Z -> K)
    (decode : K -> F) (hdecode : forall z, decode (h z) = f z) :
    condH f h m = 0 := by
  let enc : K -> F × K := fun k => (decode k, k)
  have hH := Hvar_eq_of_leftInverse hm h enc Prod.snd (fun _ => rfl)
  have hpair : enc ∘ h = fun z => (f z, h z) := by
    funext z
    exact Prod.ext (hdecode z) rfl
  rw [hpair] at hH
  unfold condH
  rw [hH]
  ring

end FiniteInfo

namespace NLatent

variable {n : Nat} {alpha delta : Type} [Fintype alpha] [DecidableEq alpha]
  [Inhabited alpha] [Fintype delta] [DecidableEq delta]
variable {p : (Fin n -> alpha) -> Real}

private theorem condH_source_lift (V : NLatent p)
    {F K : Type} [Fintype F] [Fintype K] [DecidableEq F] [DecidableEq K]
    (f : (Fin n -> alpha) -> F) (h : (Fin n -> alpha) -> K) :
    condH (fun w : V.ι × (Fin n -> alpha) => f w.2) (fun w => h w.2)
        V.joint = condH f h p := by
  unfold condH
  rw [V.Hvar_lift (fun x => (f x, h x)), V.Hvar_lift h]

private theorem condMI_source_lift (V : NLatent p)
    {F G K : Type} [Fintype F] [Fintype G] [Fintype K]
    [DecidableEq F] [DecidableEq G] [DecidableEq K]
    (f : (Fin n -> alpha) -> F) (g : (Fin n -> alpha) -> G)
    (h : (Fin n -> alpha) -> K) :
    condMI (fun w : V.ι × (Fin n -> alpha) => f w.2) (fun w => g w.2)
        (fun w => h w.2) V.joint = condMI f g h p := by
  unfold condMI
  rw [V.Hvar_lift (fun x => (f x, h x)),
    V.Hvar_lift (fun x => (g x, h x)),
    V.Hvar_lift (fun x => (f x, g x, h x)), V.Hvar_lift h]

/-- Hardening ledger for coordinate views. -/
theorem ofFunction_score_le_score_add_error (V : NLatent p)
    (hp : IsPMF p) (code : (Fin n -> alpha) -> delta) :
    (NLatent.ofFunction hp code).score
        (fun i => coordinateView (alpha := alpha) i)
        (fun i => coordinateDeletionView (alpha := alpha) i) <=
      V.score (fun i => coordinateView (alpha := alpha) i)
          (fun i => coordinateDeletionView (alpha := alpha) i) +
        ((n : Real) + 1) *
          (condMI (fun w : V.ι × (Fin n -> alpha) => w.1)
              (fun w => w.2) (fun w => code w.2) V.joint +
            condH (fun w : V.ι × (Fin n -> alpha) => code w.2)
              (fun w => w.1) V.joint) := by
  let X : V.ι × (Fin n -> alpha) -> (Fin n -> alpha) := fun w => w.2
  let C : V.ι × (Fin n -> alpha) -> V.ι := fun w => w.1
  let G : V.ι × (Fin n -> alpha) -> delta := fun w => code w.2
  let Xi : Fin n -> V.ι × (Fin n -> alpha) -> alpha := fun i w => w.2 i
  let Di : Fin n -> V.ι × (Fin n -> alpha) -> (Fin n -> alpha) :=
    fun i w => maskDelete i w.2
  let hE : Real := condH G C V.joint
  let iE : Real := condMI C X G V.joint

  have hGXC : condH G (fun w => (X w, C w)) V.joint = 0 := by
    apply FiniteInfo.condH_function_of_condition_zero V.joint_isPMF
      G (fun w => (X w, C w)) (fun z => code z.1)
    intro w
    rfl
  have hGX : condMI X G C V.joint = hE := by
    have hcomm := FiniteInfo.condMI_comm V.joint_isPMF X G C
    have hchain := condMI_eq_condH_sub_pair V.joint_isPMF G X C
    dsimp only [hE]
    rw [hGXC] at hchain
    linarith
  have hTC_adjoin :
      ((∑ i, condH (Xi i) (fun w => (G w, C w)) V.joint) -
          condH X (fun w => (G w, C w)) V.joint) <=
        ((∑ i, condH (Xi i) C V.joint) - condH X C V.joint) + hE := by
    have hmono_i (i : Fin n) :
        condH (Xi i) (fun w => (G w, C w)) V.joint <=
          condH (Xi i) C V.joint :=
      FiniteInfo.condH_pair_condition_le V.joint_isPMF (Xi i) G C
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      hmono_i i
    have hfull := condMI_eq_condH_sub_pair V.joint_isPMF X G C
    rw [hGX] at hfull
    linarith

  have hTC_forget :
      ((∑ i, condH (Xi i) G V.joint) - condH X G V.joint) <=
        ((∑ i, condH (Xi i) (fun w => (G w, C w)) V.joint) -
          condH X (fun w => (G w, C w)) V.joint) + (n : Real) * iE := by
    have hpair_eq (f : V.ι × (Fin n -> alpha) -> alpha) :
        condH f (fun w => (G w, C w)) V.joint =
          condH f (fun w => (C w, G w)) V.joint := by
      exact FiniteInfo.condH_equiv_cond V.joint_isPMF f
        (fun w => (G w, C w)) (Equiv.prodComm delta V.ι) |>.symm
    have hpairX : condH X (fun w => (G w, C w)) V.joint =
        condH X (fun w => (C w, G w)) V.joint :=
      FiniteInfo.condH_equiv_cond V.joint_isPMF X
        (fun w => (G w, C w)) (Equiv.prodComm delta V.ι) |>.symm
    have hdiff_i (i : Fin n) :
        condH (Xi i) G V.joint -
            condH (Xi i) (fun w => (G w, C w)) V.joint =
          condMI C (Xi i) G V.joint := by
      have hchain := condMI_eq_condH_sub_pair V.joint_isPMF (Xi i) C G
      have hcomm := FiniteInfo.condMI_comm V.joint_isPMF (Xi i) C G
      rw [hpair_eq (Xi i)]
      linarith
    have hdiffX : condH X G V.joint -
          condH X (fun w => (G w, C w)) V.joint = iE := by
      have hchain := condMI_eq_condH_sub_pair V.joint_isPMF X C G
      have hcomm := FiniteInfo.condMI_comm V.joint_isPMF X C G
      rw [hpairX]
      dsimp only [iE]
      linarith
    have hdata (i : Fin n) : condMI C (Xi i) G V.joint <= iE := by
      have hpair := FiniteInfo.condMI_pair_right V.joint_isPMF C
        (Xi i) (Di i) G
      have hrecode := FiniteInfo.condMI_comp_right_eq_of_injective
        V.joint_isPMF C X G
        (fun x : Fin n -> alpha => (x i, maskDelete i x))
        (coordinate_pair_injective (alpha := alpha) i)
      have hnonneg := condMI_nonneg V.joint_isPMF C (Di i)
        (fun w => (G w, Xi i w))
      dsimp only [X, C, G, Xi, Di, iE] at hpair hrecode hnonneg ⊢
      linarith
    have hsum_data := Finset.sum_le_sum fun i
        (_ : i ∈ (Finset.univ : Finset (Fin n))) => hdata i
    have hsum_diff :
        (∑ i, condH (Xi i) G V.joint) -
            ∑ i, condH (Xi i) (fun w => (G w, C w)) V.joint =
          ∑ i, condMI C (Xi i) G V.joint := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact hdiff_i i
    have hconst : (∑ _i : Fin n, iE) = (n : Real) * iE := by simp
    rw [hconst] at hsum_data
    have hiE : 0 <= iE := by
      dsimp only [iE]
      exact condMI_nonneg V.joint_isPMF C X G
    linarith

  have hrecover_i (i : Fin n) :
      condH G (Di i) V.joint <=
        condMI C (Xi i) (Di i) V.joint + hE := by
    have hzero : condH G (fun w => (Xi i w, Di i w)) V.joint = 0 := by
      let decode : alpha × (Fin n -> alpha) -> delta := fun z =>
        code (Function.update z.2 i z.1)
      apply FiniteInfo.condH_function_of_condition_zero V.joint_isPMF G
        (fun w => (Xi i w, Di i w)) decode
      intro w
      dsimp only [G, Xi, Di, decode]
      congr 1
      funext j
      by_cases hji : j = i
      · subst j
        simp [maskDelete]
      · simp [Function.update, maskDelete, hji]
    have hhard : condH G (Di i) V.joint =
        condMI G (Xi i) (Di i) V.joint := by
      have hchain := condMI_eq_condH_sub_pair V.joint_isPMF G (Xi i) (Di i)
      rw [hzero] at hchain
      linarith
    have hmono_pair : condMI G (Xi i) (Di i) V.joint <=
        condMI (fun w => (G w, C w)) (Xi i) (Di i) V.joint := by
      have hchain := FiniteInfo.condMI_pair_left V.joint_isPMF G C
        (Xi i) (Di i)
      have hnonneg := condMI_nonneg V.joint_isPMF C (Xi i)
        (fun w => (Di i w, G w))
      linarith
    have hswap_pair :
        condMI (fun w => (G w, C w)) (Xi i) (Di i) V.joint =
          condMI (fun w => (C w, G w)) (Xi i) (Di i) V.joint := by
      let swap : delta × V.ι -> V.ι × delta := fun z => (z.2, z.1)
      have hinj : Function.Injective swap := by
        intro x y hxy
        exact Prod.ext (congrArg Prod.snd hxy) (congrArg Prod.fst hxy)
      exact FiniteInfo.condMI_comp_left_eq_of_injective V.joint_isPMF
        (fun w => (G w, C w)) (Xi i) (Di i) swap hinj |>.symm
    have hchain_ref := FiniteInfo.condMI_pair_left V.joint_isPMF C G
      (Xi i) (Di i)
    have hextra : condMI G (Xi i) (fun w => (Di i w, C w)) V.joint <= hE := by
      have hleH := FiniteInfo.condMI_le_condH_left V.joint_isPMF G (Xi i)
        (fun w => (Di i w, C w))
      have hcond := FiniteInfo.condH_pair_condition_le V.joint_isPMF G (Di i) C
      dsimp only [hE]
      linarith
    rw [hhard]
    rw [hswap_pair] at hmono_pair
    linarith

  have hrecover := Finset.sum_le_sum fun i
      (_ : i ∈ (Finset.univ : Finset (Fin n))) => hrecover_i i
  have hconstE : (∑ _i : Fin n, hE) = (n : Real) * hE := by simp
  rw [Finset.sum_add_distrib, hconstE] at hrecover

  have hhardScore :
      (NLatent.ofFunction hp code).score
          (fun i => coordinateView (alpha := alpha) i)
          (fun i => coordinateDeletionView (alpha := alpha) i) =
        ((∑ i, condH (Xi i) G V.joint) - condH X G V.joint) +
          ∑ i, condH G (Di i) V.joint := by
    rw [NLatent.ofFunction_score_eq_nDetScore hp
      (fun i => coordinateView (alpha := alpha) i)
      (fun i => coordinateDeletionView (alpha := alpha) i)
      (fun i => coordinate_pair_injective (alpha := alpha) i) code]
    unfold nDetScore nCondTC
    simp only [coordinateView, coordinateDeletionView]
    have hs (i : Fin n) := V.condH_source_lift (fun x => x i) code
    have hfull := V.condH_source_lift (fun x => x) code
    have hr (i : Fin n) := V.condH_source_lift code (maskDelete i)
    dsimp only [X, G, Xi, Di] at hs hfull hr ⊢
    simp_rw [hs, hfull, hr]
    rfl
  have hVScore :
      V.score (fun i => coordinateView (alpha := alpha) i)
          (fun i => coordinateDeletionView (alpha := alpha) i) =
        ((∑ i, condH (Xi i) C V.joint) - condH X C V.joint) +
          ∑ i, condMI C (Xi i) (Di i) V.joint := by
    unfold NLatent.score
    rfl
  rw [hhardScore, hVScore]
  change _ <= _ + ((n : Real) + 1) * (iE + hE)
  have hiE : 0 <= iE := by
    dsimp only [iE]
    exact condMI_nonneg V.joint_isPMF C X G
  nlinarith

end NLatent

end stoch_to_det
