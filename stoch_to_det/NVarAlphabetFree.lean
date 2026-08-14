import stoch_to_det.NVarPosteriorCompression

/-!
# An alphabet-free coordinate bound for every `n >= 3`

This file combines posterior-replica control, the imported two-variable
compression theorem, finite seed fixing, and hardening.  Its final constant
depends only on `n`.
-/

namespace stoch_to_det

open Finset

namespace FiniteInfo

/-- Entropy is unchanged when two finite observables deterministically decode
each other on the underlying sample space. -/
lemma Hvar_eq_of_mutual_recode
    {A F G : Type*} [Fintype A] [Fintype F] [DecidableEq F]
    [Fintype G] [DecidableEq G]
    {m : A -> Real} (hm : IsPMF m) (f : A -> F) (g : A -> G)
    (enc : F -> G) (dec : G -> F)
    (henc : forall a, enc (f a) = g a)
    (hdec : forall a, dec (g a) = f a) :
    Hvar g m = Hvar f m := by
  have hforward := Hvar_comp_le hm f enc
  have hback := Hvar_comp_le hm g dec
  have hfg : enc ∘ f = g := by funext a; exact henc a
  have hgf : dec ∘ g = f := by funext a; exact hdec a
  rw [hfg] at hforward
  rw [hgf] at hback
  exact le_antisymm hforward hback

lemma condH_eq_of_mutual_recode_left
    {A F G K : Type*} [Fintype A] [Fintype F] [DecidableEq F]
    [Fintype G] [DecidableEq G] [Fintype K] [DecidableEq K]
    {m : A -> Real} (hm : IsPMF m) (f : A -> F) (g : A -> G)
    (h : A -> K) (enc : F -> G) (dec : G -> F)
    (henc : forall a, enc (f a) = g a)
    (hdec : forall a, dec (g a) = f a) :
    condH g h m = condH f h m := by
  let encPair : F × K -> G × K := fun z => (enc z.1, z.2)
  let decPair : G × K -> F × K := fun z => (dec z.1, z.2)
  have hpair := Hvar_eq_of_mutual_recode hm
    (fun a => (f a, h a)) (fun a => (g a, h a)) encPair decPair
    (fun a => Prod.ext (henc a) rfl) (fun a => Prod.ext (hdec a) rfl)
  unfold condH
  rw [hpair]

lemma condH_eq_of_mutual_recode_condition
    {A F K L : Type*} [Fintype A] [Fintype F] [DecidableEq F]
    [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
    {m : A -> Real} (hm : IsPMF m) (f : A -> F) (h : A -> K)
    (k : A -> L) (enc : K -> L) (dec : L -> K)
    (henc : forall a, enc (h a) = k a)
    (hdec : forall a, dec (k a) = h a) :
    condH f k m = condH f h m := by
  let encPair : F × K -> F × L := fun z => (z.1, enc z.2)
  let decPair : F × L -> F × K := fun z => (z.1, dec z.2)
  have hpair := Hvar_eq_of_mutual_recode hm
    (fun a => (f a, h a)) (fun a => (f a, k a)) encPair decPair
    (fun a => Prod.ext rfl (henc a)) (fun a => Prod.ext rfl (hdec a))
  have hcond := Hvar_eq_of_mutual_recode hm h k enc dec henc hdec
  unfold condH
  rw [hpair, hcond]

end FiniteInfo

section Recode

variable {Omega delta : Type} [Fintype Omega] [DecidableEq Omega]
  [Nonempty Omega] [Fintype delta] [DecidableEq delta]

/-- Assign to every realized code value a canonical representative source
point, then label that point in `Fin |Omega|`. -/
private noncomputable def finiteCodeEncoder (code : Omega -> delta) :
    delta -> Fin (Fintype.card Omega) := fun d =>
  if h : exists x, code x = d then
    Fintype.equivFin Omega (Classical.choose h)
  else Fintype.equivFin Omega (Classical.choice inferInstance)

private noncomputable def finiteCodeDecoder (code : Omega -> delta) :
    Fin (Fintype.card Omega) -> delta := fun j =>
  code ((Fintype.equivFin Omega).symm j)

private noncomputable def finiteCodeRecode (code : Omega -> delta) :
    Omega -> Fin (Fintype.card Omega) :=
  finiteCodeEncoder code ∘ code

private lemma finiteCodeDecoder_encoder (code : Omega -> delta) (x : Omega) :
    finiteCodeDecoder code (finiteCodeEncoder code (code x)) = code x := by
  unfold finiteCodeDecoder finiteCodeEncoder
  rw [dif_pos ⟨x, rfl⟩, Equiv.symm_apply_apply]
  exact Classical.choose_spec (show exists y, code y = code x from ⟨x, rfl⟩)

variable {n : Nat} {kappa gamma : Fin n -> Type}
  [forall i, Fintype (kappa i)] [forall i, DecidableEq (kappa i)]
  [forall i, Fintype (gamma i)] [forall i, DecidableEq (gamma i)]
  {p : Omega -> Real}

private theorem nDetScore_finiteCodeRecode
    (hp : IsPMF p) (f : forall i, Omega -> kappa i)
    (g : forall i, Omega -> gamma i) (code : Omega -> delta) :
    nDetScore f g p (finiteCodeRecode code) = nDetScore f g p code := by
  let enc := finiteCodeEncoder code
  let dec := finiteCodeDecoder code
  let recode := finiteCodeRecode code
  have henc (x : Omega) : enc (code x) = recode x := rfl
  have hdec (x : Omega) : dec (recode x) = code x := by
    exact finiteCodeDecoder_encoder code x
  have hcond {F : Type} [Fintype F] [DecidableEq F] (q : Omega -> F) :
      condH q recode p = condH q code p :=
    FiniteInfo.condH_eq_of_mutual_recode_condition hp q code recode
      enc dec henc hdec
  have hleft {K : Type} [Fintype K] [DecidableEq K] (q : Omega -> K) :
      condH recode q p = condH code q p :=
    FiniteInfo.condH_eq_of_mutual_recode_left hp code recode q
      enc dec henc hdec
  unfold nDetScore nCondTC
  have hsum : (∑ i, condH (f i) recode p) =
      ∑ i, condH (f i) code p := by
    apply Finset.sum_congr rfl
    intro i _
    exact hcond (f i)
  have hfull : condH (fun z : Omega => z) recode p =
      condH (fun z : Omega => z) code p := hcond _
  have hred : (∑ i, condH recode (g i) p) =
      ∑ i, condH code (g i) p := by
    apply Finset.sum_congr rfl
    intro i _
    exact hleft (g i)
  rw [hsum, hfull, hred]

private theorem ofFunction_finiteCodeRecode_score
    (hp : IsPMF p) (f : forall i, Omega -> kappa i)
    (g : forall i, Omega -> gamma i)
    (hinj : forall i, Function.Injective (fun z => (f i z, g i z)))
    (code : Omega -> delta) :
    (NLatent.ofFunction hp (finiteCodeRecode code)).score f g =
      (NLatent.ofFunction hp code).score f g := by
  rw [NLatent.ofFunction_score_eq_nDetScore hp f g hinj,
    NLatent.ofFunction_score_eq_nDetScore hp f g hinj,
    nDetScore_finiteCodeRecode hp f g code]

end Recode

namespace NVarAlphabetFree

variable {n : Nat} {alpha : Type} [Fintype alpha] [DecidableEq alpha]
  [Inhabited alpha]
variable {p : (Fin n -> alpha) -> Real}

/-- The certified alphabet-free stochastic-to-hard bound.  The centralized
`oneSidedFactor = 2 * certifiedFactor + 2` contains the complete dependence
on the imported two-variable theorem; every other factor is polynomial in
`n`. -/
theorem nT_le_alphabetFree (hp : IsPMF p) (hn : 3 <= n) :
    nT (fun i => coordinateView (alpha := alpha) i)
        (fun i => coordinateDeletionView (alpha := alpha) i) p <=
      (1 + ((n : Real) + 1) * NVarTwoVariableInput.oneSidedFactor *
          (n : Real) * ((n : Real) - 2)) *
        nTau (fun i => coordinateView (alpha := alpha) i)
          (fun i => coordinateDeletionView (alpha := alpha) i) p := by
  let f : forall i : Fin n, (Fin n -> alpha) -> alpha :=
    fun i => coordinateView (alpha := alpha) i
  let g : forall i : Fin n, (Fin n -> alpha) -> (Fin n -> alpha) :=
    fun i => coordinateDeletionView (alpha := alpha) i
  obtain ⟨V, _hcard, hoptimal⟩ := exists_nTau_optimal_latent
    (f := f) (g := g) hp (by
      intro i
      dsimp only [f, g]
      exact coordinate_pair_injective (alpha := alpha) i)
  obtain ⟨code, hcode⟩ := V.exists_hardCode_oneSided
  let hard := NLatent.ofFunction hp code
  let recode := finiteCodeRecode code
  have hdefect := V.replicaDefect_le_score_of_optimal hn hoptimal
  have hhard := V.ofFunction_score_le_score_add_error hp code
  let err :=
    condMI (fun w : V.ι × (Fin n -> alpha) => w.1) (fun w => w.2)
        (fun w => code w.2) V.joint +
      condH (fun w : V.ι × (Fin n -> alpha) => code w.2)
        (fun w => w.1) V.joint
  have herr : err <=
      NVarTwoVariableInput.oneSidedFactor * V.replicaDefect := by
    exact hcode
  have hnR : (3 : Real) <= (n : Real) := by exact_mod_cast hn
  have hfactor : 0 <= (n : Real) + 1 := by linarith
  have herr' : err <=
      NVarTwoVariableInput.oneSidedFactor *
        ((n : Real) * ((n : Real) - 2) * V.score f g) := by
    exact herr.trans (mul_le_mul_of_nonneg_left hdefect
      NVarTwoVariableInput.oneSidedFactor_nonneg)
  have hhard' : hard.score f g <=
      (1 + ((n : Real) + 1) * NVarTwoVariableInput.oneSidedFactor *
          (n : Real) * ((n : Real) - 2)) *
        V.score f g := by
    dsimp only [hard, f, g] at hhard ⊢
    dsimp only [err] at herr'
    calc
      (NLatent.ofFunction hp code).score
          (fun i => coordinateView (alpha := alpha) i)
          (fun i => coordinateDeletionView (alpha := alpha) i) <=
        V.score (fun i => coordinateView (alpha := alpha) i)
            (fun i => coordinateDeletionView (alpha := alpha) i) +
          ((n : Real) + 1) * err := hhard
      _ <= V.score (fun i => coordinateView (alpha := alpha) i)
            (fun i => coordinateDeletionView (alpha := alpha) i) +
          ((n : Real) + 1) *
            (NVarTwoVariableInput.oneSidedFactor *
              ((n : Real) * ((n : Real) - 2) *
              V.score (fun i => coordinateView (alpha := alpha) i)
                (fun i => coordinateDeletionView (alpha := alpha) i))) := by
          dsimp only [err, f, g] at herr'
          dsimp only [err]
          simpa only [add_comm] using
            (add_le_add_left (mul_le_mul_of_nonneg_left herr' hfactor)
              (V.score (fun i => coordinateView (alpha := alpha) i)
                (fun i => coordinateDeletionView (alpha := alpha) i)))
      _ = _ := by ring
  have hrecode : (NLatent.ofFunction hp recode).score f g = hard.score f g := by
    exact ofFunction_finiteCodeRecode_score hp f g
      (fun i => coordinate_pair_injective (alpha := alpha) i) code
  have hT := nT_le_code_score f g hp
    (fun i => coordinate_pair_injective (alpha := alpha) i)
    (coordinate_tuple_injective (alpha := alpha)) recode
  rw [hrecode] at hT
  calc
    nT f g p <= hard.score f g := hT
    _ <= (1 + ((n : Real) + 1) * NVarTwoVariableInput.oneSidedFactor *
          (n : Real) * ((n : Real) - 2)) *
        V.score f g := hhard'
    _ = _ := by rw [hoptimal]

end NVarAlphabetFree

end stoch_to_det
