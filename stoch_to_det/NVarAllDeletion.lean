import stoch_to_det.NVarPosteriorCompression
import stoch_to_det.NVarReplicaBound
import stoch_to_det.NVarHardening
import stoch_to_det.NVarAlphabetFree

/-!
# Natural-latent scores for an arbitrary deletion budget

For `D` of cardinality `m`, the stochastic redundancy term is
`I(V; X_D | X_{-D})`; the entropy redundancy term is `H(Z | X_{-D})`.
This file first treats the sum over all such `D`.  The max-form theorem is
obtained from the finite inequalities `max <= sum <= card * max`.
-/

namespace stoch_to_det

open Finset

set_option maxHeartbeats 1000000

/-- Coordinate subsets of cardinality `m`. -/
abbrev DeletionSet (n m : Nat) := {D : Finset (Fin n) // D.card = m}

theorem card_deletionSet (n m : Nat) :
    Fintype.card (DeletionSet n m) = Nat.choose n m := by
  classical
  let e : DeletionSet n m ≃
      {D : Finset (Fin n) // D ∈ Finset.univ.powersetCard m} :=
    { toFun := fun D => ⟨D.1, Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ D.1, D.2⟩⟩
      invFun := fun D => ⟨D.1, (Finset.mem_powersetCard.mp D.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_powersetCard]
  simp

theorem deletionSet_nonempty {n m : Nat} (hmn : m <= n) :
    Nonempty (DeletionSet n m) := by
  classical
  obtain ⟨D, _hsub, hcard⟩ := Finset.exists_superset_card_eq
    (s := (∅ : Finset (Fin n))) (n := m) (by simp) (by simpa using hmn)
  exact ⟨⟨D, hcard⟩⟩

section Masks

variable {n : Nat} {alpha : Type} [Inhabited alpha]

/-- Keep the coordinates in `S` and replace the others by the default value. -/
def maskOn (S : Finset (Fin n)) (x : Fin n -> alpha) : Fin n -> alpha :=
  fun i => if i ∈ S then x i else default

/-- The deleted block `X_D`, represented in the ambient product alphabet. -/
def deletedBlockView {m : Nat} (D : DeletionSet n m) :
    (Fin n -> alpha) -> (Fin n -> alpha) := maskOn D.1

/-- The surviving block `X_{-D}`, represented in the ambient product alphabet. -/
def survivorBlockView {m : Nat} (D : DeletionSet n m) :
    (Fin n -> alpha) -> (Fin n -> alpha) := maskOn (Finset.univ \ D.1)

theorem deleted_survivor_injective {m : Nat} (D : DeletionSet n m) :
    Function.Injective (fun x : Fin n -> alpha =>
      (deletedBlockView D x, survivorBlockView D x)) := by
  intro x y hxy
  funext i
  by_cases hi : i ∈ D.1
  · have h := congrFun (congrArg Prod.fst hxy) i
    simpa [deletedBlockView, maskOn, hi] using h
  · have h := congrFun (congrArg Prod.snd hxy) i
    have hi' : i ∈ (Finset.univ \ D.1) := by simp [hi]
    simpa [survivorBlockView, maskOn, hi'] using h

end Masks

namespace NLatent

variable {n m : Nat} {alpha : Type} [Fintype alpha] [DecidableEq alpha]
  [Inhabited alpha]
variable {p : (Fin n -> alpha) -> Real}

/-- Sum-form stochastic score for deletion budget `m`. -/
noncomputable def deletionSumScore (V : NLatent p) : Real :=
  ((∑ i, condH
      (fun w : V.ι × (Fin n -> alpha) => w.2 i) (fun w => w.1) V.joint) -
    condH (fun w : V.ι × (Fin n -> alpha) => w.2) (fun w => w.1)
      V.joint) +
    ∑ D : DeletionSet n m,
      condMI (fun w : V.ι × (Fin n -> alpha) => w.1)
        (fun w => deletedBlockView D w.2)
        (fun w => survivorBlockView D w.2) V.joint

/-- The sum-form stochastic optimum. -/
noncomputable def deletionSumTau (p : (Fin n -> alpha) -> Real) : Real :=
  ⨅ V : NLatent p, V.deletionSumScore (m := m)

/-- The conditional-TC part of the deletion score is nonnegative. -/
theorem deletionConditionalTC_nonneg [Nonempty alpha] (V : NLatent p) :
    0 <= (∑ i, condH
        (fun w : V.ι × (Fin n -> alpha) => w.2 i) (fun w => w.1) V.joint) -
      condH (fun w : V.ι × (Fin n -> alpha) => w.2) (fun w => w.1)
        V.joint := by
  exact V.conditionalTC_nonneg
    (f := fun i => coordinateView (alpha := alpha) i)
    (coordinate_tuple_injective (alpha := alpha))

theorem deletionSumScore_nonneg [Nonempty alpha] (V : NLatent p) :
    0 <= V.deletionSumScore (m := m) := by
  have htc := V.deletionConditionalTC_nonneg
  have hred : 0 <= ∑ D : DeletionSet n m,
      condMI (fun w : V.ι × (Fin n -> alpha) => w.1)
        (fun w => deletedBlockView D w.2)
        (fun w => survivorBlockView D w.2) V.joint := by
    exact Finset.sum_nonneg fun D _ => condMI_nonneg V.joint_isPMF
      (fun w => w.1) (fun w => deletedBlockView D w.2)
      (fun w => survivorBlockView D w.2)
  exact add_nonneg htc hred

/-- Posterior payoff whose concave envelope computes the sum score. -/
noncomputable def deletionPhi (m : Nat) (q : (Fin n -> alpha) -> Real) : Real :=
  ((Fintype.card (DeletionSet n m) : Real) + 1) * H q -
    ∑ i, Hvar (fun x : Fin n -> alpha => x i) q -
    ∑ D : DeletionSet n m, Hvar (survivorBlockView D) q

/-- The fixed base term in the sum-score envelope identity. -/
noncomputable def deletionPsi (m : Nat) (q : (Fin n -> alpha) -> Real) : Real :=
  ∑ D : DeletionSet n m,
    condH (deletedBlockView D) (survivorBlockView D) q

private theorem Hvar_id_eq_H (hq : IsPMF p) :
    Hvar (fun x : Fin n -> alpha => x) p = H p := by
  unfold Hvar
  change H (push (Equiv.refl (Fin n -> alpha)) p) = H p
  exact H_push_equiv (Equiv.refl (Fin n -> alpha)) p hq

private theorem condH_deleted_survivor (hq : IsPMF p)
    (D : DeletionSet n m) :
    condH (deletedBlockView D) (survivorBlockView D) p =
      H p - Hvar (survivorBlockView D) p := by
  have hpair : Hvar (fun x =>
      (deletedBlockView D x, survivorBlockView D x)) p = H p := by
    let left : ((Fin n -> alpha) × (Fin n -> alpha)) -> (Fin n -> alpha) :=
      fun z i => if i ∈ D.1 then z.1 i else z.2 i
    have hleft : Function.LeftInverse left (fun x : Fin n -> alpha =>
        (deletedBlockView D x, survivorBlockView D x)) := by
      intro x
      funext i
      by_cases hi : i ∈ D.1
      · simp [left, deletedBlockView, maskOn, hi]
      · have hi' : i ∈ (Finset.univ \ D.1) := by simp [hi]
        simp [left, survivorBlockView, maskOn, hi, hi']
    have h := Hvar_eq_of_leftInverse hq (fun x : Fin n -> alpha => x)
      (fun x => (deletedBlockView D x, survivorBlockView D x)) left hleft
    rw [Hvar_id_eq_H hq] at h
    exact h
  unfold condH
  rw [hpair]

private theorem condMI_deleted_survivor_component (V : NLatent p)
    (D : DeletionSet n m) :
    condMI (fun w : V.ι × (Fin n -> alpha) => w.1)
        (fun w => deletedBlockView D w.2)
        (fun w => survivorBlockView D w.2) V.joint =
      condH (deletedBlockView D) (survivorBlockView D) p -
        ∑ v, V.prior v *
          condH (deletedBlockView D) (survivorBlockView D) (V.comp v) := by
  let fd : Fin 1 -> (Fin n -> alpha) -> (Fin n -> alpha) :=
    fun _ => deletedBlockView D
  let gd : Fin 1 -> (Fin n -> alpha) -> (Fin n -> alpha) :=
    fun _ => survivorBlockView D
  have h := V.condMI_view (f := fd) (g := gd) (0 : Fin 1)
  simpa [fd, gd] using h

/-- Envelope decomposition of the arbitrary-budget sum score. -/
theorem deletionSumScore_eq_envelope (V : NLatent p) :
    V.deletionSumScore (m := m) =
      deletionPsi (n := n) (alpha := alpha) m p -
        ∑ v, V.prior v * deletionPhi (n := n) (alpha := alpha) m (V.comp v) := by
  have hfull :
      condH (fun w : V.ι × (Fin n -> alpha) => w.2) (fun w => w.1)
          V.joint = ∑ v, V.prior v * H (V.comp v) := by
    rw [V.condH_view_prior (fun x : Fin n -> alpha => x)]
    apply Finset.sum_congr rfl
    intro v _
    congr 1
    exact Hvar_id_eq_H (V.comp_isPMF v)
  have hcoord (i : Fin n) :
      condH (fun w : V.ι × (Fin n -> alpha) => w.2 i) (fun w => w.1)
          V.joint = ∑ v, V.prior v * Hvar (fun x : Fin n -> alpha => x i)
            (V.comp v) :=
    V.condH_view_prior (fun x : Fin n -> alpha => x i)
  have hred (D : DeletionSet n m) := V.condMI_deleted_survivor_component D
  have hcond (D : DeletionSet n m) (v : V.ι) :
      condH (deletedBlockView D) (survivorBlockView D) (V.comp v) =
        H (V.comp v) - Hvar (survivorBlockView D) (V.comp v) :=
    condH_deleted_survivor (V.comp_isPMF v) D
  unfold deletionSumScore deletionPsi deletionPhi
  simp_rw [hcoord, hred, hcond]
  rw [hfull]
  have hswapCoord :
      (∑ i : Fin n, ∑ v : V.ι,
        V.prior v * Hvar (fun x : Fin n -> alpha => x i) (V.comp v)) =
      ∑ v : V.ι, ∑ i : Fin n,
        V.prior v * Hvar (fun x : Fin n -> alpha => x i) (V.comp v) :=
    Finset.sum_comm
  have hswapDel :
      (∑ D : DeletionSet n m, ∑ v : V.ι,
        V.prior v * (H (V.comp v) -
          Hvar (survivorBlockView D) (V.comp v))) =
      ∑ v : V.ι, ∑ D : DeletionSet n m,
        V.prior v * (H (V.comp v) -
          Hvar (survivorBlockView D) (V.comp v)) := Finset.sum_comm
  rw [Finset.sum_sub_distrib, hswapCoord, hswapDel]
  have hcard (v : V.ι) :
      (∑ _D : DeletionSet n m, H (V.comp v)) =
        (Fintype.card (DeletionSet n m) : Real) * H (V.comp v) := by simp
  have hcardMul (v : V.ι) :
      (∑ _D : DeletionSet n m, V.prior v * H (V.comp v)) =
        (Fintype.card (DeletionSet n m) : Real) *
          (V.prior v * H (V.comp v)) := by simp
  simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  simp_rw [hcardMul]
  have hpoint (v : V.ι) :
      V.prior v *
          (((Fintype.card (DeletionSet n m) : Real) + 1) * H (V.comp v)) =
        (Fintype.card (DeletionSet n m) : Real) *
            (V.prior v * H (V.comp v)) +
          V.prior v * H (V.comp v) := by ring
  simp_rw [hpoint, Finset.sum_add_distrib]
  ring

end NLatent

/-- Sum-form entropy score of a hard code. -/
noncomputable def deletionSumHardScore
    {n m : Nat} {alpha delta : Type}
    [Fintype alpha] [DecidableEq alpha] [Inhabited alpha]
    [Fintype delta] [DecidableEq delta]
    (p : (Fin n -> alpha) -> Real) (code : (Fin n -> alpha) -> delta) : Real :=
  nCondTC (fun i => coordinateView (alpha := alpha) i) p code +
    ∑ D : DeletionSet n m, condH code (survivorBlockView D) p

namespace NLatent

variable {n m : Nat} {alpha delta : Type}
  [Fintype alpha] [DecidableEq alpha] [Inhabited alpha]
  [Fintype delta] [DecidableEq delta]
variable {p : (Fin n -> alpha) -> Real}

/-- On hard latents the stochastic CMI terms become the requested entropy
redundancy terms. -/
theorem ofFunction_deletionSumScore_eq_hardScore
    (hp : IsPMF p) (code : (Fin n -> alpha) -> delta) :
    (NLatent.ofFunction hp code).deletionSumScore (m := m) =
      deletionSumHardScore (m := m) p code := by
  change
    ((∑ i, condH
        (fun w : delta × (Fin n -> alpha) => w.2 i) (fun w => w.1)
        (NLatent.ofFunction hp code).joint) -
      condH (fun w : delta × (Fin n -> alpha) => w.2) (fun w => w.1)
        (NLatent.ofFunction hp code).joint) +
      ∑ D : DeletionSet n m,
        condMI (fun w : delta × (Fin n -> alpha) => w.1)
          (fun w => deletedBlockView D w.2)
          (fun w => survivorBlockView D w.2)
          (NLatent.ofFunction hp code).joint = _
  rw [NLatent.ofFunction_joint_eq_push hp code]
  unfold deletionSumHardScore nCondTC
  simp_rw [FiniteInfo.condH_push_source]
  simp_rw [FiniteInfo.condMI_push_source]
  change
    ((∑ i, condH (fun x : Fin n -> alpha => x i) code p) -
      condH (fun x : Fin n -> alpha => x) code p) +
      ∑ D : DeletionSet n m,
        condMI code (deletedBlockView D) (survivorBlockView D) p =
    ((∑ i, condH (coordinateView (alpha := alpha) i) code p) -
      condH (fun x : Fin n -> alpha => x) code p) +
      ∑ D : DeletionSet n m, condH code (survivorBlockView D) p
  have hred (D : DeletionSet n m) :
      condMI code (deletedBlockView D) (survivorBlockView D) p =
        condH code (survivorBlockView D) p := by
    let merge : ((Fin n -> alpha) × (Fin n -> alpha)) -> (Fin n -> alpha) :=
      fun z i => if i ∈ D.1 then z.1 i else z.2 i
    have hdecode (x : Fin n -> alpha) :
        code (merge (deletedBlockView D x, survivorBlockView D x)) = code x := by
      congr 1
      funext i
      by_cases hi : i ∈ D.1
      · simp [merge, deletedBlockView, maskOn, hi]
      · have hi' : i ∈ (Finset.univ \ D.1) := by simp [hi]
        simp [merge, survivorBlockView, maskOn, hi, hi']
    have hzero : condH code
        (fun x => (deletedBlockView D x, survivorBlockView D x)) p = 0 := by
      apply FiniteInfo.condH_function_of_condition_zero hp code
        (fun x => (deletedBlockView D x, survivorBlockView D x))
        (fun z => code (merge z))
      exact hdecode
    have hchain := condMI_eq_condH_sub_pair hp code
      (deletedBlockView D) (survivorBlockView D)
    rw [hzero] at hchain
    linarith
  simp_rw [hred]
  rfl

end NLatent

/-- Explicit coefficient for the arbitrary-deletion sum theorem. -/
noncomputable def deletionSumConstant (n m : Nat) : Real :=
  1 + ((n : Real) + (Fintype.card (DeletionSet n m) : Real) + 1) * 542 *
    (((n : Real) ^ 2 * ((n : Real) - 2)) + 1)

section DeletionEnvelope

variable {n m : Nat} {alpha : Type} [Fintype alpha] [DecidableEq alpha]
  [Inhabited alpha]

/-- Number of views used to realize `deletionPhi` as an ordinary `nPhi`. -/
abbrev deletionEnvelopeArity (n m : Nat) : Nat :=
  n + Fintype.card (DeletionSet n m)

/-- The first family of padded views: singleton coordinates, followed by all
survivor blocks. -/
noncomputable def deletionEnvelopeF (m : Nat) :
    Fin (deletionEnvelopeArity n m) ->
      (Fin n -> alpha) -> (Fin n -> alpha) :=
  Fin.addCases
    (fun i => maskOn ({i} : Finset (Fin n)))
    (fun j => survivorBlockView
      ((Fintype.equivFin (DeletionSet n m)).symm j))

/-- The second padded family cancels the extra full-source entropy contributed
by the singleton-coordinate slots. -/
noncomputable def deletionEnvelopeG (m : Nat) :
    Fin (deletionEnvelopeArity n m) ->
      (Fin n -> alpha) -> (Fin n -> alpha) :=
  Fin.addCases
    (fun _ x => x)
    (fun _ _ => default)

private theorem Hvar_singletonMask_eq_coordinate
    {q : (Fin n -> alpha) -> Real} (hq : IsPMF q) (i : Fin n) :
    Hvar (maskOn ({i} : Finset (Fin n))) q =
      Hvar (fun x : Fin n -> alpha => x i) q := by
  let encode : alpha -> (Fin n -> alpha) :=
    fun a j => if j = i then a else default
  let decode : (Fin n -> alpha) -> alpha := fun x => x i
  have hforward : decode ∘ maskOn ({i} : Finset (Fin n)) =
      fun x : Fin n -> alpha => x i := by
    funext x
    simp [decode, maskOn]
  have hback : encode ∘ (fun x : Fin n -> alpha => x i) =
      maskOn ({i} : Finset (Fin n)) := by
    funext x j
    by_cases hji : j = i
    · subst j
      simp [encode, maskOn]
    · simp [encode, maskOn, hji]
  exact (FiniteInfo.Hvar_eq_of_mutual_recode hq
    (maskOn ({i} : Finset (Fin n)))
    (fun x : Fin n -> alpha => x i) decode encode
    (fun x => congrFun hforward x) (fun x => congrFun hback x)).symm

private theorem Hvar_full_id_eq_H
    {q : (Fin n -> alpha) -> Real} (hq : IsPMF q) :
    Hvar (fun x : Fin n -> alpha => x) q = H q := by
  unfold Hvar
  change H (push (Equiv.refl (Fin n -> alpha)) q) = H q
  exact H_push_equiv (Equiv.refl (Fin n -> alpha)) q hq

private theorem Hvar_default_const_eq_zero
    {q : (Fin n -> alpha) -> Real} (hq : IsPMF q) :
    Hvar (fun _ : Fin n -> alpha => (default : Fin n -> alpha)) q = 0 := by
  have hunit : Hvar (fun _ : Fin n -> alpha => ()) q = 0 := by
    have hsum : ∑ z, q z = 1 := by simpa [mass] using hq.total
    simp [Hvar, H, push, mass, hsum]
  let u : (Fin n -> alpha) -> Unit := fun _ => ()
  let v : Unit -> (Fin n -> alpha) := fun _ => default
  calc
    Hvar (fun _ : Fin n -> alpha => (default : Fin n -> alpha)) q =
        Hvar (fun _ : Fin n -> alpha => ()) q :=
      (FiniteInfo.Hvar_eq_of_mutual_recode hq
        (fun _ : Fin n -> alpha => (default : Fin n -> alpha))
        (fun _ : Fin n -> alpha => ()) u v (fun _ => rfl) (fun _ => rfl)).symm
    _ = 0 := hunit

/-- The arbitrary-deletion payoff is an instance of the already certified
finite-dimensional `nPhi` envelope. -/
theorem nPhi_deletionEnvelope_eq
    {q : (Fin n -> alpha) -> Real} (hq : IsPMF q) :
    nPhi (deletionEnvelopeF (n := n) (alpha := alpha) m)
        (deletionEnvelopeG (n := n) (alpha := alpha) m) q =
      NLatent.deletionPhi (n := n) (alpha := alpha) m q := by
  classical
  unfold nPhi NLatent.deletionPhi deletionEnvelopeF deletionEnvelopeG
    deletionEnvelopeArity
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  change
    ((((n + Fintype.card (DeletionSet n m) : Nat) : Real) + 1) * H q -
        ((∑ i : Fin n, Hvar (maskOn ({i} : Finset (Fin n))) q) +
          ∑ j : Fin (Fintype.card (DeletionSet n m)),
            Hvar (survivorBlockView
              ((Fintype.equivFin (DeletionSet n m)).symm j)) q) -
        ((∑ _i : Fin n, Hvar (fun x : Fin n -> alpha => x) q) +
          ∑ _j : Fin (Fintype.card (DeletionSet n m)),
            Hvar (fun _x : Fin n -> alpha =>
              (default : Fin n -> alpha)) q)) =
      ((Fintype.card (DeletionSet n m) : Real) + 1) * H q -
        ∑ i : Fin n, Hvar (fun x : Fin n -> alpha => x i) q -
        ∑ D : DeletionSet n m, Hvar (survivorBlockView D) q
  simp_rw [Hvar_singletonMask_eq_coordinate hq]
  simp_rw [Hvar_full_id_eq_H hq]
  simp_rw [Hvar_default_const_eq_zero hq]
  have hsurv :
      (∑ j : Fin (Fintype.card (DeletionSet n m)),
          Hvar (survivorBlockView
            ((Fintype.equivFin (DeletionSet n m)).symm j)) q) =
        ∑ D : DeletionSet n m, Hvar (survivorBlockView D) q := by
    apply Fintype.sum_equiv (Fintype.equivFin (DeletionSet n m)).symm
    intro j
    rfl
  rw [hsurv]
  simp
  ring

end DeletionEnvelope

/-- The arbitrary-budget sum optimum is attained by a finite latent of the
same Caratheodory size as the source probability simplex. -/
theorem exists_deletionSumTau_optimal_latent
    {n m : Nat} {alpha : Type} [Fintype alpha] [DecidableEq alpha]
    [Inhabited alpha] {p : (Fin n -> alpha) -> Real} (hp : IsPMF p) :
    ∃ V : NLatent p,
      Fintype.card V.ι <= Fintype.card (Fin n -> alpha) + 2 ∧
      V.deletionSumScore (m := m) = NLatent.deletionSumTau (m := m) p := by
  let ef := deletionEnvelopeF (n := n) (alpha := alpha) m
  let eg := deletionEnvelopeG (n := n) (alpha := alpha) m
  let slice : Set (((Fin n -> alpha) -> Real) × Real) :=
    convexHull Real (nPhiGraph ef eg : Set (((Fin n -> alpha) -> Real) × Real)) ∩
      {x | x.1 = p}
  have hslice_compact : IsCompact slice := by
    apply (isCompact_convexHull_nPhiGraph ef eg hp).inter_right
    exact isClosed_eq continuous_fst continuous_const
  have hbase_graph : (p, nPhi ef eg p) ∈
      (nPhiGraph ef eg : Set (((Fin n -> alpha) -> Real) × Real)) :=
    ⟨p, hp, rfl⟩
  have hslice_nonempty : slice.Nonempty := by
    refine ⟨(p, nPhi ef eg p), ?_, rfl⟩
    exact subset_convexHull Real _ hbase_graph
  obtain ⟨x, hx_slice, hx_max⟩ :=
    hslice_compact.exists_isMaxOn hslice_nonempty continuous_snd.continuousOn
  have hx_eq : (p, x.2) = x := by
    apply Prod.ext
    · exact hx_slice.2.symm
    · rfl
  have hx_hull : (p, x.2) ∈
      convexHull Real (nPhiGraph ef eg :
        Set (((Fin n -> alpha) -> Real) × Real)) := by
    rw [hx_eq]
    exact hx_slice.1
  obtain ⟨V, hVcard, hVpayoff⟩ :=
    exists_bounded_latent_of_mem_convexHull_nPhiGraph ef eg hp hx_hull
  have hW_graph (W : NLatent p) :
      (p, ∑ v, W.prior v * nPhi ef eg (W.comp v)) ∈
        convexHull Real (nPhiGraph ef eg :
          Set (((Fin n -> alpha) -> Real) × Real)) := by
    apply mem_convexHull_of_exists_fintype W.prior
      (fun v => (W.comp v, nPhi ef eg (W.comp v)))
    · exact W.prior_isPMF.nonneg
    · simpa [mass] using W.prior_isPMF.total
    · intro v
      exact ⟨W.comp v, W.comp_isPMF v, rfl⟩
    · apply Prod.ext
      · rw [Prod.fst_sum]
        funext z
        simp only [Finset.sum_apply, Prod.smul_fst, Pi.smul_apply,
          smul_eq_mul]
        exact W.mixture z
      · simp only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul]
  have hpayoff_eq (W : NLatent p) :
      (∑ v, W.prior v * nPhi ef eg (W.comp v)) =
        ∑ v, W.prior v *
          NLatent.deletionPhi (n := n) (alpha := alpha) m (W.comp v) := by
    apply Finset.sum_congr rfl
    intro v _
    congr 1
    exact nPhi_deletionEnvelope_eq (m := m) (W.comp_isPMF v)
  have hVmin : ∀ W : NLatent p,
      V.deletionSumScore (m := m) <= W.deletionSumScore (m := m) := by
    intro W
    have hW_slice :
        (p, ∑ v, W.prior v * nPhi ef eg (W.comp v)) ∈ slice :=
      ⟨hW_graph W, rfl⟩
    have hpayoff_le :
        (∑ v, W.prior v * nPhi ef eg (W.comp v)) <= x.2 :=
      hx_max hW_slice
    rw [V.deletionSumScore_eq_envelope, W.deletionSumScore_eq_envelope]
    rw [← hpayoff_eq V, ← hpayoff_eq W, hVpayoff]
    linarith
  have hVcard' : Fintype.card V.ι <= Fintype.card (Fin n -> alpha) + 2 := by
    simpa [nEnvelopeSize_eq_card_add_two (Ω := Fin n -> alpha)] using hVcard
  refine ⟨V, hVcard', ?_⟩
  letI : Nonempty (NLatent p) := ⟨NLatent.const hp⟩
  have hscore_bdd : BddBelow
      (Set.range fun W : NLatent p => W.deletionSumScore (m := m)) :=
    ⟨V.deletionSumScore (m := m), by
      rintro _ ⟨W, rfl⟩
      exact hVmin W⟩
  apply le_antisymm
  · unfold NLatent.deletionSumTau
    exact le_ciInf hVmin
  · unfold NLatent.deletionSumTau
    exact ciInf_le hscore_bdd V

namespace NLatent

variable {n m : Nat} {alpha : Type} [Fintype alpha] [DecidableEq alpha]
  [Inhabited alpha] {p : (Fin n -> alpha) -> Real}

/-- The fixed part of the deletion envelope is exactly the ordinary total
correlation of the source coordinates. -/
theorem deletionPsi_sub_deletionPhi_eq_nTC (hp : IsPMF p) :
    deletionPsi (n := n) (alpha := alpha) m p -
        deletionPhi (n := n) (alpha := alpha) m p =
      nTC (fun i => coordinateView (alpha := alpha) i) p := by
  unfold deletionPsi deletionPhi nTC
  simp_rw [condH_deleted_survivor hp]
  have hcard :
      (∑ _D : DeletionSet n m, H p) =
        (Fintype.card (DeletionSet n m) : Real) * H p := by simp
  rw [Finset.sum_sub_distrib, hcard]
  change _ = (∑ i : Fin n, Hvar (fun x : Fin n -> alpha => x i) p) - H p
  ring

/-- Fusion identity for the arbitrary-deletion payoff. -/
theorem deletionPhi_fusion (hp : IsPMF p) (V : NLatent p) :
    deletionPhi (n := n) (alpha := alpha) m p -
        ∑ v, V.prior v *
          deletionPhi (n := n) (alpha := alpha) m (V.comp v) =
      ((Fintype.card (DeletionSet n m) : Real) + 1) *
          MI (fun w : V.ι × (Fin n -> alpha) => w.1) (fun w => w.2) V.joint -
        ∑ i, MI (fun w : V.ι × (Fin n -> alpha) => w.1)
          (fun w => w.2 i) V.joint -
        ∑ D : DeletionSet n m,
          MI (fun w : V.ι × (Fin n -> alpha) => w.1)
            (fun w => survivorBlockView D w.2) V.joint := by
  have hX :
      MI (fun w : V.ι × (Fin n -> alpha) => w.1) (fun w => w.2)
          V.joint = H p - ∑ v, V.prior v * H (V.comp v) := by
    have h := V.MI_view (fun x : Fin n -> alpha => x)
    rw [Hvar_id_eq_H hp] at h
    calc
      _ = H p - ∑ v, V.prior v *
          Hvar (fun x : Fin n -> alpha => x) (V.comp v) := h
      _ = H p - ∑ v, V.prior v * H (V.comp v) := by
        congr 1
        exact Finset.sum_congr rfl fun v _ => by
          rw [Hvar_id_eq_H (V.comp_isPMF v)]
  have hi (i : Fin n) := V.MI_view (fun x : Fin n -> alpha => x i)
  have hD (D : DeletionSet n m) := V.MI_view (survivorBlockView D)
  rw [hX]
  simp_rw [hi, hD]
  unfold deletionPhi
  have hswapCoord :
      (∑ i : Fin n, ∑ v : V.ι,
          V.prior v * Hvar (fun x : Fin n -> alpha => x i) (V.comp v)) =
        ∑ v : V.ι, ∑ i : Fin n,
          V.prior v * Hvar (fun x : Fin n -> alpha => x i) (V.comp v) :=
    Finset.sum_comm
  have hswapDel :
      (∑ D : DeletionSet n m, ∑ v : V.ι,
          V.prior v * Hvar (survivorBlockView D) (V.comp v)) =
        ∑ v : V.ι, ∑ D : DeletionSet n m,
          V.prior v * Hvar (survivorBlockView D) (V.comp v) :=
    Finset.sum_comm
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    hswapCoord, hswapDel]
  simp only [mul_sub, Finset.mul_sum]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hscale :
      (∑ v : V.ι, V.prior v *
          (((Fintype.card (DeletionSet n m) : Real) + 1) * H (V.comp v))) =
        ∑ v : V.ι, ((Fintype.card (DeletionSet n m) : Real) + 1) *
          (V.prior v * H (V.comp v)) := by
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hscale]
  ring

/-- Information-form identity for the arbitrary-deletion sum score. -/
theorem deletionSumScore_eq_info (V : NLatent p) :
    V.deletionSumScore (m := m) =
      nTC (fun i => coordinateView (alpha := alpha) i) p +
        (((Fintype.card (DeletionSet n m) : Real) + 1) *
            MI (fun w : V.ι × (Fin n -> alpha) => w.1)
              (fun w => w.2) V.joint -
          ∑ i, MI (fun w : V.ι × (Fin n -> alpha) => w.1)
            (fun w => w.2 i) V.joint -
          ∑ D : DeletionSet n m,
            MI (fun w : V.ι × (Fin n -> alpha) => w.1)
              (fun w => survivorBlockView D w.2) V.joint) := by
  rw [V.deletionSumScore_eq_envelope]
  have hfixed := deletionPsi_sub_deletionPhi_eq_nTC (m := m) V.base_isPMF
  have hfusion := deletionPhi_fusion (m := m) V.base_isPMF V
  linarith

/-- The total coordinate/survivor information exposed by the second
posterior replica after the first replica is known. -/
noncomputable def replicaDeletionViewInformation (V : NLatent p) : Real :=
  (∑ i : Fin n,
      condMI (fun u : (V.ι × V.ι) × (Fin n -> alpha) => u.1.2)
        (fun u => u.2 i) (fun u => u.1.1) V.replicaLaw) +
    ∑ D : DeletionSet n m,
      condMI (fun u : (V.ι × V.ι) × (Fin n -> alpha) => u.1.2)
        (fun u => survivorBlockView D u.2) (fun u => u.1.1) V.replicaLaw

/-- Exact arbitrary-deletion score increment when a posterior replica is
adjoined to the latent label. -/
theorem replicaRefinement_deletionSumScore_sub (V : NLatent p) :
    V.replicaRefinement.deletionSumScore (m := m) -
        V.deletionSumScore (m := m) =
      ((Fintype.card (DeletionSet n m) : Real) + 1) * V.replicaDefect -
        V.replicaDeletionViewInformation (m := m) := by
  let R := V.replicaLaw
  let A : (V.ι × V.ι) × (Fin n -> alpha) -> V.ι := fun u => u.1.1
  let B : (V.ι × V.ι) × (Fin n -> alpha) -> V.ι := fun u => u.1.2
  let X : (V.ι × V.ι) × (Fin n -> alpha) -> (Fin n -> alpha) :=
    fun u => u.2
  have hMI_first (h : (Fin n -> alpha) -> (Fin n -> alpha)) :
      MI A (fun u => h (X u)) R =
        MI (fun w : V.ι × (Fin n -> alpha) => w.1)
          (fun w => h w.2) V.joint := by
    apply FiniteInfo.MI_eq_of_pair_push_eq R V.joint
    exact V.push_replica_first_lift
      (fun w : V.ι × (Fin n -> alpha) => (w.1, h w.2))
  have hMI_first_coord (i : Fin n) :
      MI A (fun u => X u i) R =
        MI (fun w : V.ι × (Fin n -> alpha) => w.1)
          (fun w => w.2 i) V.joint := by
    apply FiniteInfo.MI_eq_of_pair_push_eq R V.joint
    exact V.push_replica_first_lift
      (fun w : V.ι × (Fin n -> alpha) => (w.1, w.2 i))
  have hMI_first_surv (D : DeletionSet n m) :
      MI A (fun u => survivorBlockView D (X u)) R =
        MI (fun w : V.ι × (Fin n -> alpha) => w.1)
          (fun w => survivorBlockView D w.2) V.joint :=
    hMI_first (survivorBlockView D)
  have hpairX : MI (fun u => (A u, B u)) X R =
      MI A X R + condMI B X A R :=
    MI_pair_left V.replicaLaw_isPMF A B X
  have hpairCoord (i : Fin n) :
      MI (fun u => (A u, B u)) (fun u => X u i) R =
        MI A (fun u => X u i) R + condMI B (fun u => X u i) A R :=
    MI_pair_left V.replicaLaw_isPMF A B (fun u => X u i)
  have hpairSurv (D : DeletionSet n m) :
      MI (fun u => (A u, B u)) (fun u => survivorBlockView D (X u)) R =
        MI A (fun u => survivorBlockView D (X u)) R +
          condMI B (fun u => survivorBlockView D (X u)) A R :=
    MI_pair_left V.replicaLaw_isPMF A B
      (fun u => survivorBlockView D (X u))
  have hWscore : V.replicaRefinement.deletionSumScore (m := m) =
      nTC (fun i => coordinateView (alpha := alpha) i) p +
        (((Fintype.card (DeletionSet n m) : Real) + 1) *
            MI (fun u : (V.ι × V.ι) × (Fin n -> alpha) => (u.1.1, u.1.2))
              (fun u => u.2) V.replicaLaw -
          ∑ i, MI (fun u : (V.ι × V.ι) × (Fin n -> alpha) =>
              (u.1.1, u.1.2)) (fun u => u.2 i) V.replicaLaw -
          ∑ D : DeletionSet n m,
            MI (fun u : (V.ι × V.ι) × (Fin n -> alpha) =>
                (u.1.1, u.1.2))
              (fun u => survivorBlockView D u.2) V.replicaLaw) := by
    rw [V.replicaRefinement.deletionSumScore_eq_info]
    change
      nTC (fun i => coordinateView (alpha := alpha) i) p +
          (((Fintype.card (DeletionSet n m) : Real) + 1) *
              MI (fun u : (V.ι × V.ι) × (Fin n -> alpha) =>
                  (u.1.1, u.1.2)) (fun u => u.2)
                V.replicaRefinement.joint -
            ∑ i, MI (fun u : (V.ι × V.ι) × (Fin n -> alpha) =>
                (u.1.1, u.1.2)) (fun u => u.2 i)
              V.replicaRefinement.joint -
            ∑ D : DeletionSet n m,
              MI (fun u : (V.ι × V.ι) × (Fin n -> alpha) =>
                  (u.1.1, u.1.2))
                (fun u => survivorBlockView D u.2)
                V.replicaRefinement.joint) = _
    rw [V.replicaRefinement_joint_eq]
  rw [hWscore, V.deletionSumScore_eq_info]
  dsimp only [R, A, B, X] at hMI_first hMI_first_coord hMI_first_surv hpairX hpairCoord hpairSurv ⊢
  rw [hpairX]
  simp_rw [hpairCoord, hpairSurv]
  rw [hMI_first (fun x => x)]
  simp_rw [hMI_first_coord]
  simp_rw [hMI_first_surv]
  unfold replicaDefect replicaDeletionViewInformation
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- Optimality constrains the replica's visible information. -/
theorem replicaDeletionViewInformation_le_of_optimal [Nonempty alpha]
    (V : NLatent p)
    (hoptimal : V.deletionSumScore (m := m) = deletionSumTau (m := m) p) :
    V.replicaDeletionViewInformation (m := m) <=
      ((Fintype.card (DeletionSet n m) : Real) + 1) * V.replicaDefect := by
  have hbdd : BddBelow
      (Set.range fun W : NLatent p => W.deletionSumScore (m := m)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨W, rfl⟩
    exact W.deletionSumScore_nonneg
  have hmin : V.deletionSumScore (m := m) <=
      V.replicaRefinement.deletionSumScore (m := m) := by
    rw [hoptimal]
    unfold deletionSumTau
    exact ciInf_le hbdd V.replicaRefinement
  have hdiff := V.replicaRefinement_deletionSumScore_sub (m := m)
  linarith

/-- The part of the full replica defect left after exposing one coordinate. -/
noncomputable def replicaCoordinateRemainder (V : NLatent p) : Real :=
  ∑ i : Fin n,
    condMI (fun u : (V.ι × V.ι) × (Fin n -> alpha) => u.1.2)
      (fun u => maskDelete i u.2) (fun u => (u.1.1, u.2 i)) V.replicaLaw

/-- The part of the full replica defect left after exposing the survivor
block for a deletion set. -/
noncomputable def replicaDeletionRemainder (V : NLatent p) : Real :=
  ∑ D : DeletionSet n m,
    condMI (fun u : (V.ι × V.ι) × (Fin n -> alpha) => u.1.2)
      (fun u => deletedBlockView D u.2)
      (fun u => (u.1.1, survivorBlockView D u.2)) V.replicaLaw

/-- Chain-rule ledger for the two remainder families. -/
theorem replicaRemainders_eq (V : NLatent p) :
    V.replicaCoordinateRemainder + V.replicaDeletionRemainder (m := m) =
      ((n : Real) + Fintype.card (DeletionSet n m)) * V.replicaDefect -
        V.replicaDeletionViewInformation (m := m) := by
  let R := V.replicaLaw
  let A : (V.ι × V.ι) × (Fin n -> alpha) -> V.ι := fun u => u.1.1
  let B : (V.ι × V.ι) × (Fin n -> alpha) -> V.ι := fun u => u.1.2
  let X : (V.ι × V.ι) × (Fin n -> alpha) -> (Fin n -> alpha) :=
    fun u => u.2
  have hcoord (i : Fin n) :
      V.replicaDefect =
        condMI B (fun u => X u i) A R +
          condMI B (fun u => maskDelete i (X u))
            (fun u => (A u, X u i)) R := by
    have hpair := FiniteInfo.condMI_pair_right V.replicaLaw_isPMF B
      (fun u => X u i) (fun u => maskDelete i (X u)) A
    have hrecode := FiniteInfo.condMI_comp_right_eq_of_injective
      V.replicaLaw_isPMF B X A
      (fun x : Fin n -> alpha => (x i, maskDelete i x))
      (coordinate_pair_injective (alpha := alpha) i)
    dsimp only [R, A, B, X, replicaDefect] at hpair hrecode ⊢
    rw [← hrecode]
    exact hpair
  have hdel (D : DeletionSet n m) :
      V.replicaDefect =
        condMI B (fun u => survivorBlockView D (X u)) A R +
          condMI B (fun u => deletedBlockView D (X u))
            (fun u => (A u, survivorBlockView D (X u))) R := by
    have hpair := FiniteInfo.condMI_pair_right V.replicaLaw_isPMF B
      (fun u => survivorBlockView D (X u))
      (fun u => deletedBlockView D (X u)) A
    have hinj : Function.Injective (fun x : Fin n -> alpha =>
        (survivorBlockView D x, deletedBlockView D x)) := by
      intro x y hxy
      exact deleted_survivor_injective D
        (Prod.ext (congrArg Prod.snd hxy) (congrArg Prod.fst hxy))
    have hrecode := FiniteInfo.condMI_comp_right_eq_of_injective
      V.replicaLaw_isPMF B X A
      (fun x : Fin n -> alpha =>
        (survivorBlockView D x, deletedBlockView D x)) hinj
    dsimp only [R, A, B, X, replicaDefect] at hpair hrecode ⊢
    rw [← hrecode]
    exact hpair
  unfold replicaCoordinateRemainder replicaDeletionRemainder
    replicaDeletionViewInformation
  have hcoordSum :
      (∑ i : Fin n,
          condMI B (fun u => maskDelete i (X u))
            (fun u => (A u, X u i)) R) =
        (n : Real) * V.replicaDefect -
          ∑ i : Fin n, condMI B (fun u => X u i) A R := by
    calc
      _ = ∑ i : Fin n,
          (V.replicaDefect - condMI B (fun u => X u i) A R) := by
        apply Finset.sum_congr rfl
        intro i _
        linarith [hcoord i]
      _ = (∑ _i : Fin n, V.replicaDefect) -
          ∑ i : Fin n, condMI B (fun u => X u i) A R :=
        by rw [Finset.sum_sub_distrib]
      _ = _ := by simp
  have hdelSum :
      (∑ D : DeletionSet n m,
          condMI B (fun u => deletedBlockView D (X u))
            (fun u => (A u, survivorBlockView D (X u))) R) =
        (Fintype.card (DeletionSet n m) : Real) * V.replicaDefect -
          ∑ D : DeletionSet n m,
            condMI B (fun u => survivorBlockView D (X u)) A R := by
    calc
      _ = ∑ D : DeletionSet n m,
          (V.replicaDefect -
            condMI B (fun u => survivorBlockView D (X u)) A R) := by
        apply Finset.sum_congr rfl
        intro D _
        linarith [hdel D]
      _ = (∑ _D : DeletionSet n m, V.replicaDefect) -
          ∑ D : DeletionSet n m,
            condMI B (fun u => survivorBlockView D (X u)) A R :=
        by rw [Finset.sum_sub_distrib]
      _ = _ := by simp
  dsimp only [R, A, B, X] at hcoordSum hdelSum ⊢
  rw [hcoordSum, hdelSum]
  ring

/-- Optimality leaves at least `(n-1)` copies of the replica defect in the
two remainder families. -/
theorem replicaDefect_mul_le_remainders_of_optimal [Nonempty alpha]
    (V : NLatent p)
    (hoptimal : V.deletionSumScore (m := m) = deletionSumTau (m := m) p) :
    ((n : Real) - 1) * V.replicaDefect <=
      V.replicaCoordinateRemainder + V.replicaDeletionRemainder (m := m) := by
  have hvisible := V.replicaDeletionViewInformation_le_of_optimal hoptimal
  have hledger := V.replicaRemainders_eq (m := m)
  linarith

/-- The singleton remainder is contained in the certified coordinate-cross
quantity. -/
theorem replicaCoordinateRemainder_le_coordinateCross (V : NLatent p) :
    V.replicaCoordinateRemainder <=
      ReplicaCoordinate.coordinateCross V.replicaLaw (fun u => u.2)
        (fun u => u.1.1) (fun u => u.1.2) := by
  unfold replicaCoordinateRemainder ReplicaCoordinate.coordinateCross
  apply Finset.sum_le_sum
  intro i _
  have hswap := FiniteInfo.condMI_comp_equiv_eq_of_invariant V.replicaLaw
    V.replicaSwap V.replicaLaw_swap_equiv
    (fun u : (V.ι × V.ι) × (Fin n -> alpha) => u.1.1)
    (fun u => maskDelete i u.2) (fun u => (u.1.2, u.2 i))
  have hnonneg : 0 <=
      condMI (fun u : (V.ι × V.ι) × (Fin n -> alpha) => u.1.1)
        (fun u => u.2 i) (fun u => (u.1.2, maskDelete i u.2))
        V.replicaLaw :=
    condMI_nonneg V.replicaLaw_isPMF _ _ _
  have hswap' :
      condMI (fun u : (V.ι × V.ι) × (Fin n -> alpha) => u.1.2)
          (fun u => maskDelete i u.2) (fun u => (u.1.1, u.2 i))
          V.replicaLaw =
        condMI (fun u => u.1.1) (fun u => maskDelete i u.2)
          (fun u => (u.1.2, u.2 i)) V.replicaLaw := by
    simpa [NLatent.replicaSwap, Function.comp_def] using hswap
  rw [hswap']
  linarith

/-- Conditioning additionally on the other posterior replica cannot increase
the deleted-block information, because the replicas are independent given the
full source. -/
private theorem replica_deleted_given_first_le (V : NLatent p)
    (D : DeletionSet n m) :
    condMI (fun u : (V.ι × V.ι) × (Fin n -> alpha) => u.1.2)
        (fun u => deletedBlockView D u.2)
        (fun u => (u.1.1, survivorBlockView D u.2)) V.replicaLaw <=
      condMI (fun u => u.1.2) (fun u => deletedBlockView D u.2)
        (fun u => survivorBlockView D u.2) V.replicaLaw := by
  let R := V.replicaLaw
  let A : (V.ι × V.ι) × (Fin n -> alpha) -> V.ι := fun u => u.1.1
  let B : (V.ι × V.ι) × (Fin n -> alpha) -> V.ι := fun u => u.1.2
  let S : (V.ι × V.ι) × (Fin n -> alpha) -> (Fin n -> alpha) :=
    fun u => survivorBlockView D u.2
  let E : (V.ι × V.ι) × (Fin n -> alpha) -> (Fin n -> alpha) :=
    fun u => deletedBlockView D u.2
  have hpairAE := FiniteInfo.condMI_pair_right V.replicaLaw_isPMF B A E S
  have hpairEA := FiniteInfo.condMI_pair_right V.replicaLaw_isPMF B E A S
  have hpairSwap := FiniteInfo.condMI_comp_right_eq_of_injective
    V.replicaLaw_isPMF B (fun u => (A u, E u)) S
    (Equiv.prodComm V.ι (Fin n -> alpha))
    (Equiv.prodComm V.ι (Fin n -> alpha)).injective
  have hinj : Function.Injective (fun x : Fin n -> alpha =>
      (survivorBlockView D x, deletedBlockView D x)) := by
    intro x y hxy
    exact deleted_survivor_injective D
      (Prod.ext (congrArg Prod.snd hxy) (congrArg Prod.fst hxy))
  have hrecode := FiniteInfo.condMI_comp_cond_eq_of_injective
    V.replicaLaw_isPMF B A (fun u => u.2)
    (fun x : Fin n -> alpha =>
      (survivorBlockView D x, deletedBlockView D x)) hinj
  have hmarkovBA : condMI B A (fun u => u.2) R = 0 := by
    have hcomm := FiniteInfo.condMI_comm V.replicaLaw_isPMF B A
      (fun u => u.2)
    dsimp only [R, A, B] at hcomm
    rw [hcomm, V.replica_markov]
  have hBA_S : 0 <= condMI B A S R :=
    condMI_nonneg V.replicaLaw_isPMF B A S
  have hcondSwap := FiniteInfo.condMI_equiv_cond V.replicaLaw_isPMF B E
    (fun u => (S u, A u)) (Equiv.prodComm (Fin n -> alpha) V.ι)
  dsimp only [R, A, B, S, E] at hpairAE hpairEA hpairSwap hrecode hmarkovBA hBA_S hcondSwap ⊢
  rw [hrecode, hmarkovBA] at hpairEA
  rw [← hpairSwap] at hpairAE
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk] at hpairAE hpairEA hcondSwap
  rw [← hcondSwap] at hpairAE
  linarith

/-- The deletion-family remainder is bounded by the stochastic redundancy
part of the original arbitrary-deletion score. -/
theorem replicaDeletionRemainder_le_redundancy (V : NLatent p) :
    V.replicaDeletionRemainder (m := m) <=
      ∑ D : DeletionSet n m,
        condMI (fun w : V.ι × (Fin n -> alpha) => w.1)
          (fun w => deletedBlockView D w.2)
          (fun w => survivorBlockView D w.2) V.joint := by
  unfold replicaDeletionRemainder
  apply Finset.sum_le_sum
  intro D _
  have hle := V.replica_deleted_given_first_le D
  have hswap := FiniteInfo.condMI_comp_equiv_eq_of_invariant V.replicaLaw
    V.replicaSwap V.replicaLaw_swap_equiv
    (fun u : (V.ι × V.ι) × (Fin n -> alpha) => u.1.1)
    (fun u => deletedBlockView D u.2)
    (fun u => survivorBlockView D u.2)
  have hfirst := V.replica_condMI_first
    (deletedBlockView D) (survivorBlockView D)
  have hswap' :
      condMI (fun u : (V.ι × V.ι) × (Fin n -> alpha) => u.1.2)
          (fun u => deletedBlockView D u.2)
          (fun u => survivorBlockView D u.2) V.replicaLaw =
        condMI (fun u => u.1.1) (fun u => deletedBlockView D u.2)
          (fun u => survivorBlockView D u.2) V.replicaLaw := by
    simpa [NLatent.replicaSwap, Function.comp_def] using hswap
  exact hle.trans_eq (hswap'.trans hfirst)

private theorem condH_comp_condition_eq_of_injective
    {Z F K K' : Type} [Fintype Z] [Fintype F] [Fintype K] [Fintype K']
    [DecidableEq F] [DecidableEq K] [DecidableEq K']
    {r : Z -> Real} (hr : IsPMF r) (f : Z -> F) (h : Z -> K)
    (u : K -> K') (hu : Function.Injective u) :
    condH f (fun z => u (h z)) r = condH f h r := by
  have hZ : Nonempty Z := by
    by_contra hne
    letI : IsEmpty Z := not_nonempty_iff.mp hne
    have htotal := hr.total
    simp [mass] at htotal
  letI : Nonempty K := ⟨h (Classical.choice hZ)⟩
  obtain ⟨v, huv⟩ := hu.hasLeftInverse
  have hh := Hvar_eq_of_leftInverse hr h u v huv
  have hfh := Hvar_eq_of_leftInverse hr (fun z => (f z, h z))
    (fun t => (t.1, u t.2)) (fun t => (t.1, v t.2)) (by
      intro t
      simp [huv t.2])
  change Hvar (fun z => (f z, u (h z))) r =
    Hvar (fun z => (f z, h z)) r at hfh
  change Hvar (fun z => u (h z)) r = Hvar h r at hh
  unfold condH
  rw [hfh, hh]

private theorem condH_le_processed_condition
    {Z F K K' : Type} [Fintype Z] [Fintype F] [Fintype K] [Fintype K']
    [DecidableEq F] [DecidableEq K] [DecidableEq K']
    {r : Z -> Real} (hr : IsPMF r) (f : Z -> F) (h : Z -> K)
    (u : K -> K') :
    condH f h r <= condH f (fun z => u (h z)) r := by
  let enc : K -> K × K' := fun k => (k, u k)
  have henc : Function.Injective enc := fun x y hxy => congrArg Prod.fst hxy
  have heq := condH_comp_condition_eq_of_injective hr f h enc henc
  have hchain := condMI_eq_condH_sub_pair hr f h (fun z => u (h z))
  have hnonneg := condMI_nonneg hr f h (fun z => u (h z))
  change condH f (fun z => enc (h z)) r = condH f h r at heq
  rw [heq] at hchain
  linarith

/-- A one-coordinate deletion redundancy is bounded by any larger deletion
block containing that coordinate. -/
theorem coordinateRedundancy_le_deletion (V : NLatent p)
    (i : Fin n) (D : DeletionSet n m) (hi : i ∈ D.1) :
    condMI (fun w : V.ι × (Fin n -> alpha) => w.1) (fun w => w.2 i)
        (fun w => maskDelete i w.2) V.joint <=
      condMI (fun w => w.1) (fun w => deletedBlockView D w.2)
        (fun w => survivorBlockView D w.2) V.joint := by
  let C : V.ι × (Fin n -> alpha) -> V.ι := fun w => w.1
  let X : V.ι × (Fin n -> alpha) -> (Fin n -> alpha) := fun w => w.2
  let Si : V.ι × (Fin n -> alpha) -> (Fin n -> alpha) :=
    fun w => maskDelete i (X w)
  let SD : V.ι × (Fin n -> alpha) -> (Fin n -> alpha) :=
    fun w => survivorBlockView D (X w)
  let XD : V.ι × (Fin n -> alpha) -> (Fin n -> alpha) :=
    fun w => deletedBlockView D (X w)
  let project : (Fin n -> alpha) -> (Fin n -> alpha) :=
    maskOn (Finset.univ \ D.1)
  have hproject : (fun w => project (Si w)) = SD := by
    funext w j
    by_cases hj : j ∈ Finset.univ \ D.1
    · have hji : j ≠ i := by
        intro hji
        subst j
        exact (Finset.mem_sdiff.mp hj).2 hi
      simp [project, Si, SD, X, survivorBlockView, maskOn, maskDelete,
        hj, hji]
    · simp [project, Si, SD, X, survivorBlockView, maskOn, hj]
  have hcond : condH C Si V.joint <= condH C SD V.joint := by
    have h := condH_le_processed_condition V.joint_isPMF C Si project
    rw [hproject] at h
    exact h
  have hinj_i : Function.Injective (fun x : Fin n -> alpha =>
      (x i, maskDelete i x)) := coordinate_pair_injective (alpha := alpha) i
  have hinj_D : Function.Injective (fun x : Fin n -> alpha =>
      (deletedBlockView D x, survivorBlockView D x)) :=
    deleted_survivor_injective D
  have hfull_i := condH_comp_condition_eq_of_injective V.joint_isPMF C X
    (fun x : Fin n -> alpha => (x i, maskDelete i x)) hinj_i
  have hfull_D := condH_comp_condition_eq_of_injective V.joint_isPMF C X
    (fun x : Fin n -> alpha =>
      (deletedBlockView D x, survivorBlockView D x)) hinj_D
  have hchain_i := condMI_eq_condH_sub_pair V.joint_isPMF C
    (fun w => X w i) Si
  have hchain_D := condMI_eq_condH_sub_pair V.joint_isPMF C XD SD
  dsimp only [C, X, Si, SD, XD] at hcond hfull_i hfull_D hchain_i hchain_D ⊢
  rw [hfull_i] at hchain_i
  rw [hfull_D] at hchain_D
  linarith

/-- The certified singleton-deletion score is at most `n` times the
arbitrary-`m` sum score. -/
theorem coordinateScore_le_mul_deletionSumScore (V : NLatent p)
    (hm1 : 1 <= m) (hmn : m < n) :
    V.score (fun i => coordinateView (alpha := alpha) i)
        (fun i => coordinateDeletionView (alpha := alpha) i) <=
      (n : Real) * V.deletionSumScore (m := m) := by
  have hex (i : Fin n) : ∃ D : DeletionSet n m, i ∈ D.1 := by
    obtain ⟨t, hsub, hcard⟩ := Finset.exists_superset_card_eq
      (s := ({i} : Finset (Fin n))) (n := m) (by simpa using hm1)
      (by simpa using Nat.le_of_lt hmn)
    exact ⟨⟨t, hcard⟩, hsub (by simp)⟩
  choose chooseD hchooseD using hex
  let tc : Real :=
    (∑ i, condH
        (fun w : V.ι × (Fin n -> alpha) => w.2 i) (fun w => w.1) V.joint) -
      condH (fun w : V.ι × (Fin n -> alpha) => w.2) (fun w => w.1)
        V.joint
  let oldRed : Fin n -> Real := fun i =>
    condMI (fun w : V.ι × (Fin n -> alpha) => w.1) (fun w => w.2 i)
      (fun w => maskDelete i w.2) V.joint
  let newRed : DeletionSet n m -> Real := fun D =>
    condMI (fun w : V.ι × (Fin n -> alpha) => w.1)
      (fun w => deletedBlockView D w.2)
      (fun w => survivorBlockView D w.2) V.joint
  have hnew_nonneg (D : DeletionSet n m) : 0 <= newRed D :=
    condMI_nonneg V.joint_isPMF _ _ _
  have hold_each (i : Fin n) : oldRed i <= ∑ D, newRed D := by
    calc
      oldRed i <= newRed (chooseD i) := by
        exact V.coordinateRedundancy_le_deletion i (chooseD i) (hchooseD i)
      _ <= ∑ D, newRed D := by
        exact Finset.single_le_sum (fun D _ => hnew_nonneg D) (Finset.mem_univ _)
  have hold : (∑ i, oldRed i) <= (n : Real) * ∑ D, newRed D := by
    calc
      ∑ i, oldRed i <= ∑ _i : Fin n, ∑ D, newRed D :=
        Finset.sum_le_sum fun i _ => hold_each i
      _ = (n : Real) * ∑ D, newRed D := by simp
  have htc : 0 <= tc := V.deletionConditionalTC_nonneg
  have hnR : (1 : Real) <= (n : Real) := by exact_mod_cast (hm1.trans (Nat.le_of_lt hmn))
  unfold NLatent.score deletionSumScore
  simp only [coordinateView, coordinateDeletionView]
  change tc + ∑ i, oldRed i <= (n : Real) * (tc + ∑ D, newRed D)
  nlinarith

/-- Alphabet-free posterior-replica defect bound for an optimizer of the
arbitrary-deletion sum score. -/
theorem replicaDefect_le_deletionSumScore_of_optimal [Nonempty alpha]
    (V : NLatent p) (hn : 3 <= n) (hm1 : 1 <= m) (hmn : m < n)
    (hoptimal : V.deletionSumScore (m := m) = deletionSumTau (m := m) p) :
    V.replicaDefect <=
      (((n : Real) ^ 2 * ((n : Real) - 2)) + 1) *
        V.deletionSumScore (m := m) := by
  let red : Real :=
    ∑ D : DeletionSet n m,
      condMI (fun w : V.ι × (Fin n -> alpha) => w.1)
        (fun w => deletedBlockView D w.2)
        (fun w => survivorBlockView D w.2) V.joint
  have hrem := V.replicaDefect_mul_le_remainders_of_optimal hoptimal
  have hq1 := V.replicaCoordinateRemainder_le_coordinateCross
  have hqm := V.replicaDeletionRemainder_le_redundancy (m := m)
  have hcross := V.replica_coordinateCross_le_score hn
  have hold := V.coordinateScore_le_mul_deletionSumScore hm1 hmn
  have htc := V.deletionConditionalTC_nonneg
  have hred_le : red <= V.deletionSumScore (m := m) := by
    unfold red deletionSumScore
    linarith
  have hb : 0 <= V.replicaDefect :=
    condMI_nonneg V.replicaLaw_isPMF _ _ _
  have hs : 0 <= V.deletionSumScore (m := m) :=
    V.deletionSumScore_nonneg
  have hnR : (3 : Real) <= (n : Real) := by exact_mod_cast hn
  have hn2 : 0 <= (n : Real) * ((n : Real) - 2) := by
    nlinarith
  have hq1' : V.replicaCoordinateRemainder <=
      ((n : Real) ^ 2 * ((n : Real) - 2)) *
        V.deletionSumScore (m := m) := by
    calc
      _ <= ReplicaCoordinate.coordinateCross V.replicaLaw (fun u => u.2)
          (fun u => u.1.1) (fun u => u.1.2) := hq1
      _ <= (n : Real) * ((n : Real) - 2) *
          V.score (fun i => coordinateView (alpha := alpha) i)
            (fun i => coordinateDeletionView (alpha := alpha) i) := hcross
      _ <= (n : Real) * ((n : Real) - 2) *
          ((n : Real) * V.deletionSumScore (m := m)) :=
        mul_le_mul_of_nonneg_left hold hn2
      _ = _ := by ring
  have hqm' : V.replicaDeletionRemainder (m := m) <=
      V.deletionSumScore (m := m) := hqm.trans hred_le
  have hremainders :
      V.replicaCoordinateRemainder + V.replicaDeletionRemainder (m := m) <=
        ((((n : Real) ^ 2 * ((n : Real) - 2)) + 1) *
          V.deletionSumScore (m := m)) := by
    calc
      _ <= ((n : Real) ^ 2 * ((n : Real) - 2)) *
          V.deletionSumScore (m := m) + V.deletionSumScore (m := m) :=
        add_le_add hq1' hqm'
      _ = _ := by ring
  have hb_le : V.replicaDefect <=
      ((n : Real) - 1) * V.replicaDefect := by nlinarith
  exact hb_le.trans (hrem.trans hremainders)

/-- General hardening ledger for an arbitrary deletion family. -/
theorem ofFunction_deletionSumScore_le_score_add_error
    {delta : Type} [Fintype delta] [DecidableEq delta]
    (V : NLatent p) (hp : IsPMF p) (code : (Fin n -> alpha) -> delta) :
    (NLatent.ofFunction hp code).deletionSumScore (m := m) <=
      V.deletionSumScore (m := m) +
        ((n : Real) + (Fintype.card (DeletionSet n m) : Real) + 1) *
          (condMI (fun w : V.ι × (Fin n -> alpha) => w.1)
              (fun w => w.2) (fun w => code w.2) V.joint +
            condH (fun w : V.ι × (Fin n -> alpha) => code w.2)
              (fun w => w.1) V.joint) := by
  let X : V.ι × (Fin n -> alpha) -> (Fin n -> alpha) := fun w => w.2
  let C : V.ι × (Fin n -> alpha) -> V.ι := fun w => w.1
  let G : V.ι × (Fin n -> alpha) -> delta := fun w => code w.2
  let Xi : Fin n -> V.ι × (Fin n -> alpha) -> alpha := fun i w => w.2 i
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
    have hsum := Finset.sum_le_sum fun i
      (_ : i ∈ (Finset.univ : Finset (Fin n))) => hmono_i i
    have hfull := condMI_eq_condH_sub_pair V.joint_isPMF X G C
    rw [hGX] at hfull
    linarith
  have hTC_forget :
      ((∑ i, condH (Xi i) G V.joint) - condH X G V.joint) <=
        ((∑ i, condH (Xi i) (fun w => (G w, C w)) V.joint) -
          condH X (fun w => (G w, C w)) V.joint) + (n : Real) * iE := by
    have hpair_eq (f : V.ι × (Fin n -> alpha) -> alpha) :
        condH f (fun w => (G w, C w)) V.joint =
          condH f (fun w => (C w, G w)) V.joint :=
      FiniteInfo.condH_equiv_cond V.joint_isPMF f
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
        (Xi i) (fun w => maskDelete i (X w)) G
      have hrecode := FiniteInfo.condMI_comp_right_eq_of_injective
        V.joint_isPMF C X G
        (fun x : Fin n -> alpha => (x i, maskDelete i x))
        (coordinate_pair_injective (alpha := alpha) i)
      have hnonneg := condMI_nonneg V.joint_isPMF C
        (fun w => maskDelete i (X w)) (fun w => (G w, Xi i w))
      dsimp only [X, C, G, Xi, iE] at hpair hrecode hnonneg ⊢
      linarith
    have hsum_data := Finset.sum_le_sum fun i
      (_ : i ∈ (Finset.univ : Finset (Fin n))) => hdata i
    have hsum_diff :
        (∑ i, condH (Xi i) G V.joint) -
            ∑ i, condH (Xi i) (fun w => (G w, C w)) V.joint =
          ∑ i, condMI C (Xi i) G V.joint := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => hdiff_i i
    have hconst : (∑ _i : Fin n, iE) = (n : Real) * iE := by simp
    rw [hconst] at hsum_data
    have hiE : 0 <= iE := condMI_nonneg V.joint_isPMF C X G
    linarith
  have hrecover_D (D : DeletionSet n m) :
      condH G (fun w => survivorBlockView D (X w)) V.joint <=
        condMI C (fun w => deletedBlockView D (X w))
          (fun w => survivorBlockView D (X w)) V.joint + hE := by
    let merge : ((Fin n -> alpha) × (Fin n -> alpha)) -> (Fin n -> alpha) :=
      fun z i => if i ∈ D.1 then z.1 i else z.2 i
    have hzero : condH G
        (fun w => (deletedBlockView D (X w), survivorBlockView D (X w)))
        V.joint = 0 := by
      apply FiniteInfo.condH_function_of_condition_zero V.joint_isPMF G
        (fun w => (deletedBlockView D (X w), survivorBlockView D (X w)))
        (fun z => code (merge z))
      intro w
      congr 1
      funext i
      by_cases hi : i ∈ D.1
      · simp [merge, X, deletedBlockView, maskOn, hi]
      · have hi' : i ∈ Finset.univ \ D.1 := by simp [hi]
        simp [merge, X, survivorBlockView, maskOn, hi, hi']
    have hhard :
        condH G (fun w => survivorBlockView D (X w)) V.joint =
          condMI G (fun w => deletedBlockView D (X w))
            (fun w => survivorBlockView D (X w)) V.joint := by
      have hchain := condMI_eq_condH_sub_pair V.joint_isPMF G
        (fun w => deletedBlockView D (X w))
        (fun w => survivorBlockView D (X w))
      rw [hzero] at hchain
      linarith
    have hmono_pair :
        condMI G (fun w => deletedBlockView D (X w))
            (fun w => survivorBlockView D (X w)) V.joint <=
          condMI (fun w => (G w, C w))
            (fun w => deletedBlockView D (X w))
            (fun w => survivorBlockView D (X w)) V.joint := by
      have hchain := FiniteInfo.condMI_pair_left V.joint_isPMF G C
        (fun w => deletedBlockView D (X w))
        (fun w => survivorBlockView D (X w))
      have hnonneg := condMI_nonneg V.joint_isPMF C
        (fun w => deletedBlockView D (X w))
        (fun w => (survivorBlockView D (X w), G w))
      linarith
    have hswap_pair :
        condMI (fun w => (G w, C w))
            (fun w => deletedBlockView D (X w))
            (fun w => survivorBlockView D (X w)) V.joint =
          condMI (fun w => (C w, G w))
            (fun w => deletedBlockView D (X w))
            (fun w => survivorBlockView D (X w)) V.joint := by
      exact FiniteInfo.condMI_comp_left_eq_of_injective V.joint_isPMF
        (fun w => (G w, C w)) (fun w => deletedBlockView D (X w))
        (fun w => survivorBlockView D (X w))
        (Equiv.prodComm delta V.ι) (Equiv.prodComm delta V.ι).injective |>.symm
    have hchain_ref := FiniteInfo.condMI_pair_left V.joint_isPMF C G
      (fun w => deletedBlockView D (X w))
      (fun w => survivorBlockView D (X w))
    have hextra :
        condMI G (fun w => deletedBlockView D (X w))
            (fun w => (survivorBlockView D (X w), C w)) V.joint <= hE := by
      have hleH := FiniteInfo.condMI_le_condH_left V.joint_isPMF G
        (fun w => deletedBlockView D (X w))
        (fun w => (survivorBlockView D (X w), C w))
      have hcond := FiniteInfo.condH_pair_condition_le V.joint_isPMF G
        (fun w => survivorBlockView D (X w)) C
      dsimp only [hE]
      linarith
    rw [hhard]
    rw [hswap_pair] at hmono_pair
    linarith
  have hrecover := Finset.sum_le_sum fun D
    (_ : D ∈ (Finset.univ : Finset (DeletionSet n m))) => hrecover_D D
  have hconstE : (∑ _D : DeletionSet n m, hE) =
      (Fintype.card (DeletionSet n m) : Real) * hE := by simp
  rw [Finset.sum_add_distrib, hconstE] at hrecover
  have hlift {F K : Type} [Fintype F] [Fintype K]
      [DecidableEq F] [DecidableEq K]
      (f : (Fin n -> alpha) -> F) (h : (Fin n -> alpha) -> K) :
      condH (fun w : V.ι × (Fin n -> alpha) => f w.2)
          (fun w => h w.2) V.joint = condH f h p := by
    unfold condH
    rw [V.Hvar_lift (fun x => (f x, h x)), V.Hvar_lift h]
  have hcoordLift (i : Fin n) :
      condH (Xi i) G V.joint =
        condH (coordinateView (alpha := alpha) i) code p := by
    simpa [Xi, G, coordinateView] using
      hlift (coordinateView (alpha := alpha) i) code
  have hfullLift : condH X G V.joint =
      condH (fun x : Fin n -> alpha => x) code p := by
    simpa [X, G] using hlift (fun x : Fin n -> alpha => x) code
  have hsurvLift (D : DeletionSet n m) :
      condH G (fun w => survivorBlockView D (X w)) V.joint =
        condH code (survivorBlockView D) p := by
    have h := hlift code (survivorBlockView D)
    simpa [G, X] using h
  have hhardScore :
      (NLatent.ofFunction hp code).deletionSumScore (m := m) =
        ((∑ i, condH (Xi i) G V.joint) - condH X G V.joint) +
          ∑ D : DeletionSet n m,
            condH G (fun w => survivorBlockView D (X w)) V.joint := by
    rw [NLatent.ofFunction_deletionSumScore_eq_hardScore hp code]
    unfold deletionSumHardScore nCondTC
    simp_rw [hcoordLift, hsurvLift]
    rw [hfullLift]
  have hVScore :
      V.deletionSumScore (m := m) =
        ((∑ i, condH (Xi i) C V.joint) - condH X C V.joint) +
          ∑ D : DeletionSet n m,
            condMI C (fun w => deletedBlockView D (X w))
              (fun w => survivorBlockView D (X w)) V.joint := by
    unfold deletionSumScore
    rfl
  have hiE : 0 <= iE := condMI_nonneg V.joint_isPMF C X G
  have hhE : 0 <= hE := FiniteInfo.condH_nonneg V.joint_isPMF G C
  rw [hhardScore, hVScore]
  change _ <= _ +
    ((n : Real) + (Fintype.card (DeletionSet n m) : Real) + 1) * (iE + hE)
  nlinarith

end NLatent

/-- For every deletion budget, an alphabet-free hard code matches the optimal
stochastic sum score up to `deletionSumConstant`. -/
theorem exists_hardCode_deletionSumScore_le
    {n m : Nat} {alpha : Type} [Fintype alpha] [DecidableEq alpha]
    [Inhabited alpha] [Nonempty alpha] {p : (Fin n -> alpha) -> Real}
    (hp : IsPMF p) (hn : 3 <= n) (hm1 : 1 <= m) (hmn : m < n) :
    ∃ V : NLatent p,
      ∃ code : (Fin n -> alpha) ->
          Fin (Fintype.card ((Fin n -> alpha) × V.ι)),
        deletionSumHardScore (m := m) p code <=
          deletionSumConstant n m * NLatent.deletionSumTau (m := m) p := by
  obtain ⟨V, _hcard, hoptimal⟩ :=
    exists_deletionSumTau_optimal_latent (m := m) hp
  obtain ⟨code, hcode⟩ := V.exists_hardCode_oneSided
  let err :=
    condMI (fun w : V.ι × (Fin n -> alpha) => w.1) (fun w => w.2)
        (fun w => code w.2) V.joint +
      condH (fun w : V.ι × (Fin n -> alpha) => code w.2)
        (fun w => w.1) V.joint
  have hdefect :=
    V.replicaDefect_le_deletionSumScore_of_optimal hn hm1 hmn hoptimal
  have hhard := V.ofFunction_deletionSumScore_le_score_add_error (m := m) hp code
  have herr : err <= 542 * V.replicaDefect := by exact hcode
  have herr' : err <= 542 *
      ((((n : Real) ^ 2 * ((n : Real) - 2)) + 1) *
        V.deletionSumScore (m := m)) := by
    exact herr.trans (mul_le_mul_of_nonneg_left hdefect (by norm_num))
  have hfactor : 0 <=
      (n : Real) + (Fintype.card (DeletionSet n m) : Real) + 1 := by positivity
  have hhard' :
      (NLatent.ofFunction hp code).deletionSumScore (m := m) <=
        deletionSumConstant n m * V.deletionSumScore (m := m) := by
    calc
      _ <= V.deletionSumScore (m := m) +
          ((n : Real) + (Fintype.card (DeletionSet n m) : Real) + 1) * err :=
        hhard
      _ <= V.deletionSumScore (m := m) +
          ((n : Real) + (Fintype.card (DeletionSet n m) : Real) + 1) *
            (542 * ((((n : Real) ^ 2 * ((n : Real) - 2)) + 1) *
              V.deletionSumScore (m := m))) := by
        exact add_le_add_right (mul_le_mul_of_nonneg_left herr' hfactor) _
      _ = deletionSumConstant n m * V.deletionSumScore (m := m) := by
        unfold deletionSumConstant
        ring
  refine ⟨V, code, ?_⟩
  rw [← NLatent.ofFunction_deletionSumScore_eq_hardScore hp code]
  rw [hoptimal] at hhard'
  exact hhard'

section MaxScores

variable {n m : Nat} {alpha : Type} [Fintype alpha] [DecidableEq alpha]
  [Inhabited alpha] [Nonempty alpha] [Nonempty (DeletionSet n m)]
variable {p : (Fin n -> alpha) -> Real}

/-- The user's stochastic natural-latent objective: conditional total
correlation plus the maximum deletion redundancy. -/
noncomputable def NLatent.deletionMaxScore (V : NLatent p) : Real :=
  ((∑ i, condH
      (fun w : V.ι × (Fin n -> alpha) => w.2 i) (fun w => w.1) V.joint) -
    condH (fun w : V.ι × (Fin n -> alpha) => w.2) (fun w => w.1)
      V.joint) +
    (Finset.univ : Finset (DeletionSet n m)).sup' Finset.univ_nonempty
      (fun D => condMI (fun w : V.ι × (Fin n -> alpha) => w.1)
        (fun w => deletedBlockView D w.2)
        (fun w => survivorBlockView D w.2) V.joint)

/-- The requested deterministic natural-latent objective for a hard code. -/
noncomputable def deletionMaxHardScore
    {delta : Type} [Fintype delta] [DecidableEq delta]
    (p : (Fin n -> alpha) -> Real) (code : (Fin n -> alpha) -> delta) : Real :=
  nCondTC (fun i => coordinateView (alpha := alpha) i) p code +
    (Finset.univ : Finset (DeletionSet n m)).sup' Finset.univ_nonempty
      (fun D => condH code (survivorBlockView D) p)

/-- Stochastic optimum for the maximum-redundancy objective. -/
noncomputable def deletionMaxTau (p : (Fin n -> alpha) -> Real) : Real :=
  ⨅ V : NLatent p, V.deletionMaxScore (m := m)

/-- Deterministic optimum.  Every finite hard code can be recoded into this
fixed alphabet without changing its score. -/
noncomputable def deletionMaxT (p : (Fin n -> alpha) -> Real) : Real := by
  classical
  exact if hp : IsPMF p then
    ⨅ code : (Fin n -> alpha) -> Fin (Fintype.card (Fin n -> alpha)),
      deletionMaxHardScore (m := m) p code
  else 0

/-- Final coefficient for the maximum-redundancy theorem. -/
noncomputable def deletionMaxConstant (n m : Nat) : Real :=
  (Fintype.card (DeletionSet n m) : Real) * deletionSumConstant n m

theorem deletionMaxConstant_eq_choose (n m : Nat) :
    deletionMaxConstant n m =
      (Nat.choose n m : Real) *
        (1 + ((n : Real) + (Nat.choose n m : Real) + 1) * 542 *
          (((n : Real) ^ 2 * ((n : Real) - 2)) + 1)) := by
  simp [deletionMaxConstant, deletionSumConstant, card_deletionSet]

namespace NLatent

theorem deletionMaxScore_nonneg (V : NLatent p) :
    0 <= V.deletionMaxScore (m := m) := by
  have htc := V.deletionConditionalTC_nonneg
  have hD (D : DeletionSet n m) : 0 <=
      condMI (fun w : V.ι × (Fin n -> alpha) => w.1)
        (fun w => deletedBlockView D w.2)
        (fun w => survivorBlockView D w.2) V.joint :=
    condMI_nonneg V.joint_isPMF _ _ _
  have hmax : 0 <=
      (Finset.univ : Finset (DeletionSet n m)).sup' Finset.univ_nonempty
          (fun D => condMI (fun w : V.ι × (Fin n -> alpha) => w.1)
          (fun w => deletedBlockView D w.2)
          (fun w => survivorBlockView D w.2) V.joint) := by
    let D : DeletionSet n m := Classical.choice inferInstance
    exact (hD D).trans (Finset.le_sup'
      (f := fun D => condMI
        (fun w : V.ι × (Fin n -> alpha) => w.1)
        (fun w => deletedBlockView D w.2)
        (fun w => survivorBlockView D w.2) V.joint)
      (Finset.mem_univ D))
  exact add_nonneg htc hmax

/-- Sum and max stochastic scores differ by at most the number of deletion
sets. -/
theorem deletionSumScore_le_card_mul_maxScore (V : NLatent p) :
    V.deletionSumScore (m := m) <=
      (Fintype.card (DeletionSet n m) : Real) *
        V.deletionMaxScore (m := m) := by
  let tc : Real :=
    (∑ i, condH
        (fun w : V.ι × (Fin n -> alpha) => w.2 i) (fun w => w.1) V.joint) -
      condH (fun w : V.ι × (Fin n -> alpha) => w.2) (fun w => w.1)
        V.joint
  let r : DeletionSet n m -> Real := fun D =>
    condMI (fun w : V.ι × (Fin n -> alpha) => w.1)
      (fun w => deletedBlockView D w.2)
      (fun w => survivorBlockView D w.2) V.joint
  let rmax : Real :=
    (Finset.univ : Finset (DeletionSet n m)).sup' Finset.univ_nonempty r
  have hterm (D : DeletionSet n m) : r D <= rmax :=
    Finset.le_sup' r (Finset.mem_univ D)
  have hsum := Finset.sum_le_sum fun D
    (_ : D ∈ (Finset.univ : Finset (DeletionSet n m))) => hterm D
  have htc : 0 <= tc := V.deletionConditionalTC_nonneg
  have hcard : (1 : Real) <= (Fintype.card (DeletionSet n m) : Real) := by
    exact_mod_cast Fintype.card_pos
  unfold deletionSumScore deletionMaxScore
  change tc + ∑ D, r D <=
    (Fintype.card (DeletionSet n m) : Real) * (tc + rmax)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  nlinarith

end NLatent

theorem deletionMaxHardScore_le_sumHardScore
    {delta : Type} [Fintype delta] [DecidableEq delta]
    (hp : IsPMF p) (code : (Fin n -> alpha) -> delta) :
    deletionMaxHardScore (m := m) p code <=
      deletionSumHardScore (m := m) p code := by
  let r : DeletionSet n m -> Real := fun D =>
    condH code (survivorBlockView D) p
  have hnonneg (D : DeletionSet n m) : 0 <= r D :=
    FiniteInfo.condH_nonneg hp code (survivorBlockView D)
  have hterm (D : DeletionSet n m) :
      r D <= ∑ E, r E :=
    Finset.single_le_sum (fun E _ => hnonneg E) (Finset.mem_univ D)
  have hmax :
      (Finset.univ : Finset (DeletionSet n m)).sup' Finset.univ_nonempty r <=
        ∑ D, r D :=
    Finset.sup'_le _ _ fun D _ => hterm D
  unfold deletionMaxHardScore deletionSumHardScore
  exact add_le_add_right hmax _

private noncomputable def deletionCodeEncoder
    {Omega delta : Type} [Fintype Omega] [DecidableEq Omega] [Nonempty Omega]
    [Fintype delta] [DecidableEq delta] (code : Omega -> delta) :
    delta -> Fin (Fintype.card Omega) := fun d =>
  if h : ∃ x, code x = d then Fintype.equivFin Omega (Classical.choose h)
  else Fintype.equivFin Omega (Classical.choice inferInstance)

private noncomputable def deletionCodeDecoder
    {Omega delta : Type} [Fintype Omega] [DecidableEq Omega] [Nonempty Omega]
    [Fintype delta] [DecidableEq delta] (code : Omega -> delta) :
    Fin (Fintype.card Omega) -> delta := fun j =>
  code ((Fintype.equivFin Omega).symm j)

private noncomputable def deletionCodeRecode
    {Omega delta : Type} [Fintype Omega] [DecidableEq Omega] [Nonempty Omega]
    [Fintype delta] [DecidableEq delta] (code : Omega -> delta) :
    Omega -> Fin (Fintype.card Omega) := deletionCodeEncoder code ∘ code

private theorem deletionCodeDecoder_encoder
    {Omega delta : Type} [Fintype Omega] [DecidableEq Omega] [Nonempty Omega]
    [Fintype delta] [DecidableEq delta] (code : Omega -> delta) (x : Omega) :
    deletionCodeDecoder code (deletionCodeEncoder code (code x)) = code x := by
  unfold deletionCodeDecoder deletionCodeEncoder
  rw [dif_pos ⟨x, rfl⟩, Equiv.symm_apply_apply]
  exact Classical.choose_spec (show ∃ y, code y = code x from ⟨x, rfl⟩)

private theorem deletionMaxHardScore_recode
    {delta : Type} [Fintype delta] [DecidableEq delta]
    (hp : IsPMF p) (code : (Fin n -> alpha) -> delta) :
    deletionMaxHardScore (m := m) p (deletionCodeRecode code) =
      deletionMaxHardScore (m := m) p code := by
  let enc := deletionCodeEncoder code
  let dec := deletionCodeDecoder code
  let recode := deletionCodeRecode code
  have henc (x : Fin n -> alpha) : enc (code x) = recode x := rfl
  have hdec (x : Fin n -> alpha) : dec (recode x) = code x :=
    deletionCodeDecoder_encoder code x
  have hcond {F : Type} [Fintype F] [DecidableEq F]
      (q : (Fin n -> alpha) -> F) : condH q recode p = condH q code p :=
    FiniteInfo.condH_eq_of_mutual_recode_condition hp q code recode
      enc dec henc hdec
  have hleft {K : Type} [Fintype K] [DecidableEq K]
      (q : (Fin n -> alpha) -> K) : condH recode q p = condH code q p :=
    FiniteInfo.condH_eq_of_mutual_recode_left hp code recode q
      enc dec henc hdec
  unfold deletionMaxHardScore nCondTC
  have hsum :
      (∑ i, condH (coordinateView (alpha := alpha) i) recode p) =
        ∑ i, condH (coordinateView (alpha := alpha) i) code p := by
    exact Finset.sum_congr rfl fun i _ => hcond _
  have hfull : condH (fun x : Fin n -> alpha => x) recode p =
      condH (fun x : Fin n -> alpha => x) code p := hcond _
  have hmax :
      (Finset.univ : Finset (DeletionSet n m)).sup' Finset.univ_nonempty
          (fun D => condH recode (survivorBlockView D) p) =
        (Finset.univ : Finset (DeletionSet n m)).sup' Finset.univ_nonempty
          (fun D => condH code (survivorBlockView D) p) := by
    apply Finset.sup'_congr Finset.univ_nonempty rfl
    intro D _
    exact hleft _
  rw [hsum, hfull, hmax]

theorem deletionMaxT_le_code
    (hp : IsPMF p)
    (code : (Fin n -> alpha) -> Fin (Fintype.card (Fin n -> alpha))) :
    deletionMaxT (m := m) p <= deletionMaxHardScore (m := m) p code := by
  rw [deletionMaxT, dif_pos hp]
  have hb : BddBelow
      (Set.range fun c : (Fin n -> alpha) -> Fin (Fintype.card (Fin n -> alpha)) =>
        deletionMaxHardScore (m := m) p c) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨c, rfl⟩
    have htc : 0 <= nCondTC
        (fun i => coordinateView (alpha := alpha) i) p c := by
      unfold nCondTC
      change 0 <=
        (∑ i : Fin n, condH (fun z : Fin n -> alpha => z i) c p) -
          condH (fun z : Fin n -> alpha => z) c p
      exact ReplicaCoordinate.coordinate_condTC_nonneg hp
        (fun z : Fin n -> alpha => z) c
    have hD (D : DeletionSet n m) : 0 <= condH c (survivorBlockView D) p :=
      FiniteInfo.condH_nonneg hp c (survivorBlockView D)
    have hmax : 0 <=
        (Finset.univ : Finset (DeletionSet n m)).sup' Finset.univ_nonempty
          (fun D => condH c (survivorBlockView D) p) := by
      let D : DeletionSet n m := Classical.choice inferInstance
      exact (hD D).trans (Finset.le_sup'
        (f := fun D => condH c (survivorBlockView D) p)
        (Finset.mem_univ D))
    exact add_nonneg htc hmax
  exact ciInf_le hb code

/-- Fully certified arbitrary-deletion theorem in the requested max/inf
form. -/
theorem deletionMaxT_le_alphabetFree
    (hp : IsPMF p) (hn : 3 <= n) (hm1 : 1 <= m) (hmn : m < n) :
    deletionMaxT (m := m) p <=
      deletionMaxConstant n m * deletionMaxTau (m := m) p := by
  obtain ⟨V, code, hsumHard⟩ :=
    exists_hardCode_deletionSumScore_le (m := m) hp hn hm1 hmn
  let recode := deletionCodeRecode code
  have hT := deletionMaxT_le_code (m := m) hp recode
  have hrecode := deletionMaxHardScore_recode (m := m) hp code
  have hmaxSum := deletionMaxHardScore_le_sumHardScore (m := m) hp code
  have hfixed : deletionMaxT (m := m) p <=
      deletionSumConstant n m * NLatent.deletionSumTau (m := m) p := by
    calc
      _ <= deletionMaxHardScore (m := m) p recode := hT
      _ = deletionMaxHardScore (m := m) p code := hrecode
      _ <= deletionSumHardScore (m := m) p code := hmaxSum
      _ <= _ := hsumHard
  have hbSum : BddBelow
      (Set.range fun W : NLatent p => W.deletionSumScore (m := m)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨W, rfl⟩
    exact W.deletionSumScore_nonneg
  have hn2 : 0 <= (n : Real) - 2 := by
    have hnR : (3 : Real) <= (n : Real) := by exact_mod_cast hn
    linarith
  have hreplicaFactor : 0 <=
      ((n : Real) ^ 2 * ((n : Real) - 2)) + 1 :=
    add_nonneg (mul_nonneg (sq_nonneg _) hn2) (by norm_num)
  have hfront : 0 <=
      (n : Real) + (Fintype.card (DeletionSet n m) : Real) + 1 := by
    positivity
  have hsumFactor : 0 <= deletionSumConstant n m := by
    unfold deletionSumConstant
    exact add_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg hfront (by norm_num)) hreplicaFactor)
  have hfactor : 0 <= deletionMaxConstant n m := by
    unfold deletionMaxConstant
    exact mul_nonneg (by positivity) hsumFactor
  have hall (W : NLatent p) :
      deletionMaxT (m := m) p <=
        deletionMaxConstant n m * W.deletionMaxScore (m := m) := by
    have htau := ciInf_le hbSum W
    have hsumMax := W.deletionSumScore_le_card_mul_maxScore (m := m)
    calc
      _ <= deletionSumConstant n m * NLatent.deletionSumTau (m := m) p := hfixed
      _ <= deletionSumConstant n m * W.deletionSumScore (m := m) := by
        exact mul_le_mul_of_nonneg_left htau hsumFactor
      _ <= deletionSumConstant n m *
          ((Fintype.card (DeletionSet n m) : Real) *
            W.deletionMaxScore (m := m)) := by
        exact mul_le_mul_of_nonneg_left hsumMax hsumFactor
      _ = deletionMaxConstant n m * W.deletionMaxScore (m := m) := by
        unfold deletionMaxConstant
        ring
  letI : Nonempty (NLatent p) := ⟨NLatent.const hp⟩
  unfold deletionMaxTau
  rw [Real.mul_iInf_of_nonneg hfactor]
  exact le_ciInf hall

end MaxScores

/-- User-facing form with no separate nonemptiness typeclass: the budget
hypothesis itself supplies a deletion set. -/
theorem deletionMaxT_le_alphabetFree_for_range
    {n m : Nat} {alpha : Type} [Fintype alpha] [DecidableEq alpha]
    [Inhabited alpha] [Nonempty alpha] {p : (Fin n -> alpha) -> Real}
    (hp : IsPMF p) (hn : 3 <= n) (hm1 : 1 <= m) (hmn : m < n) :
    letI : Nonempty (DeletionSet n m) := deletionSet_nonempty (Nat.le_of_lt hmn)
    deletionMaxT (m := m) p <=
      deletionMaxConstant n m * deletionMaxTau (m := m) p := by
  letI : Nonempty (DeletionSet n m) :=
    deletionSet_nonempty (Nat.le_of_lt hmn)
  exact deletionMaxT_le_alphabetFree hp hn hm1 hmn

end stoch_to_det
