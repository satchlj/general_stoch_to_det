import stoch_to_det.NVarApproxCommon
import stoch_to_det.NVarNonneg

/-!
# Genuine coordinate and deletion views

This module specializes the abstract n-variable interface to a finite product
`Fin n -> alpha`.  A deletion is represented first by replacing the deleted
coordinate by a fixed dummy value.  This has exactly the same information as
the usual tuple of all surviving coordinates, but makes the induction proving
conditional dual-total-correlation nonnegativity transparent.
-/

namespace stoch_to_det

open Finset

variable {Omega alpha delta : Type} [Fintype Omega] [DecidableEq Omega]
  [Fintype alpha] [DecidableEq alpha] [Inhabited alpha]
  [Fintype delta] [DecidableEq delta]

/-- Replace coordinate `i` by a fixed dummy symbol.  On the image of this map,
the result carries exactly the information in the genuine deletion tuple. -/
def maskDelete {n : Nat} (i : Fin n) (x : Fin n -> alpha) : Fin n -> alpha :=
  fun j => if j = i then default else x j

private lemma Hvar_eq_of_recodes {a b : Type}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {m : Omega -> Real} (hm : IsPMF m) (f : Omega -> a) (g : Omega -> b)
    (u : a -> b) (v : b -> a)
    (hfg : u ∘ f = g) (hgf : v ∘ g = f) :
    Hvar f m = Hvar g m := by
  apply le_antisymm
  · have h := Hvar_comp_le hm g v
    rwa [hgf] at h
  · have h := Hvar_comp_le hm f u
    rwa [hfg] at h

private lemma condH_eq_of_condition_recodes
    {a b c : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    {m : Omega -> Real} (hm : IsPMF m) (f : Omega -> a)
    (g : Omega -> b) (h : Omega -> c) (u : b -> c) (v : c -> b)
    (hgh : u ∘ g = h) (hhg : v ∘ h = g) :
    condH f g m = condH f h m := by
  have hc := Hvar_eq_of_recodes hm g h u v hgh hhg
  let up : a × b -> a × c := fun z => (z.1, u z.2)
  let vp : a × c -> a × b := fun z => (z.1, v z.2)
  have hup : up ∘ (fun z => (f z, g z)) = fun z => (f z, h z) := by
    funext z
    exact congrArg (fun k => (f z, k z)) hgh
  have hvp : vp ∘ (fun z => (f z, h z)) = fun z => (f z, g z) := by
    funext z
    exact congrArg (fun k => (f z, k z)) hhg
  have hj := Hvar_eq_of_recodes hm
    (fun z => (f z, g z)) (fun z => (f z, h z)) up vp hup hvp
  unfold condH
  rw [hj, hc]

private lemma condH_pair_condition_le
    {a b c : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    {m : Omega -> Real} (hm : IsPMF m)
    (f : Omega -> a) (g : Omega -> b) (h : Omega -> c) :
    condH f (fun z => (g z, h z)) m <= condH f h m := by
  have hnonneg := condMI_nonneg hm f g h
  have hswap : Hvar (fun z => (g z, h z)) m =
      Hvar (fun z => (h z, g z)) m := by
    symm
    simpa using Hvar_equiv hm (fun z => (g z, h z)) (Equiv.prodComm b c)
  have hassoc : Hvar (fun z => (f z, g z, h z)) m =
      Hvar (fun z => (f z, (g z, h z))) m := by
    simpa using Hvar_equiv hm (fun z => ((f z, g z), h z))
      (Equiv.prodAssoc a b c)
  unfold condMI at hnonneg
  unfold condH
  rw [hswap, hassoc] at hnonneg
  linarith

private def headView {n : Nat} (x : Omega -> (Fin (n + 1) -> alpha)) :
    Omega -> alpha := fun z => x z 0

private def tailView {n : Nat} (x : Omega -> (Fin (n + 1) -> alpha)) :
    Omega -> (Fin n -> alpha) := fun z i => x z i.succ

private lemma maskDelete_zero_eq_cons_tail {n : Nat}
    (x : Fin (n + 1) -> alpha) :
    maskDelete (0 : Fin (n + 1)) x = Fin.cons default (fun i => x i.succ) := by
  funext j
  cases j using Fin.cases with
  | zero => simp [maskDelete]
  | succ j => simp [maskDelete]

private lemma maskDelete_succ_eq_cons {n : Nat} (i : Fin n)
    (x : Fin (n + 1) -> alpha) :
    maskDelete i.succ x =
      Fin.cons (x 0) (maskDelete i (fun j => x j.succ)) := by
  funext j
  cases j using Fin.cases with
  | zero =>
      rw [maskDelete, if_neg (Ne.symm (Fin.succ_ne_zero i))]
      rfl
  | succ j => simp [maskDelete]

private lemma condH_maskDelete_zero_eq_tail {n : Nat}
    {m : Omega -> Real} (hm : IsPMF m)
    (x : Omega -> (Fin (n + 1) -> alpha)) (c : Omega -> delta) :
    condH (headView x)
        (fun z => (maskDelete (0 : Fin (n + 1)) (x z), c z)) m =
      condH (headView x) (fun z => (tailView x z, c z)) m := by
  let u : (Fin (n + 1) -> alpha) × delta -> (Fin n -> alpha) × delta :=
    fun z => ((fun i => z.1 i.succ), z.2)
  let v : (Fin n -> alpha) × delta -> (Fin (n + 1) -> alpha) × delta :=
    fun z => (Fin.cons default z.1, z.2)
  apply condH_eq_of_condition_recodes hm (headView x) _ _ u v
  · funext z
    rfl
  · funext z
    simp only [Function.comp_apply, v]
    apply Prod.ext
    · exact (maskDelete_zero_eq_cons_tail (x z)).symm
    · rfl

private lemma condH_maskDelete_succ_eq_tail {n : Nat} (i : Fin n)
    {m : Omega -> Real} (hm : IsPMF m)
    (x : Omega -> (Fin (n + 1) -> alpha)) (c : Omega -> delta) :
    condH (fun z => x z i.succ)
        (fun z => (maskDelete i.succ (x z), c z)) m =
      condH (fun z => tailView x z i)
        (fun z => (maskDelete i (tailView x z), (headView x z, c z))) m := by
  let u : (Fin (n + 1) -> alpha) × delta ->
      (Fin n -> alpha) × (alpha × delta) :=
    fun z => ((fun j => z.1 j.succ), (z.1 0, z.2))
  let v : (Fin n -> alpha) × (alpha × delta) ->
      (Fin (n + 1) -> alpha) × delta :=
    fun z => (Fin.cons z.2.1 z.1, z.2.2)
  apply condH_eq_of_condition_recodes hm (fun z => x z i.succ) _ _ u v
  · funext z
    simp only [Function.comp_apply, u, tailView, headView]
    rw [maskDelete_succ_eq_cons]
    rfl
  · funext z
    simp only [Function.comp_apply, v, tailView, headView]
    rw [maskDelete_succ_eq_cons]
    rfl

private lemma condH_full_chain {n : Nat}
    {m : Omega -> Real} (hm : IsPMF m)
    (x : Omega -> (Fin (n + 1) -> alpha)) (c : Omega -> delta) :
    condH x c m =
      condH (headView x) (fun z => (tailView x z, c z)) m +
        condH (tailView x) c m := by
  let u : (Fin (n + 1) -> alpha) × delta ->
      alpha × ((Fin n -> alpha) × delta) :=
    fun z => (z.1 0, ((fun i => z.1 i.succ), z.2))
  let v : alpha × ((Fin n -> alpha) × delta) ->
      (Fin (n + 1) -> alpha) × delta :=
    fun z => (Fin.cons z.1 z.2.1, z.2.2)
  have hforward : u ∘ (fun z => (x z, c z)) =
      fun z => (headView x z, (tailView x z, c z)) := by
    rfl
  have hback : v ∘ (fun z => (headView x z, (tailView x z, c z))) =
      fun z => (x z, c z) := by
    funext z
    apply Prod.ext
    · funext i
      cases i using Fin.cases <;> rfl
    · rfl
  have hjoint := Hvar_eq_of_recodes hm
    (fun z => (x z, c z))
    (fun z => (headView x z, (tailView x z, c z)))
    u v hforward hback
  unfold condH
  rw [hjoint]
  ring

private lemma condH_code_chain
    {a b c : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    {m : Omega -> Real} (hm : IsPMF m)
    (x : Omega -> a) (v : Omega -> b) (code : a -> c) :
    condH (code ∘ x) v m +
        condH x (fun z => (code (x z), v z)) m = condH x v m := by
  let enc : a × b -> a × (c × b) := fun z => (z.1, (code z.1, z.2))
  let dec : a × (c × b) -> a × b := fun z => (z.1, z.2.2)
  have hleft : Function.LeftInverse dec enc := fun _ => rfl
  have hgraph := Hvar_eq_of_leftInverse hm
    (fun z => (x z, v z)) enc dec hleft
  change Hvar (fun z => (x z, (code (x z), v z))) m =
      Hvar (fun z => (x z, v z)) m at hgraph
  unfold condH
  simp only [Function.comp_apply]
  rw [hgraph]
  ring

private lemma condH_pair_chain
    {a b c : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    {m : Omega -> Real} (hm : IsPMF m)
    (x : Omega -> a) (y : Omega -> b) (v : Omega -> c) :
    condH y v m + condH x (fun z => (y z, v z)) m =
      condH (fun z => (x z, y z)) v m := by
  have hassoc :
      Hvar (fun z => ((x z, y z), v z)) m =
        Hvar (fun z => (x z, (y z, v z))) m := by
    simpa using (Hvar_equiv hm (fun z => ((x z, y z), v z))
      (Equiv.prodAssoc a b c)).symm
  unfold condH
  rw [← hassoc]
  ring

namespace NLatent

/-- Conditional entropy given both a base view and the latent is the prior
average of the corresponding component conditional entropies. -/
lemma condH_pair_view_prior
    {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    {p : Omega -> Real} (V : NLatent p)
    (x : Omega -> a) (y : Omega -> b) :
    condH (fun w : V.ι × Omega => x w.2)
        (fun w => (y w.2, w.1)) V.joint =
      ∑ u, V.prior u * condH x y (V.comp u) := by
  have hchain := condH_pair_chain V.joint_isPMF
    (fun w : V.ι × Omega => x w.2) (fun w => y w.2) (fun w => w.1)
  have hpair := V.condH_view_prior (fun z => (x z, y z))
  have hy := V.condH_view_prior y
  calc
    condH (fun w : V.ι × Omega => x w.2)
        (fun w => (y w.2, w.1)) V.joint =
        condH (fun w : V.ι × Omega => (x w.2, y w.2))
            (fun w => w.1) V.joint -
          condH (fun w : V.ι × Omega => y w.2)
            (fun w => w.1) V.joint := by linarith
    _ = (∑ u, V.prior u * Hvar (fun z => (x z, y z)) (V.comp u)) -
          ∑ u, V.prior u * Hvar y (V.comp u) := by rw [hpair, hy]
    _ = ∑ u, V.prior u * condH x y (V.comp u) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro u _
      unfold condH
      ring

end NLatent

/-- Conditional DTC is nonnegative for actual coordinate/deletion views.
The statement is source-generic: `x` need not be injective and the code may
depend on all source information. -/
theorem coordinate_condDTC_nonneg {n : Nat}
    {m : Omega -> Real} (hm : IsPMF m)
    (x : Omega -> (Fin n -> alpha)) (c : Omega -> delta) :
    0 <= condH x c m -
      ∑ i : Fin n, condH (fun z => x z i)
        (fun z => (maskDelete i (x z), c z)) m := by
  induction n generalizing delta with
  | zero =>
      let zeroVec : Fin 0 -> alpha := fun i => Fin.elim0 i
      have hx : x = fun _ => zeroVec := by
        funext z i
        exact Fin.elim0 i
      let enc : delta -> (Fin 0 -> alpha) × delta := fun d => (zeroVec, d)
      let dec : (Fin 0 -> alpha) × delta -> delta := Prod.snd
      have hleft : Function.LeftInverse dec enc := fun _ => rfl
      have hpair := Hvar_eq_of_leftInverse hm c enc dec hleft
      change Hvar (fun z => (zeroVec, c z)) m = Hvar c m at hpair
      rw [hx]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
      unfold condH
      rw [hpair]
      linarith
  | succ n ih =>
      have hchain := condH_full_chain hm x c
      have hhead := condH_maskDelete_zero_eq_tail hm x c
      have htail : forall i : Fin n,
          condH (fun z => x z i.succ)
              (fun z => (maskDelete i.succ (x z), c z)) m =
            condH (fun z => tailView x z i)
              (fun z => (maskDelete i (tailView x z),
                (headView x z, c z))) m :=
        fun i => condH_maskDelete_succ_eq_tail i hm x c
      have hrec := ih (tailView x) (fun z => (headView x z, c z))
      have hmono : condH (tailView x) (fun z => (headView x z, c z)) m <=
          condH (tailView x) c m :=
        condH_pair_condition_le hm (tailView x) (headView x) c
      rw [Fin.sum_univ_succ]
      rw [hchain]
      have hhead' :
          condH (fun z => x z 0)
              (fun z => (maskDelete (0 : Fin (n + 1)) (x z), c z)) m =
            condH (fun z => x z 0) (fun z => (tailView x z, c z)) m := hhead
      rw [hhead']
      simp_rw [htail]
      rw [show headView x = (fun z => x z 0) from rfl]
      dsimp only [headView] at hrec hmono
      ring_nf at ⊢
      linarith

/-- A deterministic label recoverable from every deletion has conditional
entropy at most the conditional dual total correlation of the coordinates.

This is source-generic, so the conditioning variable can in particular be a
stochastic latent coupled to the coordinate vector. -/
theorem coordinate_common_code_condH_le_condDTC {n : Nat}
    {beta : Type} [Fintype beta] [DecidableEq beta]
    {m : Omega -> Real} (hm : IsPMF m)
    (x : Omega -> (Fin n -> alpha)) (v : Omega -> beta)
    (code : (Fin n -> alpha) -> delta)
    (decode : forall i : Fin n, (Fin n -> alpha) -> delta)
    (hrecover : forall (i : Fin n) y, decode i (maskDelete i y) = code y) :
    condH (code ∘ x) v m <=
      condH x v m -
        ∑ i : Fin n, condH (fun z => x z i)
          (fun z => (maskDelete i (x z), v z)) m := by
  have hnonneg := coordinate_condDTC_nonneg hm x
    (fun z => (code (x z), v z))
  have hrecoverH (i : Fin n) :
      condH (fun z => x z i)
          (fun z => (maskDelete i (x z), (code (x z), v z))) m =
        condH (fun z => x z i)
          (fun z => (maskDelete i (x z), v z)) m := by
    let u : (Fin n -> alpha) × beta ->
        (Fin n -> alpha) × (delta × beta) :=
      fun z => (z.1, (decode i z.1, z.2))
    let w : (Fin n -> alpha) × (delta × beta) ->
        (Fin n -> alpha) × beta := fun z => (z.1, z.2.2)
    symm
    apply condH_eq_of_condition_recodes hm (fun z => x z i) _ _ u w
    · funext z
      simp only [Function.comp_apply, u]
      rw [hrecover]
    · rfl
  simp_rw [hrecoverH] at hnonneg
  have hchain := condH_code_chain hm x v code
  linarith

section CoordinateLaw

variable {n : Nat}

/-- The actual coordinate projection. -/
def coordinateView (i : Fin n) : (Fin n -> alpha) -> alpha := fun x => x i

/-- The deletion view, represented by a dummy value in the deleted slot. -/
def coordinateDeletionView (i : Fin n) :
    (Fin n -> alpha) -> (Fin n -> alpha) := maskDelete i

theorem coordinate_pair_injective (i : Fin n) :
    Function.Injective
      (fun x : Fin n -> alpha => (coordinateView i x, coordinateDeletionView i x)) := by
  intro x y hxy
  funext j
  by_cases hji : j = i
  · subst j
    exact congrArg Prod.fst hxy
  · have hdel := congrArg (fun z => z.2 j) hxy
    simpa [coordinateDeletionView, maskDelete, hji] using hdel

theorem coordinate_tuple_injective :
    Function.Injective
      (tupleView (fun i : Fin n => coordinateView (alpha := alpha) i)) := by
  intro x y hxy
  funext i
  exact congrFun hxy i

private lemma Hvar_id_coord_eq_H {p : (Fin n -> alpha) -> Real}
    (hp : IsPMF p) : Hvar (fun x : Fin n -> alpha => x) p = H p := by
  unfold Hvar
  change H (push (Equiv.refl (Fin n -> alpha)) p) = H p
  exact H_push_equiv (Equiv.refl (Fin n -> alpha)) p hp

private lemma Hvar_const_eq_zero {beta : Type} [Fintype beta] [DecidableEq beta]
    {m : Omega -> Real} (hm : IsPMF m) (b : beta) :
    Hvar (fun _ : Omega => b) m = 0 := by
  have hunit : Hvar (fun _ : Omega => ()) m = 0 := by
    have hsum : ∑ z, m z = 1 := by simpa [mass] using hm.total
    simp [Hvar, H, push, mass, hsum]
  let u : beta -> Unit := fun _ => ()
  let v : Unit -> beta := fun _ => b
  have hforward : u ∘ (fun _ : Omega => b) = fun _ => () := rfl
  have hback : v ∘ (fun _ : Omega => ()) = fun _ => b := rfl
  rw [Hvar_eq_of_recodes hm (fun _ : Omega => b) (fun _ => ())
    u v hforward hback, hunit]

private lemma coordinate_condH_eq_sub {p : (Fin n -> alpha) -> Real}
    (hp : IsPMF p) (i : Fin n) :
    condH (coordinateView (alpha := alpha) i)
        (coordinateDeletionView (alpha := alpha) i) p =
      H p - Hvar (coordinateDeletionView (alpha := alpha) i) p := by
  have hinj := coordinate_pair_injective (alpha := alpha) i
  obtain ⟨left, hleft⟩ := hinj.hasLeftInverse
  have hpair := Hvar_eq_of_leftInverse hp
    (fun x : Fin n -> alpha => x)
    (fun x => (coordinateView i x, coordinateDeletionView i x)) left hleft
  change Hvar (fun x : Fin n -> alpha =>
      (coordinateView i x, coordinateDeletionView i x)) p =
        Hvar (fun x : Fin n -> alpha => x) p at hpair
  rw [Hvar_id_coord_eq_H hp] at hpair
  unfold condH
  rw [hpair]

private lemma coordinate_deletion_entropy_le {p : (Fin n -> alpha) -> Real}
    (hp : IsPMF p) (i : Fin n) :
    Hvar (coordinateDeletionView (alpha := alpha) i) p <=
      ∑ j : Fin n, if j = i then 0 else Hvar (coordinateView (alpha := alpha) j) p := by
  have hsub := Hvar_tupleView_le_sum hp
    (fun j : Fin n => fun x : Fin n -> alpha => coordinateDeletionView i x j)
  have htuple : tupleView
      (fun j : Fin n => fun x : Fin n -> alpha => coordinateDeletionView i x j) =
        coordinateDeletionView i := by
    rfl
  rw [htuple] at hsub
  have hcoord (j : Fin n) :
      Hvar (fun x : Fin n -> alpha => coordinateDeletionView i x j) p =
        if j = i then 0 else Hvar (coordinateView (alpha := alpha) j) p := by
    by_cases hji : j = i
    · subst j
      have hfun : (fun x : Fin n -> alpha => coordinateDeletionView i x i) =
          fun _ => default := by
        funext x
        simp [coordinateDeletionView, maskDelete]
      rw [hfun, Hvar_const_eq_zero hp]
      simp
    · have hfun : (fun x : Fin n -> alpha => coordinateDeletionView i x j) =
          coordinateView j := by
        funext x
        simp [coordinateDeletionView, maskDelete, coordinateView, hji]
      rw [hfun, if_neg hji]
  simpa only [hcoord] using hsub

private lemma double_deletion_sum {p : (Fin n -> alpha) -> Real}
    (hn : 1 <= n) :
    (∑ i : Fin n, ∑ j : Fin n,
      if j = i then 0 else Hvar (coordinateView (alpha := alpha) j) p) =
      ((n : Real) - 1) * ∑ j, Hvar (coordinateView (alpha := alpha) j) p := by
  rw [Finset.sum_comm]
  have hinner (j : Fin n) :
      (∑ i : Fin n, if j = i then 0 else Hvar (coordinateView (alpha := alpha) j) p) =
        ((n : Real) - 1) * Hvar (coordinateView (alpha := alpha) j) p := by
    calc
      (∑ i : Fin n, if j = i then 0 else Hvar (coordinateView j) p) =
          ∑ i ∈ (Finset.univ : Finset (Fin n)),
            if j ≠ i then Hvar (coordinateView j) p else 0 := by
              apply Finset.sum_congr rfl
              intro i _
              by_cases h : j = i <;> simp [h]
      _ = ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => j ≠ i),
          Hvar (coordinateView j) p := by
            rw [Finset.sum_filter]
      _ = ∑ i ∈ (Finset.univ : Finset (Fin n)).erase j,
          Hvar (coordinateView j) p := by
            rw [Finset.filter_ne]
      _ = ((n : Real) - 1) * Hvar (coordinateView j) p := by
            simp only [Finset.sum_const, Finset.card_erase_of_mem, Finset.mem_univ,
              Finset.card_univ, Fintype.card_fin]
            rw [nsmul_eq_mul, Nat.cast_sub hn]
            push_cast
            ring
  simp_rw [hinner]
  rw [← Finset.mul_sum]

/-- The second genuine-coordinate DTC inequality:
`DTC(X) <= (n-1) TC(X)`. -/
theorem coordinate_nDTC_le_n_minus_one_mul_nTC
    {p : (Fin n -> alpha) -> Real} (hp : IsPMF p) (hn : 1 <= n) :
    nDTC (fun i => coordinateView (alpha := alpha) i)
        (fun i => coordinateDeletionView (alpha := alpha) i) p <=
      ((n : Real) - 1) *
        nTC (fun i => coordinateView (alpha := alpha) i) p := by
  have hdel :
      (∑ i : Fin n, Hvar (coordinateDeletionView (alpha := alpha) i) p) <=
        ((n : Real) - 1) *
          ∑ j, Hvar (coordinateView (alpha := alpha) j) p := by
    calc
      (∑ i : Fin n, Hvar (coordinateDeletionView i) p) <=
          ∑ i : Fin n, ∑ j : Fin n,
            if j = i then 0 else Hvar (coordinateView j) p :=
        Finset.sum_le_sum fun i _ => coordinate_deletion_entropy_le hp i
      _ = _ := double_deletion_sum hn
  have hcond (i : Fin n) := coordinate_condH_eq_sub hp i
  have hconst : (∑ _i : Fin n, H p) = (n : Real) * H p := by
    simp
  unfold nDTC nTC
  simp_rw [hcond]
  rw [Finset.sum_sub_distrib, hconst]
  linarith

/-- The second coordinate DTC inequality after conditioning on an arbitrary
finite stochastic latent. -/
theorem coordinate_latent_condDTC_le_n_minus_one_mul_condTC
    {p : (Fin n -> alpha) -> Real} (hn : 1 <= n) (V : NLatent p) :
    condH (fun w : V.ι × (Fin n -> alpha) => w.2) (fun w => w.1) V.joint -
        ∑ i : Fin n, condH (fun w => w.2 i)
          (fun w => (coordinateDeletionView i w.2, w.1)) V.joint <=
      ((n : Real) - 1) *
        ((∑ i : Fin n, condH (fun w => w.2 i) (fun w => w.1) V.joint) -
          condH (fun w : V.ι × (Fin n -> alpha) => w.2)
            (fun w => w.1) V.joint) := by
  have hid (u : V.ι) :
      Hvar (fun z : (Fin n -> alpha) => z) (V.comp u) = H (V.comp u) :=
    Hvar_id_coord_eq_H (V.comp_isPMF u)
  have hdel (i : Fin n) :
      condH (fun w : V.ι × (Fin n -> alpha) => w.2 i)
          (fun w => (coordinateDeletionView i w.2, w.1)) V.joint =
        ∑ u, V.prior u * condH (coordinateView (alpha := alpha) i)
          (coordinateDeletionView (alpha := alpha) i) (V.comp u) := by
    simpa [coordinateView] using V.condH_pair_view_prior
      (coordinateView (alpha := alpha) i)
      (coordinateDeletionView (alpha := alpha) i)
  have hsingle (i : Fin n) :
      condH (fun w : V.ι × (Fin n -> alpha) => w.2 i)
          (fun w => w.1) V.joint =
        ∑ u, V.prior u * Hvar (coordinateView (alpha := alpha) i) (V.comp u) := by
    simpa [coordinateView] using
      V.condH_view_prior (coordinateView (alpha := alpha) i)
  have hDTC :
      condH (fun w : V.ι × (Fin n -> alpha) => w.2) (fun w => w.1) V.joint -
          ∑ i : Fin n, condH (fun w => w.2 i)
            (fun w => (coordinateDeletionView i w.2, w.1)) V.joint =
        ∑ u, V.prior u *
          nDTC (fun i => coordinateView (alpha := alpha) i)
            (fun i => coordinateDeletionView (alpha := alpha) i) (V.comp u) := by
    rw [V.condH_view_prior (fun z : (Fin n -> alpha) => z)]
    simp_rw [hid]
    simp_rw [hdel]
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u _
    unfold nDTC
    rw [mul_sub, Finset.mul_sum]
  have hTC :
      (∑ i : Fin n, condH (fun w => w.2 i) (fun w => w.1) V.joint) -
          condH (fun w : V.ι × (Fin n -> alpha) => w.2)
            (fun w => w.1) V.joint =
        ∑ u, V.prior u *
          nTC (fun i => coordinateView (alpha := alpha) i) (V.comp u) := by
    simp_rw [hsingle]
    rw [V.condH_view_prior (fun z : (Fin n -> alpha) => z)]
    simp_rw [hid]
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u _
    unfold nTC
    rw [mul_sub, Finset.mul_sum]
  rw [hDTC, hTC]
  calc
    (∑ u, V.prior u *
        nDTC (fun i => coordinateView (alpha := alpha) i)
          (fun i => coordinateDeletionView (alpha := alpha) i) (V.comp u)) <=
      ∑ u, V.prior u * (((n : Real) - 1) *
        nTC (fun i => coordinateView (alpha := alpha) i) (V.comp u)) := by
          apply Finset.sum_le_sum
          intro u _
          exact mul_le_mul_of_nonneg_left
            (coordinate_nDTC_le_n_minus_one_mul_nTC (V.comp_isPMF u) hn)
            (V.prior_isPMF.nonneg u)
    _ = ((n : Real) - 1) *
        ∑ u, V.prior u *
          nTC (fun i => coordinateView (alpha := alpha) i) (V.comp u) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring

/-- If a hard code is recoverable from every deletion, adjoining it to an
arbitrary latent costs at most a factor `n` in the score.  The left side is
written on the original joint law; it is the conditional-TC part after
revealing `(code X, V)`, plus the unchanged redundancy terms. -/
theorem coordinate_common_refined_score_le_n_mul_score
    {p : (Fin n -> alpha) -> Real} (hn : 1 <= n) (V : NLatent p)
    (code : (Fin n -> alpha) -> delta)
    (decode : forall i : Fin n, (Fin n -> alpha) -> delta)
    (hrecover : forall (i : Fin n) y, decode i (maskDelete i y) = code y) :
    ((∑ i : Fin n, condH (fun w : V.ι × (Fin n -> alpha) => w.2 i)
          (fun w => (code w.2, w.1)) V.joint) -
        condH (fun w : V.ι × (Fin n -> alpha) => w.2)
          (fun w => (code w.2, w.1)) V.joint) +
      ∑ i : Fin n, condMI (fun w : V.ι × (Fin n -> alpha) => w.1)
        (fun w => w.2 i) (fun w => coordinateDeletionView i w.2) V.joint <=
      (n : Real) * V.score
        (fun i => coordinateView (alpha := alpha) i)
        (fun i => coordinateDeletionView (alpha := alpha) i) := by
  have hcommon := coordinate_common_code_condH_le_condDTC
    V.joint_isPMF (fun w : V.ι × (Fin n -> alpha) => w.2) (fun w => w.1)
      code decode hrecover
  change condH (fun w : V.ι × (Fin n -> alpha) => code w.2)
      (fun w => w.1) V.joint <=
    condH (fun w : V.ι × (Fin n -> alpha) => w.2) (fun w => w.1) V.joint -
      ∑ i : Fin n, condH (fun w => w.2 i)
        (fun w => (coordinateDeletionView i w.2, w.1)) V.joint at hcommon
  have hdtc := coordinate_latent_condDTC_le_n_minus_one_mul_condTC
    (alpha := alpha) hn V
  have hcode :
      condH (fun w : V.ι × (Fin n -> alpha) => code w.2)
          (fun w => w.1) V.joint <=
        ((n : Real) - 1) *
          ((∑ i : Fin n, condH (fun w => w.2 i) (fun w => w.1) V.joint) -
            condH (fun w : V.ι × (Fin n -> alpha) => w.2)
              (fun w => w.1) V.joint) := le_trans hcommon hdtc
  have hmono (i : Fin n) :
      condH (fun w : V.ι × (Fin n -> alpha) => w.2 i)
          (fun w => (code w.2, w.1)) V.joint <=
        condH (fun w => w.2 i) (fun w => w.1) V.joint :=
    condH_pair_condition_le V.joint_isPMF (fun w => w.2 i)
      (fun w => code w.2) (fun w => w.1)
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    hmono i
  have hchain := condH_code_chain V.joint_isPMF
    (fun w : V.ι × (Fin n -> alpha) => w.2) (fun w => w.1) code
  change condH (fun w : V.ι × (Fin n -> alpha) => code w.2)
      (fun w => w.1) V.joint +
      condH (fun w => w.2) (fun w => (code w.2, w.1)) V.joint =
    condH (fun w => w.2) (fun w => w.1) V.joint at hchain
  have htc :
      (∑ i : Fin n, condH (fun w : V.ι × (Fin n -> alpha) => w.2 i)
          (fun w => (code w.2, w.1)) V.joint) -
        condH (fun w : V.ι × (Fin n -> alpha) => w.2)
          (fun w => (code w.2, w.1)) V.joint <=
      (n : Real) *
        ((∑ i : Fin n, condH (fun w => w.2 i) (fun w => w.1) V.joint) -
          condH (fun w : V.ι × (Fin n -> alpha) => w.2)
            (fun w => w.1) V.joint) := by
    linarith
  have hred : 0 <= ∑ i : Fin n,
      condMI (fun w : V.ι × (Fin n -> alpha) => w.1)
        (fun w => w.2 i) (fun w => coordinateDeletionView i w.2) V.joint :=
    Finset.sum_nonneg fun i _ => condMI_nonneg V.joint_isPMF
      (fun w => w.1) (fun w => w.2 i)
        (fun w => coordinateDeletionView i w.2)
  have hnreal : (1 : Real) <= (n : Real) := by exact_mod_cast hn
  have hfactor : 0 <= ((n : Real) - 1) := by linarith
  have hextra : 0 <= ((n : Real) - 1) *
      ∑ i : Fin n, condMI (fun w : V.ι × (Fin n -> alpha) => w.1)
        (fun w => w.2 i) (fun w => coordinateDeletionView i w.2) V.joint :=
    mul_nonneg hfactor hred
  unfold NLatent.score
  change _ <= (n : Real) *
    (((∑ i : Fin n, condH (fun w => w.2 i) (fun w => w.1) V.joint) -
      condH (fun w : V.ι × (Fin n -> alpha) => w.2)
        (fun w => w.1) V.joint) +
      ∑ i : Fin n, condMI (fun w => w.1) (fun w => w.2 i)
        (fun w => coordinateDeletionView i w.2) V.joint)
  nlinarith

/-- Conditional DTC nonnegativity in the `NVarApproxCommon` notation. -/
theorem coordinate_nCondDTC_nonneg
    {p : (Fin n -> alpha) -> Real} (hp : IsPMF p)
    (code : (Fin n -> alpha) -> delta) :
    0 <= nCondDTC (fun i => coordinateView (alpha := alpha) i)
      (fun i => coordinateDeletionView (alpha := alpha) i) p code := by
  change 0 <= condH (fun x : Fin n -> alpha => x) code p -
    ∑ i : Fin n, condH (fun x => x i)
      (fun x => (maskDelete i x, code x)) p
  exact coordinate_condDTC_nonneg hp (fun x : Fin n -> alpha => x) code

/-- The approximate-common hard-label theorem with both coordinate entropy
hypotheses discharged. -/
theorem coordinate_hard_score_le
    {p : (Fin n -> alpha) -> Real} (hp : IsPMF p) (hn : 1 <= n)
    (code : (Fin n -> alpha) -> delta) :
    (NLatent.ofFunction hp code).score
        (fun i => coordinateView (alpha := alpha) i)
        (fun i => coordinateDeletionView (alpha := alpha) i) <=
      (n : Real) * nTC (fun i => coordinateView (alpha := alpha) i) p +
        2 * ∑ i, condH code (coordinateDeletionView (alpha := alpha) i) p := by
  apply ofFunction_score_le_n_mul_nTC_add_two_recovery hp
  · exact fun i => coordinate_pair_injective i
  · exact coordinate_nCondDTC_nonneg hp code
  · exact coordinate_nDTC_le_n_minus_one_mul_nTC hp hn

end CoordinateLaw

end stoch_to_det
