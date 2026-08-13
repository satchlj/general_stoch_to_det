import stoch_to_det.NVarReplicaOptimal
import stoch_to_det.NVarCoordinates

/-!
# The coordinate posterior-replica Shannon certificate

The subset-orbit certificate telescopes to two standard Shannon quantities:
the conditional total correlation of every one-coordinate deletion and the
conditional dual total correlation of every deletion after conditioning on
the deleted coordinate.  This formulation avoids all binomial subset
bookkeeping while retaining the exact all-`n` inequality.
-/

namespace stoch_to_det

open Finset

namespace ReplicaCoordinate

variable {Z alpha A B K : Type} [Fintype Z] [DecidableEq Z] [Fintype alpha]
  [Fintype A] [Fintype B] [Fintype K]
  [DecidableEq alpha] [DecidableEq A] [DecidableEq B] [DecidableEq K]
  [Inhabited alpha]

private lemma Hvar_eq_of_recodes
    {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    {m : Z -> Real} (hm : IsPMF m) (f : Z -> a) (g : Z -> b)
    (u : a -> b) (v : b -> a)
    (hfg : u ∘ f = g) (hgf : v ∘ g = f) :
    Hvar f m = Hvar g m := by
  apply le_antisymm
  · have h := Hvar_comp_le hm g v
    rwa [hgf] at h
  · have h := Hvar_comp_le hm f u
    rwa [hfg] at h

private lemma condH_eq_of_condition_recodes
    {a b c : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    {m : Z -> Real} (hm : IsPMF m) (f : Z -> a)
    (g : Z -> b) (h : Z -> c) (u : b -> c) (v : c -> b)
    (hgh : u ∘ g = h) (hhg : v ∘ h = g) :
    condH f g m = condH f h m := by
  have hc := Hvar_eq_of_recodes hm g h u v hgh hhg
  let up : a × b -> a × c := fun z => (z.1, u z.2)
  let vp : a × c -> a × b := fun z => (z.1, v z.2)
  have hup : up ∘ (fun z => (f z, g z)) = fun z => (f z, h z) := by
    funext z
    exact congrArg (fun q => (f z, q z)) hgh
  have hvp : vp ∘ (fun z => (f z, h z)) = fun z => (f z, g z) := by
    funext z
    exact congrArg (fun q => (f z, q z)) hhg
  have hj := Hvar_eq_of_recodes hm
    (fun z => (f z, g z)) (fun z => (f z, h z)) up vp hup hvp
  unfold condH
  rw [hj, hc]

private lemma condH_const_zero
    {a : Type*} [Fintype a] [DecidableEq a]
    {m : Z -> Real} (hm : IsPMF m) (a0 : a) (c : Z -> K) :
    condH (fun _ : Z => a0) c m = 0 := by
  let enc : K -> a × K := fun k => (a0, k)
  have he := Hvar_eq_of_leftInverse hm c enc Prod.snd (fun _ => rfl)
  change Hvar (fun z => (a0, c z)) m = Hvar c m at he
  unfold condH
  rw [he]
  ring

private lemma push_graph_source {n : Nat} {m : Z -> Real}
    (x : Z -> (Fin n -> alpha)) (c : Z -> K) :
    push Prod.snd (push (fun z => (c z, x z)) m) = push x m := by
  simpa [Function.comp_def] using
    push_push (fun z => (c z, x z)) Prod.snd m

private lemma condH_under_graph
    {n : Nat} {delta : Type} [Fintype delta] [DecidableEq delta]
    {m : Z -> Real} (x : Z -> (Fin n -> alpha)) (c : Z -> K)
    (h : (Fin n -> alpha) -> delta) :
    condH (fun w : K × (Fin n -> alpha) => h w.2) (fun w => w.1)
        (push (fun z => (c z, x z)) m) =
      condH (fun z => h (x z)) c m := by
  apply FiniteInfo.condH_eq_of_pair_push_eq
  calc
    push (fun w : K × (Fin n -> alpha) => (h w.2, w.1))
        (push (fun z => (c z, x z)) m) =
      push (fun z => (h (x z), c z)) m := by
        simpa [Function.comp_def] using
          push_push (fun z => (c z, x z)) (fun w => (h w.2, w.1)) m
    _ = _ := rfl

/-- Conditional total correlation is nonnegative for a finite coordinate
vector, with an arbitrary finite conditioning variable. -/
theorem coordinate_condTC_nonneg {n : Nat}
    {m : Z -> Real} (hm : IsPMF m)
    (x : Z -> (Fin n -> alpha)) (c : Z -> K) :
    0 <= (∑ i, condH (fun z => x z i) c m) - condH x c m := by
  let q : (Fin n -> alpha) -> Real := push x m
  let r : K × (Fin n -> alpha) -> Real := push (fun z => (c z, x z)) m
  have hq : IsPMF q := isPMF_push hm
  have hr : IsPMF r := isPMF_push hm
  have hs : push Prod.snd r = q := push_graph_source x c
  let V : NLatent q := NLatent.ofJoint r hr hq hs
  let f : Fin n -> (Fin n -> alpha) -> alpha := fun i y => y i
  have htup : Function.Injective (tupleView f) := by
    intro y y' h
    funext i
    exact congrFun h i
  have htc := NLatent.conditionalTC_nonneg V htup
  rw [NLatent.ofJoint_joint_eq] at htc
  have hi (i : Fin n) :
      condH (fun w : K × (Fin n -> alpha) => w.2 i) (fun w => w.1) r =
        condH (fun z => x z i) c m := by
    simpa [r] using condH_under_graph x c (fun y => y i)
  have hall : condH (fun w : K × (Fin n -> alpha) => w.2)
      (fun w => w.1) r = condH x c m := by
    simpa [r] using condH_under_graph x c (fun y => y)
  change 0 <= (∑ i, condH (fun w : K × (Fin n -> alpha) => w.2 i)
      (fun w => w.1) r) - condH (fun w : K × (Fin n -> alpha) => w.2)
      (fun w => w.1) r at htc
  simp_rw [hi] at htc
  rw [hall] at htc
  exact htc

private lemma double_off_diagonal_sum {n : Nat} (hn : 1 <= n)
    (q : Fin n -> Real) :
    (∑ i : Fin n, ∑ j : Fin n, if j = i then 0 else q j) =
      ((n : Real) - 1) * ∑ j, q j := by
  rw [Finset.sum_comm]
  have hinner (j : Fin n) :
      (∑ i : Fin n, if j = i then 0 else q j) =
        ((n : Real) - 1) * q j := by
    calc
      (∑ i : Fin n, if j = i then 0 else q j) =
          ∑ i ∈ (Finset.univ : Finset (Fin n)),
            if j ≠ i then q j else 0 := by
              apply Finset.sum_congr rfl
              intro i _
              by_cases h : j = i <;> simp [h]
      _ = ∑ i ∈ (Finset.univ : Finset (Fin n)).erase j, q j := by
            rw [← Finset.filter_ne, Finset.sum_filter]
      _ = ((n : Real) - 1) * q j := by
            simp only [Finset.sum_const, Finset.card_erase_of_mem,
              Finset.mem_univ, Finset.card_univ, Fintype.card_fin]
            rw [nsmul_eq_mul, Nat.cast_sub hn]
            push_cast
            ring
  simp_rw [hinner]
  rw [← Finset.mul_sum]

/-- Sum, over all deleted coordinates and both replica labels, of the
conditional total correlation of the surviving coordinates. -/
noncomputable def deletionTC {n : Nat} (m : Z -> Real)
    (x : Z -> (Fin n -> alpha)) (a : Z -> A) (b : Z -> B) : Real :=
  ∑ i, (((∑ j, condH (fun z => maskDelete i (x z) j) a m) -
      condH (fun z => maskDelete i (x z)) a m) +
    ((∑ j, condH (fun z => maskDelete i (x z) j) b m) -
      condH (fun z => maskDelete i (x z)) b m))

theorem deletionTC_nonneg {n : Nat} {m : Z -> Real} (hm : IsPMF m)
    (x : Z -> (Fin n -> alpha)) (a : Z -> A) (b : Z -> B) :
    0 <= deletionTC m x a b := by
  unfold deletionTC
  exact Finset.sum_nonneg fun i _ => add_nonneg
    (coordinate_condTC_nonneg hm (fun z => maskDelete i (x z)) a)
    (coordinate_condTC_nonneg hm (fun z => maskDelete i (x z)) b)

private lemma condH_maskDelete_apply {n : Nat} {m : Z -> Real}
    (hm : IsPMF m) (x : Z -> (Fin n -> alpha)) (c : Z -> K)
    (i j : Fin n) :
    condH (fun z => maskDelete i (x z) j) c m =
      if j = i then 0 else condH (fun z => x z j) c m := by
  by_cases hji : j = i
  · subst j
    have hfun : (fun z => maskDelete i (x z) i) = fun _ : Z => default := by
      funext z
      simp [maskDelete]
    rw [hfun, condH_const_zero hm]
    simp
  · have hfun : (fun z => maskDelete i (x z) j) = fun z => x z j := by
      funext z
      simp [maskDelete, hji]
    rw [hfun, if_neg hji]

private lemma deletionTC_eq_aggregate {n : Nat} (hn : 1 <= n)
    {m : Z -> Real} (hm : IsPMF m)
    (x : Z -> (Fin n -> alpha)) (a : Z -> A) (b : Z -> B) :
    deletionTC m x a b =
      ((n : Real) - 1) *
          ((∑ j, condH (fun z => x z j) a m) +
            ∑ j, condH (fun z => x z j) b m) -
        ((∑ i, condH (fun z => maskDelete i (x z)) a m) +
          ∑ i, condH (fun z => maskDelete i (x z)) b m) := by
  unfold deletionTC
  simp_rw [condH_maskDelete_apply hm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib]
  rw [double_off_diagonal_sum hn, double_off_diagonal_sum hn]
  ring

/-- Sum of conditional DTCs of every deletion, conditioning also on the
deleted coordinate and on both replica labels. -/
noncomputable def deletionDTC {n : Nat} (m : Z -> Real)
    (x : Z -> (Fin n -> alpha)) (a : Z -> A) (b : Z -> B) : Real :=
  ∑ i, (condH (fun z => maskDelete i (x z))
      (fun z => (x z i, (a z, b z))) m -
    ∑ j, condH (fun z => maskDelete i (x z) j)
      (fun z => (maskDelete j (maskDelete i (x z)),
        (x z i, (a z, b z)))) m)

theorem deletionDTC_nonneg {n : Nat} {m : Z -> Real} (hm : IsPMF m)
    (x : Z -> (Fin n -> alpha)) (a : Z -> A) (b : Z -> B) :
    0 <= deletionDTC m x a b := by
  unfold deletionDTC
  exact Finset.sum_nonneg fun i _ =>
    coordinate_condDTC_nonneg hm (fun z => maskDelete i (x z))
      (fun z => (x z i, (a z, b z)))

private lemma condH_double_mask_term {n : Nat} {m : Z -> Real}
    (hm : IsPMF m) (x : Z -> (Fin n -> alpha)) (a : Z -> A) (b : Z -> B)
    (i j : Fin n) :
    condH (fun z => maskDelete i (x z) j)
        (fun z => (maskDelete j (maskDelete i (x z)),
          (x z i, (a z, b z)))) m =
      if j = i then 0 else
        condH (fun z => x z j)
          (fun z => (maskDelete j (x z), (a z, b z))) m := by
  by_cases hji : j = i
  · subst j
    have hfun : (fun z => maskDelete i (x z) i) = fun _ : Z => default := by
      funext z
      simp [maskDelete]
    rw [hfun, condH_const_zero hm]
    simp
  · have htarget : (fun z => maskDelete i (x z) j) = fun z => x z j := by
      funext z
      simp [maskDelete, hji]
    rw [htarget, if_neg hji]
    let u : (Fin n -> alpha) × (alpha × (A × B)) ->
        (Fin n -> alpha) × (A × B) := fun q =>
      ((fun k => if k = i then q.2.1 else q.1 k), q.2.2)
    let v : (Fin n -> alpha) × (A × B) ->
        (Fin n -> alpha) × (alpha × (A × B)) := fun q =>
      (maskDelete i q.1, (q.1 i, q.2))
    apply condH_eq_of_condition_recodes hm (fun z => x z j) _ _ u v
    · funext z
      apply Prod.ext
      · funext k
        by_cases hki : k = i
        · subst k
          simp [u, maskDelete, hji, Ne.symm hji]
        · simp [u, maskDelete, hki]
      · rfl
    · funext z
      apply Prod.ext
      · funext k
        by_cases hki : k = i
        · subst k
          simp [v, maskDelete]
        · simp [v, maskDelete, hki]
      · apply Prod.ext
        · simp [v, maskDelete, hji, Ne.symm hji]
        · rfl

private lemma deletionDTC_eq_aggregate {n : Nat} (hn : 1 <= n)
    {m : Z -> Real} (hm : IsPMF m)
    (x : Z -> (Fin n -> alpha)) (a : Z -> A) (b : Z -> B) :
    deletionDTC m x a b =
      (∑ i, condH (fun z => maskDelete i (x z))
        (fun z => (x z i, (a z, b z))) m) -
      ((n : Real) - 1) *
        ∑ j, condH (fun z => x z j)
          (fun z => (maskDelete j (x z), (a z, b z))) m := by
  unfold deletionDTC
  simp_rw [condH_double_mask_term hm]
  rw [Finset.sum_sub_distrib, double_off_diagonal_sum hn]

private lemma condH_pair_chain
    {P Q C : Type*} [Fintype P] [DecidableEq P]
    [Fintype Q] [DecidableEq Q] [Fintype C] [DecidableEq C]
    {m : Z -> Real} (hm : IsPMF m)
    (p : Z -> P) (q : Z -> Q) (c : Z -> C) :
    condH p c m + condH q (fun z => (p z, c z)) m =
      condH (fun z => (q z, p z)) c m := by
  have ha : Hvar (fun z => ((q z, p z), c z)) m =
      Hvar (fun z => (q z, (p z, c z))) m := by
    simpa using (Hvar_equiv hm (fun z => ((q z, p z), c z))
      (Equiv.prodAssoc Q P C)).symm
  unfold condH
  rw [ha]
  ring

private lemma coordinate_pair_condH_eq_full {n : Nat} {m : Z -> Real}
    (hm : IsPMF m) (x : Z -> (Fin n -> alpha)) (c : Z -> K) (i : Fin n) :
    condH (fun z => (x z i, maskDelete i (x z))) c m = condH x c m := by
  simpa [coordinateView, coordinateDeletionView] using
    FiniteInfo.condH_comp_left_eq_of_injective hm x c
    (fun y => (coordinateView (alpha := alpha) i y,
      coordinateDeletionView (alpha := alpha) i y))
    (coordinate_pair_injective (alpha := alpha) i)

private lemma coordinate_swap_pair_condH_eq_full {n : Nat} {m : Z -> Real}
    (hm : IsPMF m) (x : Z -> (Fin n -> alpha)) (c : Z -> K) (i : Fin n) :
    condH (fun z => (maskDelete i (x z), x z i)) c m = condH x c m := by
  have hinj : Function.Injective
      (fun y : Fin n -> alpha => (coordinateDeletionView i y,
        coordinateView i y)) := by
    intro y y' h
    apply coordinate_pair_injective (alpha := alpha) i
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  simpa [coordinateView, coordinateDeletionView] using
    FiniteInfo.condH_comp_left_eq_of_injective hm x c
    (fun y => (coordinateDeletionView (alpha := alpha) i y,
      coordinateView (alpha := alpha) i y)) hinj

private lemma full_condH_sum_single_delete {n : Nat} {m : Z -> Real}
    (hm : IsPMF m) (x : Z -> (Fin n -> alpha)) (c : Z -> K) :
    (n : Real) * condH x c m =
      (∑ i, condH (fun z => x z i) c m) +
        ∑ i, condH (fun z => maskDelete i (x z))
          (fun z => (x z i, c z)) m := by
  calc
    (n : Real) * condH x c m = ∑ _i : Fin n, condH x c m := by simp
    _ = ∑ i, (condH (fun z => x z i) c m +
        condH (fun z => maskDelete i (x z))
          (fun z => (x z i, c z)) m) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [condH_pair_chain hm, coordinate_swap_pair_condH_eq_full hm]
    _ = _ := Finset.sum_add_distrib

private lemma full_condH_sum_delete_single {n : Nat} {m : Z -> Real}
    (hm : IsPMF m) (x : Z -> (Fin n -> alpha)) (c : Z -> K) :
    (n : Real) * condH x c m =
      (∑ i, condH (fun z => maskDelete i (x z)) c m) +
        ∑ i, condH (fun z => x z i)
          (fun z => (maskDelete i (x z), c z)) m := by
  calc
    (n : Real) * condH x c m = ∑ _i : Fin n, condH x c m := by simp
    _ = ∑ i, (condH (fun z => maskDelete i (x z)) c m +
        condH (fun z => x z i)
          (fun z => (maskDelete i (x z), c z)) m) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [condH_pair_chain hm, coordinate_pair_condH_eq_full hm]
    _ = _ := Finset.sum_add_distrib

private def rotateConditionEquiv (P Q R : Type*) : P × (Q × R) ≃ R × (P × Q) where
  toFun z := (z.2.2, (z.1, z.2.1))
  invFun z := (z.2.1, (z.2.2, z.1))
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

private lemma condMI_label_view_eq_condH_sub
    {L R X Y : Type*} [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R] [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] {m : Z -> Real} (hm : IsPMF m)
    (l : Z -> L) (r : Z -> R) (x : Z -> X) (y : Z -> Y) :
    condMI l y (fun z => (r z, x z)) m =
      condH y (fun z => (x z, r z)) m -
        condH y (fun z => (x z, (l z, r z))) m := by
  have hcomm := FiniteInfo.condMI_comm hm l y (fun z => (r z, x z))
  have hsub := condMI_eq_condH_sub_pair hm y l (fun z => (r z, x z))
  have hpair := FiniteInfo.condH_equiv_cond hm y
    (fun z => (r z, x z)) (Equiv.prodComm R X)
  change condH y (fun z => (x z, r z)) m =
    condH y (fun z => (r z, x z)) m at hpair
  have htriple := FiniteInfo.condH_equiv_cond hm y
    (fun z => (l z, (r z, x z))) (rotateConditionEquiv L R X)
  change condH y (fun z => (x z, (l z, r z))) m =
    condH y (fun z => (l z, (r z, x z))) m at htriple
  linarith

private lemma condH_swap_inner
    {X : Type*} [Fintype X] [DecidableEq X]
    {m : Z -> Real} (hm : IsPMF m)
    (h : Z -> alpha) (x : Z -> X) (a : Z -> A) (b : Z -> B) :
    condH h (fun z => (x z, (b z, a z))) m =
      condH h (fun z => (x z, (a z, b z))) m := by
  let e : X × (B × A) ≃ X × (A × B) :=
    Equiv.prodCongr (Equiv.refl X) (Equiv.prodComm B A)
  have he := FiniteInfo.condH_equiv_cond hm h
    (fun z => (x z, (b z, a z))) e
  change condH h (fun z => (x z, (a z, b z))) m =
    condH h (fun z => (x z, (b z, a z))) m at he
  exact he.symm

/-- Coordinate score of a finite auxiliary label. -/
noncomputable def coordinateScore {n : Nat} (m : Z -> Real)
    (x : Z -> (Fin n -> alpha)) (a : Z -> A) : Real :=
  ((∑ i, condH (fun z => x z i) a m) - condH x a m) +
    ∑ i, condMI a (fun z => x z i) (fun z => maskDelete i (x z)) m

/-- Cross information appearing in the posterior-replica certificate. -/
noncomputable def coordinateCross {n : Nat} (m : Z -> Real)
    (x : Z -> (Fin n -> alpha)) (a : Z -> A) (b : Z -> B) : Real :=
  ∑ i, (condMI a (fun z => maskDelete i (x z))
      (fun z => (b z, x z i)) m +
    condMI a (fun z => x z i)
      (fun z => (b z, maskDelete i (x z))) m)

private lemma coordinateCross_eq_aggregate {n : Nat} {m : Z -> Real}
    (hm : IsPMF m) (x : Z -> (Fin n -> alpha)) (a : Z -> A) (b : Z -> B) :
    coordinateCross m x a b =
      ((∑ i, condH (fun z => maskDelete i (x z))
          (fun z => (x z i, b z)) m) -
        ∑ i, condH (fun z => maskDelete i (x z))
          (fun z => (x z i, (a z, b z))) m) +
      ((∑ i, condH (fun z => x z i)
          (fun z => (maskDelete i (x z), b z)) m) -
        ∑ i, condH (fun z => x z i)
          (fun z => (maskDelete i (x z), (a z, b z))) m) := by
  unfold coordinateCross
  rw [Finset.sum_add_distrib]
  simp_rw [condMI_label_view_eq_condH_sub hm]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]

private lemma coordinateCross_swap_eq_aggregate {n : Nat} {m : Z -> Real}
    (hm : IsPMF m) (x : Z -> (Fin n -> alpha)) (a : Z -> A) (b : Z -> B) :
    coordinateCross m x b a =
      ((∑ i, condH (fun z => maskDelete i (x z))
          (fun z => (x z i, a z)) m) -
        ∑ i, condH (fun z => maskDelete i (x z))
          (fun z => (x z i, (a z, b z))) m) +
      ((∑ i, condH (fun z => x z i)
          (fun z => (maskDelete i (x z), a z)) m) -
        ∑ i, condH (fun z => x z i)
          (fun z => (maskDelete i (x z), (a z, b z))) m) := by
  rw [coordinateCross_eq_aggregate hm]
  simp_rw [condH_swap_inner hm]

private lemma coordinate_interaction {n : Nat} {L R : Type*}
    [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
    {m : Z -> Real} (hm : IsPMF m) (x : Z -> (Fin n -> alpha))
    (l : Z -> L) (r : Z -> R) (i : Fin n) :
    condMI l r (fun z => maskDelete i (x z)) m +
        condMI l (fun z => x z i)
          (fun z => (r z, maskDelete i (x z))) m =
      condMI l (fun z => x z i) (fun z => maskDelete i (x z)) m +
        condMI l r x m := by
  have hBR := FiniteInfo.condMI_pair_right hm l r (fun z => x z i)
    (fun z => maskDelete i (x z))
  have hRB := FiniteInfo.condMI_pair_right hm l (fun z => x z i) r
    (fun z => maskDelete i (x z))
  have hpair := FiniteInfo.condMI_comp_right_eq_of_injective hm l
    (fun z => (r z, x z i)) (fun z => maskDelete i (x z))
    (Equiv.prodComm R alpha) (Equiv.prodComm R alpha).injective
  change condMI l (fun z => (x z i, r z))
      (fun z => maskDelete i (x z)) m =
    condMI l (fun z => (r z, x z i))
      (fun z => maskDelete i (x z)) m at hpair
  have hcondR := FiniteInfo.condMI_equiv_cond hm l (fun z => x z i)
    (fun z => (maskDelete i (x z), r z))
    (Equiv.prodComm (Fin n -> alpha) R)
  change condMI l (fun z => x z i)
      (fun z => (r z, maskDelete i (x z))) m =
    condMI l (fun z => x z i)
      (fun z => (maskDelete i (x z), r z)) m at hcondR
  have hinj : Function.Injective
      (fun y : Fin n -> alpha => (maskDelete i y, y i)) := by
    intro y y' h
    apply coordinate_pair_injective (alpha := alpha) i
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  have hfull := FiniteInfo.condMI_comp_cond_eq_of_injective hm l r x
    (fun y : Fin n -> alpha => (maskDelete i y, y i)) hinj
  linarith

private lemma twice_sum_AB_deletion {n : Nat} {m : Z -> Real}
    (hm : IsPMF m) (x : Z -> (Fin n -> alpha)) (a : Z -> A) (b : Z -> B) :
    2 * (∑ i, condMI a b (fun z => maskDelete i (x z)) m) =
      2 * (n : Real) * condMI a b x m +
      (∑ i, condMI a (fun z => x z i)
        (fun z => maskDelete i (x z)) m) +
      (∑ i, condMI b (fun z => x z i)
        (fun z => maskDelete i (x z)) m) -
      (∑ i, condH (fun z => x z i)
        (fun z => (maskDelete i (x z), a z)) m) -
      (∑ i, condH (fun z => x z i)
        (fun z => (maskDelete i (x z), b z)) m) +
      2 * ∑ i, condH (fun z => x z i)
        (fun z => (maskDelete i (x z), (a z, b z))) m := by
  have hterm (i : Fin n) :
      2 * condMI a b (fun z => maskDelete i (x z)) m =
        2 * condMI a b x m +
        condMI a (fun z => x z i) (fun z => maskDelete i (x z)) m +
        condMI b (fun z => x z i) (fun z => maskDelete i (x z)) m -
        condH (fun z => x z i)
          (fun z => (maskDelete i (x z), a z)) m -
        condH (fun z => x z i)
          (fun z => (maskDelete i (x z), b z)) m +
        2 * condH (fun z => x z i)
          (fun z => (maskDelete i (x z), (a z, b z))) m := by
    have ha := coordinate_interaction hm x a b i
    have hb := coordinate_interaction hm x b a i
    have habdel := FiniteInfo.condMI_comm hm a b
      (fun z => maskDelete i (x z))
    have habfull := FiniteInfo.condMI_comm hm a b x
    have hqa := condMI_label_view_eq_condH_sub hm a b
      (fun z => maskDelete i (x z)) (fun z => x z i)
    have hqb := condMI_label_view_eq_condH_sub hm b a
      (fun z => maskDelete i (x z)) (fun z => x z i)
    have hswap := condH_swap_inner hm (fun z => x z i)
      (fun z => maskDelete i (x z)) a b
    linarith
  calc
    2 * (∑ i, condMI a b (fun z => maskDelete i (x z)) m) =
        ∑ i, 2 * condMI a b (fun z => maskDelete i (x z)) m := by
          rw [Finset.mul_sum]
    _ = ∑ i, (2 * condMI a b x m +
        condMI a (fun z => x z i) (fun z => maskDelete i (x z)) m +
        condMI b (fun z => x z i) (fun z => maskDelete i (x z)) m -
        condH (fun z => x z i)
          (fun z => (maskDelete i (x z), a z)) m -
        condH (fun z => x z i)
          (fun z => (maskDelete i (x z), b z)) m +
        2 * condH (fun z => x z i)
          (fun z => (maskDelete i (x z), (a z, b z))) m) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hterm i
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      ring

/-- Exact all-`n` Shannon identity in its collapsed coordinate form.  Every
term on the right except the final Markov term is a nonnegative conditional
mutual information, deletion TC, or deletion DTC. -/
theorem coordinate_replica_certificate_identity {n : Nat} (hn : 1 <= n)
    {m : Z -> Real} (hm : IsPMF m)
    (x : Z -> (Fin n -> alpha)) (a : Z -> A) (b : Z -> B) :
    (n : Real) * ((n : Real) - 2) *
          (coordinateScore m x a + coordinateScore m x b) -
        (coordinateCross m x a b + coordinateCross m x b a) =
      2 * (n : Real) *
          (∑ i, condMI a b (fun z => maskDelete i (x z)) m) +
        (n : Real) * ((n : Real) - 3) *
          ((∑ i, condMI a (fun z => x z i)
              (fun z => maskDelete i (x z)) m) +
            ∑ i, condMI b (fun z => x z i)
              (fun z => maskDelete i (x z)) m) +
        2 * deletionDTC m x a b +
        ((n : Real) - 1) * deletionTC m x a b -
        2 * (n : Real) ^ 2 * condMI a b x m := by
  have hcrossA := coordinateCross_eq_aggregate hm x a b
  have hcrossB := coordinateCross_swap_eq_aggregate hm x a b
  have htc := deletionTC_eq_aggregate hn hm x a b
  have hdtc := deletionDTC_eq_aggregate hn hm x a b
  have hsingleA := full_condH_sum_single_delete hm x a
  have hsingleB := full_condH_sum_single_delete hm x b
  have hdeleteA := full_condH_sum_delete_single hm x a
  have hdeleteB := full_condH_sum_delete_single hm x b
  have hab := twice_sum_AB_deletion hm x a b
  rw [hcrossA, hcrossB, htc, hdtc]
  unfold coordinateScore
  linear_combination
    (hsingleA + hsingleB) - ((n : Real) - 1) * (hdeleteA + hdeleteB) +
      -(n : Real) * hab

/-- The all-`n` posterior-replica Shannon inequality in coordinate form. -/
theorem coordinateCross_le_mul_coordinateScore {n : Nat} (hn : 3 <= n)
    {m : Z -> Real} (hm : IsPMF m)
    (x : Z -> (Fin n -> alpha)) (a : Z -> A) (b : Z -> B)
    (hmarkov : condMI a b x m = 0)
    (hscore : coordinateScore m x a = coordinateScore m x b)
    (hcross : coordinateCross m x a b = coordinateCross m x b a) :
    coordinateCross m x a b <=
      (n : Real) * ((n : Real) - 2) * coordinateScore m x a := by
  have hn1 : 1 <= n := by omega
  have hnR : (3 : Real) <= (n : Real) := by exact_mod_cast hn
  have hab : 0 <= ∑ i, condMI a b (fun z => maskDelete i (x z)) m :=
    Finset.sum_nonneg fun i _ => condMI_nonneg hm a b
      (fun z => maskDelete i (x z))
  have hreda : 0 <= ∑ i, condMI a (fun z => x z i)
      (fun z => maskDelete i (x z)) m :=
    Finset.sum_nonneg fun i _ => condMI_nonneg hm a (fun z => x z i)
      (fun z => maskDelete i (x z))
  have hredb : 0 <= ∑ i, condMI b (fun z => x z i)
      (fun z => maskDelete i (x z)) m :=
    Finset.sum_nonneg fun i _ => condMI_nonneg hm b (fun z => x z i)
      (fun z => maskDelete i (x z))
  have hdtc := deletionDTC_nonneg hm x a b
  have htc := deletionTC_nonneg hm x a b
  have hid := coordinate_replica_certificate_identity hn1 hm x a b
  rw [hmarkov, mul_zero, sub_zero] at hid
  have hcert : 0 <=
      2 * (n : Real) *
          (∑ i, condMI a b (fun z => maskDelete i (x z)) m) +
        (n : Real) * ((n : Real) - 3) *
          ((∑ i, condMI a (fun z => x z i)
              (fun z => maskDelete i (x z)) m) +
            ∑ i, condMI b (fun z => x z i)
              (fun z => maskDelete i (x z)) m) +
        2 * deletionDTC m x a b +
        ((n : Real) - 1) * deletionTC m x a b := by
    have hn0 : 0 <= (n : Real) := Nat.cast_nonneg n
    have hn3 : 0 <= (n : Real) - 3 := by linarith
    have hn1R : 0 <= (n : Real) - 1 := by linarith
    have hfirst : 0 <= 2 * (n : Real) *
        (∑ i, condMI a b (fun z => maskDelete i (x z)) m) :=
      mul_nonneg (mul_nonneg (by norm_num) hn0) hab
    have hsecond : 0 <= (n : Real) * ((n : Real) - 3) *
        ((∑ i, condMI a (fun z => x z i)
            (fun z => maskDelete i (x z)) m) +
          ∑ i, condMI b (fun z => x z i)
            (fun z => maskDelete i (x z)) m) :=
      mul_nonneg (mul_nonneg hn0 hn3) (add_nonneg hreda hredb)
    have hthird : 0 <= 2 * deletionDTC m x a b :=
      mul_nonneg (by norm_num) hdtc
    have hfourth : 0 <= ((n : Real) - 1) * deletionTC m x a b :=
      mul_nonneg hn1R htc
    exact add_nonneg (add_nonneg (add_nonneg hfirst hsecond) hthird) hfourth
  rw [← hscore, ← hcross] at hid
  nlinarith

end ReplicaCoordinate

end stoch_to_det
