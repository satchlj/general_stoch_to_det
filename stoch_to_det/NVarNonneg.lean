import stoch_to_det.NVar

/-!
# Nonnegativity of the n-variable latent score

The coordinate views are assumed to determine the underlying cell jointly.
This makes the conditional total-correlation part of `NLatent.score`
nonnegative; the conditional mutual-information terms are nonnegative
individually.
-/

namespace stoch_to_det

open Finset

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
variable {p : Ω → ℝ}

section Views

variable {n : ℕ} {κ γ : Fin n → Type}
  [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
  [∀ i, Fintype (γ i)] [∀ i, DecidableEq (γ i)]

/-- The joint tuple of all coordinate views. -/
def tupleView (f : ∀ i, Ω → κ i) : Ω → (∀ i, κ i) :=
  fun z i => f i z

theorem Hvar_tupleView_le_sum
    {α : Type} [Fintype α] [DecidableEq α]
    {m : α → ℝ} (hm : IsPMF m) (f : ∀ i, α → κ i) :
    Hvar (tupleView f) m ≤ ∑ i, Hvar (f i) m := by
  induction n with
  | zero =>
      let e : (∀ i : Fin 0, κ i) ≃ Unit :=
        { toFun := fun _ => ()
          invFun := fun _ i => Fin.elim0 i
          left_inv := fun x => by
            funext i
            exact Fin.elim0 i
          right_inv := fun x => by cases x; rfl }
      have he := Hvar_equiv hm (tupleView f) e
      have htotal : ∑ a, m a = 1 := by simpa [mass] using hm.total
      have hconst : Hvar (fun _ : α => ()) m = 0 := by
        simp [Hvar, H, push, mass, htotal]
      rw [← he]
      simpa [e] using le_of_eq hconst
  | succ n ih =>
      let f0 : α → κ 0 := f 0
      let ft : ∀ i : Fin n, α → κ i.succ := fun i => f i.succ
      have hpair :
          Hvar (fun a => (f0 a, tupleView ft a)) m ≤
            Hvar f0 m + Hvar (tupleView ft) m := by
        have hmi := MI_nonneg hm f0 (tupleView ft)
        unfold MI at hmi
        linarith
      have hsplit :
          Hvar (tupleView f) m = Hvar (fun a => (f0 a, tupleView ft a)) m := by
        have he := Hvar_equiv hm (fun a => (f0 a, tupleView ft a)) (Fin.consEquiv κ)
        have hfun :
            (fun a => (Fin.consEquiv κ) (f0 a, tupleView ft a)) = tupleView f := by
          funext a i
          cases i using Fin.cases with
          | zero => rfl
          | succ i => rfl
        rw [hfun] at he
        exact he
      have htail : Hvar (tupleView ft) m ≤ ∑ i, Hvar (ft i) m :=
        ih (κ := fun i : Fin n => κ i.succ) ft
      rw [hsplit]
      calc
        Hvar (fun a => (f0 a, tupleView ft a)) m
            ≤ Hvar f0 m + Hvar (tupleView ft) m := hpair
        _ ≤ Hvar f0 m + ∑ i, Hvar (ft i) m := by linarith
        _ = ∑ i, Hvar (f i) m := by
          rw [Fin.sum_univ_succ]

namespace NLatent

variable {f : ∀ i, Ω → κ i} {g : ∀ i, Ω → γ i}

/-- The conditional total-correlation part of the score is nonnegative when
the tuple of coordinate views determines the cell. -/
theorem conditionalTC_nonneg [Nonempty Ω] (V : NLatent p)
    (htup : Function.Injective (tupleView f)) :
    0 ≤ (∑ i, condH (fun w : V.ι × Ω => f i w.2)
          (fun w => w.1) V.joint) -
        condH (fun w : V.ι × Ω => w.2) (fun w => w.1) V.joint := by
  have hcomponent : ∀ v : V.ι,
      0 ≤ (∑ i, Hvar (f i) (V.comp v)) - H (V.comp v) := by
    intro v
    obtain ⟨u, hu⟩ := htup.hasLeftInverse
    have htuple := Hvar_eq_of_leftInverse (V.comp_isPMF v)
      (fun z : Ω => z) (tupleView f) u hu
    have hid : Hvar (fun z : Ω => z) (V.comp v) = H (V.comp v) := by
      unfold Hvar
      change H (push (Equiv.refl Ω) (V.comp v)) = H (V.comp v)
      exact H_push_equiv (Equiv.refl Ω) (V.comp v) (V.comp_isPMF v)
    have htuple' : Hvar (tupleView f) (V.comp v) =
        Hvar (fun z : Ω => z) (V.comp v) := by
      simpa [Function.comp_def] using htuple
    have hsub := Hvar_tupleView_le_sum (V.comp_isPMF v) f
    rw [htuple', hid] at hsub
    linarith
  have hid :
      condH (fun w : V.ι × Ω => w.2) (fun w => w.1) V.joint =
        ∑ v, V.prior v * H (V.comp v) := by
    rw [V.condH_view_prior (fun z : Ω => z)]
    apply Finset.sum_congr rfl
    intro v _
    congr 1
    unfold Hvar
    change H (push (Equiv.refl Ω) (V.comp v)) = H (V.comp v)
    exact H_push_equiv (Equiv.refl Ω) (V.comp v) (V.comp_isPMF v)
  have hviews : ∀ i : Fin n,
      condH (fun w : V.ι × Ω => f i w.2) (fun w => w.1) V.joint =
        ∑ v, V.prior v * Hvar (f i) (V.comp v) :=
    fun i => V.condH_view_prior (f i)
  simp_rw [hviews]
  rw [hid, Finset.sum_comm, ← Finset.sum_sub_distrib]
  exact Finset.sum_nonneg fun v _ => by
    simpa [mul_sub, Finset.mul_sum] using
      mul_nonneg (V.prior_isPMF.nonneg v) (hcomponent v)

/-- The n-variable score is nonnegative when every singleton/deletion pair
identifies the cell and the full tuple of singleton views identifies the cell. -/
theorem score_nonneg [Nonempty Ω] (V : NLatent p)
    (hinj : ∀ i, Function.Injective (fun z => (f i z, g i z)))
    (htup : Function.Injective (tupleView f)) :
    0 ≤ V.score f g := by
  have hcomponent : ∀ v : V.ι,
      0 ≤ (∑ i, Hvar (f i) (V.comp v)) - H (V.comp v) := by
    intro v
    obtain ⟨u, hu⟩ := htup.hasLeftInverse
    have htuple := Hvar_eq_of_leftInverse (V.comp_isPMF v)
      (fun z : Ω => z) (tupleView f) u hu
    have hid : Hvar (fun z : Ω => z) (V.comp v) = H (V.comp v) := by
      unfold Hvar
      change H (push (Equiv.refl Ω) (V.comp v)) = H (V.comp v)
      exact H_push_equiv (Equiv.refl Ω) (V.comp v) (V.comp_isPMF v)
    have htuple' : Hvar (tupleView f) (V.comp v) = Hvar (fun z : Ω => z) (V.comp v) := by
      simpa [Function.comp_def] using htuple
    have hsub := Hvar_tupleView_le_sum (V.comp_isPMF v) f
    rw [htuple', hid] at hsub
    linarith
  have hTC :
      0 ≤ (∑ i, condH (fun w : V.ι × Ω => f i w.2) (fun w => w.1) V.joint)
          - condH (fun w : V.ι × Ω => w.2) (fun w => w.1) V.joint := by
    have hid :
        condH (fun w : V.ι × Ω => w.2) (fun w => w.1) V.joint =
          ∑ v, V.prior v * H (V.comp v) := by
      rw [V.condH_view_prior (fun z : Ω => z)]
      apply Finset.sum_congr rfl
      intro v _
      congr 1
      unfold Hvar
      change H (push (Equiv.refl Ω) (V.comp v)) = H (V.comp v)
      exact H_push_equiv (Equiv.refl Ω) (V.comp v) (V.comp_isPMF v)
    have hviews : ∀ i : Fin n,
        condH (fun w : V.ι × Ω => f i w.2) (fun w => w.1) V.joint =
          ∑ v, V.prior v * Hvar (f i) (V.comp v) :=
      fun i => V.condH_view_prior (f i)
    simp_rw [hviews]
    rw [hid, Finset.sum_comm, ← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun v _ => by
      simpa [mul_sub, Finset.mul_sum] using
        mul_nonneg (V.prior_isPMF.nonneg v) (hcomponent v)
  have hred : 0 ≤ ∑ i,
      condMI (fun w : V.ι × Ω => w.1) (fun w => f i w.2)
        (fun w => g i w.2) V.joint :=
    Finset.sum_nonneg fun i _ =>
      condMI_nonneg V.joint_isPMF (fun w => w.1) (fun w => f i w.2)
        (fun w => g i w.2)
  unfold NLatent.score
  exact add_nonneg hTC hred

end NLatent
end Views
end stoch_to_det
