import stoch_to_det.Functionals
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# §1. The two functionals as envelopes


Three results, in dependency order:

* `Latent.score_eq` (Lemma 1.1, decomposition identity) — `S_p(V) = Ψ(p) − ∑ λᵥ Φ(qᵥ)`.
* `Latent.score_sub_Ixy` (Lemma 1.2, score identity) — the interaction-information form.
  This is the workhorse: §2.8(c), §4.3 and §5.3 all invoke it.
* `tau_eq_Psi_sub_envelope` (Corollary 1.3) — `τ = Ψ − Φ̂`, with the infimum **attained**.

## Mathlib background

Lemmas 1.1 and 1.2 are `Finset.sum` algebra over `stoch_to_det.Entropy`. The
proof of Corollary 1.3 uses Carathéodory for the hypograph together with a
compactness argument; the relevant Mathlib entries are `convexHull_eq_union`,
`IsCompact.exists_isMaxOn`, and — for concavity of the entropy —
`Real.strictConcaveOn_negMulLog` via `stoch_to_det.Entropy.H_eq_negMulLog`.
-/

namespace stoch_to_det

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable {p : α × β → ℝ}

private lemma Latent.push_snd_joint (V : Latent p) :
    push (fun w : V.ι × (α × β) => w.2) V.joint = p := by
  funext z
  unfold push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simpa [Latent.joint] using V.mixture z

private lemma Latent.push_fst_joint (V : Latent p) :
    push (fun w : V.ι × (α × β) => w.1) V.joint = V.prior := by
  funext v
  have hcomp : ∀ u, ∑ z, V.comp u z = 1 := fun u => by
    simpa [mass] using (V.comp_isPMF u).total
  unfold push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Latent.joint]
  calc
    (∑ x, ∑ y, if x = v then V.prior x * V.comp x y else 0) =
        ∑ x, if x = v then V.prior x * (∑ y, V.comp x y) else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x = v
          · simp [hx, Finset.mul_sum]
          · simp [hx]
    _ = V.prior v := by simp [hcomp]

private lemma Latent.Hvar_lift {γ : Type*} [Fintype γ] [DecidableEq γ]
    (V : Latent p) (f : α × β → γ) :
    Hvar (fun w : V.ι × (α × β) => f w.2) V.joint = Hvar f p := by
  unfold Hvar
  congr 1
  calc
    push (fun w : V.ι × (α × β) => f w.2) V.joint =
        push f (push (fun w : V.ι × (α × β) => w.2) V.joint) := by
          symm
          simpa [Function.comp_def] using
            (push_push (fun w : V.ι × (α × β) => w.2) f V.joint)
    _ = push f p := by rw [V.push_snd_joint]

private lemma Latent.Hvar_prior (V : Latent p) :
    Hvar (fun w : V.ι × (α × β) => w.1) V.joint = H V.prior := by
  unfold Hvar
  rw [V.push_fst_joint]

private lemma Hvar_id {γ : Type*} [Fintype γ] [DecidableEq γ]
    {m : γ → ℝ} (hm : IsPMF m) : Hvar (fun z : γ => z) m = H m := by
  unfold Hvar
  change H (push (Equiv.refl γ) m) = H m
  exact H_push_equiv (Equiv.refl γ) m hm

private lemma Latent.Hvar_lift_pair_prior {γ : Type*} [Fintype γ] [DecidableEq γ]
    (V : Latent p) (f : α × β → γ) :
    Hvar (fun w : V.ι × (α × β) => (f w.2, w.1)) V.joint =
      H V.prior + ∑ v, V.prior v * Hvar f (V.comp v) := by
  have hdecomp := Hvar_pair_eq_sum_fibers V.joint_isPMF
    (fun w : V.ι × (α × β) => f w.2) (fun w => w.1)
  rw [V.Hvar_prior] at hdecomp
  rw [hdecomp]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  have hfiber :
      push (fun w : V.ι × (α × β) => f w.2)
          (fun w => if w.1 = v then V.joint w else 0) =
        fun c => V.prior v * push f (V.comp v) c := by
    funext c
    unfold push
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp only [Latent.joint]
    rw [Finset.sum_comm]
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : f z = c
    · simp only [hz, if_true]
      have hvsum :
          (∑ x, if x = v then V.prior x * V.comp x z else 0) =
            (if v = v then V.prior v * V.comp v z else 0) := by
        apply Finset.sum_eq_single v
        · intro u _ huv
          simp [huv]
        · simp
      simpa using hvsum
    · simp [hz]
  rw [hfiber]
  by_cases hv : V.prior v = 0
  · simp [hv, Hvar, H, mass]
  · have hvpos : 0 < V.prior v :=
      lt_of_le_of_ne (V.prior_isPMF.nonneg v) (Ne.symm hv)
    simpa [Hvar] using
      (H_smul (isFinMeas_push (V.comp_isPMF v).isFinMeas) hvpos.le)

private lemma Latent.MI_prior_lift {γ : Type*} [Fintype γ] [DecidableEq γ]
    (V : Latent p) (f : α × β → γ) :
    MI (fun w : V.ι × (α × β) => w.1) (fun w => f w.2) V.joint =
      Hvar f p - ∑ v, V.prior v * Hvar f (V.comp v) := by
  have hpair :
      Hvar (fun w : V.ι × (α × β) => (w.1, f w.2)) V.joint =
        H V.prior + ∑ v, V.prior v * Hvar f (V.comp v) := by
    calc
      _ = Hvar (fun w : V.ι × (α × β) => (f w.2, w.1)) V.joint := by
        simpa using Hvar_equiv V.joint_isPMF
          (fun w : V.ι × (α × β) => (f w.2, w.1))
          (Equiv.prodComm γ V.ι)
      _ = _ := V.Hvar_lift_pair_prior f
  unfold MI
  rw [V.Hvar_prior, V.Hvar_lift f, hpair]
  ring

private lemma Latent.sum_prior_mul_Phi (V : Latent p) :
    (∑ v, V.prior v * Phi (V.comp v)) =
      3 * (∑ v, V.prior v * H (V.comp v))
        - 2 * (∑ v, V.prior v * H (mX (V.comp v)))
        - 2 * (∑ v, V.prior v * H (mY (V.comp v))) := by
  calc
    _ = ∑ v, (3 * (V.prior v * H (V.comp v))
        - 2 * (V.prior v * H (mX (V.comp v)))
        - 2 * (V.prior v * H (mY (V.comp v)))) := by
          apply Finset.sum_congr rfl
          intro v _
          unfold Phi
          ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      simp only [← Finset.mul_sum]

/-- **Lemma 1.1** (decomposition identity).
`S_p(V) = Ψ(p) − ∑ᵥ λᵥ Φ(qᵥ)`. -/
theorem Latent.score_eq (hp : IsPMF p) (V : Latent p) :
    V.score = Psi p - ∑ v, V.prior v * Phi (V.comp v) := by
  have hX : Hvar (fun w : V.ι × (α × β) => w.2.1) V.joint = H (mX p) := by
    simpa [Hvar] using V.Hvar_lift (fun z : α × β => z.1)
  have hY : Hvar (fun w : V.ι × (α × β) => w.2.2) V.joint = H (mY p) := by
    simpa [Hvar] using V.Hvar_lift (fun z : α × β => z.2)
  have hXY :
      Hvar (fun w : V.ι × (α × β) => (w.2.1, w.2.2)) V.joint = H p := by
    calc
      _ = Hvar (fun w : V.ι × (α × β) => w.2) V.joint := by rfl
      _ = Hvar (fun z : α × β => z) p := V.Hvar_lift (fun z => z)
      _ = H p := Hvar_id hp
  have hV : Hvar (fun w : V.ι × (α × β) => w.1) V.joint = H V.prior :=
    V.Hvar_prior
  have hXV :
      Hvar (fun w : V.ι × (α × β) => (w.2.1, w.1)) V.joint =
        H V.prior + ∑ v, V.prior v * H (mX (V.comp v)) := by
    simpa [Hvar] using V.Hvar_lift_pair_prior (fun z : α × β => z.1)
  have hYV :
      Hvar (fun w : V.ι × (α × β) => (w.2.2, w.1)) V.joint =
        H V.prior + ∑ v, V.prior v * H (mY (V.comp v)) := by
    simpa [Hvar] using V.Hvar_lift_pair_prior (fun z : α × β => z.2)
  have hVY :
      Hvar (fun w : V.ι × (α × β) => (w.1, w.2.2)) V.joint =
        H V.prior + ∑ v, V.prior v * H (mY (V.comp v)) := by
    calc
      _ = Hvar (fun w : V.ι × (α × β) => (w.2.2, w.1)) V.joint := by
        simpa using Hvar_equiv V.joint_isPMF
          (fun w : V.ι × (α × β) => (w.2.2, w.1))
          (Equiv.prodComm β V.ι)
      _ = _ := hYV
  have hVX :
      Hvar (fun w : V.ι × (α × β) => (w.1, w.2.1)) V.joint =
        H V.prior + ∑ v, V.prior v * H (mX (V.comp v)) := by
    calc
      _ = Hvar (fun w : V.ι × (α × β) => (w.2.1, w.1)) V.joint := by
        simpa using Hvar_equiv V.joint_isPMF
          (fun w : V.ι × (α × β) => (w.2.1, w.1))
          (Equiv.prodComm α V.ι)
      _ = _ := hXV
  have hZV :
      Hvar (fun w : V.ι × (α × β) => ((w.2.1, w.2.2), w.1)) V.joint =
        H V.prior + ∑ v, V.prior v * H (V.comp v) := by
    calc
      _ = H V.prior + ∑ v, V.prior v * Hvar (fun z : α × β => z) (V.comp v) :=
        V.Hvar_lift_pair_prior (fun z => z)
      _ = H V.prior + ∑ v, V.prior v * H (V.comp v) := by
        congr 1
        apply Finset.sum_congr rfl
        intro v _
        rw [Hvar_id (V.comp_isPMF v)]
  have hXYV :
      Hvar (fun w : V.ι × (α × β) => (w.2.1, w.2.2, w.1)) V.joint =
        H V.prior + ∑ v, V.prior v * H (V.comp v) := by
    calc
      _ = Hvar (fun w : V.ι × (α × β) => ((w.2.1, w.2.2), w.1)) V.joint := by
        simpa using Hvar_equiv V.joint_isPMF
          (fun w : V.ι × (α × β) => ((w.2.1, w.2.2), w.1))
          (Equiv.prodAssoc α β V.ι)
      _ = _ := hZV
  have hVXY :
      Hvar (fun w : V.ι × (α × β) => (w.1, w.2.1, w.2.2)) V.joint =
        H V.prior + ∑ v, V.prior v * H (V.comp v) := by
    calc
      _ = Hvar (fun w : V.ι × (α × β) => ((w.2.1, w.2.2), w.1)) V.joint := by
        simpa using Hvar_equiv V.joint_isPMF
          (fun w : V.ι × (α × β) => ((w.2.1, w.2.2), w.1))
          (Equiv.prodComm (α × β) V.ι)
      _ = _ := hZV
  let eVYX : (α × β) × V.ι ≃ V.ι × (β × α) :=
    (Equiv.prodComm (α × β) V.ι).trans
      (Equiv.prodCongr (Equiv.refl V.ι) (Equiv.prodComm α β))
  have hVYX :
      Hvar (fun w : V.ι × (α × β) => (w.1, w.2.2, w.2.1)) V.joint =
        H V.prior + ∑ v, V.prior v * H (V.comp v) := by
    calc
      _ = Hvar (fun w : V.ι × (α × β) => ((w.2.1, w.2.2), w.1)) V.joint := by
        have he :
            (fun w : V.ι × (α × β) => eVYX ((w.2.1, w.2.2), w.1)) =
              fun w => (w.1, w.2.2, w.2.1) := by
          funext w
          rfl
        have heq := Hvar_equiv V.joint_isPMF
          (fun w : V.ι × (α × β) => ((w.2.1, w.2.2), w.1)) eVYX
        rw [he] at heq
        exact heq
      _ = _ := hZV
  have hYX :
      Hvar (fun w : V.ι × (α × β) => (w.2.2, w.2.1)) V.joint = H p := by
    calc
      _ = Hvar (fun w : V.ι × (α × β) => (w.2.1, w.2.2)) V.joint := by
        have hswap :
            (fun w : V.ι × (α × β) =>
                (Equiv.prodComm α β) (w.2.1, w.2.2)) =
              fun w => (w.2.2, w.2.1) := by
          funext w
          rfl
        have heq := Hvar_equiv V.joint_isPMF
          (fun w : V.ι × (α × β) => (w.2.1, w.2.2))
          (Equiv.prodComm α β)
        rw [hswap] at heq
        exact heq
      _ = H p := hXY
  have hPhiSum := V.sum_prior_mul_Phi
  unfold Latent.score condMI
  rw [hXV, hYV, hXYV, hV, hVY, hXY, hVXY, hY, hVX, hYX, hVYX, hX]
  rw [hPhiSum]
  unfold Psi
  ring

/-- **Lemma 1.2** (score identity).
`S_p(V) − I(X;Y) = 3 I(V;Z) − 2 I(V;X) − 2 I(V;Y)`. -/
theorem Latent.score_sub_Ixy (hp : IsPMF p) (V : Latent p) :
    V.score - Ixy p
      = 3 * MI (fun w => w.1) (fun w => w.2) V.joint
        - 2 * MI (fun w => w.1) (fun w => w.2.1) V.joint
        - 2 * MI (fun w => w.1) (fun w => w.2.2) V.joint := by
  have hMIZ :
      MI (fun w : V.ι × (α × β) => w.1) (fun w => w.2) V.joint =
        H p - ∑ v, V.prior v * H (V.comp v) := by
    calc
      _ = Hvar (fun z : α × β => z) p
          - ∑ v, V.prior v * Hvar (fun z : α × β => z) (V.comp v) :=
        V.MI_prior_lift (fun z => z)
      _ = H p - ∑ v, V.prior v * H (V.comp v) := by
        rw [Hvar_id hp]
        congr 1
        apply Finset.sum_congr rfl
        intro v _
        rw [Hvar_id (V.comp_isPMF v)]
  have hMIX :
      MI (fun w : V.ι × (α × β) => w.1) (fun w => w.2.1) V.joint =
        H (mX p) - ∑ v, V.prior v * H (mX (V.comp v)) := by
    simpa [Hvar] using V.MI_prior_lift (fun z : α × β => z.1)
  have hMIY :
      MI (fun w : V.ι × (α × β) => w.1) (fun w => w.2.2) V.joint =
        H (mY p) - ∑ v, V.prior v * H (mY (V.comp v)) := by
    simpa [Hvar] using V.MI_prior_lift (fun z : α × β => z.2)
  rw [V.score_eq hp, hMIZ, hMIX, hMIY, V.sum_prior_mul_Phi]
  unfold Psi Ixy
  ring

/-- The upper concave envelope of `Φ` on the simplex `Δ(𝒮)`, evaluated at `p`:
the supremum of `∑ᵥ λᵥ Φ(qᵥ)` over finite mixture representations of `p`
supported in `𝒮`. Defined as an `⨆` over `Latent p` (Lemma 1.1 shows this is
the same optimization as minimizing the score). -/
noncomputable def concaveEnvelopePhi (p : α × β → ℝ) : ℝ :=
  ⨆ V : Latent p, ∑ v, V.prior v * Phi (V.comp v)

/-- **Corollary 1.3**, first half: `τ(p) = Ψ(p) − Φ̂(p)`. -/
theorem tau_eq_Psi_sub_envelope (hp : IsPMF p) :
    tau p = Psi p - concaveEnvelopePhi p := by
  let payoff : Latent p → ℝ := fun V => ∑ v, V.prior v * Phi (V.comp v)
  letI : Nonempty (Latent p) := ⟨Latent.const hp⟩
  have hscore (V : Latent p) : V.score = Psi p - payoff V := by
    simpa [payoff] using V.score_eq hp
  have hscore_bdd : BddBelow (Set.range fun V : Latent p => V.score) :=
    ⟨0, by
      rintro _ ⟨V, rfl⟩
      exact V.score_nonneg⟩
  have hpayoff_bdd : BddAbove (Set.range payoff) :=
    ⟨Psi p, by
      rintro _ ⟨V, rfl⟩
      have hs := V.score_nonneg
      rw [hscore V] at hs
      linarith⟩
  unfold tau concaveEnvelopePhi
  change (⨅ V : Latent p, V.score) = Psi p - ⨆ V : Latent p, payoff V
  apply le_antisymm
  · have hsup :
        (⨆ V : Latent p, payoff V) ≤ Psi p - ⨅ V : Latent p, V.score := by
      refine ciSup_le fun V => ?_
      have hinf : (⨅ W : Latent p, W.score) ≤ V.score := ciInf_le hscore_bdd V
      rw [hscore V] at hinf
      linarith
    linarith
  · refine le_ciInf fun V => ?_
    have hle : payoff V ≤ ⨆ W : Latent p, payoff W := le_ciSup hpayoff_bdd V
    rw [hscore V]
    linarith

private noncomputable def conditionedComp {γ : Type} [Fintype γ] [DecidableEq γ]
    (f : α × β → γ) (c : γ) : α × β → ℝ :=
  fun z =>
    if push f p c = 0 then p z
    else if f z = c then (push f p c)⁻¹ * p z else 0

private lemma conditionedComp_isPMF {γ : Type} [Fintype γ] [DecidableEq γ]
    (hp : IsPMF p) (f : α × β → γ) (c : γ) :
    IsPMF (conditionedComp (p := p) f c) := by
  classical
  by_cases hc : push f p c = 0
  · have hcomp : conditionedComp (p := p) f c = p := by
      funext z
      simp [conditionedComp, hc]
    rw [hcomp]
    exact hp
  · have hprior_nonneg : 0 ≤ push f p c := (isPMF_push hp).nonneg c
    have hprior_pos : 0 < push f p c := lt_of_le_of_ne hprior_nonneg (Ne.symm hc)
    constructor
    · intro z
      simp only [conditionedComp, hc, if_false]
      split
      · exact mul_nonneg (inv_nonneg.mpr hprior_nonneg) (hp.nonneg z)
      · exact le_rfl
    · unfold mass conditionedComp
      simp only [hc, if_false]
      calc
        (∑ z, if f z = c then (push f p c)⁻¹ * p z else 0) =
            (push f p c)⁻¹ * ∑ z ∈ univ.filter (fun z => f z = c), p z := by
              rw [Finset.mul_sum, Finset.sum_filter]
        _ = (push f p c)⁻¹ * push f p c := by rfl
        _ = 1 := inv_mul_cancel₀ hc

private lemma push_mul_conditionedComp {γ : Type} [Fintype γ] [DecidableEq γ]
    (hp : IsPMF p) (f : α × β → γ) (c : γ) (z : α × β) :
    push f p c * conditionedComp (p := p) f c z =
      if f z = c then p z else 0 := by
  classical
  by_cases hfc : f z = c
  · subst c
    have hz_le : p z ≤ push f p (f z) := by
      unfold push
      exact Finset.single_le_sum (fun w _ => hp.nonneg w) (by simp)
    by_cases hc : push f p (f z) = 0
    · have hz : p z = 0 := le_antisymm (by simpa [hc] using hz_le) (hp.nonneg z)
      simp [conditionedComp, hc, hz]
    · rw [show conditionedComp (p := p) f (f z) z =
          (push f p (f z))⁻¹ * p z by simp [conditionedComp, hc]]
      rw [if_pos rfl]
      field_simp [hc]
  · by_cases hc : push f p c = 0
    · simp [conditionedComp, hfc, hc]
    · simp [conditionedComp, hfc, hc]

private noncomputable def functionLatent {γ : Type} [Fintype γ] [DecidableEq γ]
    (hp : IsPMF p) (f : α × β → γ) : Latent p where
  ι := γ
  fin := inferInstance
  dec := inferInstance
  prior := push f p
  comp := conditionedComp (p := p) f
  prior_isPMF := isPMF_push hp
  comp_isPMF := conditionedComp_isPMF hp f
  mixture := by
    intro z
    calc
      (∑ c, push f p c * conditionedComp (p := p) f c z) =
          ∑ c, if f z = c then p z else 0 := by
            apply Finset.sum_congr rfl
            intro c _
            exact push_mul_conditionedComp hp f c z
      _ = p z := by
        have hsingle :
            (∑ c, if f z = c then p z else 0) =
              (if f z = f z then p z else 0) := by
          apply Finset.sum_eq_single (f z)
          · intro c _ hne
            simp [hne, Ne.symm hne]
          · simp
        simpa using hsingle

private lemma functionLatent_isDet {γ : Type} [Fintype γ] [DecidableEq γ]
    (hp : IsPMF p) (f : α × β → γ) : (functionLatent hp f).IsDet := by
  unfold Latent.IsDet
  change ∀ z, ∀ c c' : γ,
    push f p c * conditionedComp (p := p) f c z ≠ 0 →
    push f p c' * conditionedComp (p := p) f c' z ≠ 0 → c = c'
  intro z c c' hc hc'
  have hfc : f z = c := by
    by_contra h
    rw [push_mul_conditionedComp hp f c z] at hc
    exact hc (by simp [h])
  have hfc' : f z = c' := by
    by_contra h
    rw [push_mul_conditionedComp hp f c' z] at hc'
    exact hc' (by simp [h])
  exact hfc.symm.trans hfc'

/-- The finite latent induced by a deterministic function of `(X,Y)`. -/
noncomputable def Latent.ofFunction {γ : Type} [Fintype γ] [DecidableEq γ]
    (hp : IsPMF p) (f : α × β → γ) : Latent p :=
  functionLatent hp f

/-- A function-induced latent is deterministic. -/
theorem Latent.ofFunction_isDet {γ : Type} [Fintype γ] [DecidableEq γ]
    (hp : IsPMF p) (f : α × β → γ) :
    (Latent.ofFunction hp f).IsDet := by
  exact functionLatent_isDet hp f

/-- The joint law of a function-induced latent is the pushforward along its
graph embedding. -/
theorem Latent.ofFunction_joint_eq_push
    {γ : Type} [Fintype γ] [DecidableEq γ]
    (hp : IsPMF p) (f : α × β → γ) :
    (Latent.ofFunction hp f).joint =
      push (fun z : α × β => (f z, z)) p := by
  classical
  change (fun w : γ × (α × β) =>
      push f p w.1 * conditionedComp (p := p) f w.1 w.2) =
    push (fun z : α × β => (f z, z)) p
  funext w
  rcases w with ⟨c, z⟩
  change push f p c * conditionedComp (p := p) f c z =
    push (fun z : α × β => (f z, z)) p (c, z)
  rw [push_mul_conditionedComp hp f c z]
  unfold push
  rw [Finset.sum_filter]
  have hsum :
      (∑ x, if (f x, x) = (c, z) then p x else 0) =
        (if (f z, z) = (c, z) then p z else 0) := by
    apply Finset.sum_eq_single z
    · intro x _ hx
      by_cases hpair : (f x, x) = (c, z)
      · exact (hx (congrArg Prod.snd hpair)).elim
      · simp [hpair]
    · simp
  calc
    (if f z = c then p z else 0) =
        (if (f z, z) = (c, z) then p z else 0) := by simp
    _ = ∑ x, if (f x, x) = (c, z) then p x else 0 := hsum.symm
    _ = ∑ a, if (fun z => (f z, z)) a = (c, z) then p a else 0 := by rfl

private lemma Hvar_push_source
    {Ω Ω' κ : Type*} [Fintype Ω] [Fintype Ω'] [DecidableEq Ω']
    [Fintype κ] [DecidableEq κ]
    (e : Ω → Ω') (a : Ω' → κ) (m : Ω → ℝ) :
    Hvar a (push e m) = Hvar (a ∘ e) m := by
  unfold Hvar
  rw [push_push]

private lemma condMI_push_source
    {Ω Ω' κ δ ε : Type*} [Fintype Ω] [Fintype Ω'] [DecidableEq Ω']
    [Fintype κ] [DecidableEq κ]
    [Fintype δ] [DecidableEq δ]
    [Fintype ε] [DecidableEq ε]
    (e : Ω → Ω') (a : Ω' → κ) (b : Ω' → δ) (c : Ω' → ε)
    (m : Ω → ℝ) :
    condMI a b c (push e m) =
      condMI (a ∘ e) (b ∘ e) (c ∘ e) m := by
  unfold condMI
  change Hvar (fun x => (a x, c x)) (push e m) +
      Hvar (fun x => (b x, c x)) (push e m) -
      Hvar (fun x => (a x, b x, c x)) (push e m) -
      Hvar c (push e m) = _
  rw [Hvar_push_source, Hvar_push_source, Hvar_push_source,
    Hvar_push_source]
  rfl

/-- The score of a function-induced latent is exactly the deterministic
LessWrong expression computed under `p`. -/
theorem Latent.ofFunction_score_eq_detScore
    {γ : Type} [Fintype γ] [DecidableEq γ]
    (hp : IsPMF p) (Γ : α × β → γ) :
    (Latent.ofFunction hp Γ).score = detScore p Γ := by
  change
    condMI (fun w : γ × (α × β) => w.2.1)
        (fun w => w.2.2) (fun w => w.1) (functionLatent hp Γ).joint
      + condMI (fun w : γ × (α × β) => w.1)
          (fun w => w.2.1) (fun w => w.2.2) (functionLatent hp Γ).joint
      + condMI (fun w : γ × (α × β) => w.1)
          (fun w => w.2.2) (fun w => w.2.1) (functionLatent hp Γ).joint =
      detScore p Γ
  rw [show (functionLatent hp Γ).joint =
      push (fun z : α × β => (Γ z, z)) p by
        simpa [Latent.ofFunction] using Latent.ofFunction_joint_eq_push hp Γ]
  rw [condMI_push_source, condMI_push_source, condMI_push_source]
  change condMI Prod.fst Prod.snd Γ p
      + condMI Γ Prod.fst Prod.snd p
      + condMI Γ Prod.snd Prod.fst p = detScore p Γ
  rw [condMI_code_X_given_Y hp Γ, condMI_code_Y_given_X hp Γ]
  unfold detScore
  ring

/-- On a function-induced latent, the unrestricted finite-latent `DScore`
reduces exactly to the deterministic function expression `detScore`. -/
@[simp] theorem Latent.ofFunction_DScore_eq_detScore
    {γ : Type} [Fintype γ] [DecidableEq γ]
    (hp : IsPMF p) (Γ : α × β → γ) :
    (Latent.ofFunction hp Γ).DScore = detScore p Γ := by
  rw [Latent.DScore_eq_score_add_two_condH_pair,
    Latent.ofFunction_score_eq_detScore]
  have hzero :
      condH
          (fun w : γ × (α × β) => w.1)
          (fun w => w.2)
          (Latent.ofFunction hp Γ).joint = 0 := by
    change condH (fun w : γ × (α × β) => w.1) (fun w => w.2)
      (functionLatent hp Γ).joint = 0
    rw [show (functionLatent hp Γ).joint =
        push (fun z : α × β => (Γ z, z)) p by
          simpa [Latent.ofFunction] using
            Latent.ofFunction_joint_eq_push hp Γ]
    unfold condH
    rw [Hvar_push_source, Hvar_push_source]
    simpa [condH, Function.comp_def] using
      condH_function_given_pair_zero hp Γ
  change detScore p Γ +
      2 * condH (fun w : γ × (α × β) => w.1) (fun w => w.2)
        (Latent.ofFunction hp Γ).joint = detScore p Γ
  rw [hzero]
  ring

private lemma Latent.exists_comp_ne_zero (V : Latent p) (v : V.ι) :
    ∃ z, V.comp v z ≠ 0 := by
  by_contra h
  push_neg at h
  have hzero : mass (V.comp v) = 0 := by simp [mass, h]
  have hone := (V.comp_isPMF v).total
  rw [hzero] at hone
  norm_num at hone

private noncomputable def Latent.representative (V : Latent p) (v : V.ι) : α × β :=
  Classical.choose (V.exists_comp_ne_zero v)

private lemma Latent.comp_representative_ne_zero (V : Latent p) (v : V.ι) :
    V.comp v (V.representative v) ≠ 0 :=
  Classical.choose_spec (V.exists_comp_ne_zero v)

private noncomputable def Latent.activeIndex (V : Latent p) (z : α × β) : V.ι :=
  if h : ∃ v, V.joint (v, z) ≠ 0 then Classical.choose h else Classical.arbitrary V.ι

private lemma Latent.activeIndex_spec (V : Latent p) (z : α × β)
    (h : ∃ v, V.joint (v, z) ≠ 0) : V.joint (V.activeIndex z, z) ≠ 0 := by
  simp only [activeIndex, dif_pos h]
  exact Classical.choose_spec h

private noncomputable def Latent.detLabel (V : Latent p) (v : V.ι) :
    Fin (Fintype.card (α × β)) :=
  Fintype.equivFin (α × β) (V.representative v)

private noncomputable def Latent.detCode (V : Latent p) :
    α × β → Fin (Fintype.card (α × β)) :=
  fun z => V.detLabel (V.activeIndex z)

private lemma Latent.detCode_eq_label_of_active (V : Latent p) (hV : V.IsDet)
    {z : α × β} {v : V.ι} (hv : V.joint (v, z) ≠ 0) :
    V.detCode z = V.detLabel v := by
  have hex : ∃ u, V.joint (u, z) ≠ 0 := ⟨v, hv⟩
  have hactive := V.activeIndex_spec z hex
  have huv : V.activeIndex z = v := hV z (V.activeIndex z) v hactive hv
  simp [detCode, huv]

private lemma Latent.detLabel_inj_of_prior_ne_zero (V : Latent p) (hV : V.IsDet)
    {v u : V.ι} (hv : V.prior v ≠ 0) (hu : V.prior u ≠ 0)
    (hlabel : V.detLabel v = V.detLabel u) : v = u := by
  have hrep : V.representative v = V.representative u := by
    exact (Fintype.equivFin (α × β)).injective hlabel
  have hvactive : V.joint (v, V.representative v) ≠ 0 := by
    exact mul_ne_zero hv (V.comp_representative_ne_zero v)
  have huactive : V.joint (u, V.representative v) ≠ 0 := by
    unfold Latent.joint
    apply mul_ne_zero hu
    rw [hrep]
    exact V.comp_representative_ne_zero u
  exact hV (V.representative v) v u hvactive huactive

private lemma Latent.sum_joint_fiber (V : Latent p) (v : V.ι) :
    ∑ z, V.joint (v, z) = V.prior v := by
  unfold Latent.joint
  change (∑ z, V.prior v * V.comp v z) = V.prior v
  rw [← Finset.mul_sum]
  have htotal : ∑ z, V.comp v z = 1 := by
    simpa [mass] using (V.comp_isPMF v).total
  rw [htotal, mul_one]

private lemma Latent.push_detCode_eq_push_detLabel (V : Latent p) (hV : V.IsDet) :
    push V.detCode p = push V.detLabel V.prior := by
  funext c
  unfold push
  rw [Finset.sum_filter, Finset.sum_filter]
  calc
    (∑ z, if V.detCode z = c then p z else 0) =
        ∑ z, ∑ v, if V.detCode z = c then V.joint (v, z) else 0 := by
          apply Finset.sum_congr rfl
          intro z _
          by_cases hz : V.detCode z = c
          · simp only [hz, if_true]
            exact (V.mixture z).symm
          · simp [hz]
    _ = ∑ z, ∑ v, if V.detLabel v = c then V.joint (v, z) else 0 := by
          apply Finset.sum_congr rfl
          intro z _
          apply Finset.sum_congr rfl
          intro v _
          by_cases hv : V.joint (v, z) = 0
          · simp [hv]
          · rw [V.detCode_eq_label_of_active hV hv]
    _ = ∑ v, ∑ z, if V.detLabel v = c then V.joint (v, z) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ v, if V.detLabel v = c then V.prior v else 0 := by
          apply Finset.sum_congr rfl
          intro v _
          by_cases hv : V.detLabel v = c
          · simp [hv, V.sum_joint_fiber]
          · simp [hv]

private lemma Latent.mixture_eq_joint_of_active (V : Latent p) (hV : V.IsDet)
    {z : α × β} {v : V.ι} (hv : V.joint (v, z) ≠ 0) :
    p z = V.joint (v, z) := by
  calc
    p z = ∑ u, V.joint (u, z) := by
      simpa [Latent.joint] using (V.mixture z).symm
    _ = V.joint (v, z) := by
      apply Finset.sum_eq_single v
      · intro u _ huv
        by_contra hu
        exact huv (hV z u v hu hv)
      · simp

private lemma Latent.p_eq_zero_of_no_active (V : Latent p) {z : α × β}
    (h : ¬ ∃ v, V.joint (v, z) ≠ 0) : p z = 0 := by
  have hjoint : ∀ v, V.joint (v, z) = 0 := by
    intro v
    exact not_ne_iff.mp (not_exists.mp h v)
  calc
    p z = ∑ v, V.joint (v, z) := by
      simpa [Latent.joint] using (V.mixture z).symm
    _ = 0 := Finset.sum_eq_zero fun v _ => hjoint v

private lemma Latent.detCode_fiber_eq_joint (V : Latent p) (hV : V.IsDet)
    {v : V.ι} (hvprior : V.prior v ≠ 0) (z : α × β) :
    (if V.detCode z = V.detLabel v then p z else 0) = V.joint (v, z) := by
  by_cases hex : ∃ u, V.joint (u, z) ≠ 0
  · have huactive := V.activeIndex_spec z hex
    have hpjoint := V.mixture_eq_joint_of_active hV huactive
    have hcodelabel := V.detCode_eq_label_of_active hV huactive
    by_cases hcode : V.detCode z = V.detLabel v
    · rw [if_pos hcode, hpjoint]
      have huprior : V.prior (V.activeIndex z) ≠ 0 := by
        intro hu
        apply huactive
        simp [Latent.joint, hu]
      have hlabels : V.detLabel (V.activeIndex z) = V.detLabel v :=
        hcodelabel.symm.trans hcode
      have huv := V.detLabel_inj_of_prior_ne_zero hV huprior hvprior hlabels
      rw [huv]
    · rw [if_neg hcode]
      by_contra hvjoint
      exact hcode (V.detCode_eq_label_of_active hV (Ne.symm hvjoint))
  · have hpzero := V.p_eq_zero_of_no_active hex
    have hvjoint : V.joint (v, z) = 0 := not_ne_iff.mp (not_exists.mp hex v)
    simp [hpzero, hvjoint]

private lemma Latent.push_detLabel_self (V : Latent p) (hV : V.IsDet)
    {v : V.ι} (hv : V.prior v ≠ 0) :
    push V.detLabel V.prior (V.detLabel v) = V.prior v := by
  unfold push
  apply Finset.sum_eq_single v
  · intro u hu huv
    by_cases huprior : V.prior u = 0
    · exact huprior
    · have hlabels : V.detLabel u = V.detLabel v := (Finset.mem_filter.mp hu).2
      exact (huv (V.detLabel_inj_of_prior_ne_zero hV huprior hv hlabels)).elim
  · simp

private lemma Latent.push_detCode_self (V : Latent p) (hV : V.IsDet)
    {v : V.ι} (hv : V.prior v ≠ 0) :
    push V.detCode p (V.detLabel v) = V.prior v := by
  rw [V.push_detCode_eq_push_detLabel hV]
  exact V.push_detLabel_self hV hv

private lemma Latent.functionLatent_comp_detLabel (hp : IsPMF p) (V : Latent p)
    (hV : V.IsDet) {v : V.ι} (hv : V.prior v ≠ 0) :
    (functionLatent hp V.detCode).comp (V.detLabel v) = V.comp v := by
  change conditionedComp (p := p) V.detCode (V.detLabel v) = V.comp v
  have hpush := V.push_detCode_self hV hv
  funext z
  have hfiber := V.detCode_fiber_eq_joint hV hv z
  unfold Latent.joint at hfiber
  by_cases hcode : V.detCode z = V.detLabel v
  · rw [if_pos hcode] at hfiber
    simp only [conditionedComp, hpush, hv, if_false, hcode, if_true]
    rw [hfiber]
    field_simp [hv]
  · rw [if_neg hcode] at hfiber
    have hcomp : V.comp v z = 0 := by
      have hprod : V.prior v * V.comp v z = 0 := hfiber.symm
      exact (mul_eq_zero.mp hprod).resolve_left hv
    simp [conditionedComp, hpush, hv, hcode, hcomp]

private lemma Latent.functionLatent_detCode_score_eq (hp : IsPMF p) (V : Latent p)
    (hV : V.IsDet) : (functionLatent hp V.detCode).score = V.score := by
  let W : Latent p := functionLatent hp V.detCode
  have hprior : W.prior = push V.detLabel V.prior := by
    change push V.detCode p = push V.detLabel V.prior
    exact V.push_detCode_eq_push_detLabel hV
  have hpayoff :
      (∑ c, W.prior c * Phi (W.comp c)) =
        ∑ v, V.prior v * Phi (V.comp v) := by
    calc
      _ = ∑ c, push V.detLabel V.prior c * Phi (W.comp c) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [hprior]
      _ = ∑ v, V.prior v * Phi (W.comp (V.detLabel v)) :=
        sum_push_mul V.detLabel V.prior (fun c => Phi (W.comp c))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : V.prior v = 0
        · simp [hv]
        · have hcomp : W.comp (V.detLabel v) = V.comp v := by
            simpa [W] using V.functionLatent_comp_detLabel hp hV hv
          rw [hcomp]
  rw [W.score_eq hp, V.score_eq hp, hpayoff]

noncomputable def continuousEntropy {γ : Type*} [Fintype γ]
    (m : γ → ℝ) : ℝ :=
  (∑ a, Real.negMulLog (m a)) / Real.log 2

lemma H_eq_continuousEntropy {γ : Type*} [Fintype γ]
    {m : γ → ℝ} (hm : IsPMF m) : H m = continuousEntropy m := by
  have h := H_eq_negMulLog hm.isFinMeas
  rw [hm.total, Real.log_one, mul_zero, zero_add] at h
  apply (eq_div_iff (Real.log_pos one_lt_two).ne').2
  rw [mul_comm]
  exact h

lemma continuous_continuousEntropy {γ : Type*} [Fintype γ] :
    Continuous (continuousEntropy : (γ → ℝ) → ℝ) := by
  unfold continuousEntropy
  fun_prop

noncomputable def continuousPhi (q : α × β → ℝ) : ℝ :=
  3 * continuousEntropy q
    - 2 * continuousEntropy (push Prod.fst q)
    - 2 * continuousEntropy (push Prod.snd q)

lemma continuous_push_map {γ δ : Type*} [Fintype γ] [Fintype δ]
    [DecidableEq δ] (f : γ → δ) :
    Continuous (fun m : γ → ℝ => push f m) := by
  apply continuous_pi
  intro c
  unfold push
  fun_prop

lemma continuous_continuousPhi :
    Continuous (continuousPhi : (α × β → ℝ) → ℝ) := by
  unfold continuousPhi
  have hq : Continuous (fun q : α × β → ℝ => continuousEntropy q) :=
    continuous_continuousEntropy
  have hqX : Continuous (fun q : α × β → ℝ => continuousEntropy (push Prod.fst q)) :=
    continuous_continuousEntropy.comp (continuous_push_map Prod.fst)
  have hqY : Continuous (fun q : α × β → ℝ => continuousEntropy (push Prod.snd q)) :=
    continuous_continuousEntropy.comp (continuous_push_map Prod.snd)
  exact ((continuous_const.mul hq).sub (continuous_const.mul hqX)).sub
    (continuous_const.mul hqY)

lemma Phi_eq_continuousPhi {q : α × β → ℝ} (hq : IsPMF q) :
    Phi q = continuousPhi q := by
  have hqX : IsPMF (mX q) := isPMF_push hq
  have hqY : IsPMF (mY q) := isPMF_push hq
  unfold Phi continuousPhi
  rw [H_eq_continuousEntropy hq, H_eq_continuousEntropy hqX,
    H_eq_continuousEntropy hqY]

def pmfSet : Set (α × β → ℝ) := {q | IsPMF q}

noncomputable def phiGraph : Set ((α × β → ℝ) × ℝ) :=
  (fun q => (q, Phi q)) '' pmfSet

lemma isCompact_pmfSet : IsCompact (pmfSet : Set (α × β → ℝ)) := by
  have heq : (pmfSet : Set (α × β → ℝ)) = stdSimplex ℝ (α × β) := by
    ext q
    constructor
    · intro hq
      exact ⟨hq.nonneg, by simpa [mass] using hq.total⟩
    · rintro ⟨hq, htotal⟩
      exact ⟨hq, by simpa [mass] using htotal⟩
  rw [heq]
  exact isCompact_stdSimplex ℝ (α × β)

lemma isCompact_phiGraph : IsCompact (phiGraph : Set ((α × β → ℝ) × ℝ)) := by
  let graphMap : (α × β → ℝ) → (α × β → ℝ) × ℝ :=
    fun q => (q, continuousPhi q)
  have hgraphMap : Continuous graphMap :=
    continuous_id.prodMk continuous_continuousPhi
  have heq : phiGraph = graphMap '' pmfSet := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, by simp [graphMap, Phi_eq_continuousPhi hq]⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, by simp [graphMap, Phi_eq_continuousPhi hq]⟩
  rw [heq]
  exact isCompact_pmfSet.image hgraphMap

private noncomputable def envelopeSize : ℕ :=
  Module.finrank ℝ ((α × β → ℝ) × ℝ) + 1

private noncomputable def envelopeBarycenter
    (a : (Fin (envelopeSize (α := α) (β := β)) → ℝ) ×
      (Fin (envelopeSize (α := α) (β := β)) → (α × β → ℝ) × ℝ)) :
    (α × β → ℝ) × ℝ :=
  ∑ i, a.1 i • a.2 i

private noncomputable def envelopeParams :
    Set ((Fin (envelopeSize (α := α) (β := β)) → ℝ) ×
      (Fin (envelopeSize (α := α) (β := β)) → (α × β → ℝ) × ℝ)) :=
  stdSimplex ℝ (Fin (envelopeSize (α := α) (β := β))) ×ˢ
    Set.pi (Set.univ : Set (Fin (envelopeSize (α := α) (β := β))))
      (fun _ => phiGraph)

private lemma continuous_envelopeBarycenter :
    Continuous (envelopeBarycenter (α := α) (β := β)) := by
  unfold envelopeBarycenter
  fun_prop

private lemma isCompact_envelopeParams :
    IsCompact (envelopeParams (α := α) (β := β)) := by
  unfold envelopeParams
  apply IsCompact.prod (isCompact_stdSimplex ℝ _)
  exact isCompact_univ_pi fun _ => isCompact_phiGraph

private lemma isCompact_envelopeBarycenter_image :
    IsCompact (envelopeBarycenter (α := α) (β := β) ''
      envelopeParams (α := α) (β := β)) :=
  isCompact_envelopeParams.image continuous_envelopeBarycenter

private lemma envelopeBarycenter_image_subset_convexHull :
    envelopeBarycenter (α := α) (β := β) '' envelopeParams ⊆
      convexHull ℝ (phiGraph : Set ((α × β → ℝ) × ℝ)) := by
  rintro x ⟨a, ha, rfl⟩
  rcases ha with ⟨hw, hq⟩
  apply mem_convexHull_of_exists_fintype a.1 a.2
  · exact hw.1
  · exact hw.2
  · intro i
    exact hq i (Set.mem_univ i)
  · rfl

private lemma convexHull_subset_envelopeBarycenter_image (hp : IsPMF p) :
    convexHull ℝ (phiGraph : Set ((α × β → ℝ) × ℝ)) ⊆
      envelopeBarycenter (α := α) (β := β) '' envelopeParams := by
  intro x hx
  rw [convexHull_eq_union] at hx
  simp only [Set.mem_iUnion, exists_prop] at hx
  rcases hx with ⟨t, htGraph, htIndependent, hxt⟩
  have htcard : Fintype.card t ≤ envelopeSize (α := α) (β := β) := by
    calc
      Fintype.card t ≤
          Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → (α × β → ℝ) × ℝ))) + 1 :=
        htIndependent.card_le_finrank_succ
      _ ≤ Module.finrank ℝ ((α × β → ℝ) × ℝ) + 1 :=
        Nat.add_le_add_right (Submodule.finrank_le _) 1
      _ = envelopeSize (α := α) (β := β) := rfl
  let e : t ↪ Fin (envelopeSize (α := α) (β := β)) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using htcard))
  rcases (Finset.mem_convexHull'.mp hxt) with ⟨w, hw_nonneg, hw_sum, hw_center⟩
  let weights : Fin (envelopeSize (α := α) (β := β)) → ℝ :=
    fun j => ∑ i : t, if e i = j then w i.1 else 0
  let points : Fin (envelopeSize (α := α) (β := β)) → (α × β → ℝ) × ℝ :=
    fun j => if h : ∃ i : t, e i = j then (Classical.choose h).1 else (p, Phi p)
  have hinner_weight (i : t) :
      (∑ j, if e i = j then w i.1 else 0) = w i.1 := by
    have hsingle :
        (∑ j, if e i = j then w i.1 else 0) =
          (if e i = e i then w i.1 else 0) := by
      apply Finset.sum_eq_single (e i)
      · intro j _ hji
        simp [Ne.symm hji]
      · simp
    simpa using hsingle
  have hweights_nonneg : ∀ j, 0 ≤ weights j := by
    intro j
    dsimp [weights]
    apply Finset.sum_nonneg
    intro i _
    split
    · exact hw_nonneg i.1 i.2
    · exact le_rfl
  have hweights_sum : ∑ j, weights j = 1 := by
    calc
      (∑ j, weights j) = ∑ j, ∑ i : t, if e i = j then w i.1 else 0 := rfl
      _ = ∑ i : t, ∑ j, if e i = j then w i.1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ i : t, w i.1 := by
        apply Finset.sum_congr rfl
        intro i _
        exact hinner_weight i
      _ = ∑ y ∈ t, w y := by
        simp only [univ_eq_attach]
        rw [Finset.sum_attach]
      _ = 1 := hw_sum
  have hpoints (j : Fin (envelopeSize (α := α) (β := β))) : points j ∈ phiGraph := by
    by_cases hj : ∃ i : t, e i = j
    · rw [show points j = (Classical.choose hj).1 by simp [points, hj]]
      exact htGraph (Classical.choose hj).2
    · rw [show points j = (p, Phi p) by simp [points, hj]]
      exact ⟨p, hp, rfl⟩
  have hterm (j : Fin (envelopeSize (α := α) (β := β))) :
      weights j • points j =
        ∑ i : t, if e i = j then w i.1 • i.1 else 0 := by
    by_cases hj : ∃ i : t, e i = j
    · let i₀ : t := Classical.choose hj
      have hi₀ : e i₀ = j := Classical.choose_spec hj
      have hweight : weights j = w i₀.1 := by
        dsimp [weights]
        have hsingle :
            (∑ i : t, if e i = j then w i.1 else 0) =
              (if e i₀ = j then w i₀.1 else 0) := by
          apply Finset.sum_eq_single i₀
          · intro i _ hii₀
            have hei : e i ≠ j := by
              intro hei
              exact hii₀ (e.injective (hei.trans hi₀.symm))
            simp [hei]
          · simp
        simpa [hi₀] using hsingle
      have hpoint : points j = i₀.1 := by
        dsimp [points, i₀]
        rw [dif_pos hj]
      rw [hweight, hpoint]
      symm
      have hsingle :
          (∑ i : t, if e i = j then w i.1 • i.1 else 0) =
            (if e i₀ = j then w i₀.1 • i₀.1 else 0) := by
        apply Finset.sum_eq_single i₀
        · intro i _ hii₀
          have hei : e i ≠ j := by
            intro hei
            exact hii₀ (e.injective (hei.trans hi₀.symm))
          simp [hei]
        · simp
      simpa [hi₀] using hsingle
    · have hnot (i : t) : e i ≠ j := fun hi => hj ⟨i, hi⟩
      have hweight : weights j = 0 := by
        dsimp [weights]
        exact Finset.sum_eq_zero fun i _ => by simp [hnot i]
      rw [hweight, zero_smul]
      symm
      exact Finset.sum_eq_zero fun i _ => by simp [hnot i]
  have hbary : envelopeBarycenter (weights, points) = x := by
    calc
      envelopeBarycenter (weights, points) = ∑ j, weights j • points j := rfl
      _ = ∑ j, ∑ i : t, if e i = j then w i.1 • i.1 else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        exact hterm j
      _ = ∑ i : t, ∑ j, if e i = j then w i.1 • i.1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ i : t, w i.1 • i.1 := by
        apply Finset.sum_congr rfl
        intro i _
        have hsingle :
            (∑ j, if e i = j then w i.1 • i.1 else 0) =
              (if e i = e i then w i.1 • i.1 else 0) := by
          apply Finset.sum_eq_single (e i)
          · intro j _ hji
            simp [Ne.symm hji]
          · simp
        simpa using hsingle
      _ = ∑ y ∈ t, w y • y := by
        simp only [univ_eq_attach]
        simpa using (Finset.sum_attach t (fun y => w y • y))
      _ = x := hw_center
  refine ⟨(weights, points), ?_, hbary⟩
  exact ⟨⟨hweights_nonneg, hweights_sum⟩, fun j _ => hpoints j⟩

private lemma convexHull_phiGraph_eq_barycenter_image (hp : IsPMF p) :
    convexHull ℝ (phiGraph : Set ((α × β → ℝ) × ℝ)) =
      envelopeBarycenter (α := α) (β := β) '' envelopeParams :=
  Set.Subset.antisymm (convexHull_subset_envelopeBarycenter_image hp)
    envelopeBarycenter_image_subset_convexHull

lemma isCompact_convexHull_phiGraph (hp : IsPMF p) :
    IsCompact (convexHull ℝ (phiGraph : Set ((α × β → ℝ) × ℝ))) := by
  rw [convexHull_phiGraph_eq_barycenter_image hp]
  exact isCompact_envelopeBarycenter_image

private lemma Latent.graphMixture_mem_convexHull (V : Latent p) :
    (p, ∑ v, V.prior v * Phi (V.comp v)) ∈
      convexHull ℝ (phiGraph : Set ((α × β → ℝ) × ℝ)) := by
  apply mem_convexHull_of_exists_fintype V.prior
    (fun v => (V.comp v, Phi (V.comp v)))
  · exact V.prior_isPMF.nonneg
  · simpa [mass] using V.prior_isPMF.total
  · intro v
    exact ⟨V.comp v, V.comp_isPMF v, rfl⟩
  · apply Prod.ext
    · rw [Prod.fst_sum]
      funext z
      simp only [Finset.sum_apply, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
      exact V.mixture z
    · simp only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul]

lemma exists_latent_of_mem_convexHull_phiGraph (hp : IsPMF p) {r : ℝ}
    (h : (p, r) ∈ convexHull ℝ (phiGraph : Set ((α × β → ℝ) × ℝ))) :
    ∃ V : Latent p, (∑ v, V.prior v * Phi (V.comp v)) = r := by
  rcases mem_convexHull_iff_exists_fintype.mp h with
    ⟨ι, hι, w, z, hw_nonneg, hw_sum, hz, hcenter⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := Classical.decEq ι
  have hz' : ∀ i, ∃ q : α × β → ℝ, IsPMF q ∧ (q, Phi q) = z i := by
    intro i
    rcases hz i with ⟨q, hq, hqz⟩
    exact ⟨q, hq, hqz⟩
  choose q hq hqz using hz'
  have hcenter' : ∑ i, w i • (q i, Phi (q i)) = (p, r) := by
    calc
      _ = ∑ i, w i • z i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hqz i]
      _ = (p, r) := hcenter
  have hfirst : ∑ i, w i • q i = p := by
    have hfst := congrArg Prod.fst hcenter'
    simpa only [Prod.fst_sum, Prod.smul_fst] using hfst
  have hmixture : ∀ a, ∑ i, w i * q i a = p a := by
    intro a
    have ha := congrFun hfirst a
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using ha
  have hpayoff : ∑ i, w i * Phi (q i) = r := by
    have hr := congrArg Prod.snd hcenter'
    simpa only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul] using hr
  let V : Latent p :=
    { ι := ι
      fin := inferInstance
      dec := inferInstance
      prior := w
      comp := q
      prior_isPMF := ⟨hw_nonneg, by simpa [mass] using hw_sum⟩
      comp_isPMF := hq
      mixture := hmixture }
  refine ⟨V, ?_⟩
  exact hpayoff

/-- **Corollary 1.3**, attainment half: the infimum defining
`τ` is attained by a finite latent. Only finiteness of the attaining latent is
used downstream; a sharper `|𝒮| + 1` cardinality bound is not needed. -/
theorem exists_tau_optimal_latent (hp : IsPMF p) :
    ∃ V : Latent p, V.score = tau p := by
  let slice : Set ((α × β → ℝ) × ℝ) :=
    convexHull ℝ (phiGraph : Set ((α × β → ℝ) × ℝ)) ∩ {x | x.1 = p}
  have hslice_compact : IsCompact slice := by
    apply (isCompact_convexHull_phiGraph hp).inter_right
    exact isClosed_eq continuous_fst continuous_const
  have hbase_graph : (p, Phi p) ∈ (phiGraph : Set ((α × β → ℝ) × ℝ)) :=
    ⟨p, hp, rfl⟩
  have hslice_nonempty : slice.Nonempty := by
    refine ⟨(p, Phi p), ?_, rfl⟩
    exact subset_convexHull ℝ _ hbase_graph
  obtain ⟨x, hx_slice, hx_max⟩ :=
    hslice_compact.exists_isMaxOn hslice_nonempty continuous_snd.continuousOn
  have hx_eq : (p, x.2) = x := by
    apply Prod.ext
    · exact hx_slice.2.symm
    · rfl
  have hx_hull : (p, x.2) ∈
      convexHull ℝ (phiGraph : Set ((α × β → ℝ) × ℝ)) := by
    rw [hx_eq]
    exact hx_slice.1
  obtain ⟨V, hVpayoff⟩ := exists_latent_of_mem_convexHull_phiGraph hp hx_hull
  refine ⟨V, ?_⟩
  have hscore_bdd : BddBelow (Set.range fun W : Latent p => W.score) :=
    ⟨0, by
      rintro _ ⟨W, rfl⟩
      exact W.score_nonneg⟩
  apply le_antisymm
  · unfold tau
    letI : Nonempty (Latent p) := ⟨Latent.const hp⟩
    refine le_ciInf fun W => ?_
    have hW_slice :
        (p, ∑ v, W.prior v * Phi (W.comp v)) ∈ slice :=
      ⟨W.graphMixture_mem_convexHull, rfl⟩
    have hpayoff_le :
        (∑ v, W.prior v * Phi (W.comp v)) ≤ x.2 := hx_max hW_slice
    rw [V.score_eq hp, W.score_eq hp, hVpayoff]
    linarith
  · unfold tau
    exact ciInf_le hscore_bdd V

/-- **Corollary 1.3**, partition half: the same statement for `T` over
deterministic latents. -/
theorem exists_T_optimal_latent (hp : IsPMF p) :
    ∃ V : Latent p, V.IsDet ∧ V.score = T p := by
  let Code := (α × β) → Fin (Fintype.card (α × β))
  let scoreOf : Code → ℝ := fun f => (functionLatent hp f).score
  have hcodes : (univ : Finset Code).Nonempty := by
    exact ⟨(Latent.const hp).detCode, Finset.mem_univ _⟩
  obtain ⟨f₀, _hf₀, hf₀min⟩ :=
    Finset.exists_min_image (univ : Finset Code) scoreOf hcodes
  let V₀ : Latent p := functionLatent hp f₀
  have hV₀det : V₀.IsDet := by
    simpa [V₀] using functionLatent_isDet hp f₀
  have hV₀_le_T : V₀.score ≤ T p := by
    letI : Nonempty {V : Latent p // V.IsDet} :=
      ⟨⟨Latent.const hp, Latent.const_isDet hp⟩⟩
    unfold T
    refine le_ciInf fun W => ?_
    have hmin := hf₀min W.1.detCode (Finset.mem_univ _)
    have hscore := W.1.functionLatent_detCode_score_eq hp W.2
    simpa [scoreOf, V₀] using hmin.trans_eq hscore
  have hT_le_V₀ : T p ≤ V₀.score := T_le_score V₀ hV₀det
  exact ⟨V₀, hV₀det, le_antisymm hV₀_le_T hT_le_V₀⟩

/-- Function-level form of deterministic attainment.  The returned code has
the fixed alphabet `Fin (card (α × β))`, and depends only on `p`. -/
theorem exists_T_optimal_code (hp : IsPMF p) :
    ∃ Γ : α × β → Fin (Fintype.card (α × β)),
      (Latent.ofFunction hp Γ).score = T p := by
  obtain ⟨V, hVdet, hVscore⟩ := exists_T_optimal_latent hp
  refine ⟨V.detCode, ?_⟩
  calc
    (Latent.ofFunction hp V.detCode).score = V.score := by
      exact V.functionLatent_detCode_score_eq hp hVdet
    _ = T p := hVscore

/-- Literal function-code formulation of `T`: optimizing over bundled
deterministic latents is exactly the same as optimizing `detScore` over codes
with the fixed alphabet `Fin (card (α × β))`. -/
theorem T_eq_iInf_detScore_codes
    {p : α × β → ℝ} (hp : IsPMF p) :
    T p =
      ⨅ Γ : α × β → Fin (Fintype.card (α × β)), detScore p Γ := by
  obtain ⟨Γ₀, hΓ₀⟩ := exists_T_optimal_code hp
  letI : Nonempty (α × β → Fin (Fintype.card (α × β))) := ⟨Γ₀⟩
  apply le_antisymm
  · refine le_ciInf fun Γ => ?_
    rw [← Latent.ofFunction_score_eq_detScore hp Γ]
    exact T_le_score (Latent.ofFunction hp Γ)
      (Latent.ofFunction_isDet hp Γ)
  · have hb : BddBelow
        (Set.range fun f : α × β → Fin (Fintype.card (α × β)) =>
          detScore p f) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨f, rfl⟩
      change 0 ≤ detScore p f
      rw [← Latent.ofFunction_score_eq_detScore hp f]
      exact (Latent.ofFunction hp f).score_nonneg
    calc
      (⨅ f : α × β → Fin (Fintype.card (α × β)), detScore p f) ≤
          detScore p Γ₀ := ciInf_le hb Γ₀
      _ = (Latent.ofFunction hp Γ₀).score :=
        (Latent.ofFunction_score_eq_detScore hp Γ₀).symm
      _ = T p := hΓ₀

end stoch_to_det
