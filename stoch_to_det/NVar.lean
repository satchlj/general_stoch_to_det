import stoch_to_det.Entropy

/-!
# n-variable envelope layer for the sum score

Generalizes the two-observable decomposition identity `Latent.score_eq`
(`Envelope.lean`, Lemma 1.1) to `n` observables with single-deletion
redundancy, in the *sum* form:

  `S_n(V) = TC(X ∣ V) + ∑ i, I(V; X_i ∣ X_{-i})`
         `= Ψ_n(p) − ∑ v, λ_v Φ_n(q_v)`,

where `Φ_n(q) = (n+1) H(q) − ∑ i H(q_i) − ∑ i H(q_{-i})` and
`Ψ_n(p) = ∑ i H_p(X_i ∣ X_{-i})`.

Design: rather than dependent products of alphabets, observables enter only
through *views*: for each `i : Fin n`, a singleton view `f i : Ω → κ i`
(the coordinate `X_i`) and a deletion view `g i : Ω → γ i` (the tuple
`X_{-i}`). The only structural hypothesis is that each pair `(f i, g i)` is
jointly injective — `(X_i, X_{-i})` determines the cell — which holds by
construction when `Ω` is the joint alphabet and the views are coordinate
projections. At `n = 2` with `f 0 = fst`, `f 1 = snd`, `g 0 = snd`,
`g 1 = fst`, `nPhi` is definitionally the two-variable `Phi` and `score`
agrees with `Latent.score`.

The mixture structure `NLatent` and its lift lemmas are ports of `Latent`
(`Functionals.lean`) and the private lemmas of `Envelope.lean`, with the
hardwired base `α × β` replaced by an arbitrary finite `Ω`; the proofs are
unchanged because they never use the product structure of the base.
-/

namespace stoch_to_det

open Finset

private lemma Hvar_id' {γ : Type*} [Fintype γ] [DecidableEq γ]
    {m : γ → ℝ} (hm : IsPMF m) : Hvar (fun z : γ => z) m = H m := by
  unfold Hvar
  change H (push (Equiv.refl γ) m) = H m
  exact H_push_equiv (Equiv.refl γ) m hm

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
variable {p : Ω → ℝ}

/-- A finite-mixture latent for a law `p` on an arbitrary finite cell space
`Ω` : a prior `λ` and components `q_v` with `∑ v, λ_v q_v = p`. -/
structure NLatent (p : Ω → ℝ) where
  /-- The (finite) alphabet of the latent variable `V`. -/
  ι : Type
  /-- Finiteness of the latent alphabet. -/
  fin : Fintype ι
  /-- Decidable equality on the latent alphabet. -/
  dec : DecidableEq ι
  /-- The prior `λ`. -/
  prior : ι → ℝ
  /-- The components `qᵥ = P_{Z ∣ V = v}`. -/
  comp : ι → (Ω → ℝ)
  /-- `λ` is a probability law. -/
  prior_isPMF : IsPMF prior
  /-- Each component is a probability law. -/
  comp_isPMF : ∀ v, IsPMF (comp v)
  /-- The mixture reconstructs `p`. -/
  mixture : ∀ z, ∑ v, prior v * comp v z = p z

attribute [instance] NLatent.fin NLatent.dec

namespace NLatent

/-- The joint law of `(V, Z)` on `ι × Ω`. -/
noncomputable def joint (V : NLatent p) : V.ι × Ω → ℝ :=
  fun w => V.prior w.1 * V.comp w.1 w.2

lemma joint_isPMF (V : NLatent p) : IsPMF V.joint := by
  refine ⟨?_, ?_⟩
  · intro w
    exact mul_nonneg (V.prior_isPMF.nonneg w.1) ((V.comp_isPMF w.1).nonneg w.2)
  · rw [mass, Fintype.sum_prod_type]
    simp only [joint]
    simp_rw [← mul_sum]
    have hcomp : ∀ v, ∑ z, V.comp v z = 1 := fun v => by
      simpa [mass] using (V.comp_isPMF v).total
    simp_rw [hcomp, mul_one]
    simpa [mass] using V.prior_isPMF.total

lemma push_snd_joint (V : NLatent p) :
    push (fun w : V.ι × Ω => w.2) V.joint = p := by
  funext z
  unfold push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simpa [NLatent.joint] using V.mixture z

lemma push_fst_joint (V : NLatent p) :
    push (fun w : V.ι × Ω => w.1) V.joint = V.prior := by
  funext v
  have hcomp : ∀ u, ∑ z, V.comp u z = 1 := fun u => by
    simpa [mass] using (V.comp_isPMF u).total
  unfold push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [NLatent.joint]
  calc
    (∑ x, ∑ y, if x = v then V.prior x * V.comp x y else 0) =
        ∑ x, if x = v then V.prior x * (∑ y, V.comp x y) else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x = v
          · simp [hx, Finset.mul_sum]
          · simp [hx]
    _ = V.prior v := by simp [hcomp]

lemma Hvar_lift {γ : Type*} [Fintype γ] [DecidableEq γ]
    (V : NLatent p) (f : Ω → γ) :
    Hvar (fun w : V.ι × Ω => f w.2) V.joint = Hvar f p := by
  unfold Hvar
  congr 1
  calc
    push (fun w : V.ι × Ω => f w.2) V.joint =
        push f (push (fun w : V.ι × Ω => w.2) V.joint) := by
          symm
          simpa [Function.comp_def] using
            (push_push (fun w : V.ι × Ω => w.2) f V.joint)
    _ = push f p := by rw [V.push_snd_joint]

lemma Hvar_prior (V : NLatent p) :
    Hvar (fun w : V.ι × Ω => w.1) V.joint = H V.prior := by
  unfold Hvar
  rw [V.push_fst_joint]

/-- Conditional chain rule for the mixture joint: the entropy of `(f(Z), V)`
is the prior entropy plus the average per-component entropy of `f`. -/
lemma Hvar_lift_pair_prior {γ : Type*} [Fintype γ] [DecidableEq γ]
    (V : NLatent p) (f : Ω → γ) :
    Hvar (fun w : V.ι × Ω => (f w.2, w.1)) V.joint =
      H V.prior + ∑ v, V.prior v * Hvar f (V.comp v) := by
  have hdecomp := Hvar_pair_eq_sum_fibers V.joint_isPMF
    (fun w : V.ι × Ω => f w.2) (fun w => w.1)
  rw [V.Hvar_prior] at hdecomp
  rw [hdecomp]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  have hfiber :
      push (fun w : V.ι × Ω => f w.2)
          (fun w => if w.1 = v then V.joint w else 0) =
        fun c => V.prior v * push f (V.comp v) c := by
    funext c
    unfold push
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp only [NLatent.joint]
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

/-- Pair form with the prior on the left, obtained by re-encoding. -/
lemma Hvar_prior_pair_lift {γ : Type*} [Fintype γ] [DecidableEq γ]
    (V : NLatent p) (f : Ω → γ) :
    Hvar (fun w : V.ι × Ω => (w.1, f w.2)) V.joint =
      H V.prior + ∑ v, V.prior v * Hvar f (V.comp v) := by
  calc
    Hvar (fun w : V.ι × Ω => (w.1, f w.2)) V.joint
        = Hvar (fun w : V.ι × Ω => (f w.2, w.1)) V.joint := by
          simpa using Hvar_equiv V.joint_isPMF
            (fun w : V.ι × Ω => (f w.2, w.1)) (Equiv.prodComm γ V.ι)
    _ = _ := V.Hvar_lift_pair_prior f

end NLatent

section Views

variable {n : ℕ} {κ γ : Fin n → Type}
  [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
  [∀ i, Fintype (γ i)] [∀ i, DecidableEq (γ i)]

variable (f : ∀ i, Ω → κ i) (g : ∀ i, Ω → γ i)

/-- The n-variable posterior payoff
`Φ_n(q) = (n+1) H(q) − ∑ i H(f_i # q) − ∑ i H(g_i # q)`.
At `n = 2` with coordinate views this is the two-variable `Phi`. -/
noncomputable def nPhi (q : Ω → ℝ) : ℝ :=
  (n + 1) * H q - ∑ i, Hvar (f i) q - ∑ i, Hvar (g i) q

/-- `Ψ_n(p) = ∑ i H_p(f_i ∣ g_i)`, the sum of per-deletion conditional
entropies of the base law. -/
noncomputable def nPsi (p : Ω → ℝ) : ℝ :=
  ∑ i, condH (f i) (g i) p

/-- The n-variable sum score of a latent:
`TC(X ∣ V) + ∑ i I(V ; f_i ∣ g_i)`, all information quantities taken under
the joint law of `(V, Z)`. The conditional total correlation is
`∑ i H(f_i ∣ V) − H(Z ∣ V)`. -/
noncomputable def NLatent.score (V : NLatent p) : ℝ :=
  ((∑ i, condH (fun w : V.ι × Ω => f i w.2) (fun w => w.1) V.joint)
      - condH (fun w : V.ι × Ω => w.2) (fun w => w.1) V.joint)
    + ∑ i, condMI (fun w : V.ι × Ω => w.1) (fun w => f i w.2)
        (fun w => g i w.2) V.joint

namespace NLatent

variable {f g}

/-- Per-view conditional entropy of the joint collapses to the average
component conditional entropy: `H(f_i ∣ V) = ∑ v λ_v H_{q_v}(f_i)`. -/
lemma condH_view_prior {δ : Type*} [Fintype δ] [DecidableEq δ]
    (V : NLatent p) (h : Ω → δ) :
    condH (fun w : V.ι × Ω => h w.2) (fun w => w.1) V.joint =
      ∑ v, V.prior v * Hvar h (V.comp v) := by
  unfold condH
  rw [V.Hvar_lift_pair_prior h, V.Hvar_prior]
  ring

/-- The conditional mutual information `I(V ; f_i ∣ g_i)` under the joint
equals the base-law conditional entropy minus the average component
conditional entropy. No injectivity is needed. -/
lemma condMI_view (V : NLatent p) (i : Fin n) :
    condMI (fun w : V.ι × Ω => w.1) (fun w => f i w.2)
        (fun w => g i w.2) V.joint =
      condH (f i) (g i) p - ∑ v, V.prior v * condH (f i) (g i) (V.comp v) := by
  have hVg :
      Hvar (fun w : V.ι × Ω => (w.1, g i w.2)) V.joint =
        H V.prior + ∑ v, V.prior v * Hvar (g i) (V.comp v) :=
    V.Hvar_prior_pair_lift (g i)
  have hfg :
      Hvar (fun w : V.ι × Ω => (f i w.2, g i w.2)) V.joint =
        Hvar (fun z => (f i z, g i z)) p :=
    V.Hvar_lift (fun z => (f i z, g i z))
  have hVfg :
      Hvar (fun w : V.ι × Ω => (w.1, f i w.2, g i w.2)) V.joint =
        H V.prior + ∑ v, V.prior v * Hvar (fun z => (f i z, g i z)) (V.comp v) := by
    calc
      Hvar (fun w : V.ι × Ω => (w.1, f i w.2, g i w.2)) V.joint
          = Hvar (fun w : V.ι × Ω => ((f i w.2, g i w.2), w.1)) V.joint := by
            simpa using Hvar_equiv V.joint_isPMF
              (fun w : V.ι × Ω => ((f i w.2, g i w.2), w.1))
              (Equiv.prodComm (κ i × γ i) V.ι)
      _ = _ := V.Hvar_lift_pair_prior (fun z => (f i z, g i z))
  have hg :
      Hvar (fun w : V.ι × Ω => g i w.2) V.joint = Hvar (g i) p :=
    V.Hvar_lift (g i)
  unfold condMI
  rw [hVg, hfg, hVfg, hg]
  unfold condH
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

/-- **n-variable decomposition identity** (envelope form of the sum score).
If each pair `(f i, g i)` is jointly injective — `(X_i, X_{-i})` determines
the cell — then

`S_n(V) = Ψ_n(p) − ∑ v, λ_v Φ_n(q_v)`.

This is the n-observable generalization of `Latent.score_eq`
(Lemma 1.1 of the two-variable development). -/
theorem score_eq [Nonempty Ω] (hp : IsPMF p) (V : NLatent p)
    (hinj : ∀ i, Function.Injective (fun z => (f i z, g i z))) :
    V.score f g = nPsi f g p - ∑ v, V.prior v * nPhi f g (V.comp v) := by
  -- each pair view has full entropy on every component
  have hpair : ∀ (i : Fin n) (v : V.ι),
      Hvar (fun z => (f i z, g i z)) (V.comp v) = H (V.comp v) := by
    intro i v
    obtain ⟨u, hu⟩ := (hinj i).hasLeftInverse
    have := Hvar_eq_of_leftInverse (V.comp_isPMF v)
      (fun z : Ω => z) (fun z => (f i z, g i z)) u ?_
    · calc
        Hvar (fun z => (f i z, g i z)) (V.comp v)
            = Hvar ((fun z : Ω => (f i z, g i z)) ∘ (fun z : Ω => z))
                (V.comp v) := rfl
        _ = Hvar (fun z : Ω => z) (V.comp v) := this
        _ = H (V.comp v) := Hvar_id' (V.comp_isPMF v)
    · exact hu
  -- the conditional total correlation term
  have hTC :
      (∑ i, condH (fun w : V.ι × Ω => f i w.2) (fun w => w.1) V.joint)
          - condH (fun w : V.ι × Ω => w.2) (fun w => w.1) V.joint =
        ∑ v, V.prior v *
          ((∑ i, Hvar (f i) (V.comp v)) - H (V.comp v)) := by
    have hid :
        condH (fun w : V.ι × Ω => w.2) (fun w => w.1) V.joint =
          ∑ v, V.prior v * H (V.comp v) := by
      have := V.condH_view_prior (fun z : Ω => z)
      rw [this]
      apply Finset.sum_congr rfl
      intro v _
      rw [Hvar_id' (V.comp_isPMF v)]
    have hviews : ∀ i : Fin n,
        condH (fun w : V.ι × Ω => f i w.2) (fun w => w.1) V.joint =
          ∑ v, V.prior v * Hvar (f i) (V.comp v) :=
      fun i => V.condH_view_prior (f i)
    simp_rw [hviews]
    rw [hid, Finset.sum_comm, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rw [mul_sub, Finset.mul_sum]
  -- the redundancy terms
  have hred : ∀ i : Fin n,
      condMI (fun w : V.ι × Ω => w.1) (fun w => f i w.2)
          (fun w => g i w.2) V.joint =
        condH (f i) (g i) p -
          ∑ v, V.prior v * condH (f i) (g i) (V.comp v) :=
    fun i => V.condMI_view i
  unfold NLatent.score
  rw [hTC]
  simp_rw [hred]
  unfold nPsi nPhi condH
  simp_rw [hpair]
  -- reduce to a per-component identity
  have hkey : ∀ v : V.ι,
      V.prior v * ((∑ i, Hvar (f i) (V.comp v)) - H (V.comp v))
        - ∑ i, V.prior v * (H (V.comp v) - Hvar (g i) (V.comp v)) =
      - (V.prior v * (((n : ℝ) + 1) * H (V.comp v)
          - ∑ i, Hvar (f i) (V.comp v) - ∑ i, Hvar (g i) (V.comp v))) := by
    intro v
    have hconst : (∑ _i : Fin n, H (V.comp v)) = (n : ℝ) * H (V.comp v) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hconst]
    ring
  have hswap :
      (∑ x : Fin n, ∑ v : V.ι,
          V.prior v * (H (V.comp v) - Hvar (g x) (V.comp v))) =
        ∑ v : V.ι, ∑ x : Fin n,
          V.prior v * (H (V.comp v) - Hvar (g x) (V.comp v)) :=
    Finset.sum_comm
  have hsum :
      (∑ v, V.prior v * ((∑ i, Hvar (f i) (V.comp v)) - H (V.comp v)))
        - ∑ v, ∑ i, V.prior v * (H (V.comp v) - Hvar (g i) (V.comp v)) =
      - ∑ v, V.prior v * (((n : ℝ) + 1) * H (V.comp v)
          - ∑ i, Hvar (f i) (V.comp v) - ∑ i, Hvar (g i) (V.comp v)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun v _ => hkey v)
  simp only [Finset.sum_sub_distrib]
  rw [hswap]
  linarith [hsum]


/-- Mutual information between the latent and any view collapses through the
mixture: `I(V ; h(Z)) = H_p(h) − ∑ v λ_v H_{q_v}(h)`. -/
lemma MI_view {δ : Type*} [Fintype δ] [DecidableEq δ]
    (V : NLatent p) (h : Ω → δ) :
    MI (fun w : V.ι × Ω => w.1) (fun w => h w.2) V.joint =
      Hvar h p - ∑ v, V.prior v * Hvar h (V.comp v) := by
  unfold MI
  rw [V.Hvar_prior, V.Hvar_lift h, V.Hvar_prior_pair_lift h]
  ring

/-- **n-variable fusion identity** (the engine of the duality layer): splitting
the base law by any latent changes the total posterior payoff by an exact
information ledger,

`Φ_n(p) − ∑ v λ_v Φ_n(q_v) = (n+1) I(V;Z) − ∑ i I(V;f_i) − ∑ i I(V;g_i)`.

Since the linear part `E_q[ln w]` of any dual defect `G_w` is affine in `q`,
this is also the exact change in total defect under the split — the
generalization of `Gdef_fusion` (`Duality.lean`). -/
theorem nPhi_fusion (hp : IsPMF p) (V : NLatent p) :
    nPhi f g p - ∑ v, V.prior v * nPhi f g (V.comp v) =
      ((n : ℝ) + 1) * MI (fun w : V.ι × Ω => w.1) (fun w => w.2) V.joint
        - ∑ i, MI (fun w : V.ι × Ω => w.1) (fun w => f i w.2) V.joint
        - ∑ i, MI (fun w : V.ι × Ω => w.1) (fun w => g i w.2) V.joint := by
  have hZ : MI (fun w : V.ι × Ω => w.1) (fun w => w.2) V.joint =
      H p - ∑ v, V.prior v * H (V.comp v) := by
    have := V.MI_view (fun z : Ω => z)
    rw [Hvar_id' hp] at this
    calc
      MI (fun w : V.ι × Ω => w.1) (fun w => w.2) V.joint
          = MI (fun w : V.ι × Ω => w.1) (fun w => (fun z : Ω => z) w.2)
              V.joint := rfl
      _ = H p - ∑ v, V.prior v * Hvar (fun z : Ω => z) (V.comp v) := this
      _ = H p - ∑ v, V.prior v * H (V.comp v) := by
            congr 1
            exact Finset.sum_congr rfl fun v _ => by
              rw [Hvar_id' (V.comp_isPMF v)]
  have hf : ∀ i : Fin n,
      MI (fun w : V.ι × Ω => w.1) (fun w => f i w.2) V.joint =
        Hvar (f i) p - ∑ v, V.prior v * Hvar (f i) (V.comp v) :=
    fun i => V.MI_view (f i)
  have hg : ∀ i : Fin n,
      MI (fun w : V.ι × Ω => w.1) (fun w => g i w.2) V.joint =
        Hvar (g i) p - ∑ v, V.prior v * Hvar (g i) (V.comp v) :=
    fun i => V.MI_view (g i)
  rw [hZ]
  simp_rw [hf, hg]
  unfold nPhi
  have hswapf :
      (∑ i : Fin n, ∑ v : V.ι, V.prior v * Hvar (f i) (V.comp v)) =
        ∑ v : V.ι, ∑ i : Fin n, V.prior v * Hvar (f i) (V.comp v) :=
    Finset.sum_comm
  have hswapg :
      (∑ i : Fin n, ∑ v : V.ι, V.prior v * Hvar (g i) (V.comp v)) =
        ∑ v : V.ι, ∑ i : Fin n, V.prior v * Hvar (g i) (V.comp v) :=
    Finset.sum_comm
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hswapf, hswapg]
  have hmul : (∑ v, V.prior v * (((n : ℝ) + 1) * H (V.comp v))) =
      ∑ v, ((n : ℝ) + 1) * (V.prior v * H (V.comp v)) :=
    Finset.sum_congr rfl fun v _ => by ring
  rw [hmul]
  ring

end NLatent

end Views

end stoch_to_det
