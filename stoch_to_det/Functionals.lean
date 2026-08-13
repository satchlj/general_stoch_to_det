import stoch_to_det.Entropy

/-!
# Latents, the score, and the two functionals `τ` and `T`


## Support handling

We fix `𝒮 := supp p` without modelling it as a subtype: every object lives on
the ambient finite product
`α × β`, and membership in the support appears as a hypothesis (`p z ≠ 0`) or a
support condition (`Supported`). A connected component is then a law on the
same `α × β` that vanishes off the component, and `reduce_to_connected`
quantifies over the same `α`, `β`.

Statements consequently carry `Supported` / positivity hypotheses explicitly;
see the junk-value note in `stoch_to_det.Prelude`.
-/

namespace stoch_to_det

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-! ### Supports and connectedness -/

/-- The support of a finite measure, as a `Finset`. -/
noncomputable def support (m : α × β → ℝ) : Finset (α × β) := univ.filter (fun z => m z ≠ 0)

/-- `m` vanishes outside `S`. -/
def Supported (S : Finset (α × β)) (m : α × β → ℝ) : Prop := ∀ z ∉ S, m z = 0

/-- Two cells are adjacent when they share a row or a column. The connected
components of this relation on `S` are exactly the connected components of the
bipartite support graph of §3 (a component occupies a set of columns and a set
of rows disjoint from every other component's). -/
def Adj (z z' : α × β) : Prop := z.1 = z'.1 ∨ z.2 = z'.2

/-- `S` is connected: any two of its cells are joined by a chain of cells of `S`
each sharing a row or column with the next. -/
def IsConnected (S : Finset (α × β)) : Prop :=
  ∀ z ∈ S, ∀ z' ∈ S, Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ Adj a b) z z'

/-! ### Latents -/

/-- A **latent** for `p`: a finite mixture representation `p = ∑ᵥ λᵥ qᵥ`
(§0). The index type is bundled, so `Latent p` lives one universe up. -/
structure Latent (p : α × β → ℝ) where
  /-- The (finite) alphabet of the latent variable `V`. -/
  ι : Type
  /-- Finiteness of the latent alphabet. -/
  fin : Fintype ι
  /-- Decidable equality on the latent alphabet. -/
  dec : DecidableEq ι
  /-- The prior `λ`. -/
  prior : ι → ℝ
  /-- The components `qᵥ = P_{Z ∣ V = v}`. -/
  comp : ι → (α × β → ℝ)
  /-- `λ` is a probability law. -/
  prior_isPMF : IsPMF prior
  /-- Each component is a probability law. -/
  comp_isPMF : ∀ v, IsPMF (comp v)
  /-- The mixture reconstructs `p`. -/
  mixture : ∀ z, ∑ v, prior v * comp v z = p z

attribute [instance] Latent.fin Latent.dec

namespace Latent

variable {p : α × β → ℝ}

/-- A latent's index type is never empty: its prior is a probability law,
and an empty sum cannot be `1`. -/
instance nonempty_ι (V : Latent p) : Nonempty V.ι := by
  by_contra h
  letI : IsEmpty V.ι := not_nonempty_iff.mp h
  have htotal := V.prior_isPMF.total
  simp [mass] at htotal

/-- The joint law of `(V, Z)` on `ι × (α × β)`. -/
noncomputable def joint (V : Latent p) : V.ι × (α × β) → ℝ :=
  fun w => V.prior w.1 * V.comp w.1 w.2

lemma joint_isPMF (V : Latent p) : IsPMF V.joint := by
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

/-- The **score** `S_p(V) := I(X;Y ∣ V) + I(V;X ∣ Y) + I(V;Y ∣ X)` (§0). -/
noncomputable def score (V : Latent p) : ℝ :=
  condMI (fun w => w.2.1) (fun w => w.2.2) (fun w => w.1) V.joint
    + condMI (fun w => w.1) (fun w => w.2.1) (fun w => w.2.2) V.joint
    + condMI (fun w => w.1) (fun w => w.2.2) (fun w => w.2.1) V.joint

/-- The LessWrong deterministic-side expression, defined for every finite
latent (with no determinism assumption):
`I(X;Y | Γ) + H(Γ | X) + H(Γ | Y)`. -/
noncomputable def DScore (G : Latent p) : ℝ :=
  condMI
      (fun w : G.ι × (α × β) => w.2.1)
      (fun w => w.2.2)
      (fun w => w.1)
      G.joint
    + condH
      (fun w : G.ι × (α × β) => w.1)
      (fun w => w.2.1)
      G.joint
    + condH
      (fun w : G.ι × (α × β) => w.1)
      (fun w => w.2.2)
      G.joint

lemma score_nonneg (V : Latent p) : 0 ≤ V.score := by
  unfold score
  exact add_nonneg
    (add_nonneg
      (condMI_nonneg V.joint_isPMF (fun w => w.2.1) (fun w => w.2.2) (fun w => w.1))
      (condMI_nonneg V.joint_isPMF (fun w => w.1) (fun w => w.2.1) (fun w => w.2.2)))
    (condMI_nonneg V.joint_isPMF (fun w => w.1) (fun w => w.2.2) (fun w => w.2.1))

/-- A latent is **deterministic** when its components have pairwise disjoint
supports, i.e. `V = f(Z)` for a function `f` (§0). -/
def IsDet (V : Latent p) : Prop :=
  ∀ z, ∀ v v', V.prior v * V.comp v z ≠ 0 → V.prior v' * V.comp v' z ≠ 0 → v = v'

/-- The constant latent, witnessing `T p ≤ I(X;Y)` and, in particular,
nonemptiness of both index sets below. -/
noncomputable def const (hp : IsPMF p) : Latent p where
  ι := Unit
  fin := inferInstance
  dec := inferInstance
  prior := fun _ => 1
  comp := fun _ => p
  prior_isPMF := ⟨fun _ => zero_le_one, by simp [mass]⟩
  comp_isPMF := fun _ => hp
  mixture := by intro z; simp

lemma const_isDet (hp : IsPMF p) : (const hp).IsDet := by
  haveI : Subsingleton (const hp).ι := inferInstanceAs (Subsingleton Unit)
  intro z v v' _ _; exact Subsingleton.elim v v'

private lemma Hvar_const_joint_equiv {γ δ : Type*} [Fintype γ] [DecidableEq γ]
    [Fintype δ] [DecidableEq δ] (hp : IsPMF p) (e : γ ≃ δ) (f : α × β → γ) :
    Hvar (fun w : (const hp).ι × (α × β) => e (f w.2)) (const hp).joint =
      Hvar f p := by
  unfold Hvar
  have hpush_joint :
      push (fun w : (const hp).ι × (α × β) => e (f w.2)) (const hp).joint =
        push (fun z => e (f z)) p := by
    have hjoint : (const hp).joint = fun w => p w.2 := by
      funext w
      simp [joint, const]
    rw [hjoint]
    change push (fun w : Unit × (α × β) => e (f w.2))
        (fun w : Unit × (α × β) => p w.2) = push (fun z => e (f z)) p
    funext c
    simp only [push]
    simp_rw [Finset.sum_filter]
    rw [Fintype.sum_prod_type]
    simp
  rw [hpush_joint]
  change H (push (e ∘ f) p) = H (push f p)
  rw [← push_push f e p]
  let m := push f p
  change H (push e m) = H m
  have hpush : push e m = fun d => m (e.symm d) := by
    funext d
    rw [push]
    apply Finset.sum_eq_single (e.symm d)
    · intro b hb hne
      have heb : e b = d := (Finset.mem_filter.mp hb).2
      exact (hne (e.apply_eq_iff_eq_symm_apply.mp heb)).elim
    · intro hnot
      exact (hnot (by simp)).elim
  rw [hpush]
  unfold H mass
  rw [e.symm.sum_comp m]
  exact e.symm.sum_comp (fun a => m a * lg ((∑ b, m b) / m a))

/-- §0: the constant latent has score `I(X;Y)`. -/
lemma score_const (hp : IsPMF p) : (const hp).score = Ixy p := by
  have hId : Hvar (fun z : α × β => z) p = H p := by
    unfold Hvar
    apply congrArg H
    funext z
    rw [push]
    apply Finset.sum_eq_single z
    · intro b hb hne
      have hbz : b = z := (Finset.mem_filter.mp hb).2
      exact (hne hbz).elim
    · intro hnot
      exact (hnot (by simp)).elim
  have Hvar_const : Hvar (fun _ : α × β => ()) p = 0 := by
    have hsum : ∑ z, p z = 1 := by simpa [mass] using hp.total
    simp [Hvar, H, push, mass, hsum]
  have hXV :
      Hvar (fun w : (const hp).ι × (α × β) => (w.2.1, w.1)) (const hp).joint =
        H (mX p) := by
    calc
      _ = Hvar
          (fun w : (const hp).ι × (α × β) =>
            ((Equiv.prodPUnit α).symm : α ≃ α × Unit) w.2.1)
          (const hp).joint := by
            apply congrArg (fun k => Hvar k (const hp).joint)
            funext w
            rcases w with ⟨⟨⟩, ⟨x, y⟩⟩
            rfl
      _ = Hvar (fun z : α × β => z.1) p :=
        Hvar_const_joint_equiv hp
          ((Equiv.prodPUnit α).symm : α ≃ α × Unit) (fun z => z.1)
      _ = H (mX p) := rfl
  have hYV :
      Hvar (fun w : (const hp).ι × (α × β) => (w.2.2, w.1)) (const hp).joint =
        H (mY p) := by
    calc
      _ = Hvar
          (fun w : (const hp).ι × (α × β) =>
            ((Equiv.prodPUnit β).symm : β ≃ β × Unit) w.2.2)
          (const hp).joint := by
            apply congrArg (fun k => Hvar k (const hp).joint)
            funext w
            rcases w with ⟨⟨⟩, ⟨x, y⟩⟩
            rfl
      _ = Hvar (fun z : α × β => z.2) p :=
        Hvar_const_joint_equiv hp
          ((Equiv.prodPUnit β).symm : β ≃ β × Unit) (fun z => z.2)
      _ = H (mY p) := rfl
  have hXYV :
      Hvar (fun w : (const hp).ι × (α × β) => (w.2.1, w.2.2, w.1))
          (const hp).joint = H p := by
    calc
      _ = Hvar
          (fun w : (const hp).ι × (α × β) =>
            (Equiv.prodCongr (Equiv.refl α)
              ((Equiv.prodPUnit β).symm : β ≃ β × Unit)) w.2)
          (const hp).joint := by
            apply congrArg (fun k => Hvar k (const hp).joint)
            funext w
            rcases w with ⟨⟨⟩, ⟨x, y⟩⟩
            rfl
      _ = Hvar (fun z : α × β => z) p :=
        Hvar_const_joint_equiv hp
          (Equiv.prodCongr (Equiv.refl α)
            ((Equiv.prodPUnit β).symm : β ≃ β × Unit)) (fun z => z)
      _ = H p := hId
  have hV :
      Hvar (fun w : (const hp).ι × (α × β) => w.1) (const hp).joint = 0 := by
    calc
      _ = Hvar
          (fun w : (const hp).ι × (α × β) => (Equiv.refl Unit) ())
          (const hp).joint := by
            apply congrArg (fun k => Hvar k (const hp).joint)
            funext w
            rcases w with ⟨⟨⟩, ⟨x, y⟩⟩
            rfl
      _ = Hvar (fun _ : α × β => ()) p :=
        Hvar_const_joint_equiv hp (Equiv.refl Unit) (fun _ : α × β => ())
      _ = 0 := Hvar_const
  have hVY :
      Hvar (fun w : (const hp).ι × (α × β) => (w.1, w.2.2)) (const hp).joint =
        H (mY p) := by
    calc
      _ = Hvar
          (fun w : (const hp).ι × (α × β) =>
            ((Equiv.punitProd β).symm : β ≃ Unit × β) w.2.2)
          (const hp).joint := by
            apply congrArg (fun k => Hvar k (const hp).joint)
            funext w
            rcases w with ⟨⟨⟩, ⟨x, y⟩⟩
            rfl
      _ = Hvar (fun z : α × β => z.2) p :=
        Hvar_const_joint_equiv hp
          ((Equiv.punitProd β).symm : β ≃ Unit × β) (fun z => z.2)
      _ = H (mY p) := rfl
  have hXY :
      Hvar (fun w : (const hp).ι × (α × β) => (w.2.1, w.2.2))
          (const hp).joint = H p := by
    calc
      _ = Hvar
          (fun w : (const hp).ι × (α × β) => (Equiv.refl (α × β)) w.2)
          (const hp).joint := by
            apply congrArg (fun k => Hvar k (const hp).joint)
            funext w
            rcases w with ⟨u, ⟨x, y⟩⟩
            rfl
      _ = Hvar (fun z : α × β => z) p :=
        Hvar_const_joint_equiv hp (Equiv.refl (α × β)) (fun z => z)
      _ = H p := hId
  have hVXY :
      Hvar (fun w : (const hp).ι × (α × β) => (w.1, w.2.1, w.2.2))
          (const hp).joint = H p := by
    calc
      _ = Hvar
          (fun w : (const hp).ι × (α × β) =>
            ((Equiv.punitProd (α × β)).symm : (α × β) ≃ Unit × (α × β)) w.2)
          (const hp).joint := by
            apply congrArg (fun k => Hvar k (const hp).joint)
            funext w
            rcases w with ⟨⟨⟩, ⟨x, y⟩⟩
            rfl
      _ = Hvar (fun z : α × β => z) p :=
        Hvar_const_joint_equiv hp
          ((Equiv.punitProd (α × β)).symm : (α × β) ≃ Unit × (α × β)) (fun z => z)
      _ = H p := hId
  have hY :
      Hvar (fun w : (const hp).ι × (α × β) => w.2.2) (const hp).joint =
        H (mY p) := by
    calc
      _ = Hvar
          (fun w : (const hp).ι × (α × β) => (Equiv.refl β) w.2.2)
          (const hp).joint := rfl
      _ = Hvar (fun z : α × β => z.2) p :=
        Hvar_const_joint_equiv hp (Equiv.refl β) (fun z => z.2)
      _ = H (mY p) := rfl
  have hVX :
      Hvar (fun w : (const hp).ι × (α × β) => (w.1, w.2.1)) (const hp).joint =
        H (mX p) := by
    calc
      _ = Hvar
          (fun w : (const hp).ι × (α × β) =>
            ((Equiv.punitProd α).symm : α ≃ Unit × α) w.2.1)
          (const hp).joint := by
            apply congrArg (fun k => Hvar k (const hp).joint)
            funext w
            rcases w with ⟨⟨⟩, ⟨x, y⟩⟩
            rfl
      _ = Hvar (fun z : α × β => z.1) p :=
        Hvar_const_joint_equiv hp
          ((Equiv.punitProd α).symm : α ≃ Unit × α) (fun z => z.1)
      _ = H (mX p) := rfl
  have hYX :
      Hvar (fun w : (const hp).ι × (α × β) => (w.2.2, w.2.1))
          (const hp).joint = H p := by
    calc
      _ = Hvar
          (fun w : (const hp).ι × (α × β) => (Equiv.prodComm α β) w.2)
          (const hp).joint := by
            apply congrArg (fun k => Hvar k (const hp).joint)
            funext w
            rcases w with ⟨u, ⟨x, y⟩⟩
            rfl
      _ = Hvar (fun z : α × β => z) p :=
        Hvar_const_joint_equiv hp (Equiv.prodComm α β) (fun z => z)
      _ = H p := hId
  have hVYX :
      Hvar (fun w : (const hp).ι × (α × β) => (w.1, w.2.2, w.2.1))
          (const hp).joint = H p := by
    calc
      _ = Hvar
          (fun w : (const hp).ι × (α × β) =>
            ((Equiv.prodComm α β).trans
              ((Equiv.punitProd (β × α)).symm : (β × α) ≃ Unit × (β × α))) w.2)
          (const hp).joint := by
            apply congrArg (fun k => Hvar k (const hp).joint)
            funext w
            rcases w with ⟨⟨⟩, ⟨x, y⟩⟩
            rfl
      _ = Hvar (fun z : α × β => z) p :=
        Hvar_const_joint_equiv hp
          ((Equiv.prodComm α β).trans
            ((Equiv.punitProd (β × α)).symm : (β × α) ≃ Unit × (β × α))) (fun z => z)
      _ = H p := hId
  have hX :
      Hvar (fun w : (const hp).ι × (α × β) => w.2.1) (const hp).joint =
        H (mX p) := by
    calc
      _ = Hvar
          (fun w : (const hp).ι × (α × β) => (Equiv.refl α) w.2.1)
          (const hp).joint := rfl
      _ = Hvar (fun z : α × β => z.1) p :=
        Hvar_const_joint_equiv hp (Equiv.refl α) (fun z => z.1)
      _ = H (mX p) := rfl
  unfold score condMI
  rw [hXV, hYV, hXYV, hV, hVY, hXY, hVXY, hY, hVX, hYX, hVYX, hX]
  unfold Ixy
  ring

end Latent

/-! ### The two functionals

`τ` ranges over all finite latents; `T` over the deterministic ones. Both are
`⨅` over a bundled index; when `p` is not a law the index type may be empty
and the value is Lean's junk `sInf ∅ = 0`, so every substantive statement
carries `IsPMF p`. -/

/-- `τ(p) := inf over finite latents `V` of `S_p(V)` (Main Theorem). -/
noncomputable def tau (p : α × β → ℝ) : ℝ := ⨅ V : Latent p, V.score

/-- `T(p) := inf over deterministic `A = f(X,Y)` of `S_p(A)` (Main Theorem). -/
noncomputable def T (p : α × β → ℝ) : ℝ := ⨅ V : {V : Latent p // V.IsDet}, V.1.score

/-- The deterministic LessWrong expression
`I(X;Y | Γ) + H(Γ | X) + H(Γ | Y)`. -/
noncomputable def detScore {γ : Type*} [Fintype γ] [DecidableEq γ]
    (p : α × β → ℝ) (Γ : α × β → γ) : ℝ :=
  condMI (fun z : α × β => z.1) (fun z => z.2) Γ p +
    condH Γ (fun z : α × β => z.1) p +
    condH Γ (fun z : α × β => z.2) p

/-- Conditional mutual information as a difference of conditional
entropies. -/
theorem condMI_eq_condH_sub_pair
    {Ω γ δ ε : Type*} [Fintype Ω]
    [Fintype γ] [DecidableEq γ]
    [Fintype δ] [DecidableEq δ]
    [Fintype ε] [DecidableEq ε]
    {m : Ω → ℝ} (hm : IsPMF m)
    (f : Ω → γ) (g : Ω → δ) (h : Ω → ε) :
    condMI f g h m =
      condH f h m - condH f (fun ω => (g ω, h ω)) m := by
  have hassoc :
      Hvar (fun ω : Ω => (f ω, (g ω, h ω))) m =
        Hvar (fun ω : Ω => (f ω, g ω, h ω)) m := by
    simpa using Hvar_equiv hm (fun ω : Ω => (f ω, g ω, h ω))
      (Equiv.prodAssoc γ δ ε)
  unfold condMI condH
  rw [hassoc]
  ring

/-- A deterministic function has zero conditional entropy given its input. -/
theorem condH_function_given_pair_zero
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    {p : α × β → ℝ} (hp : IsPMF p) (Γ : α × β → γ) :
    condH Γ (fun z : α × β => z) p = 0 := by
  let graph : α × β → γ × (α × β) := fun z => (Γ z, z)
  have hforward : Hvar graph p ≤ Hvar (fun z : α × β => z) p := by
    simpa [graph, Function.comp_def] using
      Hvar_comp_le hp (fun z : α × β => z) graph
  have hback : Hvar (fun z : α × β => z) p ≤ Hvar graph p := by
    simpa [graph, Function.comp_def] using
      Hvar_comp_le hp graph Prod.snd
  unfold condH
  change Hvar graph p - Hvar (fun z : α × β => z) p = 0
  linarith

theorem condMI_code_X_given_Y
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    {p : α × β → ℝ} (hp : IsPMF p) (Γ : α × β → γ) :
    condMI Γ (fun z : α × β => z.1) (fun z => z.2) p =
      condH Γ (fun z : α × β => z.2) p := by
  rw [condMI_eq_condH_sub_pair hp]
  have hz := condH_function_given_pair_zero hp Γ
  have hz' : condH Γ (fun z : α × β => (z.1, z.2)) p = 0 := by
    simpa using hz
  rw [hz', sub_zero]

theorem condMI_code_Y_given_X
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    {p : α × β → ℝ} (hp : IsPMF p) (Γ : α × β → γ) :
    condMI Γ (fun z : α × β => z.2) (fun z => z.1) p =
      condH Γ (fun z : α × β => z.1) p := by
  rw [condMI_eq_condH_sub_pair hp]
  have hz := condH_function_given_pair_zero hp Γ
  have hz' : condH Γ (fun z : α × β => (z.2, z.1)) p = 0 := by
    unfold condH at hz ⊢
    have hswap :
        Hvar (fun z : α × β => (Γ z, (z.2, z.1))) p =
          Hvar (fun z : α × β => (Γ z, (z.1, z.2))) p := by
      let e : γ × (α × β) ≃ γ × (β × α) :=
        Equiv.prodCongr (Equiv.refl γ) (Equiv.prodComm α β)
      have he : (fun z : α × β => (Γ z, (z.2, z.1))) =
          fun z => e (Γ z, (z.1, z.2)) := by
        funext z
        rcases z with ⟨x, y⟩
        rfl
      rw [he]
      exact Hvar_equiv hp (fun z : α × β => (Γ z, (z.1, z.2))) e
    have hbase : Hvar (fun z : α × β => (z.2, z.1)) p =
        Hvar (fun z : α × β => (z.1, z.2)) p := by
      have he : (fun z : α × β => (z.2, z.1)) =
          fun z => (Equiv.prodComm α β) (z.1, z.2) := by
        funext z
        rcases z with ⟨x, y⟩
        rfl
      rw [he]
      exact Hvar_equiv hp (fun z : α × β => (z.1, z.2))
        (Equiv.prodComm α β)
    rw [hswap, hbase]
    exact hz
  rw [hz', sub_zero]

/-- For every finite latent, the LessWrong expression differs from the stoch_to_det
score by exactly twice the residual nondeterminism `H(Γ | X,Y)`. -/
theorem Latent.DScore_eq_score_add_two_condH_pair
    {p : α × β → ℝ} (G : Latent p) :
    G.DScore =
      G.score +
        2 * condH
          (fun w : G.ι × (α × β) => w.1)
          (fun w => w.2)
          G.joint := by
  have hGX := condMI_eq_condH_sub_pair G.joint_isPMF
    (fun w : G.ι × (α × β) => w.1)
    (fun w => w.2.1) (fun w => w.2.2)
  have hGY := condMI_eq_condH_sub_pair G.joint_isPMF
    (fun w : G.ι × (α × β) => w.1)
    (fun w => w.2.2) (fun w => w.2.1)
  have hswap :
      condH
          (fun w : G.ι × (α × β) => w.1)
          (fun w => (w.2.2, w.2.1))
          G.joint =
        condH
          (fun w : G.ι × (α × β) => w.1)
          (fun w => w.2)
          G.joint := by
    have htop :
        Hvar
            (fun w : G.ι × (α × β) => (w.1, (w.2.2, w.2.1)))
            G.joint =
          Hvar (fun w : G.ι × (α × β) => (w.1, w.2)) G.joint := by
      let e : G.ι × (β × α) ≃ G.ι × (α × β) :=
        Equiv.prodCongr (Equiv.refl G.ι) (Equiv.prodComm β α)
      simpa [e] using (Hvar_equiv G.joint_isPMF
        (fun w : G.ι × (α × β) => (w.1, (w.2.2, w.2.1))) e).symm
    have hbase :
        Hvar (fun w : G.ι × (α × β) => (w.2.2, w.2.1)) G.joint =
          Hvar (fun w : G.ι × (α × β) => w.2) G.joint := by
      simpa using (Hvar_equiv G.joint_isPMF
        (fun w : G.ι × (α × β) => (w.2.2, w.2.1))
        (Equiv.prodComm β α)).symm
    unfold condH
    rw [htop, hbase]
  unfold Latent.DScore Latent.score
  rw [hGX, hGY, hswap]
  ring

lemma tau_nonneg (p : α × β → ℝ) : 0 ≤ tau p := by
  unfold tau
  exact Real.iInf_nonneg fun V => V.score_nonneg

/-- The infimum `tau p` is below the score of every finite latent. -/
lemma tau_le_score {p : α × β → ℝ} (V : Latent p) : tau p ≤ V.score := by
  unfold tau
  have hb : BddBelow (Set.range fun W : Latent p => W.score) :=
    ⟨0, by
      rintro _ ⟨W, rfl⟩
      exact W.score_nonneg⟩
  exact ciInf_le hb V

lemma T_nonneg (p : α × β → ℝ) : 0 ≤ T p := by
  unfold T
  exact Real.iInf_nonneg fun V => V.1.score_nonneg

/-- §0: `τ ≤ T ≤ I(X;Y)`. -/
lemma tau_le_T {p : α × β → ℝ} (hp : IsPMF p) : tau p ≤ T p := by
  let V0 : {V : Latent p // V.IsDet} := ⟨Latent.const hp, Latent.const_isDet hp⟩
  letI : Nonempty {V : Latent p // V.IsDet} := ⟨V0⟩
  unfold tau T
  refine le_ciInf fun V => ?_
  have hb : BddBelow (Set.range fun W : Latent p => W.score) :=
    ⟨0, by rintro _ ⟨W, rfl⟩; exact W.score_nonneg⟩
  exact ciInf_le hb V.1

lemma T_le_Ixy {p : α × β → ℝ} (hp : IsPMF p) : T p ≤ Ixy p := by
  rw [← Latent.score_const hp]
  unfold T
  have hb : BddBelow (Set.range fun W : {W : Latent p // W.IsDet} => W.1.score) :=
    ⟨0, by rintro _ ⟨W, rfl⟩; exact W.1.score_nonneg⟩
  exact ciInf_le_of_le hb ⟨Latent.const hp, Latent.const_isDet hp⟩ le_rfl

/-- The score of any single deterministic latent bounds `T` from above. This is
how §12 uses `T`: Corollary 4.4 exhibits one good seed. -/
lemma T_le_score {p : α × β → ℝ} (V : Latent p) (hV : V.IsDet) : T p ≤ V.score := by
  unfold T
  have hb : BddBelow (Set.range fun W : {W : Latent p // W.IsDet} => W.1.score) :=
    ⟨0, by rintro _ ⟨W, rfl⟩; exact W.1.score_nonneg⟩
  exact ciInf_le_of_le hb ⟨V, hV⟩ le_rfl

end stoch_to_det
