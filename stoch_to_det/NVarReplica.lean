import stoch_to_det.NVarEnvelope

/-!
# Posterior replicas for an arbitrary finite n-variable latent

This file isolates the finite probability bookkeeping used by the
alphabet-free multivariate argument.  If `V : NLatent p`, `replicaLaw V` is
the joint law of `(C₀,C₁,X)` obtained by drawing `X ~ p` and then drawing
`C₀,C₁` conditionally independently from the posterior of `V` given `X`.

Nothing in this file uses optimality or coordinate structure.
-/

namespace stoch_to_det

open Finset

variable {Omega : Type} [Fintype Omega] [DecidableEq Omega]
variable {p : Omega -> Real}

namespace FiniteInfo

/-- Conditional mutual information is the sum of the (homogeneous) mutual
informations of its conditioning fibres. -/
lemma condMI_eq_sum_MI_fibers
    {A Gamma Delta K : Type*} [Fintype A] [Fintype Gamma] [Fintype Delta]
    [Fintype K] [DecidableEq Gamma] [DecidableEq Delta] [DecidableEq K]
    {m : A -> Real} (hm : IsPMF m) (f : A -> Gamma) (g : A -> Delta)
    (h : A -> K) :
    condMI f g h m =
      ∑ k, MI f g (fun a => if h a = k then m a else 0) := by
  let mh : K -> A -> Real := fun k a => if h a = k then m a else 0
  have hF := Hvar_pair_eq_sum_fibers hm f h
  have hG := Hvar_pair_eq_sum_fibers hm g h
  have hFG := Hvar_pair_eq_sum_fibers hm (fun a => (f a, g a)) h
  change Hvar (fun a => (f a, h a)) m =
    Hvar h m + ∑ k, H (push f (mh k)) at hF
  change Hvar (fun a => (g a, h a)) m =
    Hvar h m + ∑ k, H (push g (mh k)) at hG
  change Hvar (fun a => ((f a, g a), h a)) m =
    Hvar h m + ∑ k, H (push (fun a => (f a, g a)) (mh k)) at hFG
  have hAssoc : Hvar (fun a => (f a, g a, h a)) m =
      Hvar (fun a => ((f a, g a), h a)) m := by
    simpa using Hvar_equiv hm (fun a => ((f a, g a), h a))
      (Equiv.prodAssoc Gamma Delta K)
  unfold condMI
  rw [hF, hG, hAssoc, hFG]
  simp only [MI, Hvar, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

lemma push_id {A : Type*} [Fintype A] [DecidableEq A] (m : A -> Real) :
    push (fun a => a) m = m := by
  funext a
  unfold push
  apply Finset.sum_eq_single a
  · intro b hb hba
    exact (hba (Finset.mem_filter.mp hb).2).elim
  · intro ha
    exact (ha (by simp)).elim

/-- Reindexing an invariant finite law does not change any pushforward. -/
lemma push_comp_equiv_eq_of_invariant
    {A Gamma : Type*} [Fintype A] [Fintype Gamma] [DecidableEq Gamma]
    (m : A -> Real) (e : A ≃ A) (hm : forall a, m (e a) = m a)
    (f : A -> Gamma) : push (f ∘ e) m = push f m := by
  funext y
  unfold push
  simp only [Finset.sum_filter, Function.comp_apply]
  calc
    (∑ a, if f (e a) = y then m a else 0) =
        ∑ a, if f (e a) = y then m (e a) else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hm a]
    _ = ∑ a, if f a = y then m a else 0 :=
      e.sum_comp (fun a => if f a = y then m a else 0)

lemma condH_comp_equiv_eq_of_invariant
    {A Gamma K : Type*} [Fintype A] [Fintype Gamma] [Fintype K]
    [DecidableEq Gamma] [DecidableEq K]
    (m : A -> Real) (e : A ≃ A) (hm : forall a, m (e a) = m a)
    (f : A -> Gamma) (h : A -> K) :
    condH (f ∘ e) (h ∘ e) m = condH f h m := by
  have hpair := push_comp_equiv_eq_of_invariant m e hm
    (fun a => (f a, h a))
  have hh := push_comp_equiv_eq_of_invariant m e hm h
  have hpair' : push (fun a => ((f ∘ e) a, (h ∘ e) a)) m =
      push (fun a => (f a, h a)) m := by
    change push ((fun a => (f a, h a)) ∘ e) m = _
    exact hpair
  unfold condH Hvar
  rw [hpair', hh]

lemma condMI_comp_equiv_eq_of_invariant
    {A Gamma Delta K : Type*} [Fintype A] [Fintype Gamma] [Fintype Delta]
    [Fintype K] [DecidableEq Gamma] [DecidableEq Delta] [DecidableEq K]
    (m : A -> Real) (e : A ≃ A) (hm : forall a, m (e a) = m a)
    (f : A -> Gamma) (g : A -> Delta) (h : A -> K) :
    condMI (f ∘ e) (g ∘ e) (h ∘ e) m = condMI f g h m := by
  have hfh := push_comp_equiv_eq_of_invariant m e hm (fun a => (f a, h a))
  have hgh := push_comp_equiv_eq_of_invariant m e hm (fun a => (g a, h a))
  have hfgh := push_comp_equiv_eq_of_invariant m e hm
    (fun a => (f a, g a, h a))
  have hh := push_comp_equiv_eq_of_invariant m e hm h
  have hfh' : push (fun a => ((f ∘ e) a, (h ∘ e) a)) m =
      push (fun a => (f a, h a)) m := by
    change push ((fun a => (f a, h a)) ∘ e) m = _
    exact hfh
  have hgh' : push (fun a => ((g ∘ e) a, (h ∘ e) a)) m =
      push (fun a => (g a, h a)) m := by
    change push ((fun a => (g a, h a)) ∘ e) m = _
    exact hgh
  have hfgh' : push (fun a => ((f ∘ e) a, (g ∘ e) a, (h ∘ e) a)) m =
      push (fun a => (f a, g a, h a)) m := by
    change push ((fun a => (f a, g a, h a)) ∘ e) m = _
    exact hfgh
  unfold condMI Hvar
  rw [hfh', hgh', hfgh', hh]

/-- Mutual information depends only on the joint pushforward of its two
arguments. -/
lemma MI_eq_of_pair_push_eq
    {A A' Gamma Delta : Type*} [Fintype A] [Fintype A'] [Fintype Gamma]
    [Fintype Delta] [DecidableEq Gamma] [DecidableEq Delta]
    (m : A -> Real) (n : A' -> Real) (f : A -> Gamma) (g : A -> Delta)
    (f' : A' -> Gamma) (g' : A' -> Delta)
    (hpair : push (fun a => (f a, g a)) m =
      push (fun a => (f' a, g' a)) n) :
    MI f g m = MI f' g' n := by
  have hf : push f m = push f' n := by
    calc
      push f m = push Prod.fst (push (fun a => (f a, g a)) m) := by
        symm
        simpa [Function.comp_def] using
          (push_push (fun a => (f a, g a)) Prod.fst m)
      _ = push Prod.fst (push (fun a => (f' a, g' a)) n) := by rw [hpair]
      _ = push f' n := by
        simpa [Function.comp_def] using
          (push_push (fun a => (f' a, g' a)) Prod.fst n)
  have hg : push g m = push g' n := by
    calc
      push g m = push Prod.snd (push (fun a => (f a, g a)) m) := by
        symm
        simpa [Function.comp_def] using
          (push_push (fun a => (f a, g a)) Prod.snd m)
      _ = push Prod.snd (push (fun a => (f' a, g' a)) n) := by rw [hpair]
      _ = push g' n := by
        simpa [Function.comp_def] using
          (push_push (fun a => (f' a, g' a)) Prod.snd n)
  unfold MI Hvar
  rw [hf, hg, hpair]

lemma condH_eq_of_pair_push_eq
    {A A' Gamma Delta : Type*} [Fintype A] [Fintype A'] [Fintype Gamma]
    [Fintype Delta] [DecidableEq Gamma] [DecidableEq Delta]
    (m : A -> Real) (n : A' -> Real) (f : A -> Gamma) (g : A -> Delta)
    (f' : A' -> Gamma) (g' : A' -> Delta)
    (hpair : push (fun a => (f a, g a)) m =
      push (fun a => (f' a, g' a)) n) :
    condH f g m = condH f' g' n := by
  have hg : push g m = push g' n := by
    calc
      push g m = push Prod.snd (push (fun a => (f a, g a)) m) := by
        symm
        simpa [Function.comp_def] using
          (push_push (fun a => (f a, g a)) Prod.snd m)
      _ = push Prod.snd (push (fun a => (f' a, g' a)) n) := by rw [hpair]
      _ = push g' n := by
        simpa [Function.comp_def] using
          (push_push (fun a => (f' a, g' a)) Prod.snd n)
  unfold condH Hvar
  rw [hpair, hg]

lemma condMI_eq_of_triple_push_eq
    {A A' Gamma Delta K : Type*} [Fintype A] [Fintype A'] [Fintype Gamma]
    [Fintype Delta] [Fintype K] [DecidableEq Gamma] [DecidableEq Delta]
    [DecidableEq K]
    (m : A -> Real) (n : A' -> Real) (f : A -> Gamma) (g : A -> Delta)
    (h : A -> K) (f' : A' -> Gamma) (g' : A' -> Delta) (h' : A' -> K)
    (htriple : push (fun a => (f a, g a, h a)) m =
      push (fun a => (f' a, g' a, h' a)) n) :
    condMI f g h m = condMI f' g' h' n := by
  let pfh : Gamma × Delta × K -> Gamma × K := fun t => (t.1, t.2.2)
  let pgh : Gamma × Delta × K -> Delta × K := fun t => (t.2.1, t.2.2)
  let ph : Gamma × Delta × K -> K := fun t => t.2.2
  have hfh : push (fun a => (f a, h a)) m =
      push (fun a => (f' a, h' a)) n := by
    calc
      push (fun a => (f a, h a)) m =
          push pfh (push (fun a => (f a, g a, h a)) m) := by
            symm
            simpa [pfh, Function.comp_def] using
              (push_push (fun a => (f a, g a, h a)) pfh m)
      _ = push pfh (push (fun a => (f' a, g' a, h' a)) n) := by rw [htriple]
      _ = push (fun a => (f' a, h' a)) n := by
            simpa [pfh, Function.comp_def] using
              (push_push (fun a => (f' a, g' a, h' a)) pfh n)
  have hgh : push (fun a => (g a, h a)) m =
      push (fun a => (g' a, h' a)) n := by
    calc
      push (fun a => (g a, h a)) m =
          push pgh (push (fun a => (f a, g a, h a)) m) := by
            symm
            simpa [pgh, Function.comp_def] using
              (push_push (fun a => (f a, g a, h a)) pgh m)
      _ = push pgh (push (fun a => (f' a, g' a, h' a)) n) := by rw [htriple]
      _ = push (fun a => (g' a, h' a)) n := by
            simpa [pgh, Function.comp_def] using
              (push_push (fun a => (f' a, g' a, h' a)) pgh n)
  have hh : push h m = push h' n := by
    calc
      push h m = push ph (push (fun a => (f a, g a, h a)) m) := by
        symm
        simpa [ph, Function.comp_def] using
          (push_push (fun a => (f a, g a, h a)) ph m)
      _ = push ph (push (fun a => (f' a, g' a, h' a)) n) := by rw [htriple]
      _ = push h' n := by
        simpa [ph, Function.comp_def] using
          (push_push (fun a => (f' a, g' a, h' a)) ph n)
  unfold condMI Hvar
  rw [hfh, hgh, htriple, hh]

lemma condMI_comm
    {A Gamma Delta K : Type*} [Fintype A] [Fintype Gamma] [Fintype Delta]
    [Fintype K] [DecidableEq Gamma] [DecidableEq Delta] [DecidableEq K]
    {m : A -> Real} (hm : IsPMF m) (f : A -> Gamma) (g : A -> Delta)
    (h : A -> K) : condMI f g h m = condMI g f h m := by
  let e : Gamma × Delta × K ≃ Delta × Gamma × K :=
    { toFun := fun t => (t.2.1, t.1, t.2.2)
      invFun := fun t => (t.2.1, t.1, t.2.2)
      left_inv := by rintro ⟨x, y, k⟩; rfl
      right_inv := by rintro ⟨y, x, k⟩; rfl }
  have htrip : Hvar (fun a => (g a, f a, h a)) m =
      Hvar (fun a => (f a, g a, h a)) m := by
    simpa [e] using Hvar_equiv hm (fun a => (f a, g a, h a)) e
  unfold condMI
  rw [htrip]
  ring

lemma MI_equiv_left
    {A Gamma Gamma' Delta : Type*} [Fintype A] [Fintype Gamma]
    [Fintype Gamma'] [Fintype Delta] [DecidableEq Gamma] [DecidableEq Gamma']
    [DecidableEq Delta] {m : A -> Real} (hm : IsPMF m) (f : A -> Gamma)
    (e : Gamma ≃ Gamma') (g : A -> Delta) :
    MI (fun a => e (f a)) g m = MI f g m := by
  have hf := Hvar_equiv hm f e
  have hfg := Hvar_equiv hm (fun a => (f a, g a))
    (Equiv.prodCongr e (Equiv.refl Delta))
  change Hvar (fun a => (e (f a), g a)) m =
    Hvar (fun a => (f a, g a)) m at hfg
  unfold MI
  rw [hf, hfg]

lemma condMI_eq_MI_pair_sub
    {A Gamma Delta K : Type*} [Fintype A] [Fintype Gamma] [Fintype Delta]
    [Fintype K] [DecidableEq Gamma] [DecidableEq Delta] [DecidableEq K]
    {m : A -> Real} (hm : IsPMF m) (f : A -> Gamma) (g : A -> Delta)
    (h : A -> K) :
    condMI f g h m = MI (fun a => (h a, f a)) g m - MI h g m := by
  have hchain := MI_pair_left hm h f g
  linarith

lemma condMI_pair_left
    {A Gamma Delta E K : Type*} [Fintype A] [Fintype Gamma] [Fintype Delta]
    [Fintype E] [Fintype K] [DecidableEq Gamma] [DecidableEq Delta]
    [DecidableEq E] [DecidableEq K]
    {m : A -> Real} (hm : IsPMF m) (f : A -> Gamma) (g : A -> Delta)
    (k : A -> E) (h : A -> K) :
    condMI (fun a => (f a, g a)) k h m =
      condMI f k h m + condMI g k (fun a => (h a, f a)) m := by
  have hleft := condMI_eq_MI_pair_sub hm (fun a => (f a, g a)) k h
  have hfirst := condMI_eq_MI_pair_sub hm f k h
  have hsecond := condMI_eq_MI_pair_sub hm g k (fun a => (h a, f a))
  have hassoc := MI_equiv_left hm (fun a => ((h a, f a), g a))
    (Equiv.prodAssoc K Gamma Delta) k
  change MI (fun a => (h a, f a, g a)) k m =
    MI (fun a => ((h a, f a), g a)) k m at hassoc
  linarith

lemma condMI_pair_right
    {A Gamma Delta E K : Type*} [Fintype A] [Fintype Gamma] [Fintype Delta]
    [Fintype E] [Fintype K] [DecidableEq Gamma] [DecidableEq Delta]
    [DecidableEq E] [DecidableEq K]
    {m : A -> Real} (hm : IsPMF m) (k : A -> E) (f : A -> Gamma)
    (g : A -> Delta) (h : A -> K) :
    condMI k (fun a => (f a, g a)) h m =
      condMI k f h m + condMI k g (fun a => (h a, f a)) m := by
  rw [condMI_comm hm k (fun a => (f a, g a)) h,
    condMI_pair_left hm f g k h,
    condMI_comm hm f k h,
    condMI_comm hm g k (fun a => (h a, f a))]

lemma condMI_equiv_cond
    {A Gamma Delta K K' : Type*} [Fintype A] [Fintype Gamma] [Fintype Delta]
    [Fintype K] [Fintype K'] [DecidableEq Gamma] [DecidableEq Delta]
    [DecidableEq K] [DecidableEq K']
    {m : A -> Real} (hm : IsPMF m) (f : A -> Gamma) (g : A -> Delta)
    (h : A -> K) (e : K ≃ K') :
    condMI f g (fun a => e (h a)) m = condMI f g h m := by
  have hfh := Hvar_equiv hm (fun a => (f a, h a))
    (Equiv.prodCongr (Equiv.refl Gamma) e)
  have hgh := Hvar_equiv hm (fun a => (g a, h a))
    (Equiv.prodCongr (Equiv.refl Delta) e)
  have htrip := Hvar_equiv hm (fun a => (f a, g a, h a))
    (Equiv.prodCongr (Equiv.refl Gamma) (Equiv.prodCongr (Equiv.refl Delta) e))
  have hh := Hvar_equiv hm h e
  change Hvar (fun a => (f a, e (h a))) m = Hvar (fun a => (f a, h a)) m at hfh
  change Hvar (fun a => (g a, e (h a))) m = Hvar (fun a => (g a, h a)) m at hgh
  change Hvar (fun a => (f a, g a, e (h a))) m =
    Hvar (fun a => (f a, g a, h a)) m at htrip
  unfold condMI
  rw [hfh, hgh, htrip, hh]

lemma condH_equiv_cond
    {A Gamma K K' : Type*} [Fintype A] [Fintype Gamma] [Fintype K]
    [Fintype K'] [DecidableEq Gamma] [DecidableEq K] [DecidableEq K']
    {m : A -> Real} (hm : IsPMF m) (f : A -> Gamma) (h : A -> K)
    (e : K ≃ K') :
    condH f (fun a => e (h a)) m = condH f h m := by
  have hfh := Hvar_equiv hm (fun a => (f a, h a))
    (Equiv.prodCongr (Equiv.refl Gamma) e)
  have hh := Hvar_equiv hm h e
  change Hvar (fun a => (f a, e (h a))) m = Hvar (fun a => (f a, h a)) m at hfh
  unfold condH
  rw [hfh, hh]

lemma condMI_comp_right_eq_of_injective
    {A Gamma Delta Delta' K : Type*} [Fintype A] [Fintype Gamma]
    [Fintype Delta] [Fintype Delta'] [Fintype K] [DecidableEq Gamma]
    [DecidableEq Delta] [DecidableEq Delta'] [DecidableEq K]
    {m : A -> Real} (hm : IsPMF m) (f : A -> Gamma) (g : A -> Delta)
    (h : A -> K) (u : Delta -> Delta') (hu : Function.Injective u) :
    condMI f (fun a => u (g a)) h m = condMI f g h m := by
  have hA : Nonempty A := by
    by_contra hne
    letI : IsEmpty A := not_nonempty_iff.mp hne
    have htotal := hm.total
    simp [mass] at htotal
  letI : Nonempty Delta := ⟨g (Classical.choice hA)⟩
  obtain ⟨v, huv⟩ := hu.hasLeftInverse
  have hgh := Hvar_eq_of_leftInverse hm (fun a => (g a, h a))
    (fun t => (u t.1, t.2)) (fun t => (v t.1, t.2)) (by
      intro t
      simp [huv t.1])
  have hfgh := Hvar_eq_of_leftInverse hm (fun a => (f a, g a, h a))
    (fun t => (t.1, u t.2.1, t.2.2))
    (fun t => (t.1, v t.2.1, t.2.2)) (by
      intro t
      simp [huv t.2.1])
  change Hvar (fun a => (u (g a), h a)) m = Hvar (fun a => (g a, h a)) m at hgh
  change Hvar (fun a => (f a, u (g a), h a)) m =
    Hvar (fun a => (f a, g a, h a)) m at hfgh
  unfold condMI
  change Hvar (fun a => (f a, h a)) m +
      Hvar (fun a => (u (g a), h a)) m -
      Hvar (fun a => (f a, u (g a), h a)) m - Hvar h m = _
  rw [hgh, hfgh]

lemma condMI_comp_left_eq_of_injective
    {A Gamma Gamma' Delta K : Type*} [Fintype A] [Fintype Gamma]
    [Fintype Gamma'] [Fintype Delta] [Fintype K] [DecidableEq Gamma]
    [DecidableEq Gamma'] [DecidableEq Delta] [DecidableEq K]
    {m : A -> Real} (hm : IsPMF m) (f : A -> Gamma) (g : A -> Delta)
    (h : A -> K) (u : Gamma -> Gamma') (hu : Function.Injective u) :
    condMI (fun a => u (f a)) g h m = condMI f g h m := by
  rw [condMI_comm hm (fun a => u (f a)) g h,
    condMI_comp_right_eq_of_injective hm g f h u hu,
    condMI_comm hm g f h]

lemma condMI_comp_cond_eq_of_injective
    {A Gamma Delta K K' : Type*} [Fintype A] [Fintype Gamma]
    [Fintype Delta] [Fintype K] [Fintype K'] [DecidableEq Gamma]
    [DecidableEq Delta] [DecidableEq K] [DecidableEq K']
    {m : A -> Real} (hm : IsPMF m) (f : A -> Gamma) (g : A -> Delta)
    (h : A -> K) (u : K -> K') (hu : Function.Injective u) :
    condMI f g (fun a => u (h a)) m = condMI f g h m := by
  have hA : Nonempty A := by
    by_contra hne
    letI : IsEmpty A := not_nonempty_iff.mp hne
    have htotal := hm.total
    simp [mass] at htotal
  letI : Nonempty K := ⟨h (Classical.choice hA)⟩
  obtain ⟨v, huv⟩ := hu.hasLeftInverse
  have hh := Hvar_eq_of_leftInverse hm h u v huv
  have hfh := Hvar_eq_of_leftInverse hm (fun a => (f a, h a))
    (fun t => (t.1, u t.2)) (fun t => (t.1, v t.2)) (by
      intro t
      simp [huv t.2])
  have hgh := Hvar_eq_of_leftInverse hm (fun a => (g a, h a))
    (fun t => (t.1, u t.2)) (fun t => (t.1, v t.2)) (by
      intro t
      simp [huv t.2])
  have hfgh := Hvar_eq_of_leftInverse hm (fun a => (f a, g a, h a))
    (fun t => (t.1, t.2.1, u t.2.2))
    (fun t => (t.1, t.2.1, v t.2.2)) (by
      intro t
      simp [huv t.2.2])
  change Hvar (fun a => u (h a)) m = Hvar h m at hh
  change Hvar (fun a => (f a, u (h a))) m =
    Hvar (fun a => (f a, h a)) m at hfh
  change Hvar (fun a => (g a, u (h a))) m =
    Hvar (fun a => (g a, h a)) m at hgh
  change Hvar (fun a => (f a, g a, u (h a))) m =
    Hvar (fun a => (f a, g a, h a)) m at hfgh
  unfold condMI
  rw [hh, hfh, hgh, hfgh]

lemma condH_comp_left_eq_of_injective
    {A Gamma Gamma' K : Type*} [Fintype A] [Fintype Gamma]
    [Fintype Gamma'] [Fintype K] [DecidableEq Gamma] [DecidableEq Gamma']
    [DecidableEq K] {m : A -> Real} (hm : IsPMF m) (f : A -> Gamma)
    (h : A -> K) (u : Gamma -> Gamma') (hu : Function.Injective u) :
    condH (fun a => u (f a)) h m = condH f h m := by
  have hA : Nonempty A := by
    by_contra hne
    letI : IsEmpty A := not_nonempty_iff.mp hne
    have htotal := hm.total
    simp [mass] at htotal
  letI : Nonempty Gamma := ⟨f (Classical.choice hA)⟩
  obtain ⟨v, huv⟩ := hu.hasLeftInverse
  have hfh := Hvar_eq_of_leftInverse hm (fun a => (f a, h a))
    (fun t => (u t.1, t.2)) (fun t => (v t.1, t.2)) (by
      intro t
      simp [huv t.1])
  change Hvar (fun a => (u (f a), h a)) m =
    Hvar (fun a => (f a, h a)) m at hfh
  unfold condH
  simpa only using congrArg (fun t => t - Hvar h m) hfh

lemma MI_iidProduct_zero
    {A : Type*} [Fintype A] [DecidableEq A] {t : A -> Real} (ht : IsPMF t) :
    MI Prod.fst Prod.snd (fun u : A × A => t u.1 * t u.2) = 0 := by
  let q : A × A -> Real := fun u => t u.1 * t u.2
  have ht_sum : ∑ a, t a = 1 := by simpa [mass] using ht.total
  have hq : IsPMF q := by
    constructor
    · intro u
      exact mul_nonneg (ht.nonneg u.1) (ht.nonneg u.2)
    · unfold mass q
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [ht_sum]
      simp [ht_sum]
  have hfst : push Prod.fst q = t := by
    funext a
    unfold push
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp [q, ← Finset.mul_sum, ht_sum]
  have hsnd : push Prod.snd q = t := by
    funext b
    unfold push
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp [q, ← Finset.sum_mul, ht_sum]
  have hpair : push (fun u : A × A => (u.1, u.2)) q = q := by
    simpa only using push_id q
  have hfiber (b : A) : H (fun a => q (a, b)) = t b * H t := by
    have heq : (fun a => q (a, b)) = fun a => t b * t a := by
      funext a
      dsimp only [q]
      ring
    rw [heq]
    exact H_smul ht.isFinMeas (ht.nonneg b)
  have hqH := H_prod_eq_snd_add_fibers hq
  rw [hsnd] at hqH
  simp_rw [hfiber] at hqH
  rw [← Finset.sum_mul, ht_sum, one_mul] at hqH
  change MI Prod.fst Prod.snd q = 0
  unfold MI Hvar
  rw [hfst, hsnd, hpair, hqH]
  ring

end FiniteInfo

namespace NLatent

variable (V : NLatent p)

section OfJoint

variable {I : Type} [Fintype I] [DecidableEq I]

private noncomputable def jointConditionedComp (r : I × Omega -> Real)
    (hp : IsPMF p) (i : I) : Omega -> Real :=
  fun x =>
    if push Prod.fst r i = 0 then p x
    else (push Prod.fst r i)⁻¹ * r (i, x)

private lemma joint_fiber_mass (r : I × Omega -> Real) (i : I) :
    mass (fun x => r (i, x)) = push Prod.fst r i := by
  unfold mass push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp [eq_comm]

private lemma jointConditionedComp_isPMF (r : I × Omega -> Real)
    (hr : IsPMF r) (hp : IsPMF p) (i : I) :
    IsPMF (jointConditionedComp r hp i) := by
  by_cases hi : push Prod.fst r i = 0
  · have heq : jointConditionedComp r hp i = p := by
      funext x
      simp [jointConditionedComp, hi]
    rw [heq]
    exact hp
  · have hipos : 0 < push Prod.fst r i :=
      lt_of_le_of_ne ((isPMF_push hr).nonneg i) (Ne.symm hi)
    constructor
    · intro x
      simp only [jointConditionedComp, hi, if_false]
      exact mul_nonneg (inv_nonneg.mpr hipos.le) (hr.nonneg (i, x))
    · unfold mass jointConditionedComp
      simp only [hi, if_false, ← Finset.mul_sum]
      have hmass : (∑ x, r (i, x)) = push Prod.fst r i := by
        simpa [mass] using joint_fiber_mass r i
      rw [hmass, inv_mul_cancel₀ hi]

private lemma prior_mul_jointConditionedComp (r : I × Omega -> Real)
    (hr : IsPMF r) (hp : IsPMF p) (i : I) (x : Omega) :
    push Prod.fst r i * jointConditionedComp r hp i x = r (i, x) := by
  by_cases hi : push Prod.fst r i = 0
  · have hle : r (i, x) <= push Prod.fst r i := by
      unfold push
      exact Finset.single_le_sum (fun u _ => hr.nonneg u) (by simp)
    have hzero : r (i, x) = 0 :=
      le_antisymm (by simpa [hi] using hle) (hr.nonneg (i, x))
    simp [jointConditionedComp, hi, hzero]
  · simp only [jointConditionedComp, hi, if_false]
    field_simp [hi]

/-- Bundle any finite joint law of `(I,X)` with source marginal `p` as an
`NLatent p`. -/
noncomputable def ofJoint (r : I × Omega -> Real) (hr : IsPMF r)
    (hp : IsPMF p) (hsource : push Prod.snd r = p) : NLatent p where
  ι := I
  fin := inferInstance
  dec := inferInstance
  prior := push Prod.fst r
  comp := jointConditionedComp r hp
  prior_isPMF := isPMF_push hr
  comp_isPMF := jointConditionedComp_isPMF r hr hp
  mixture := by
    intro x
    calc
      (∑ i, push Prod.fst r i * jointConditionedComp r hp i x) =
          ∑ i, r (i, x) := by
            apply Finset.sum_congr rfl
            intro i _
            exact prior_mul_jointConditionedComp r hr hp i x
      _ = push Prod.snd r x := by
            unfold push
            rw [Finset.sum_filter, Fintype.sum_prod_type]
            simp
      _ = p x := congrFun hsource x

theorem ofJoint_joint_eq (r : I × Omega -> Real) (hr : IsPMF r)
    (hp : IsPMF p) (hsource : push Prod.snd r = p) :
    (ofJoint r hr hp hsource).joint = r := by
  funext u
  exact prior_mul_jointConditionedComp r hr hp u.1 u.2

end OfJoint

/-- The posterior probability `P(C=c | X=x)`.  At a zero-mass source atom
the value is immaterial; the quotient convention makes it zero. -/
noncomputable def post (c : V.ι) (x : Omega) : Real :=
  V.prior c * V.comp c x / p x

lemma post_nonneg (c : V.ι) (x : Omega) : 0 <= V.post c x := by
  exact div_nonneg
    (mul_nonneg (V.prior_isPMF.nonneg c) ((V.comp_isPMF c).nonneg x))
    (by
      have hp := V.mixture x
      rw [← hp]
      exact Finset.sum_nonneg fun a _ =>
        mul_nonneg (V.prior_isPMF.nonneg a) ((V.comp_isPMF a).nonneg x))

lemma sum_post_of_pos (x : Omega) (hx : 0 < p x) :
    (∑ c, V.post c x) = 1 := by
  unfold post
  calc
    (∑ c, V.prior c * V.comp c x / p x) =
        (∑ c, V.prior c * V.comp c x) / p x := by
          rw [Finset.sum_div]
    _ = p x / p x := by rw [V.mixture x]
    _ = 1 := div_self hx.ne'

lemma base_isPMF (V : NLatent p) : IsPMF p := by
  have h := isPMF_push (f := fun w : V.ι × Omega => w.2) V.joint_isPMF
  rw [V.push_snd_joint] at h
  exact h

/-- The source-resolved law of two conditionally iid posterior replicas. -/
noncomputable def replicaLaw : (V.ι × V.ι) × Omega -> Real :=
  fun u => p u.2 * V.post u.1.1 u.2 * V.post u.1.2 u.2

/-- Exchange the two posterior replicas while leaving the source fixed. -/
def replicaSwap : ((V.ι × V.ι) × Omega) ≃ ((V.ι × V.ι) × Omega) where
  toFun u := ((u.1.2, u.1.1), u.2)
  invFun u := ((u.1.2, u.1.1), u.2)
  left_inv := by rintro ⟨⟨c₀, c₁⟩, x⟩; rfl
  right_inv := by rintro ⟨⟨c₀, c₁⟩, x⟩; rfl

private lemma sum_replica_at (x : Omega) :
    (∑ c0, ∑ c1, p x * V.post c0 x * V.post c1 x) = p x := by
  rcases (show 0 <= p x from by
    rw [← V.mixture x]
    exact Finset.sum_nonneg fun a _ =>
      mul_nonneg (V.prior_isPMF.nonneg a) ((V.comp_isPMF a).nonneg x)).eq_or_lt with hx | hx
  · have hx' : p x = 0 := hx.symm
    simp [hx']
  · have hpost := V.sum_post_of_pos x hx
    calc
      (∑ c0, ∑ c1, p x * V.post c0 x * V.post c1 x) =
          ∑ c0, (p x * V.post c0 x) * (∑ c1, V.post c1 x) := by
            apply Finset.sum_congr rfl
            intro c0 _
            rw [Finset.mul_sum]
      _ = ∑ c0, p x * V.post c0 x := by rw [hpost]; simp
      _ = p x * (∑ c0, V.post c0 x) := by rw [Finset.mul_sum]
      _ = p x := by rw [hpost, mul_one]

lemma replicaLaw_isPMF : IsPMF V.replicaLaw := by
  refine ⟨?_, ?_⟩
  · intro u
    exact mul_nonneg
      (mul_nonneg (by
        rw [← V.mixture u.2]
        exact Finset.sum_nonneg fun a _ =>
          mul_nonneg (V.prior_isPMF.nonneg a)
            ((V.comp_isPMF a).nonneg u.2))
        (V.post_nonneg u.1.1 u.2))
      (V.post_nonneg u.1.2 u.2)
  · unfold mass
    calc
      (∑ u, V.replicaLaw u) =
          ∑ pair : V.ι × V.ι, ∑ x, V.replicaLaw (pair, x) := by
            rw [Fintype.sum_prod_type]
      _ = ∑ c0, ∑ c1, ∑ x, V.replicaLaw ((c0, c1), x) := by
            rw [Fintype.sum_prod_type]
      _ = ∑ c0, ∑ x, ∑ c1,
          p x * V.post c0 x * V.post c1 x := by
            simp only [replicaLaw]
            apply Finset.sum_congr rfl
            intro c0 _
            exact Finset.sum_comm
      _ = ∑ x, ∑ c0, ∑ c1,
          p x * V.post c0 x * V.post c1 x := Finset.sum_comm
      _ = ∑ x, p x := by
            apply Finset.sum_congr rfl
            intro x _
            exact sum_replica_at V x
      _ = 1 := by simpa [mass] using V.base_isPMF.total

/-- Swapping the two replicas preserves the law pointwise. -/
lemma replicaLaw_swap (u : (V.ι × V.ι) × Omega) :
    V.replicaLaw ((u.1.2, u.1.1), u.2) = V.replicaLaw u := by
  unfold replicaLaw
  ring

lemma replicaLaw_swap_equiv (u : (V.ι × V.ι) × Omega) :
    V.replicaLaw (V.replicaSwap u) = V.replicaLaw u := by
  exact V.replicaLaw_swap u

private lemma sum_replica_second (c0 : V.ι) (x : Omega) :
    (∑ c1, V.replicaLaw ((c0, c1), x)) = V.joint (c0, x) := by
  by_cases hx : p x = 0
  · have hweighted : V.prior c0 * V.comp c0 x = 0 := by
      have hmix := V.mixture x
      rw [hx] at hmix
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun a _ => mul_nonneg (V.prior_isPMF.nonneg a)
          ((V.comp_isPMF a).nonneg x))).mp hmix c0 (Finset.mem_univ c0)
    simp [replicaLaw, hx, joint, hweighted]
  · have hxpos : 0 < p x := lt_of_le_of_ne (by
      rw [← V.mixture x]
      exact Finset.sum_nonneg fun a _ =>
        mul_nonneg (V.prior_isPMF.nonneg a) ((V.comp_isPMF a).nonneg x))
      (Ne.symm hx)
    have hpost := V.sum_post_of_pos x hxpos
    calc
      (∑ c1, V.replicaLaw ((c0, c1), x)) =
          (p x * V.post c0 x) * (∑ c1, V.post c1 x) := by
            unfold replicaLaw
            rw [Finset.mul_sum]
      _ = p x * V.post c0 x := by rw [hpost, mul_one]
      _ = V.joint (c0, x) := by
            unfold post joint
            field_simp [hx]

/-- The `(C₀,X)` marginal is the original latent joint law. -/
lemma push_replica_first_source :
    push (fun u : (V.ι × V.ι) × Omega => (u.1.1, u.2)) V.replicaLaw = V.joint := by
  funext v
  rcases v with ⟨c0, x⟩
  unfold push
  rw [Finset.sum_filter]
  have hite (a b : V.ι) (y : Omega) :
      (if a = c0 ∧ y = x then V.replicaLaw ((a, b), y) else 0) =
        if a = c0 then if y = x then V.replicaLaw ((a, b), y) else 0 else 0 := by
    by_cases ha : a = c0 <;> by_cases hy : y = x <;> simp [ha, hy]
  calc
    (∑ u : (V.ι × V.ι) × Omega,
        if (u.1.1, u.2) = (c0, x) then V.replicaLaw u else 0) =
        ∑ c1, V.replicaLaw ((c0, c1), x) := by
          rw [Fintype.sum_prod_type]
          simp only [Fintype.sum_prod_type, Prod.mk.injEq]
          simp_rw [hite]
          simp
    _ = V.joint (c0, x) := V.sum_replica_second c0 x

/-- The `(C₁,X)` marginal is also the original latent joint law. -/
lemma push_replica_second_source :
    push (fun u : (V.ι × V.ι) × Omega => (u.1.2, u.2)) V.replicaLaw = V.joint := by
  funext v
  rcases v with ⟨c1, x⟩
  unfold push
  rw [Finset.sum_filter]
  have hite (a b : V.ι) (y : Omega) :
      (if b = c1 ∧ y = x then V.replicaLaw ((a, b), y) else 0) =
        if b = c1 then if y = x then V.replicaLaw ((a, b), y) else 0 else 0 := by
    by_cases hb : b = c1 <;> by_cases hy : y = x <;> simp [hb, hy]
  have hreduce :
      (∑ u : (V.ι × V.ι) × Omega,
        if (u.1.2, u.2) = (c1, x) then V.replicaLaw u else 0) =
        ∑ c0, V.replicaLaw ((c0, c1), x) := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type, Prod.mk.injEq]
    simp_rw [hite]
    simp
  rw [hreduce]
  have hswap : ∀ a, V.replicaLaw ((a, c1), x) = V.replicaLaw ((c1, a), x) := by
    intro a
    symm
    exact V.replicaLaw_swap ((a, c1), x)
  simp_rw [hswap]
  exact V.sum_replica_second c1 x

/-- The source marginal of the replica law is `p`. -/
lemma push_replica_source :
    push (fun u : (V.ι × V.ι) × Omega => u.2) V.replicaLaw = p := by
  have h := congrArg (push Prod.snd) V.push_replica_first_source
  rw [push_push] at h
  have hbase := V.push_snd_joint
  simpa [Function.comp_def] using h.trans hbase

/-- Any observable of `(C₀,X)` has the same law under the replica coupling as
under the original latent joint law. -/
lemma push_replica_first_lift {Delta : Type*} [Fintype Delta] [DecidableEq Delta]
    (h : V.ι × Omega -> Delta) :
    push (fun u : (V.ι × V.ι) × Omega => h (u.1.1, u.2)) V.replicaLaw =
      push h V.joint := by
  let base : (V.ι × V.ι) × Omega -> V.ι × Omega :=
    fun u => (u.1.1, u.2)
  calc
    push (fun u : (V.ι × V.ι) × Omega => h (u.1.1, u.2)) V.replicaLaw =
        push h (push base V.replicaLaw) := by
          symm
          simpa [base, Function.comp_def] using push_push base h V.replicaLaw
    _ = push h V.joint := by rw [V.push_replica_first_source]

lemma replica_condH_first {Delta : Type*} [Fintype Delta] [DecidableEq Delta]
    (h : Omega -> Delta) :
    condH (fun u : (V.ι × V.ι) × Omega => h u.2) (fun u => u.1.1)
        V.replicaLaw =
      condH (fun w : V.ι × Omega => h w.2) (fun w => w.1) V.joint := by
  apply FiniteInfo.condH_eq_of_pair_push_eq V.replicaLaw V.joint
  exact V.push_replica_first_lift (fun w : V.ι × Omega => (h w.2, w.1))

lemma replica_condMI_first {Delta E : Type*} [Fintype Delta] [Fintype E]
    [DecidableEq Delta] [DecidableEq E] (h : Omega -> Delta) (k : Omega -> E) :
    condMI (fun u : (V.ι × V.ι) × Omega => u.1.1) (fun u => h u.2)
        (fun u => k u.2) V.replicaLaw =
      condMI (fun w : V.ι × Omega => w.1) (fun w => h w.2)
        (fun w => k w.2) V.joint := by
  apply FiniteInfo.condMI_eq_of_triple_push_eq V.replicaLaw V.joint
  exact V.push_replica_first_lift
    (fun w : V.ι × Omega => (w.1, h w.2, k w.2))

private noncomputable def replicaSourceFiber (x : Omega) :
    (V.ι × V.ι) × Omega -> Real :=
  fun u => if u.2 = x then V.replicaLaw u else 0

private lemma push_replicaSourceFiber_pair (x : Omega) :
    push (fun u : (V.ι × V.ι) × Omega => u.1)
      (V.replicaSourceFiber x) =
      fun v : V.ι × V.ι => p x * V.post v.1 x * V.post v.2 x := by
  funext v
  rcases v with ⟨c0, c1⟩
  unfold push replicaSourceFiber
  rw [Finset.sum_filter]
  have hite (a b : V.ι) (y : Omega) :
      (if a = c0 ∧ b = c1 then
          if y = x then V.replicaLaw ((a, b), y) else 0 else 0) =
        if a = c0 then if b = c1 then
          if y = x then V.replicaLaw ((a, b), y) else 0 else 0 else 0 := by
    by_cases ha : a = c0 <;> by_cases hb : b = c1 <;> by_cases hy : y = x <;>
      simp [ha, hb, hy]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Prod.mk.injEq]
  simp_rw [hite]
  simp [replicaLaw]

private lemma MI_replicaSourceFiber_zero (x : Omega) :
    MI (fun u : (V.ι × V.ι) × Omega => u.1.1) (fun u => u.1.2)
      (V.replicaSourceFiber x) = 0 := by
  let n : V.ι × V.ι -> Real := fun v => p x * V.post v.1 x * V.post v.2 x
  have hpair :
      push (fun u : (V.ι × V.ι) × Omega => u.1)
          (V.replicaSourceFiber x) =
        push (fun v : V.ι × V.ι => (v.1, v.2)) n := by
    rw [V.push_replicaSourceFiber_pair x]
    symm
    simpa only using FiniteInfo.push_id n
  rw [FiniteInfo.MI_eq_of_pair_push_eq (V.replicaSourceFiber x) n
    (fun u : (V.ι × V.ι) × Omega => u.1.1) (fun u => u.1.2)
    (fun v : V.ι × V.ι => v.1) (fun v => v.2) hpair]
  by_cases hx : p x = 0
  · simp [n, hx, MI, Hvar, H, push, mass]
  · have hxpos : 0 < p x := lt_of_le_of_ne (V.base_isPMF.nonneg x) (Ne.symm hx)
    let t : V.ι -> Real := fun c => V.post c x
    have ht : IsPMF t := by
      constructor
      · intro c
        exact V.post_nonneg c x
      · simpa [mass, t] using V.sum_post_of_pos x hxpos
    let q : V.ι × V.ι -> Real := fun v => t v.1 * t v.2
    have hq : IsPMF q := by
      constructor
      · intro v
        exact mul_nonneg (ht.nonneg v.1) (ht.nonneg v.2)
      · unfold mass q
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum]
        have ht_sum : ∑ c, t c = 1 := by simpa [mass] using ht.total
        rw [ht_sum]
        simp [ht_sum]
    have hzero : MI Prod.fst Prod.snd q = 0 :=
      FiniteInfo.MI_iidProduct_zero ht
    have hscale := MI_smul hq.isFinMeas Prod.fst Prod.snd
      (V.base_isPMF.nonneg x)
    have hn : n = fun v : V.ι × V.ι => p x * q v := by
      funext v
      simp [n, q, t]
      ring
    rw [hn, hscale, hzero, mul_zero]

/-- The two posterior replicas are conditionally independent given the
source. -/
theorem replica_markov :
    condMI (fun u : (V.ι × V.ι) × Omega => u.1.1) (fun u => u.1.2)
      (fun u => u.2) V.replicaLaw = 0 := by
  have h := FiniteInfo.condMI_eq_sum_MI_fibers V.replicaLaw_isPMF
    (fun u : (V.ι × V.ι) × Omega => u.1.1) (fun u => u.1.2)
    (fun u => u.2)
  change condMI (fun u : (V.ι × V.ι) × Omega => u.1.1) (fun u => u.1.2)
      (fun u => u.2) V.replicaLaw =
    ∑ x, MI (fun u => u.1.1) (fun u => u.1.2) (V.replicaSourceFiber x) at h
  rw [h]
  exact Finset.sum_eq_zero fun x _ => V.MI_replicaSourceFiber_zero x

/-- The refinement whose label is the posterior-replica pair `(C₀,C₁)`. -/
noncomputable def replicaRefinement : NLatent p :=
  ofJoint V.replicaLaw V.replicaLaw_isPMF V.base_isPMF V.push_replica_source

theorem replicaRefinement_joint_eq : V.replicaRefinement.joint = V.replicaLaw := by
  exact ofJoint_joint_eq V.replicaLaw V.replicaLaw_isPMF V.base_isPMF
    V.push_replica_source

end NLatent

end stoch_to_det
