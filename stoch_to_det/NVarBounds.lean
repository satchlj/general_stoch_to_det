import stoch_to_det.NVarEnvelope
import stoch_to_det.NVarNonneg

/-!
# Baseline unconditional bounds for the n-variable hard-code functional

This module records the elementary endpoint available before the genuinely
quantitative stochastic-to-deterministic comparison is proved.  The injective
hard code revealing the whole cell has zero conditional total correlation and
cost exactly `nPsi`; hence `nT <= nPsi` for every finite number of views.

This is an absolute bound, not yet a multiplicative comparison with `nTau`.
-/

namespace stoch_to_det

open Finset

variable {Omega : Type} [Fintype Omega] [DecidableEq Omega]
variable {p : Omega -> Real}
variable {n : Nat} {kappa gamma : Fin n -> Type}
  [forall i, Fintype (kappa i)] [forall i, DecidableEq (kappa i)]
  [forall i, Fintype (gamma i)] [forall i, DecidableEq (gamma i)]
variable (f : forall i, Omega -> kappa i) (g : forall i, Omega -> gamma i)

private lemma H_eq_zero_of_subsingleton_support {delta : Type*}
    [Fintype delta] [DecidableEq delta] {m : delta -> Real}
    (hm : IsFinMeas m)
    (hsing : forall x y, m x ≠ 0 -> m y ≠ 0 -> x = y) : H m = 0 := by
  classical
  by_cases hne : exists x, m x ≠ 0
  · obtain ⟨x, hx⟩ := hne
    have hzero : forall y, y ≠ x -> m y = 0 := by
      intro y hy
      by_contra hmy
      exact hy (hsing y x hmy hx)
    have hmass : mass m = m x := by
      unfold mass
      apply Finset.sum_eq_single x
      · intro y _ hy
        exact hzero y hy
      · simp
    unfold H
    rw [hmass]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : y = x
    · subst y
      simp [hx]
    · simp [hzero y hy]
  · push_neg at hne
    have hm0 : m = fun _ => 0 := funext hne
    simp [hm0, H, mass]

private lemma exists_ne_zero_of_push_ne_zero {delta : Type*}
    [DecidableEq delta] {h : Omega -> delta} {m : Omega -> Real} {d : delta}
    (hd : push h m d ≠ 0) : exists z, m z ≠ 0 ∧ h z = d := by
  classical
  by_contra hn
  apply hd
  unfold push
  apply Finset.sum_eq_zero
  intro z hz
  by_contra hmz
  apply hn
  exact ⟨z, hmz, (Finset.mem_filter.mp hz).2⟩

private lemma Hvar_eq_zero_of_subsingleton_support
    {delta : Type*} [Fintype delta] [DecidableEq delta]
    {m : Omega -> Real} (hm : IsPMF m)
    (hsing : forall x y, m x ≠ 0 -> m y ≠ 0 -> x = y)
    (h : Omega -> delta) : Hvar h m = 0 := by
  unfold Hvar
  apply H_eq_zero_of_subsingleton_support (isPMF_push hm).isFinMeas
  intro a b ha hb
  obtain ⟨x, hx, hxa⟩ := exists_ne_zero_of_push_ne_zero ha
  obtain ⟨y, hy, hyb⟩ := exists_ne_zero_of_push_ne_zero hb
  rw [← hxa, ← hyb, hsing x y hx hy]

private lemma nPhi_eq_zero_of_subsingleton_support
    {q : Omega -> Real} (hq : IsPMF q)
    (hsing : forall x y, q x ≠ 0 -> q y ≠ 0 -> x = y) :
    nPhi f g q = 0 := by
  have hH : H q = 0 :=
    H_eq_zero_of_subsingleton_support hq.isFinMeas hsing
  have hf : forall i, Hvar (f i) q = 0 := fun i =>
    Hvar_eq_zero_of_subsingleton_support hq hsing (f i)
  have hg : forall i, Hvar (g i) q = 0 := fun i =>
    Hvar_eq_zero_of_subsingleton_support hq hsing (g i)
  unfold nPhi
  simp_rw [hH, hf, hg]
  simp

private lemma Hvar_eq_H_of_injective [Nonempty Omega]
    {delta : Type*} [Fintype delta] [DecidableEq delta]
    {m : Omega -> Real} (hm : IsPMF m) (h : Omega -> delta)
    (hinj : Function.Injective h) : Hvar h m = H m := by
  obtain ⟨u, hu⟩ := hinj.hasLeftInverse
  have heq := Hvar_eq_of_leftInverse hm (fun z : Omega => z) h u hu
  have hid : Hvar (fun z : Omega => z) m = H m := by
    unfold Hvar
    change H (push (Equiv.refl Omega) m) = H m
    exact H_push_equiv (Equiv.refl Omega) m hm
  calc
    Hvar h m = Hvar (h ∘ (fun z : Omega => z)) m := rfl
    _ = Hvar (fun z : Omega => z) m := heq
    _ = H m := hid

private lemma condH_view_le_H [Nonempty Omega] (hp : IsPMF p)
    (hinjViews : forall i, Function.Injective (fun z => (f i z, g i z)))
    (i : Fin n) : condH (f i) (g i) p <= H p := by
  unfold condH
  rw [Hvar_eq_H_of_injective hp _ (hinjViews i)]
  have hg : 0 <= Hvar (g i) p := by
    unfold Hvar
    exact H_nonneg_of_isPMF (isPMF_push hp)
  linarith

/-- The hard-code infimum is below the score of any particular fixed code. -/
theorem nT_le_code_score [Nonempty Omega] (hp : IsPMF p)
    (hinj : forall i, Function.Injective (fun z => (f i z, g i z)))
    (htup : Function.Injective (tupleView f))
    (Gamma : Omega -> Fin (Fintype.card Omega)) :
    nT (f := f) (g := g) p <= (NLatent.ofFunction hp Gamma).score f g := by
  rw [nT, dif_pos hp]
  have hb : BddBelow (Set.range fun code : Omega -> Fin (Fintype.card Omega) =>
      (NLatent.ofFunction hp code).score f g) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨code, rfl⟩
    exact NLatent.score_nonneg (NLatent.ofFunction hp code) hinj htup
  exact ciInf_le hb Gamma

/-- An injective deterministic code has score exactly `nPsi`: every posterior
component is a point mass, so its `nPhi` payoff vanishes. -/
theorem score_ofFunction_eq_nPsi_of_injective [Nonempty Omega] (hp : IsPMF p)
    (hinjViews : forall i, Function.Injective (fun z => (f i z, g i z)))
    {delta : Type} [Fintype delta] [DecidableEq delta]
    (Gamma : Omega -> delta) (hGamma : Function.Injective Gamma) :
    (NLatent.ofFunction hp Gamma).score f g = nPsi f g p := by
  rw [NLatent.score_eq hp (NLatent.ofFunction hp Gamma) hinjViews]
  have hterm : forall c : delta,
      (NLatent.ofFunction hp Gamma).prior c *
        nPhi f g ((NLatent.ofFunction hp Gamma).comp c) = 0 := by
    intro c
    by_cases hc : (NLatent.ofFunction hp Gamma).prior c = 0
    · simp [hc]
    · have hsing : forall x y,
          (NLatent.ofFunction hp Gamma).comp c x ≠ 0 ->
          (NLatent.ofFunction hp Gamma).comp c y ≠ 0 -> x = y := by
        have hpush : push Gamma p c ≠ 0 := by
          simpa [NLatent.ofFunction] using hc
        intro x y hx hy
        have hxc : Gamma x = c := by
          by_contra h
          exact hx (NLatent.ofFunction_comp_eq_zero_of_ne hp Gamma hpush h)
        have hyc : Gamma y = c := by
          by_contra h
          exact hy (NLatent.ofFunction_comp_eq_zero_of_ne hp Gamma hpush h)
        exact hGamma (hxc.trans hyc.symm)
      rw [nPhi_eq_zero_of_subsingleton_support f g
        ((NLatent.ofFunction hp Gamma).comp_isPMF c) hsing]
      simp
  have hsum : (∑ c : delta, (NLatent.ofFunction hp Gamma).prior c *
      nPhi f g ((NLatent.ofFunction hp Gamma).comp c)) = 0 :=
    Finset.sum_eq_zero fun c _ => hterm c
  calc
    nPsi f g p - ∑ c : delta, (NLatent.ofFunction hp Gamma).prior c *
        nPhi f g ((NLatent.ofFunction hp Gamma).comp c) = nPsi f g p - 0 :=
      congrArg (fun t => nPsi f g p - t) hsum
    _ = nPsi f g p := sub_zero _

/-- **Unconditional all-n baseline.** Revealing the whole cell is an admissible
hard code, so the deterministic n-variable score is at most `nPsi`.

Unlike the desired stochastic-to-deterministic theorem, this statement does
not compare `nT` to `nTau`; it is recorded to make the current certified scope
explicit while that relative bound is developed. -/
theorem nT_le_nPsi [Nonempty Omega] (hp : IsPMF p)
    (hinjViews : forall i, Function.Injective (fun z => (f i z, g i z)))
    (htup : Function.Injective (tupleView f)) :
    nT (f := f) (g := g) p <= nPsi f g p := by
  let Gamma : Omega -> Fin (Fintype.card Omega) := Fintype.equivFin Omega
  calc
    nT (f := f) (g := g) p <= (NLatent.ofFunction hp Gamma).score f g :=
      nT_le_code_score f g hp hinjViews htup Gamma
    _ = nPsi f g p :=
      score_ofFunction_eq_nPsi_of_injective f g hp hinjViews Gamma
        (Fintype.equivFin Omega).injective

/-- The sum of deletion-conditional entropies is bounded by `n` times the
entropy of the full cell, and hence by `n log_2 |Omega|`. -/
theorem nPsi_le_n_mul_lg_card [Nonempty Omega] (hp : IsPMF p)
    (hinjViews : forall i, Function.Injective (fun z => (f i z, g i z))) :
    nPsi f g p <= (n : Real) * lg (Fintype.card Omega) := by
  have hsum : nPsi f g p <= ∑ _i : Fin n, H p := by
    unfold nPsi
    exact Finset.sum_le_sum fun i _ => condH_view_le_H f g hp hinjViews i
  have hconst : (∑ _i : Fin n, H p) = (n : Real) * H p := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hconst] at hsum
  exact hsum.trans (mul_le_mul_of_nonneg_left (H_le_card hp) (Nat.cast_nonneg n))

/-- The stochastic n-variable infimum is nonnegative under genuine coordinate
views. -/
theorem nTau_nonneg [Nonempty Omega]
    (hinjViews : forall i, Function.Injective (fun z => (f i z, g i z)))
    (htup : Function.Injective (tupleView f)) :
    0 <= nTau f g p := by
  unfold nTau
  exact Real.iInf_nonneg fun V => NLatent.score_nonneg V hinjViews htup

/-- **Explicit all-n stochastic-to-deterministic comparison with an additive
alphabet term.** For all finite `n` (therefore in particular for `n >= 3`),

`nT(p) <= nTau(p) + n log_2 |Omega|`.

The desired alphabet-free multiplicative comparison remains a separate open
problem; this theorem makes no such claim. -/
theorem nT_le_nTau_add_n_mul_lg_card [Nonempty Omega] (hp : IsPMF p)
    (hinjViews : forall i, Function.Injective (fun z => (f i z, g i z)))
    (htup : Function.Injective (tupleView f)) :
    nT (f := f) (g := g) p <=
      nTau f g p + (n : Real) * lg (Fintype.card Omega) := by
  calc
    nT (f := f) (g := g) p <= nPsi f g p :=
      nT_le_nPsi f g hp hinjViews htup
    _ <= (n : Real) * lg (Fintype.card Omega) :=
      nPsi_le_n_mul_lg_card f g hp hinjViews
    _ <= nTau f g p + (n : Real) * lg (Fintype.card Omega) := by
      linarith [nTau_nonneg f g (p := p) hinjViews htup]

/-- The explicit `n >= 3` specialization requested by the multivariate
program. The proof in fact works for every `n`. -/
theorem nT_le_nTau_add_n_mul_lg_card_of_three_le [Nonempty Omega]
    (_hn : 3 <= n) (hp : IsPMF p)
    (hinjViews : forall i, Function.Injective (fun z => (f i z, g i z)))
    (htup : Function.Injective (tupleView f)) :
    nT (f := f) (g := g) p <=
      nTau f g p + (n : Real) * lg (Fintype.card Omega) :=
  nT_le_nTau_add_n_mul_lg_card f g hp hinjViews htup

/-- A multiplicative corollary on any class of laws with a certified positive
lower bound `epsilon <= nTau`. Its constant is explicit but depends on the
alphabet and on that nondegeneracy threshold. -/
theorem nT_le_mul_nTau_of_epsilon_le [Nonempty Omega]
    (_hn : 3 <= n) (hp : IsPMF p) {epsilon : Real} (hepsilon : 0 < epsilon)
    (htau : epsilon <= nTau f g p)
    (hinjViews : forall i, Function.Injective (fun z => (f i z, g i z)))
    (htup : Function.Injective (tupleView f)) :
    nT (f := f) (g := g) p <=
      (1 + ((n : Real) * lg (Fintype.card Omega)) / epsilon) * nTau f g p := by
  let A : Real := (n : Real) * lg (Fintype.card Omega)
  have hlog : 0 <= lg (Fintype.card Omega) :=
    (H_nonneg_of_isPMF hp).trans (H_le_card hp)
  have hA : 0 <= A := mul_nonneg (Nat.cast_nonneg n) hlog
  have hscale : A <= (A / epsilon) * nTau f g p := by
    calc
      A = (A / epsilon) * epsilon := by field_simp [hepsilon.ne']
      _ <= (A / epsilon) * nTau f g p :=
        mul_le_mul_of_nonneg_left htau (div_nonneg hA hepsilon.le)
  calc
    nT (f := f) (g := g) p <= nTau f g p + A := by
      simpa [A] using nT_le_nTau_add_n_mul_lg_card f g hp hinjViews htup
    _ <= (1 + A / epsilon) * nTau f g p := by
      nlinarith
    _ = (1 + ((n : Real) * lg (Fintype.card Omega)) / epsilon) * nTau f g p := by
      rfl

end stoch_to_det
