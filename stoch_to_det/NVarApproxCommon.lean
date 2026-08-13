import stoch_to_det.NVarEnvelope

/-!
# Alphabet-free cost of an approximately deletion-common hard label

For genuine coordinate/deletion views, dual total correlation satisfies

`0 <= DTC(X | Gamma)` and `DTC(X) <= (n-1) TC(X)`.

This file isolates the entropy algebra around those two standard inequalities.
For every deterministic code `Gamma`, it proves

`H(Gamma) <= (n-1) TC(X) + sum_i H(Gamma | g_i(X))`

and consequently

`score(Gamma) <= n TC(X) + 2 sum_i H(Gamma | g_i(X))`.

The theorem is stated with the two DTC inequalities as explicit hypotheses, so
the generic abstract-view interface does not silently claim coordinate facts
that are false for arbitrary views.  A concrete dependent-product coordinate
module can discharge them by Shearer's inequality.
-/

namespace stoch_to_det

open Finset

variable {Omega : Type} [Fintype Omega] [DecidableEq Omega]
variable {p : Omega -> Real}
variable {n : Nat} {kappa gamma : Fin n -> Type}
  [forall i, Fintype (kappa i)] [forall i, DecidableEq (kappa i)]
  [forall i, Fintype (gamma i)] [forall i, DecidableEq (gamma i)]

/-- Total correlation of the singleton views. -/
noncomputable def nTC (f : forall i : Fin n, Omega -> kappa i)
    (p : Omega -> Real) : Real :=
  (∑ i, Hvar (f i) p) - H p

/-- Dual total correlation for singleton/deletion views. -/
noncomputable def nDTC
    (f : forall i : Fin n, Omega -> kappa i)
    (g : forall i : Fin n, Omega -> gamma i)
    (p : Omega -> Real) : Real :=
  H p - ∑ i, condH (f i) (g i) p

/-- Conditional total correlation after revealing a deterministic code. -/
noncomputable def nCondTC
    (f : forall i : Fin n, Omega -> kappa i)
    (p : Omega -> Real) {delta : Type} [Fintype delta] [DecidableEq delta]
    (code : Omega -> delta) : Real :=
  (∑ i, condH (f i) code p) - condH (fun z : Omega => z) code p

/-- Conditional dual total correlation after revealing a deterministic code. -/
noncomputable def nCondDTC
    (f : forall i : Fin n, Omega -> kappa i)
    (g : forall i : Fin n, Omega -> gamma i)
    (p : Omega -> Real) {delta : Type} [Fintype delta] [DecidableEq delta]
    (code : Omega -> delta) : Real :=
  condH (fun z : Omega => z) code p -
    ∑ i, condH (f i) (fun z => (g i z, code z)) p

/-- The deterministic n-variable score written directly under the base law. -/
noncomputable def nDetScore
    (f : forall i : Fin n, Omega -> kappa i)
    (g : forall i : Fin n, Omega -> gamma i)
    (p : Omega -> Real) {delta : Type} [Fintype delta] [DecidableEq delta]
    (code : Omega -> delta) : Real :=
  nCondTC f p code + ∑ i, condH code (g i) p

private lemma Hvar_id_eq_H (hp : IsPMF p) :
    Hvar (fun z : Omega => z) p = H p := by
  unfold Hvar
  change H (push (Equiv.refl Omega) p) = H p
  exact H_push_equiv (Equiv.refl Omega) p hp

private lemma Hvar_eq_H_of_injective [Nonempty Omega]
    {delta : Type} [Fintype delta] [DecidableEq delta]
    (hp : IsPMF p) (h : Omega -> delta) (hinj : Function.Injective h) :
    Hvar h p = H p := by
  obtain ⟨u, hu⟩ := hinj.hasLeftInverse
  have heq := Hvar_eq_of_leftInverse hp (fun z : Omega => z) h u hu
  calc
    Hvar h p = Hvar (h ∘ (fun z : Omega => z)) p := rfl
    _ = Hvar (fun z : Omega => z) p := heq
    _ = H p := Hvar_id_eq_H hp

private lemma Hvar_push_source
    {source target out : Type} [Fintype source] [Fintype target]
    [DecidableEq target] [Fintype out] [DecidableEq out]
    (embed : source -> target) (a : target -> out) (m : source -> Real) :
    Hvar a (push embed m) = Hvar (a ∘ embed) m := by
  unfold Hvar
  rw [push_push]

private lemma condH_push_source
    {source target out₁ out₂ : Type} [Fintype source] [Fintype target]
    [DecidableEq target] [Fintype out₁] [DecidableEq out₁]
    [Fintype out₂] [DecidableEq out₂]
    (embed : source -> target) (a : target -> out₁) (b : target -> out₂)
    (m : source -> Real) :
    condH a b (push embed m) = condH (a ∘ embed) (b ∘ embed) m := by
  unfold condH
  change Hvar (fun x => (a x, b x)) (push embed m) -
      Hvar b (push embed m) = _
  rw [Hvar_push_source, Hvar_push_source]
  rfl

private lemma condMI_push_source
    {source target out₁ out₂ out₃ : Type} [Fintype source] [Fintype target]
    [DecidableEq target] [Fintype out₁] [DecidableEq out₁]
    [Fintype out₂] [DecidableEq out₂]
    [Fintype out₃] [DecidableEq out₃]
    (embed : source -> target) (a : target -> out₁) (b : target -> out₂)
    (c : target -> out₃) (m : source -> Real) :
    condMI a b c (push embed m) =
      condMI (a ∘ embed) (b ∘ embed) (c ∘ embed) m := by
  unfold condMI
  change Hvar (fun x => (a x, c x)) (push embed m) +
      Hvar (fun x => (b x, c x)) (push embed m) -
      Hvar (fun x => (a x, b x, c x)) (push embed m) -
      Hvar c (push embed m) = _
  rw [Hvar_push_source, Hvar_push_source, Hvar_push_source,
    Hvar_push_source]
  rfl

private lemma condMI_code_eq_condH [Nonempty Omega]
    {delta single deletion : Type}
    [Fintype delta] [DecidableEq delta]
    [Fintype single] [DecidableEq single]
    [Fintype deletion] [DecidableEq deletion]
    (hp : IsPMF p) (code : Omega -> delta)
    (f : Omega -> single) (g : Omega -> deletion)
    (hinj : Function.Injective (fun z => (f z, g z))) :
    condMI code f g p = condH code g p := by
  have hfg : Hvar (fun z => (f z, g z)) p = H p :=
    Hvar_eq_H_of_injective hp _ hinj
  have hcfg : Hvar (fun z => (code z, f z, g z)) p = H p := by
    apply Hvar_eq_H_of_injective hp
    intro x y hxy
    exact hinj (congrArg (fun t => (t.2.1, t.2.2)) hxy)
  unfold condMI condH
  rw [hfg, hcfg]
  ring

/-- The `NLatent.ofFunction` score is exactly the direct deterministic score. -/
theorem NLatent.ofFunction_score_eq_nDetScore [Nonempty Omega]
    {delta : Type} [Fintype delta] [DecidableEq delta]
    (hp : IsPMF p) (f : forall i : Fin n, Omega -> kappa i)
    (g : forall i : Fin n, Omega -> gamma i)
    (hinj : forall i, Function.Injective (fun z => (f i z, g i z)))
    (code : Omega -> delta) :
    (NLatent.ofFunction hp code).score f g = nDetScore f g p code := by
  change
    ((∑ i, condH (fun w : delta × Omega => f i w.2)
        (fun w => w.1) (NLatent.ofFunction hp code).joint) -
      condH (fun w : delta × Omega => w.2) (fun w => w.1)
        (NLatent.ofFunction hp code).joint) +
      ∑ i, condMI (fun w : delta × Omega => w.1)
        (fun w => f i w.2) (fun w => g i w.2)
        (NLatent.ofFunction hp code).joint = _
  rw [NLatent.ofFunction_joint_eq_push hp code]
  unfold nDetScore nCondTC
  simp_rw [condH_push_source]
  simp_rw [condMI_push_source]
  change ((∑ i, condH (f i) code p) -
      condH (fun z : Omega => z) code p) +
      ∑ i, condMI code (f i) (g i) p = _
  simp_rw [condMI_code_eq_condH hp code _ _ (hinj _)]

/-- Conditional TC after a hard code is at most base TC plus code entropy. -/
theorem nCondTC_le_nTC_add_code_entropy [Nonempty Omega]
    {delta : Type} [Fintype delta] [DecidableEq delta]
    (hp : IsPMF p) (f : forall i : Fin n, Omega -> kappa i)
    (code : Omega -> delta) :
    nCondTC f p code <= nTC f p + Hvar code p := by
  have hMI : 0 <= ∑ i, MI code (f i) p :=
    Finset.sum_nonneg fun i _ => MI_nonneg hp code (f i)
  have hcond : forall i,
      condH (f i) code p = Hvar (f i) p - MI code (f i) p := by
    intro i
    unfold condH MI
    have hswap : Hvar (fun z => (f i z, code z)) p =
        Hvar (fun z => (code z, f i z)) p := by
      symm
      simpa using Hvar_equiv hp (fun z => (f i z, code z))
        (Equiv.prodComm (kappa i) delta)
    rw [hswap]
    ring
  have hid : condH (fun z : Omega => z) code p = H p - Hvar code p := by
    unfold condH
    rw [Hvar_eq_H_of_injective hp (fun z => (z, code z))
      (fun _ _ hxy => congrArg Prod.fst hxy)]
  unfold nCondTC nTC
  simp_rw [hcond]
  rw [hid, Finset.sum_sub_distrib]
  linarith

/-- Exact DTC split across a deterministic code. -/
theorem nDTC_eq_code_entropy_sub_recovery_add_condDTC [Nonempty Omega]
    {delta : Type} [Fintype delta] [DecidableEq delta]
    (hp : IsPMF p) (f : forall i : Fin n, Omega -> kappa i)
    (g : forall i : Fin n, Omega -> gamma i)
    (hinj : forall i, Function.Injective (fun z => (f i z, g i z)))
    (code : Omega -> delta) :
    nDTC f g p = Hvar code p - (∑ i, condH code (g i) p) +
      nCondDTC f g p code := by
  have hchain : forall i,
      condH (f i) (g i) p = condH code (g i) p +
        condH (f i) (fun z => (g i z, code z)) p := by
    intro i
    have hfg : Hvar (fun z => (f i z, g i z)) p = H p :=
      Hvar_eq_H_of_injective hp _ (hinj i)
    have hfgc : Hvar (fun z => (f i z, (g i z, code z))) p = H p := by
      apply Hvar_eq_H_of_injective hp
      intro x y hxy
      exact (hinj i) (congrArg (fun t => (t.1, t.2.1)) hxy)
    have hswap : Hvar (fun z => (code z, g i z)) p =
        Hvar (fun z => (g i z, code z)) p := by
      symm
      simpa using Hvar_equiv hp (fun z => (code z, g i z))
        (Equiv.prodComm delta (gamma i))
    unfold condH
    rw [hfg, hfgc, hswap]
    ring
  have hid : condH (fun z : Omega => z) code p = H p - Hvar code p := by
    unfold condH
    rw [Hvar_eq_H_of_injective hp (fun z => (z, code z))
      (fun _ _ hxy => congrArg Prod.fst hxy)]
  unfold nDTC nCondDTC
  simp_rw [hchain]
  rw [hid, Finset.sum_add_distrib]
  ring

/-- Approximate common-label entropy bound.  The two hypotheses are exactly
the coordinate DTC inequalities; no alphabet or minimum mass occurs. -/
theorem code_entropy_le_n_minus_one_mul_nTC_add_recovery [Nonempty Omega]
    {delta : Type} [Fintype delta] [DecidableEq delta]
    (hp : IsPMF p) (f : forall i : Fin n, Omega -> kappa i)
    (g : forall i : Fin n, Omega -> gamma i)
    (hinj : forall i, Function.Injective (fun z => (f i z, g i z)))
    (code : Omega -> delta)
    (hcondDTC : 0 <= nCondDTC f g p code)
    (hDTCle : nDTC f g p <= ((n : Real) - 1) * nTC f p) :
    Hvar code p <= ((n : Real) - 1) * nTC f p +
      ∑ i, condH code (g i) p := by
  have hsplit :=
    nDTC_eq_code_entropy_sub_recovery_add_condDTC hp f g hinj code
  linarith

/-- **Alphabet-free cost of an approximately deletion-common hard code.** -/
theorem ofFunction_score_le_n_mul_nTC_add_two_recovery [Nonempty Omega]
    {delta : Type} [Fintype delta] [DecidableEq delta]
    (hp : IsPMF p) (f : forall i : Fin n, Omega -> kappa i)
    (g : forall i : Fin n, Omega -> gamma i)
    (hinj : forall i, Function.Injective (fun z => (f i z, g i z)))
    (code : Omega -> delta)
    (hcondDTC : 0 <= nCondDTC f g p code)
    (hDTCle : nDTC f g p <= ((n : Real) - 1) * nTC f p) :
    (NLatent.ofFunction hp code).score f g <=
      (n : Real) * nTC f p + 2 * ∑ i, condH code (g i) p := by
  have htc := nCondTC_le_nTC_add_code_entropy hp f code
  have hcode := code_entropy_le_n_minus_one_mul_nTC_add_recovery
    hp f g hinj code hcondDTC hDTCle
  rw [NLatent.ofFunction_score_eq_nDetScore hp f g hinj code]
  unfold nDetScore
  linarith

end stoch_to_det
