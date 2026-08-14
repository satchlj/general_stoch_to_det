import stoch_to_det.NVarHardening
import stoch_to_det.NVarTwoVariableInput

/-!
# One-sided posterior compression

The calibrated two-variable theorem is applied to `(X,C₀)` with latent `C₁`.
An independent finite table realizes `C₀` as a function of `X` and a seed;
finite averaging then fixes the seed without an alphabet loss.
-/

namespace stoch_to_det

open Finset

namespace FiniteInfo

lemma Hvar_push_source
    {S T F : Type*} [Fintype S] [Fintype T] [DecidableEq T]
    [Fintype F] [DecidableEq F]
    (embed : S -> T) (f : T -> F) (m : S -> Real) :
    Hvar f (push embed m) = Hvar (f ∘ embed) m := by
  unfold Hvar
  rw [push_push]

lemma condH_push_source
    {S T F K : Type*} [Fintype S] [Fintype T] [DecidableEq T]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    (embed : S -> T) (f : T -> F) (h : T -> K) (m : S -> Real) :
    condH f h (push embed m) = condH (f ∘ embed) (h ∘ embed) m := by
  unfold condH
  change Hvar (fun x => (f x, h x)) (push embed m) -
    Hvar h (push embed m) = _
  rw [Hvar_push_source, Hvar_push_source]
  rfl

lemma condMI_push_source
    {S T F G K : Type*} [Fintype S] [Fintype T] [DecidableEq T]
    [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype K] [DecidableEq K]
    (embed : S -> T) (f : T -> F) (g : T -> G) (h : T -> K)
    (m : S -> Real) :
    condMI f g h (push embed m) =
      condMI (f ∘ embed) (g ∘ embed) (h ∘ embed) m := by
  unfold condMI
  change Hvar (fun x => (f x, h x)) (push embed m) +
      Hvar (fun x => (g x, h x)) (push embed m) -
      Hvar (fun x => (f x, g x, h x)) (push embed m) -
      Hvar h (push embed m) = _
  rw [Hvar_push_source, Hvar_push_source, Hvar_push_source,
    Hvar_push_source]
  rfl

/-- Mutual information vanishes under a finite product law. -/
lemma MI_product_zero
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    {r : A -> Real} {s : B -> Real} (hr : IsPMF r) (hs : IsPMF s) :
    MI Prod.fst Prod.snd (fun u : A × B => r u.1 * s u.2) = 0 := by
  let q : A × B -> Real := fun u => r u.1 * s u.2
  have hr_sum : ∑ a, r a = 1 := by simpa [mass] using hr.total
  have hs_sum : ∑ b, s b = 1 := by simpa [mass] using hs.total
  have hq : IsPMF q := by
    constructor
    · intro u
      exact mul_nonneg (hr.nonneg u.1) (hs.nonneg u.2)
    · unfold mass q
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [hs_sum]
      simp [hr_sum]
  have hfst : push Prod.fst q = r := by
    funext a
    unfold push
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp [q, ← Finset.mul_sum, hs_sum]
  have hsnd : push Prod.snd q = s := by
    funext b
    unfold push
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp [q, ← Finset.sum_mul, hr_sum]
  have hpair : push (fun u : A × B => (u.1, u.2)) q = q := by
    simpa only using push_id q
  have hfiber (b : B) : H (fun a => q (a, b)) = s b * H r := by
    have heq : (fun a => q (a, b)) = fun a => s b * r a := by
      funext a
      dsimp only [q]
      ring
    rw [heq]
    exact H_smul hr.isFinMeas (hs.nonneg b)
  have hqH := H_prod_eq_snd_add_fibers hq
  rw [hsnd] at hqH
  simp_rw [hfiber] at hqH
  rw [← Finset.sum_mul, hs_sum, one_mul] at hqH
  change MI Prod.fst Prod.snd q = 0
  unfold MI Hvar
  rw [hfst, hsnd, hpair, hqH]
  ring

/-- Conditional mutual information vanishes when its left input is already a
function of the conditioning input. -/
lemma condMI_function_of_condition_left_zero
    {A F G K : Type*} [Fintype A] [Fintype F] [Fintype G] [Fintype K]
    [DecidableEq F] [DecidableEq G] [DecidableEq K]
    {m : A -> Real} (hm : IsPMF m) (f : A -> F) (g : A -> G)
    (h : A -> K) (decode : K -> F)
    (hdecode : forall a, decode (h a) = f a) :
    condMI f g h m = 0 := by
  have hH := condH_function_of_condition_zero hm f h decode hdecode
  have hle := condMI_le_condH_left hm f g h
  have hnonneg := condMI_nonneg hm f g h
  linarith

/-- The abstract Shannon ledger behind one-sided posterior compression.  No
alphabet size occurs: `Z` only needs to be a function of `(X,C₀)`. -/
lemma oneSided_bridge
    {A XTy CTy ZTy : Type*} [Fintype A]
    [Fintype XTy] [DecidableEq XTy] [Fintype CTy] [DecidableEq CTy]
    [Fintype ZTy] [DecidableEq ZTy]
    {m : A -> Real} (hm : IsPMF m)
    (X : A -> XTy) (C₀ C₁ : A -> CTy) (Z : A -> ZTy)
    (decode : XTy × CTy -> ZTy)
    (hdecode : forall a, decode (X a, C₀ a) = Z a)
    (hsymm : condMI C₀ X C₁ m = condMI C₁ X C₀ m) :
    condMI C₁ X Z m + condH Z C₁ m <=
      condMI X C₀ Z m + condH Z X m + condH Z C₀ m +
        2 * condMI C₁ X C₀ m := by
  let swapCC : CTy × CTy -> CTy × CTy := fun z => (z.2, z.1)
  let swapZX : ZTy × XTy -> XTy × ZTy := fun z => (z.2, z.1)
  let swapXZ : XTy × ZTy -> ZTy × XTy := fun z => (z.2, z.1)
  let swapCX : CTy × XTy -> XTy × CTy := fun z => (z.2, z.1)
  have hinjCC : Function.Injective swapCC := by
    intro a b hab
    exact Prod.ext (congrArg Prod.snd hab) (congrArg Prod.fst hab)
  have hinjZX : Function.Injective swapZX := by
    intro a b hab
    exact Prod.ext (congrArg Prod.snd hab) (congrArg Prod.fst hab)
  have hinjXZ : Function.Injective swapXZ := by
    intro a b hab
    exact Prod.ext (congrArg Prod.snd hab) (congrArg Prod.fst hab)
  have hinjCX : Function.Injective swapCX := by
    intro a b hab
    exact Prod.ext (congrArg Prod.snd hab) (congrArg Prod.fst hab)
  have hZzero : condH Z (fun a => (X a, C₀ a)) m = 0 := by
    exact condH_function_of_condition_zero hm Z (fun a => (X a, C₀ a))
      decode hdecode
  have hZmi : condMI Z C₁ (fun a => (C₀ a, X a)) m = 0 := by
    apply condMI_function_of_condition_left_zero hm Z C₁
      (fun a => (C₀ a, X a)) (fun z => decode (z.2, z.1))
    intro a
    exact hdecode a

  have hrefine : condMI X C₁ (fun a => (Z a, C₀ a)) m <=
      condMI C₁ X C₀ m := by
    have hXZ := condMI_pair_left hm X Z C₁ C₀
    have hZX := condMI_pair_left hm Z X C₁ C₀
    have hreorder := condMI_comp_left_eq_of_injective hm
      (fun a => (Z a, X a)) C₁ C₀ swapZX hinjZX
    have hcond := condMI_equiv_cond hm X C₁
      (fun a => (C₀ a, Z a)) (Equiv.prodComm CTy ZTy)
    have hnonneg := condMI_nonneg hm Z C₁ C₀
    have hcomm := condMI_comm hm X C₁ C₀
    dsimp only [swapZX] at hreorder
    rw [hZmi] at hXZ
    have htarget : condMI X C₁ (fun a => (Z a, C₀ a)) m =
        condMI X C₁ (fun a => (C₀ a, Z a)) m := by
      simpa using hcond
    rw [htarget]
    linarith

  have hten : condMI C₁ X Z m <=
      condMI X C₀ Z m + condMI C₁ X C₀ m := by
    have hleft := condMI_pair_right hm X C₁ C₀ Z
    have hright := condMI_pair_right hm X C₀ C₁ Z
    have hreorder := condMI_comp_right_eq_of_injective hm X
      (fun a => (C₁ a, C₀ a)) Z swapCC hinjCC
    have hcond := condMI_equiv_cond hm X C₁
      (fun a => (Z a, C₀ a)) (Equiv.prodComm ZTy CTy)
    have hnonneg := condMI_nonneg hm X C₀ (fun a => (Z a, C₁ a))
    have hcomm1 := condMI_comm hm X C₁ Z
    have hcomm2 := condMI_comm hm X C₀ Z
    dsimp only [swapCC] at hreorder
    have hrefine' : condMI X C₁ (fun a => (Z a, C₀ a)) m <=
        condMI C₁ X C₀ m := hrefine
    linarith

  have heleven : condMI Z X C₁ m <=
      condMI C₁ X C₀ m + condH Z C₀ m := by
    have hmonoPair := condMI_pair_left hm Z C₀ X C₁
    have hnonneg0 := condMI_nonneg hm C₀ X (fun a => (C₁ a, Z a))
    have hreorder := condMI_comp_left_eq_of_injective hm
      (fun a => (Z a, C₀ a)) X C₁
      (fun z : ZTy × CTy => (z.2, z.1)) (by
        intro a b hab
        exact Prod.ext (congrArg Prod.snd hab) (congrArg Prod.fst hab))
    have hexpand := condMI_pair_left hm C₀ Z X C₁
    have hleH := condMI_le_condH_left hm Z X (fun a => (C₁ a, C₀ a))
    have hcondH := condH_pair_condition_le hm Z C₁ C₀
    dsimp only at hreorder
    linarith

  have hentropy : condH Z C₁ m <= condMI Z X C₁ m + condH Z X m := by
    have hchain := condMI_eq_condH_sub_pair hm Z X C₁
    have hcondH := condH_pair_condition_le hm Z C₁ X
    have hequiv := condH_equiv_cond hm Z (fun a => (C₁ a, X a))
      (Equiv.prodComm CTy XTy)
    have hequiv' : condH Z (fun a => (X a, C₁ a)) m =
        condH Z (fun a => (C₁ a, X a)) m := by
      simpa using hequiv
    linarith

  linarith

/-- Revealing an independent functional-representation seed cannot increase
the averaged one-sided hardening error. -/
lemma seed_conditioning_le
    {A XTy CTy ETy ZTy : Type*} [Fintype A]
    [Fintype XTy] [DecidableEq XTy] [Fintype CTy] [DecidableEq CTy]
    [Fintype ETy] [DecidableEq ETy] [Fintype ZTy] [DecidableEq ZTy]
    {m : A -> Real} (hm : IsPMF m)
    (X : A -> XTy) (C : A -> CTy) (E : A -> ETy) (Z : A -> ZTy)
    (decode : XTy × ETy -> ZTy)
    (hdecode : forall a, decode (X a, E a) = Z a)
    (hindep : MI E (fun a => (C a, X a)) m = 0) :
    condMI C X (fun a => (Z a, E a)) m +
        condH Z (fun a => (C a, E a)) m <=
      condMI C X Z m + condH Z C m := by
  let swapXC : XTy × CTy -> CTy × XTy := fun z => (z.2, z.1)
  let swapEZ : ETy × ZTy -> ZTy × ETy := fun z => (z.2, z.1)
  let swapXE : XTy × ETy -> ETy × XTy := fun z => (z.2, z.1)
  have hinjEZ : Function.Injective swapEZ := by
    intro a b hab
    exact Prod.ext (congrArg Prod.snd hab) (congrArg Prod.fst hab)
  have hinjXE : Function.Injective swapXE := by
    intro a b hab
    exact Prod.ext (congrArg Prod.snd hab) (congrArg Prod.fst hab)

  have hCEX : condMI C E X m = 0 := by
    have hpair := MI_pair_left hm X C E
    have hreorder := MI_equiv_left hm (fun a => (C a, X a))
      (Equiv.prodComm CTy XTy) E
    have hcomm := MI_comm hm (fun a => (C a, X a)) E
    have hnonneg := MI_nonneg hm X E
    have hcondnonneg := condMI_nonneg hm C E X
    have hreorder' : MI (fun a => (X a, C a)) E m =
        MI (fun a => (C a, X a)) E m := by
      simpa using hreorder
    linarith

  have hZmi : condMI Z C (fun a => (X a, E a)) m = 0 := by
    exact condMI_function_of_condition_left_zero hm Z C
      (fun a => (X a, E a)) decode hdecode
  have hCE_XZ : condMI C E (fun a => (X a, Z a)) m = 0 := by
    have hEZ := condMI_pair_right hm C E Z X
    have hZE := condMI_pair_right hm C Z E X
    have hreorder := condMI_comp_right_eq_of_injective hm C
      (fun a => (E a, Z a)) X swapEZ hinjEZ
    have hcommZ := condMI_comm hm Z C (fun a => (X a, E a))
    have hnonneg := condMI_nonneg hm C Z X
    have htarget_nonneg := condMI_nonneg hm C E (fun a => (X a, Z a))
    dsimp only [swapEZ] at hreorder
    linarith

  have hMI : condMI C X (fun a => (Z a, E a)) m <= condMI C X Z m := by
    have hXE := condMI_pair_right hm C X E Z
    have hEX := condMI_pair_right hm C E X Z
    have hreorder := condMI_comp_right_eq_of_injective hm C
      (fun a => (X a, E a)) Z swapXE hinjXE
    have hcond := condMI_equiv_cond hm C E (fun a => (X a, Z a))
      (Equiv.prodComm XTy ZTy)
    have hnonneg := condMI_nonneg hm C E Z
    have hCE' : condMI C E (fun a => (Z a, X a)) m = 0 := by
      have := hcond
      simpa [hCE_XZ] using this
    dsimp only [swapXE] at hreorder
    linarith

  have hH : condH Z (fun a => (C a, E a)) m <= condH Z C m := by
    have hmono := condH_pair_condition_le hm Z E C
    have hequiv := condH_equiv_cond hm Z (fun a => (E a, C a))
      (Equiv.prodComm ETy CTy)
    have hequiv' : condH Z (fun a => (C a, E a)) m =
        condH Z (fun a => (E a, C a)) m := by
      simpa using hequiv
    linarith
  linarith

/-- Entropy chain rule for an independent finite seed and a seed-indexed
observable. -/
lemma Hvar_seed_product
    {E W F : Type*} [Fintype E] [DecidableEq E]
    [Fintype W] [Fintype F] [DecidableEq F]
    {r : E -> Real} {s : W -> Real} (hr : IsPMF r) (hs : IsPMF s)
    (f : E -> W -> F) :
    Hvar (fun u : E × W => (f u.1 u.2, u.1))
        (fun u => r u.1 * s u.2) =
      Hvar Prod.fst (fun u : E × W => r u.1 * s u.2) +
        ∑ e, r e * Hvar (f e) s := by
  let m : E × W -> Real := fun u => r u.1 * s u.2
  have hm : IsPMF m := by
    constructor
    · intro u
      exact mul_nonneg (hr.nonneg u.1) (hs.nonneg u.2)
    · unfold mass m
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      have hs_sum : ∑ w, s w = 1 := by simpa [mass] using hs.total
      have hr_sum : ∑ e, r e = 1 := by simpa [mass] using hr.total
      rw [hs_sum]
      simp [hr_sum]
  have hchain := Hvar_pair_eq_sum_fibers hm
    (fun u : E × W => f u.1 u.2) Prod.fst
  have hfiber (e : E) :
      push (fun u : E × W => f u.1 u.2)
          (fun u => if u.1 = e then m u else 0) =
        fun y => r e * push (f e) s y := by
    funext y
    unfold push m
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    calc
      (∑ a, ∑ w, if f a w = y then
          (if a = e then r a * s w else 0) else 0) =
        ∑ a, if a = e then
          ∑ w, if f a w = y then r a * s w else 0 else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases hae : a = e <;> simp [hae]
      _ =
        ∑ w, if f e w = y then r e * s w else 0 := by
          simp
      _ = r e * ∑ w, if f e w = y then s w else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w _
          split_ifs <;> ring
      _ = r e * push (f e) s y := by
          unfold push
          rw [Finset.sum_filter]
  change Hvar (fun u : E × W => (f u.1 u.2, u.1)) m = _
  rw [hchain]
  simp_rw [hfiber]
  have hscale (e : E) : H (fun y => r e * push (f e) s y) =
      r e * Hvar (f e) s := by
    unfold Hvar
    exact H_smul (isFinMeas_push hs.isFinMeas) (hr.nonneg e)
  simp_rw [hscale]
  simpa [m]

/-- The expectation of the fixed-seed one-sided errors is the conditional
error before fixing the seed. -/
lemma average_fixed_error_eq
    {E W XTy CTy ZTy : Type*} [Fintype E] [DecidableEq E]
    [Fintype W] [Fintype XTy] [DecidableEq XTy]
    [Fintype CTy] [DecidableEq CTy] [Fintype ZTy] [DecidableEq ZTy]
    {r : E -> Real} {s : W -> Real} (hr : IsPMF r) (hs : IsPMF s)
    (X : W -> XTy) (C : W -> CTy) (z : E -> W -> ZTy) :
    (∑ e, r e * (condMI C X (z e) s + condH (z e) C s)) =
      condMI (fun u : E × W => C u.2) (fun u => X u.2)
          (fun u => (z u.1 u.2, u.1)) (fun u => r u.1 * s u.2) +
        condH (fun u : E × W => z u.1 u.2)
          (fun u => (C u.2, u.1)) (fun u => r u.1 * s u.2) := by
  let m : E × W -> Real := fun u => r u.1 * s u.2
  let Evar : E × W -> E := Prod.fst
  have hCZ := Hvar_seed_product hr hs (fun e w => (C w, z e w))
  have hXZ := Hvar_seed_product hr hs (fun e w => (X w, z e w))
  have hCXZ := Hvar_seed_product hr hs (fun e w => (C w, X w, z e w))
  have hZ := Hvar_seed_product hr hs z
  have hZC := Hvar_seed_product hr hs (fun e w => (z e w, C w))
  have hC := Hvar_seed_product hr hs (fun _e w => C w)
  have hCZassoc : Hvar (fun u : E × W => (C u.2, z u.1 u.2, u.1)) m =
      Hvar (fun u => ((C u.2, z u.1 u.2), u.1)) m := by
    have hm : IsPMF m := by
      constructor
      · intro u; exact mul_nonneg (hr.nonneg u.1) (hs.nonneg u.2)
      · unfold mass m
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum]
        have hs_sum : ∑ w, s w = 1 := by simpa [mass] using hs.total
        have hr_sum : ∑ e, r e = 1 := by simpa [mass] using hr.total
        rw [hs_sum]
        simp [hr_sum]
    simpa using Hvar_equiv hm
      (fun u : E × W => ((C u.2, z u.1 u.2), u.1))
      (Equiv.prodAssoc CTy ZTy E)
  have hXZassoc : Hvar (fun u : E × W => (X u.2, z u.1 u.2, u.1)) m =
      Hvar (fun u => ((X u.2, z u.1 u.2), u.1)) m := by
    have hm : IsPMF m := by
      constructor
      · intro u; exact mul_nonneg (hr.nonneg u.1) (hs.nonneg u.2)
      · unfold mass m
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum]
        have hs_sum : ∑ w, s w = 1 := by simpa [mass] using hs.total
        have hr_sum : ∑ e, r e = 1 := by simpa [mass] using hr.total
        rw [hs_sum]
        simp [hr_sum]
    simpa using Hvar_equiv hm
      (fun u : E × W => ((X u.2, z u.1 u.2), u.1))
      (Equiv.prodAssoc XTy ZTy E)
  have hCXZassoc :
      Hvar (fun u : E × W => (C u.2, X u.2, z u.1 u.2, u.1)) m =
        Hvar (fun u => ((C u.2, X u.2, z u.1 u.2), u.1)) m := by
    have hm : IsPMF m := by
      constructor
      · intro u; exact mul_nonneg (hr.nonneg u.1) (hs.nonneg u.2)
      · unfold mass m
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum]
        have hs_sum : ∑ w, s w = 1 := by simpa [mass] using hs.total
        have hr_sum : ∑ e, r e = 1 := by simpa [mass] using hr.total
        rw [hs_sum]
        simp [hr_sum]
    let assoc : (CTy × XTy × ZTy) × E ≃ CTy × XTy × ZTy × E :=
      (Equiv.prodAssoc CTy (XTy × ZTy) E).trans
        (Equiv.prodCongr (Equiv.refl CTy) (Equiv.prodAssoc XTy ZTy E))
    simpa [assoc] using Hvar_equiv hm
      (fun u : E × W => ((C u.2, X u.2, z u.1 u.2), u.1)) assoc
  have hZCassoc : Hvar (fun u : E × W => (z u.1 u.2, C u.2, u.1)) m =
      Hvar (fun u => ((z u.1 u.2, C u.2), u.1)) m := by
    have hm : IsPMF m := by
      constructor
      · intro u; exact mul_nonneg (hr.nonneg u.1) (hs.nonneg u.2)
      · unfold mass m
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum]
        have hs_sum : ∑ w, s w = 1 := by simpa [mass] using hs.total
        have hr_sum : ∑ e, r e = 1 := by simpa [mass] using hr.total
        rw [hs_sum]
        simp [hr_sum]
    simpa using Hvar_equiv hm
      (fun u : E × W => ((z u.1 u.2, C u.2), u.1))
      (Equiv.prodAssoc ZTy CTy E)
  unfold condMI condH
  change (∑ e, r e *
      ((Hvar (fun w => (C w, z e w)) s + Hvar (fun w => (X w, z e w)) s -
          Hvar (fun w => (C w, X w, z e w)) s - Hvar (z e) s) +
        (Hvar (fun w => (z e w, C w)) s - Hvar C s))) = _
  rw [hCZassoc, hXZassoc, hCXZassoc, hZCassoc]
  dsimp only [m, Evar] at hCZ hXZ hCXZ hZ hZC hC ⊢
  rw [hCZ, hXZ, hCXZ, hZ, hZC, hC]
  have hsum :
      (∑ e, r e *
        (Hvar (fun w => (C w, z e w)) s + Hvar (fun w => (X w, z e w)) s -
            Hvar (fun w => (C w, X w, z e w)) s - Hvar (z e) s +
          (Hvar (fun w => (z e w, C w)) s - Hvar C s))) =
      ∑ e, (r e * Hvar (fun w => (C w, z e w)) s +
          r e * Hvar (fun w => (X w, z e w)) s -
          r e * Hvar (fun w => (C w, X w, z e w)) s -
          r e * Hvar (z e) s +
          (r e * Hvar (fun w => (z e w, C w)) s - r e * Hvar C s)) := by
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hsum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring

/-- Some point is no larger than its expectation under a finite PMF. -/
lemma exists_le_weighted_average
    {E : Type*} [Fintype E] [DecidableEq E]
    {r : E -> Real} (hr : IsPMF r) (a : E -> Real) :
    exists e, a e <= ∑ j, r j * a j := by
  let s : Finset E := Finset.univ.filter fun e => r e ≠ 0
  have htotal : ∑ e, r e = 1 := by simpa [mass] using hr.total
  have hs : s.Nonempty := by
    by_contra hsempty
    have hz (e : E) : r e = 0 := by
      by_contra he
      exact hsempty ⟨e, by simp [s, he]⟩
    simp_rw [hz] at htotal
    norm_num at htotal
  have hfilter (f : E -> Real) : (∑ e ∈ s, r e * f e) = ∑ e, r e * f e := by
    rw [show (∑ e, r e * f e) = ∑ e ∈ Finset.univ, r e * f e by rfl]
    dsimp only [s]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro e _ he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    simp [not_ne_iff.mp he]
  let avg : Real := ∑ j, r j * a j
  have hsumR : (∑ e ∈ s, r e) = 1 := by
    simpa using (hfilter fun _ => (1 : Real)).trans (by
      simpa using htotal)
  have hle : (∑ e ∈ s, r e * a e) <= ∑ e ∈ s, r e * avg := by
    rw [hfilter]
    dsimp only [avg]
    rw [← Finset.sum_mul, hsumR, one_mul]
  obtain ⟨e, hes, he⟩ := Finset.exists_le_of_sum_le hs hle
  have hre : 0 < r e := by
    have hne : r e ≠ 0 := (Finset.mem_filter.mp hes).2
    exact lt_of_le_of_ne (hr.nonneg e) (Ne.symm hne)
  refine ⟨e, ?_⟩
  dsimp only [avg] at he ⊢
  nlinarith

/-- Product-sum identity for a finite table with `N` independent entries. -/
lemma sum_fin_table_prod {C : Type} [Fintype C] (N : Nat)
    (q : Fin N -> C -> Real) :
    (∑ e : Fin N -> C, ∏ j, q j (e j)) = ∏ j, ∑ c, q j c := by
  classical
  induction N with
  | zero => simp
  | succ N ih =>
      let pe : (Fin (N + 1) -> C) ≃ C × (Fin N -> C) :=
        (Fin.consEquiv (fun _ : Fin (N + 1) => C)).symm
      calc
        (∑ e : Fin (N + 1) -> C, ∏ j, q j (e j)) =
            ∑ z : C × (Fin N -> C),
              q 0 z.1 * ∏ j : Fin N, q j.succ (z.2 j) := by
                apply Fintype.sum_equiv pe
                intro e
                rw [Fin.prod_univ_succ]
                rfl
        _ = ∑ c : C, ∑ e : Fin N -> C,
              q 0 c * ∏ j : Fin N, q j.succ (e j) := by
                rw [Fintype.sum_prod_type]
        _ = (∑ c : C, q 0 c) *
              (∑ e : Fin N -> C, ∏ j : Fin N, q j.succ (e j)) := by
                rw [Finset.mul_sum]
                simp_rw [Finset.sum_mul]
                exact Finset.sum_comm
        _ = (∑ c : C, q 0 c) * ∏ j : Fin N, ∑ c, q j.succ c := by
                rw [ih (fun j => q j.succ)]
        _ = ∏ j : Fin (N + 1), ∑ c, q j c := by
                rw [Fin.prod_univ_succ]

/-- One-coordinate marginal of the finite independent table. -/
lemma sum_fin_table_eval {C : Type} [Fintype C] [DecidableEq C]
    (N : Nat) (q : Fin N -> C -> Real) (hq : forall j, ∑ c, q j c = 1)
    (j : Fin N) (c : C) :
    (∑ e : Fin N -> C,
      (∏ k, q k (e k)) * (if e j = c then 1 else 0)) = q j c := by
  classical
  let q' : Fin N -> C -> Real := fun k d =>
    if k = j then if d = c then q k d else 0 else q k d
  have hterm (e : Fin N -> C) :
      (∏ k, q k (e k)) * (if e j = c then 1 else 0) =
        ∏ k, q' k (e k) := by
    by_cases he : e j = c
    · have heq : (fun k => q' k (e k)) = fun k => q k (e k) := by
        funext k
        by_cases hkj : k = j
        · subst k
          simp [q', he]
        · simp [q', hkj]
      rw [if_pos he, mul_one, heq]
    · rw [if_neg he, mul_zero]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [q', he]
  simp_rw [hterm]
  rw [sum_fin_table_prod N q']
  have hsum (k : Fin N) :
      (∑ d, q' k d) = if k = j then q j c else 1 := by
    by_cases hkj : k = j
    · subst k
      simp [q']
    · simp [q', hkj, hq k]
  simp_rw [hsum]
  rw [Finset.prod_eq_single j]
  · simp
  · intro k _ hkj
    simp [hkj]
  · simp

end FiniteInfo

namespace NLatent

variable {Omega : Type} [Fintype Omega] [DecidableEq Omega]
variable {p : Omega -> Real}

/-- Law of the pair `(X,C₀)`. -/
noncomputable def posteriorPairLaw (V : NLatent p) : Omega × V.ι -> Real :=
  push (fun w : V.ι × Omega => (w.2, w.1)) V.joint

lemma posteriorPairLaw_isPMF (V : NLatent p) : IsPMF V.posteriorPairLaw :=
  isPMF_push V.joint_isPMF

lemma posteriorPairLaw_eq_replica_push (V : NLatent p) :
    V.posteriorPairLaw =
      push (fun u : (V.ι × V.ι) × Omega => (u.2, u.1.1)) V.replicaLaw := by
  unfold posteriorPairLaw
  calc
    push (fun w : V.ι × Omega => (w.2, w.1)) V.joint =
        push (fun w : V.ι × Omega => (w.2, w.1))
          (push (fun u : (V.ι × V.ι) × Omega => (u.1.1, u.2))
            V.replicaLaw) := by rw [V.push_replica_first_source]
    _ = _ := by
      rw [push_push]
      rfl

private def pairJointReorder (V : NLatent p) :
    ((V.ι × V.ι) × Omega) -> V.ι × (Omega × V.ι) :=
  fun u => (u.1.2, (u.2, u.1.1))

/-- Joint law of latent `C₁` and source `(X,C₀)`. -/
noncomputable def posteriorPairJoint (V : NLatent p) :
    V.ι × (Omega × V.ι) -> Real :=
  push V.pairJointReorder V.replicaLaw

lemma posteriorPairJoint_isPMF (V : NLatent p) :
    IsPMF V.posteriorPairJoint := isPMF_push V.replicaLaw_isPMF

lemma push_posteriorPairJoint_source (V : NLatent p) :
    push Prod.snd V.posteriorPairJoint = V.posteriorPairLaw := by
  unfold posteriorPairJoint posteriorPairLaw
  rw [push_push]
  change push (fun u : (V.ι × V.ι) × Omega => (u.2, u.1.1)) V.replicaLaw =
    push (fun w : V.ι × Omega => (w.2, w.1)) V.joint
  calc
    _ = push (fun w : V.ι × Omega => (w.2, w.1))
          (push (fun u : (V.ι × V.ι) × Omega => (u.1.1, u.2))
            V.replicaLaw) := by
          symm
          rw [push_push]
          rfl
    _ = _ := by rw [V.push_replica_first_source]

noncomputable def posteriorPairNLatent (V : NLatent p) :
    NLatent V.posteriorPairLaw :=
  NLatent.ofJoint V.posteriorPairJoint V.posteriorPairJoint_isPMF
    V.posteriorPairLaw_isPMF V.push_posteriorPairJoint_source

theorem posteriorPairNLatent_joint (V : NLatent p) :
    V.posteriorPairNLatent.joint = V.posteriorPairJoint := by
  exact NLatent.ofJoint_joint_eq V.posteriorPairJoint
    V.posteriorPairJoint_isPMF V.posteriorPairLaw_isPMF
    V.push_posteriorPairJoint_source

/-- Regard the preceding arbitrary-source latent as the ordinary two-variable
latent required by the certified endpoint. -/
noncomputable def posteriorPairLatent (V : NLatent p) :
    Latent V.posteriorPairLaw where
  ι := V.posteriorPairNLatent.ι
  fin := V.posteriorPairNLatent.fin
  dec := V.posteriorPairNLatent.dec
  prior := V.posteriorPairNLatent.prior
  comp := V.posteriorPairNLatent.comp
  prior_isPMF := V.posteriorPairNLatent.prior_isPMF
  comp_isPMF := V.posteriorPairNLatent.comp_isPMF
  mixture := V.posteriorPairNLatent.mixture

theorem posteriorPairLatent_joint (V : NLatent p) :
    V.posteriorPairLatent.joint = V.posteriorPairJoint := by
  change V.posteriorPairNLatent.joint = V.posteriorPairJoint
  exact V.posteriorPairNLatent_joint

private theorem posteriorPair_condMI_lift (V : NLatent p)
    {F G K : Type} [Fintype F] [Fintype G] [Fintype K]
    [DecidableEq F] [DecidableEq G] [DecidableEq K]
    (f : V.ι × (Omega × V.ι) -> F)
    (g : V.ι × (Omega × V.ι) -> G)
    (h : V.ι × (Omega × V.ι) -> K) :
    condMI f g h V.posteriorPairJoint =
      condMI (f ∘ V.pairJointReorder) (g ∘ V.pairJointReorder)
        (h ∘ V.pairJointReorder) V.replicaLaw := by
  exact FiniteInfo.condMI_push_source V.pairJointReorder f g h V.replicaLaw

theorem posteriorPairLatent_score (V : NLatent p) :
    V.posteriorPairLatent.score = 2 * V.replicaDefect := by
  let A : ((V.ι × V.ι) × Omega) -> V.ι := fun u => u.1.1
  let B : ((V.ι × V.ι) × Omega) -> V.ι := fun u => u.1.2
  let X : ((V.ι × V.ι) × Omega) -> Omega := fun u => u.2
  have hfirst :
      condMI
          (fun w : V.ι × (Omega × V.ι) => w.2.1)
          (fun w => w.2.2) (fun w => w.1) V.posteriorPairJoint =
        V.replicaDefect := by
    have hlift := V.posteriorPair_condMI_lift
      (fun w : V.ι × (Omega × V.ι) => w.2.1)
      (fun w => w.2.2) (fun w => w.1)
    have hswap := FiniteInfo.condMI_comp_equiv_eq_of_invariant V.replicaLaw
      V.replicaSwap V.replicaLaw_swap_equiv B X A
    have hcomm := FiniteInfo.condMI_comm V.replicaLaw_isPMF X A B
    have hswap' : condMI A X B V.replicaLaw = V.replicaDefect := by
      simpa [A, B, X, NLatent.replicaDefect, NLatent.replicaSwap,
        Function.comp_def] using hswap
    dsimp only [pairJointReorder, A, B, X, Function.comp_def] at hlift hcomm
    rw [hlift, hcomm, hswap']
  have hsecond :
      condMI
          (fun w : V.ι × (Omega × V.ι) => w.1)
          (fun w => w.2.1) (fun w => w.2.2) V.posteriorPairJoint =
        V.replicaDefect := by
    have hlift := V.posteriorPair_condMI_lift
      (fun w : V.ι × (Omega × V.ι) => w.1)
      (fun w => w.2.1) (fun w => w.2.2)
    dsimp only [pairJointReorder, NLatent.replicaDefect] at hlift ⊢
    exact hlift
  have hthird :
      condMI
          (fun w : V.ι × (Omega × V.ι) => w.1)
          (fun w => w.2.2) (fun w => w.2.1) V.posteriorPairJoint = 0 := by
    have hlift := V.posteriorPair_condMI_lift
      (fun w : V.ι × (Omega × V.ι) => w.1)
      (fun w => w.2.2) (fun w => w.2.1)
    rw [hlift]
    have hcomm := FiniteInfo.condMI_comm V.replicaLaw_isPMF
      (fun u : (V.ι × V.ι) × Omega => u.1.2) (fun u => u.1.1)
      (fun u => u.2)
    simpa [pairJointReorder, Function.comp_def] using hcomm.trans V.replica_markov
  change
    condMI (fun w : V.ι × (Omega × V.ι) => w.2.1) (fun w => w.2.2)
        (fun w => w.1) V.posteriorPairLatent.joint +
      condMI (fun w => w.1) (fun w => w.2.1) (fun w => w.2.2)
          V.posteriorPairLatent.joint +
      condMI (fun w => w.1) (fun w => w.2.2) (fun w => w.2.1)
          V.posteriorPairLatent.joint = 2 * V.replicaDefect
  rw [V.posteriorPairLatent_joint, hfirst]
  change V.replicaDefect +
      condMI (fun w : V.ι × (Omega × V.ι) => w.1) (fun w => w.2.1)
          (fun w => w.2.2) V.posteriorPairJoint +
      condMI (fun w => w.1) (fun w => w.2.2) (fun w => w.2.1)
          V.posteriorPairJoint = 2 * V.replicaDefect
  rw [hsecond, hthird]
  ring

/-- The centralized two-variable theorem supplies the pair code at cost
`2 * certifiedFactor * b`. -/
theorem exists_posteriorPair_code (V : NLatent p) :
    exists phi : Omega × V.ι -> Fin (Fintype.card (Omega × V.ι)),
      detScore V.posteriorPairLaw phi <=
        (2 * NVarTwoVariableInput.certifiedFactor) * V.replicaDefect := by
  let hpPair := V.posteriorPairLaw_isPMF
  obtain ⟨phi, hphi⟩ := exists_T_optimal_code hpPair
  refine ⟨phi, ?_⟩
  have htwo := NVarTwoVariableInput.T_le_certifiedFactor hpPair
  have htau := tau_le_score V.posteriorPairLatent
  have hscore := V.posteriorPairLatent_score
  rw [← Latent.ofFunction_score_eq_detScore hpPair phi, hphi]
  calc
    T V.posteriorPairLaw <=
        NVarTwoVariableInput.certifiedFactor *
          tau V.posteriorPairLaw := htwo
    _ <= NVarTwoVariableInput.certifiedFactor *
        V.posteriorPairLatent.score := by
      exact mul_le_mul_of_nonneg_left htau (by
        rw [NVarTwoVariableInput.certifiedFactor_eq]
        norm_num)
    _ = (2 * NVarTwoVariableInput.certifiedFactor) *
        V.replicaDefect := by rw [hscore]; ring

/-- A pair code supplied by the two-variable theorem already has small
one-sided error when regarded as a stochastic code of `X`. -/
theorem replica_oneSided_le_detScore_add (V : NLatent p)
    {delta : Type*} [Fintype delta] [DecidableEq delta]
    (phi : Omega × V.ι -> delta) :
    let Z : ((V.ι × V.ι) × Omega) -> delta :=
      fun u => phi (u.2, u.1.1)
    condMI (fun u => u.1.2) (fun u => u.2) Z V.replicaLaw +
        condH Z (fun u => u.1.2) V.replicaLaw <=
      detScore V.posteriorPairLaw phi + 2 * V.replicaDefect := by
  let X : ((V.ι × V.ι) × Omega) -> Omega := fun u => u.2
  let C₀ : ((V.ι × V.ι) × Omega) -> V.ι := fun u => u.1.1
  let C₁ : ((V.ι × V.ι) × Omega) -> V.ι := fun u => u.1.2
  let Z : ((V.ι × V.ι) × Omega) -> delta := fun u => phi (u.2, u.1.1)
  have hsymm : condMI C₀ X C₁ V.replicaLaw =
      condMI C₁ X C₀ V.replicaLaw := by
    have h := FiniteInfo.condMI_comp_equiv_eq_of_invariant V.replicaLaw
      V.replicaSwap V.replicaLaw_swap_equiv C₁ X C₀
    simpa [X, C₀, C₁, NLatent.replicaSwap, Function.comp_def] using h
  have hbridge := FiniteInfo.oneSided_bridge V.replicaLaw_isPMF
    X C₀ C₁ Z phi (fun _ => rfl) hsymm
  have hlaw := V.posteriorPairLaw_eq_replica_push
  let embed : ((V.ι × V.ι) × Omega) -> Omega × V.ι :=
    fun u => (u.2, u.1.1)
  have hmi := FiniteInfo.condMI_push_source embed Prod.fst Prod.snd phi
    V.replicaLaw
  have hHX := FiniteInfo.condH_push_source embed phi Prod.fst V.replicaLaw
  have hHC := FiniteInfo.condH_push_source embed phi Prod.snd V.replicaLaw
  have hdet : detScore V.posteriorPairLaw phi =
      condMI X C₀ Z V.replicaLaw + condH Z X V.replicaLaw +
        condH Z C₀ V.replicaLaw := by
    unfold detScore
    rw [hlaw]
    rw [hmi, hHX, hHC]
    rfl
  dsimp only [NLatent.replicaDefect]
  dsimp only [X, C₀, C₁, Z] at hbridge hdet ⊢
  rw [hdet]
  exact hbridge

/-! ## The independent finite posterior table -/

private abbrev TableSeed (V : NLatent p) :=
  Fin (Fintype.card Omega) -> V.ι

private noncomputable def tableChannel (V : NLatent p)
    (j : Fin (Fintype.card Omega)) (c : V.ι) : Real :=
  let x := (Fintype.equivFin Omega).symm j
  if p x = 0 then V.prior c else V.post c x

private lemma tableChannel_nonneg (V : NLatent p)
    (j : Fin (Fintype.card Omega)) (c : V.ι) :
  0 <= V.tableChannel j c := by
  simp only [tableChannel]
  split_ifs
  · exact V.prior_isPMF.nonneg c
  · exact V.post_nonneg c _

private lemma sum_tableChannel (V : NLatent p)
    (j : Fin (Fintype.card Omega)) : (∑ c, V.tableChannel j c) = 1 := by
  simp only [tableChannel]
  split_ifs with hx
  · simpa [mass] using V.prior_isPMF.total
  · have hxpos : 0 < p ((Fintype.equivFin Omega).symm j) :=
      lt_of_le_of_ne (V.base_isPMF.nonneg _) (Ne.symm hx)
    exact V.sum_post_of_pos _ hxpos

private noncomputable def tableLaw (V : NLatent p) : V.TableSeed -> Real :=
  fun e => ∏ j, V.tableChannel j (e j)

private lemma tableLaw_isPMF (V : NLatent p) : IsPMF V.tableLaw := by
  constructor
  · intro e
    exact Finset.prod_nonneg fun j _ => V.tableChannel_nonneg j (e j)
  · unfold mass tableLaw
    rw [FiniteInfo.sum_fin_table_prod]
    simp_rw [V.sum_tableChannel]
    simp

private noncomputable def selectedPosterior (V : NLatent p)
    (e : V.TableSeed) (x : Omega) : V.ι :=
  e (Fintype.equivFin Omega x)

/-- The seed is independent of `(C₁,X)` before applying the table entry. -/
private noncomputable def seededLaw (V : NLatent p) :
    V.TableSeed × (V.ι × Omega) -> Real :=
  fun u => V.tableLaw u.1 * V.joint u.2

private lemma seededLaw_isPMF (V : NLatent p) : IsPMF V.seededLaw := by
  constructor
  · intro u
    exact mul_nonneg (V.tableLaw_isPMF.nonneg u.1) (V.joint_isPMF.nonneg u.2)
  · unfold mass seededLaw
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    have hj : ∑ w, V.joint w = 1 := by simpa [mass] using V.joint_isPMF.total
    rw [hj]
    simp only [mul_one]
    simpa [mass] using V.tableLaw_isPMF.total

private noncomputable def seededReplicaMap (V : NLatent p) :
    V.TableSeed × (V.ι × Omega) -> (V.ι × V.ι) × Omega :=
  fun u => ((V.selectedPosterior u.1 u.2.2, u.2.1), u.2.2)

/-- Selecting the table entry indexed by `X` produces the posterior replica
`C₀`, jointly with the untouched `(C₁,X)`. -/
private theorem push_seededReplicaMap (V : NLatent p) :
    push V.seededReplicaMap V.seededLaw = V.replicaLaw := by
  funext u
  rcases u with ⟨⟨c₀, c₁⟩, x⟩
  unfold push seededReplicaMap seededLaw
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  have hcollapse (e : V.TableSeed) :
      (∑ w : V.ι × Omega,
        if ((V.selectedPosterior e w.2, w.1), w.2) = ((c₀, c₁), x) then
          V.tableLaw e * V.joint w else 0) =
        (if V.selectedPosterior e x = c₀ then
          V.tableLaw e * V.joint (c₁, x) else 0) := by
    rw [Fintype.sum_prod_type]
    simp only [Prod.fst, Prod.snd, Prod.mk.injEq]
    calc
      (∑ c, ∑ y,
        if (V.selectedPosterior e y = c₀ ∧ c = c₁) ∧ y = x then
          V.tableLaw e * V.joint (c, y) else 0) =
        ∑ y, if (V.selectedPosterior e y = c₀ ∧ c₁ = c₁) ∧ y = x then
          V.tableLaw e * V.joint (c₁, y) else 0 := by
            apply Finset.sum_eq_single c₁
            · intro c _ hne
              apply Finset.sum_eq_zero
              intro y _
              simp [hne]
            · simp
      _ = (if (V.selectedPosterior e x = c₀ ∧ c₁ = c₁) ∧ x = x then
          V.tableLaw e * V.joint (c₁, x) else 0) := by
            apply Finset.sum_eq_single x
            · intro y _ hy
              simp [hy]
            · simp
      _ = if V.selectedPosterior e x = c₀ then
          V.tableLaw e * V.joint (c₁, x) else 0 := by
            simp
  simp_rw [hcollapse]
  have heval := FiniteInfo.sum_fin_table_eval (Fintype.card Omega)
    V.tableChannel V.sum_tableChannel (Fintype.equivFin Omega x) c₀
  unfold tableLaw at heval
  change (∑ e : V.TableSeed,
      if V.selectedPosterior e x = c₀ then
        V.tableLaw e * V.joint (c₁, x) else 0) = _
  have hrewrite (e : V.TableSeed) :
      (if V.selectedPosterior e x = c₀ then
          V.tableLaw e * V.joint (c₁, x) else 0) =
        (V.tableLaw e *
          (if e (Fintype.equivFin Omega x) = c₀ then 1 else 0)) *
            V.joint (c₁, x) := by
    by_cases he : e (Fintype.equivFin Omega x) = c₀ <;>
      simp [selectedPosterior, he]
  simp_rw [hrewrite, ← Finset.sum_mul]
  change (∑ e : V.TableSeed,
      (∏ k, V.tableChannel k (e k)) *
        (if e (Fintype.equivFin Omega x) = c₀ then 1 else 0)) *
      V.joint (c₁, x) = _
  rw [heval]
  unfold tableChannel replicaLaw NLatent.joint
  simp only [Equiv.symm_apply_apply]
  by_cases hx : p x = 0
  · have hjoint : V.prior c₁ * V.comp c₁ x = 0 := by
      have hmix := V.mixture x
      rw [hx] at hmix
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun c _ => mul_nonneg (V.prior_isPMF.nonneg c)
          ((V.comp_isPMF c).nonneg x))).mp hmix c₁ (Finset.mem_univ c₁)
    simp [hx, hjoint]
  · have hxid : p x * V.post c₁ x = V.prior c₁ * V.comp c₁ x := by
      unfold post
      field_simp [hx]
    rw [if_neg hx, ← hxid]
    ring

private noncomputable def fixedPosteriorCode (V : NLatent p)
    {delta : Type*} (phi : Omega × V.ι -> delta) (e : V.TableSeed) :
    Omega -> delta := fun x => phi (x, V.selectedPosterior e x)

private noncomputable def seededPosteriorCode (V : NLatent p)
    {delta : Type*} (phi : Omega × V.ι -> delta) :
    V.TableSeed × (V.ι × Omega) -> delta :=
  fun u => phi (u.2.2, V.selectedPosterior u.1 u.2.2)

private theorem seeded_oneSided_le (V : NLatent p)
    {delta : Type*} [Fintype delta] [DecidableEq delta]
    (phi : Omega × V.ι -> delta) :
    let X : V.TableSeed × (V.ι × Omega) -> Omega := fun u => u.2.2
    let C : V.TableSeed × (V.ι × Omega) -> V.ι := fun u => u.2.1
    let E : V.TableSeed × (V.ι × Omega) -> V.TableSeed := fun u => u.1
    let Z := V.seededPosteriorCode phi
    condMI C X (fun u => (Z u, E u)) V.seededLaw +
        condH Z (fun u => (C u, E u)) V.seededLaw <=
      detScore V.posteriorPairLaw phi + 2 * V.replicaDefect := by
  let X : V.TableSeed × (V.ι × Omega) -> Omega := fun u => u.2.2
  let C : V.TableSeed × (V.ι × Omega) -> V.ι := fun u => u.2.1
  let E : V.TableSeed × (V.ι × Omega) -> V.TableSeed := fun u => u.1
  let Z := V.seededPosteriorCode phi
  have hindep : MI E (fun u => (C u, X u)) V.seededLaw = 0 := by
    have h := FiniteInfo.MI_product_zero V.tableLaw_isPMF V.joint_isPMF
    change MI Prod.fst Prod.snd
      (fun u : V.TableSeed × (V.ι × Omega) =>
        V.tableLaw u.1 * V.joint u.2) = 0
    exact h
  have hseed := FiniteInfo.seed_conditioning_le V.seededLaw_isPMF
    X C E Z (fun z : Omega × V.TableSeed =>
      phi (z.1, V.selectedPosterior z.2 z.1)) (fun _ => rfl) hindep
  have hlaw := V.push_seededReplicaMap
  have hmi := FiniteInfo.condMI_push_source V.seededReplicaMap
    (fun u : (V.ι × V.ι) × Omega => u.1.2)
    (fun u => u.2) (fun u => phi (u.2, u.1.1)) V.seededLaw
  have hH := FiniteInfo.condH_push_source V.seededReplicaMap
    (fun u : (V.ι × V.ι) × Omega => phi (u.2, u.1.1))
    (fun u => u.1.2) V.seededLaw
  rw [hlaw] at hmi hH
  have hpair := V.replica_oneSided_le_detScore_add phi
  have hglobal : condMI C X Z V.seededLaw + condH Z C V.seededLaw <=
      detScore V.posteriorPairLaw phi + 2 * V.replicaDefect := by
    dsimp only at hpair
    dsimp only [seededReplicaMap, X, C, Z, seededPosteriorCode,
      selectedPosterior, Function.comp_def] at hmi hH
    change
      condMI (fun x => x.2.1) (fun x => x.2.2)
          (fun x => phi (x.2.2, x.1 (Fintype.equivFin Omega x.2.2)))
            V.seededLaw +
        condH (fun x => phi (x.2.2,
            x.1 (Fintype.equivFin Omega x.2.2)))
          (fun x => x.2.1) V.seededLaw <= _
    rw [← hmi, ← hH]
    exact hpair
  dsimp only [X, C, E, Z]
  exact hseed.trans hglobal

/-- Alphabet-free one-sided compression.  The codomain shown here is merely
the fixed codomain supplied by the imported two-variable theorem; a later
relabeling shrinks the realized image to at most `|Omega|`. -/
theorem exists_hardCode_oneSided (V : NLatent p) :
    exists code : Omega -> Fin (Fintype.card (Omega × V.ι)),
      condMI (fun w : V.ι × Omega => w.1) (fun w => w.2)
          (fun w => code w.2) V.joint +
        condH (fun w : V.ι × Omega => code w.2) (fun w => w.1)
          V.joint <=
        NVarTwoVariableInput.oneSidedFactor * V.replicaDefect := by
  obtain ⟨phi, hphi⟩ := V.exists_posteriorPair_code
  let err : V.TableSeed -> Real := fun e =>
    condMI (fun w : V.ι × Omega => w.1) (fun w => w.2)
        (fun w => V.fixedPosteriorCode phi e w.2) V.joint +
      condH (fun w : V.ι × Omega => V.fixedPosteriorCode phi e w.2)
        (fun w => w.1) V.joint
  have havg := FiniteInfo.average_fixed_error_eq V.tableLaw_isPMF
    V.joint_isPMF (fun w : V.ι × Omega => w.2) (fun w => w.1)
    (fun e w => V.fixedPosteriorCode phi e w.2)
  have hseed := V.seeded_oneSided_le phi
  have havg_le : (∑ e, V.tableLaw e * err e) <=
      detScore V.posteriorPairLaw phi + 2 * V.replicaDefect := by
    dsimp only [err]
    rw [havg]
    dsimp only [fixedPosteriorCode, seededPosteriorCode] at hseed ⊢
    exact hseed
  have havg_final : (∑ e, V.tableLaw e * err e) <=
      NVarTwoVariableInput.oneSidedFactor * V.replicaDefect := by
    calc
      _ <= detScore V.posteriorPairLaw phi +
          2 * V.replicaDefect := havg_le
      _ <= (2 * NVarTwoVariableInput.certifiedFactor) * V.replicaDefect +
          2 * V.replicaDefect := add_le_add hphi (le_refl _)
      _ = NVarTwoVariableInput.oneSidedFactor * V.replicaDefect := by
        unfold NVarTwoVariableInput.oneSidedFactor
        ring
  obtain ⟨e, he⟩ := FiniteInfo.exists_le_weighted_average
    V.tableLaw_isPMF err
  refine ⟨V.fixedPosteriorCode phi e, ?_⟩
  dsimp only [err] at he
  exact he.trans havg_final

end NLatent

end stoch_to_det
