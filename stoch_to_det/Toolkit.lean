import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import stoch_to_det.Entropy

/-!
# Lemma 0.1 — the classical toolkit


Four standard facts, none of which is available in Mathlib in the form used
here (Mathlib's `klDiv` is `ℝ≥0∞`-valued and in nats; there is no finite
bits-valued KL, no Bhattacharyya coefficient, and no differential entropy).
All four proofs are included below.

| Lean name | Label | Used by |
|---|---|---|
| `variational_le` | (T1) | Lemma 5.2 |
| `pinsker` | (T2) | Thm 6.1, Thm 9.1 |
| `bhattacharyya` | (T3) | Thm 9.1 (far part) |
| `diffEntropy_le_of_abs_le` | (T4) | Thm 8.1 (off-diagonal contexts) |

(T4) is the only item here that leaves the finite world; it is stated for a
real random variable given by a Lebesgue density, which is exactly how §8 uses
it (`X + N` with `N = ln T`, `T ~ Exp(1)`).
-/

namespace stoch_to_det

open Finset MeasureTheory
open Filter
open scoped ENNReal Topology

variable {ω : Type*} [Fintype ω] [DecidableEq ω]

/-- KL divergence in **bits** between finite laws, `D(P ‖ Q) := ∑ P lg(P/Q)`.
The junk-value convention makes `P a = 0` contribute `0`; when `Q a = 0 < P a`
the summand is `P a * lg (P a / 0) = 0`, which is **wrong** (it should be `+∞`),
so every lemma about `KL` carries an absolute-continuity hypothesis. -/
noncomputable def KL (P Q : ω → ℝ) : ℝ := ∑ a, P a * lg (P a / Q a)

/-- Absolute continuity `P ≪ Q` for finite laws. -/
def AbsCont (P Q : ω → ℝ) : Prop := ∀ a, Q a = 0 → P a = 0

/-- Total variation between finite laws, `TV(P,Q) := ½ ∑ |P − Q|`. -/
noncomputable def tvDist (P Q : ω → ℝ) : ℝ := (∑ a, |P a - Q a|) / 2

/-- The Bhattacharyya coefficient `BC(P,Q) := ∑ √(P Q)`. -/
noncomputable def BC (P Q : ω → ℝ) : ℝ := ∑ a, Real.sqrt (P a * Q a)

/-- Finite Gibbs inequality for the bits-valued `KL`. -/
private lemma KL_nonneg {P Q : ω → ℝ} (hP : IsPMF P) (hQ : IsPMF Q)
    (hac : AbsCont P Q) : 0 ≤ KL P Q := by
  have hterm : ∀ a : ω, P a - Q a ≤ P a * Real.log (P a / Q a) := by
    intro a
    by_cases hPa : P a = 0
    · simp [hPa, hQ.nonneg a]
    · have hPa_pos : 0 < P a := lt_of_le_of_ne (hP.nonneg a) (Ne.symm hPa)
      have hQa : Q a ≠ 0 := fun h ↦ hPa (hac a h)
      have hQa_pos : 0 < Q a := lt_of_le_of_ne (hQ.nonneg a) (Ne.symm hQa)
      have hlog := Real.log_le_sub_one_of_pos (div_pos hQa_pos hPa_pos)
      have hmul := mul_le_mul_of_nonneg_left hlog hPa_pos.le
      have hlog_eq : Real.log (Q a / P a) = -Real.log (P a / Q a) := by
        rw [Real.log_div hQa hPa, Real.log_div hPa hQa]
        ring
      calc
        P a - Q a = -(Q a - P a) := by ring
        _ = -(P a * (Q a / P a - 1)) := by field_simp
        _ ≤ -(P a * Real.log (Q a / P a)) := neg_le_neg hmul
        _ = P a * Real.log (P a / Q a) := by rw [hlog_eq]; ring
  have hnats : 0 ≤ ∑ a, P a * Real.log (P a / Q a) := by
    calc
      0 = ∑ a, (P a - Q a) := by
        rw [sum_sub_distrib, ← mass, ← mass, hP.total, hQ.total]
        norm_num
      _ ≤ ∑ a, P a * Real.log (P a / Q a) := sum_le_sum fun a _ ↦ hterm a
  rw [KL]
  change 0 ≤ ∑ a, P a * (Real.log (P a / Q a) / Real.log 2)
  simp_rw [← mul_div_assoc]
  rw [← sum_div]
  exact div_nonneg hnats (Real.log_pos (by norm_num)).le

/-- **(T1)** variational inequality:
`E_r h − lg E_Q 2^h ≤ D(r ‖ Q)`. -/
theorem variational_le {r Q : ω → ℝ} (hr : IsPMF r) (hQ : IsPMF Q) (hac : AbsCont r Q)
    (h : ω → ℝ) :
    (∑ a, r a * h a) - lg (∑ a, Q a * (2 : ℝ) ^ h a) ≤ KL r Q := by
  let Z : ℝ := ∑ a, Q a * (2 : ℝ) ^ h a
  let S : ω → ℝ := fun a ↦ Q a * (2 : ℝ) ^ h a / Z
  obtain ⟨a₀, ha₀⟩ : ∃ a, 0 < Q a := by
    have hsum : 0 < ∑ a, Q a := by
      rw [← mass, hQ.total]
      norm_num
    rcases (Finset.sum_pos_iff_of_nonneg (fun a _ ↦ hQ.nonneg a)).mp hsum with
      ⟨a, _, ha⟩
    exact ⟨a, ha⟩
  have hZ : 0 < Z := by
    apply Finset.sum_pos'
    · intro a _
      exact mul_nonneg (hQ.nonneg a) (by positivity)
    · exact ⟨a₀, Finset.mem_univ _, mul_pos ha₀ (by positivity)⟩
  have hS : IsPMF S := by
    constructor
    · intro a
      dsimp [S]
      exact div_nonneg (mul_nonneg (hQ.nonneg a) (by positivity)) hZ.le
    · dsimp [mass, S]
      rw [← sum_div]
      exact div_self hZ.ne'
  have hacS : AbsCont r S := by
    intro a hSa
    apply hac a
    have hnum : Q a * (2 : ℝ) ^ h a = 0 := by
      dsimp [S] at hSa
      exact (div_eq_zero_iff).mp hSa |>.resolve_right hZ.ne'
    exact (mul_eq_zero.mp hnum).resolve_right (by positivity)
  have hnonneg : 0 ≤ KL r S := KL_nonneg hr hS hacS
  have hterm : ∀ a : ω,
      r a * lg (r a / S a) =
        r a * lg (r a / Q a) - r a * h a + r a * lg Z := by
    intro a
    by_cases hra : r a = 0
    · simp [hra]
    · have hra_pos : 0 < r a := lt_of_le_of_ne (hr.nonneg a) (Ne.symm hra)
      have hQa : Q a ≠ 0 := fun hQ0 ↦ hra (hac a hQ0)
      have hQa_pos : 0 < Q a := lt_of_le_of_ne (hQ.nonneg a) (Ne.symm hQa)
      have hpw : (2 : ℝ) ^ h a ≠ 0 := (by positivity)
      have hSa_pos : 0 < S a := by
        dsimp [S]
        positivity
      change r a * (Real.log (r a / S a) / Real.log 2) =
        r a * (Real.log (r a / Q a) / Real.log 2) - r a * h a +
          r a * (Real.log Z / Real.log 2)
      rw [Real.log_div hra hSa_pos.ne', Real.log_div hra hQa,
        show Real.log (S a) = Real.log (Q a) + h a * Real.log 2 - Real.log Z by
          dsimp [S]
          rw [Real.log_div (mul_ne_zero hQa hpw) hZ.ne', Real.log_mul hQa hpw,
            Real.log_rpow (by norm_num : (0 : ℝ) < 2)]]
      field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2)
        (by norm_num : (2 : ℝ) ≠ 1)]
      ring
  have hid : KL r S = KL r Q - (∑ a, r a * h a) + lg Z := by
    rw [KL, KL]
    calc
      (∑ a, r a * lg (r a / S a)) =
          ∑ a, (r a * lg (r a / Q a) - r a * h a + r a * lg Z) := by
            apply sum_congr rfl
            intro a _
            exact hterm a
      _ = (∑ a, r a * lg (r a / Q a)) - (∑ a, r a * h a) +
          (∑ a, r a) * lg Z := by
            rw [sum_add_distrib, sum_sub_distrib, ← sum_mul]
      _ = (∑ a, r a * lg (r a / Q a)) - (∑ a, r a * h a) + lg Z := by
            have hsumr : ∑ a, r a = 1 := by simpa [mass] using hr.total
            rw [hsumr, one_mul]
  change (∑ a, r a * h a) - lg Z ≤ KL r Q
  rw [hid] at hnonneg
  linarith

/-- The two-point Pinsker inequality in nats, in the orientation used by the
`{P > Q}` partition. -/
private lemma binary_pinsker_of_le {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (ha : a ≤ 1) :
    2 * (a - b) ^ 2 ≤
      a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b)) := by
  have ha_pos : 0 < a := hb.trans_le hba
  by_cases ha_one : a = 1
  · subst a
    let g : ℝ → ℝ := fun x ↦ -Real.log x - 2 * (1 - x) ^ 2
    have hg' (x : ℝ) (hx : x ≠ 0) :
        HasDerivAt g (-1 / x + 4 * (1 - x)) x := by
      have hsub : HasDerivAt (fun y : ℝ ↦ 1 - y) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
      have hquad := (hsub.pow 2).const_mul 2
      have hraw := (Real.hasDerivAt_log hx).neg.sub hquad
      have hraw' : HasDerivAt g
          (-x⁻¹ - 2 * ((2 : ℝ) * (1 - x) ^ (2 - 1) * -1)) x :=
        hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ by
          dsimp [g])
      apply hraw'.congr_deriv
      field_simp [hx]
      ring
    have hcont : ContinuousOn g (Set.Icc b 1) := by
      intro x hx
      exact (hg' x (ne_of_gt (hb.trans_le hx.1))).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ g (interior (Set.Icc b 1)) := by
      intro x hx
      have hx' := interior_subset hx
      exact (hg' x (ne_of_gt (hb.trans_le hx'.1))).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ interior (Set.Icc b 1), deriv g x ≤ 0 := by
      intro x hx
      have hx' := interior_subset hx
      have hxpos : 0 < x := hb.trans_le hx'.1
      rw [(hg' x hxpos.ne').deriv]
      have hsq : 0 ≤ (2 * x - 1) ^ 2 := sq_nonneg _
      have hbound : 4 * (1 - x) * x ≤ 1 := by nlinarith
      have hinv : 4 * (1 - x) ≤ 1 / x := (le_div_iff₀ hxpos).2 (by nlinarith)
      calc
        -1 / x + 4 * (1 - x) = -(1 / x) + 4 * (1 - x) := by ring
        _ ≤ 0 := by linarith
    have hanti : AntitoneOn g (Set.Icc b 1) :=
      antitoneOn_of_deriv_nonpos (convex_Icc b 1) hcont hdiff hderiv
    have hmin := hanti (by exact ⟨le_rfl, hba⟩) (by exact ⟨hba, le_rfl⟩) hba
    dsimp [g] at hmin
    norm_num at hmin
    rw [Real.log_div one_ne_zero hb.ne']
    norm_num
    linarith
  · have ha_lt : a < 1 := lt_of_le_of_ne ha ha_one
    have h1a_pos : 0 < 1 - a := sub_pos.mpr ha_lt
    let g : ℝ → ℝ := fun x ↦
      a * (Real.log a - Real.log x) +
        (1 - a) * (Real.log (1 - a) - Real.log (1 - x)) -
        2 * (a - x) ^ 2
    have hg' (x : ℝ) (hx0 : x ≠ 0) (hx1 : 1 - x ≠ 0) :
        HasDerivAt g ((x - a) * (1 / (x * (1 - x)) - 4)) x := by
      have hden : HasDerivAt (fun y : ℝ ↦ 1 - y) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
      have hfirst :=
        ((hasDerivAt_const x (Real.log a)).sub (Real.hasDerivAt_log hx0)).const_mul a
      have hlogden := hden.log hx1
      have hsecond :=
        ((hasDerivAt_const x (Real.log (1 - a))).sub hlogden).const_mul (1 - a)
      have hsub : HasDerivAt (fun y : ℝ ↦ a - y) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub a
      have hquad := (hsub.pow 2).const_mul 2
      have hraw := (hfirst.add hsecond).sub hquad
      have hraw' : HasDerivAt g
          (a * (0 - x⁻¹) + (1 - a) * (0 - (-1 / (1 - x))) -
            2 * ((2 : ℝ) * (a - x) ^ (2 - 1) * -1)) x :=
        hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ by
          dsimp [g])
      apply hraw'.congr_deriv
      field_simp [hx0, hx1]
      ring
    have hcont : ContinuousOn g (Set.Icc b a) := by
      intro x hx
      have hxpos : 0 < x := hb.trans_le hx.1
      have hxlt : x < 1 := hx.2.trans_lt ha_lt
      exact (hg' x hxpos.ne' (sub_ne_zero.mpr hxlt.ne')).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ g (interior (Set.Icc b a)) := by
      intro x hx
      have hx' := interior_subset hx
      have hxpos : 0 < x := hb.trans_le hx'.1
      have hxlt : x < 1 := hx'.2.trans_lt ha_lt
      exact (hg' x hxpos.ne' (sub_ne_zero.mpr hxlt.ne')).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ interior (Set.Icc b a), deriv g x ≤ 0 := by
      intro x hx
      have hx' := interior_subset hx
      have hxpos : 0 < x := hb.trans_le hx'.1
      have hxlt : x < 1 := hx'.2.trans_lt ha_lt
      rw [(hg' x hxpos.ne' (sub_ne_zero.mpr hxlt.ne')).deriv]
      have hprod : 0 < x * (1 - x) := mul_pos hxpos (sub_pos.mpr hxlt)
      have hsq : 0 ≤ (2 * x - 1) ^ 2 := sq_nonneg _
      have hbound : 4 * (x * (1 - x)) ≤ 1 := by nlinarith
      have hinv : 4 ≤ 1 / (x * (1 - x)) := (le_div_iff₀ hprod).2 hbound
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx'.2) (sub_nonneg.mpr hinv)
    have hanti : AntitoneOn g (Set.Icc b a) :=
      antitoneOn_of_deriv_nonpos (convex_Icc b a) hcont hdiff hderiv
    have hmin := hanti (by exact ⟨le_rfl, hba⟩) (by exact ⟨hba, le_rfl⟩) hba
    have hga : g a = 0 := by
      dsimp [g]
      ring
    rw [hga] at hmin
    dsimp [g] at hmin
    have hb_lt : b < 1 := hba.trans_lt ha_lt
    rw [Real.log_div ha_pos.ne' hb.ne']
    rw [Real.log_div h1a_pos.ne' (sub_ne_zero.mpr hb_lt.ne')]
    linarith

/-- Log-sum inequality on a finite subset, derived from Gibbs' inequality. -/
private lemma log_sum_le (s : Finset ω) {P Q : ω → ℝ}
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 ≤ Q i) (hac : AbsCont P Q)
    (hPs : 0 < ∑ i ∈ s, P i) (hQs : 0 < ∑ i ∈ s, Q i) :
    (∑ i ∈ s, P i) * Real.log ((∑ i ∈ s, P i) / ∑ i ∈ s, Q i) ≤
      ∑ i ∈ s, P i * Real.log (P i / Q i) := by
  let X : ℝ := ∑ i ∈ s, P i
  let Y : ℝ := ∑ i ∈ s, Q i
  have hterm : ∀ i ∈ s,
      P i - X / Y * Q i ≤ P i * Real.log ((P i * Y) / (Q i * X)) := by
    intro i hi
    by_cases hPi : P i = 0
    · simp only [hPi, zero_mul, zero_div, Real.log_zero]
      rw [zero_sub]
      exact neg_nonpos.mpr (mul_nonneg (div_nonneg hPs.le hQs.le) (hQ i))
    · have hPi_pos : 0 < P i := lt_of_le_of_ne (hP i) (Ne.symm hPi)
      have hQi : Q i ≠ 0 := fun h ↦ hPi (hac i h)
      have hQi_pos : 0 < Q i := lt_of_le_of_ne (hQ i) (Ne.symm hQi)
      have hz : 0 < (X * Q i) / (Y * P i) :=
        div_pos (mul_pos hPs hQi_pos) (mul_pos hQs hPi_pos)
      have hlog := Real.log_le_sub_one_of_pos hz
      have hmul := mul_le_mul_of_nonneg_left hlog hPi_pos.le
      have hscale : P i * ((X * Q i) / (Y * P i) - 1) = X / Y * Q i - P i := by
        field_simp [hPi, hQs.ne']
      have hlog_inv :
          Real.log ((P i * Y) / (Q i * X)) = -Real.log ((X * Q i) / (Y * P i)) := by
        rw [Real.log_div (mul_ne_zero hPi hQs.ne') (mul_ne_zero hQi hPs.ne'),
          Real.log_div (mul_ne_zero hPs.ne' hQi) (mul_ne_zero hQs.ne' hPi),
          Real.log_mul hPi hQs.ne', Real.log_mul hQi hPs.ne',
          Real.log_mul hPs.ne' hQi, Real.log_mul hQs.ne' hPi]
        ring
      calc
        P i - X / Y * Q i = -(X / Y * Q i - P i) := by ring
        _ = -(P i * ((X * Q i) / (Y * P i) - 1)) := by rw [hscale]
        _ ≤ -(P i * Real.log ((X * Q i) / (Y * P i))) := neg_le_neg hmul
        _ = P i * Real.log ((P i * Y) / (Q i * X)) := by rw [hlog_inv]; ring
  have hnorm_nonneg : 0 ≤ ∑ i ∈ s, P i * Real.log ((P i * Y) / (Q i * X)) := by
    calc
      0 = ∑ i ∈ s, (P i - X / Y * Q i) := by
        rw [sum_sub_distrib, ← mul_sum]
        dsimp [X, Y]
        field_simp [hQs.ne']
        ring
      _ ≤ ∑ i ∈ s, P i * Real.log ((P i * Y) / (Q i * X)) :=
        sum_le_sum hterm
  have hrewrite : ∀ i ∈ s,
      P i * Real.log ((P i * Y) / (Q i * X)) =
        P i * Real.log (P i / Q i) - P i * Real.log (X / Y) := by
    intro i hi
    by_cases hPi : P i = 0
    · simp [hPi]
    · have hQi : Q i ≠ 0 := fun h ↦ hPi (hac i h)
      rw [Real.log_div (mul_ne_zero hPi hQs.ne') (mul_ne_zero hQi hPs.ne'),
        Real.log_div hPi hQi, Real.log_div hPs.ne' hQs.ne',
        Real.log_mul hPi hQs.ne', Real.log_mul hQi hPs.ne']
      ring
  have hid :
      (∑ i ∈ s, P i * Real.log ((P i * Y) / (Q i * X))) =
        (∑ i ∈ s, P i * Real.log (P i / Q i)) - X * Real.log (X / Y) := by
    calc
      (∑ i ∈ s, P i * Real.log ((P i * Y) / (Q i * X))) =
          ∑ i ∈ s, (P i * Real.log (P i / Q i) - P i * Real.log (X / Y)) := by
            apply sum_congr rfl
            exact hrewrite
      _ = (∑ i ∈ s, P i * Real.log (P i / Q i)) - X * Real.log (X / Y) := by
        rw [sum_sub_distrib, ← sum_mul]
  change X * Real.log (X / Y) ≤ ∑ i ∈ s, P i * Real.log (P i / Q i)
  rw [hid] at hnorm_nonneg
  linarith

/-- **(T2)** Pinsker: `D(P ‖ Q) ≥ (2/ln 2) TV(P,Q)²` bits. -/
theorem pinsker {P Q : ω → ℝ} (hP : IsPMF P) (hQ : IsPMF Q) (hac : AbsCont P Q) :
    2 / Real.log 2 * tvDist P Q ^ 2 ≤ KL P Q := by
  classical
  let A : Finset ω := Finset.univ.filter fun x ↦ Q x < P x
  let C : Finset ω := Finset.univ.filter fun x ↦ ¬Q x < P x
  let a : ℝ := ∑ x ∈ A, P x
  let b : ℝ := ∑ x ∈ A, Q x
  have hsumP : ∑ x, P x = 1 := by simpa [mass] using hP.total
  have hsumQ : ∑ x, Q x = 1 := by simpa [mass] using hQ.total
  have hpartition (f : ω → ℝ) :
      (∑ x ∈ A, f x) + (∑ x ∈ C, f x) = ∑ x, f x := by
    simpa [A, C] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ (fun x ↦ Q x < P x) f)
  have hCP : ∑ x ∈ C, P x = 1 - a := by
    have h := hpartition P
    rw [hsumP] at h
    change a + (∑ x ∈ C, P x) = 1 at h
    linarith
  have hCQ : ∑ x ∈ C, Q x = 1 - b := by
    have h := hpartition Q
    rw [hsumQ] at h
    change b + (∑ x ∈ C, Q x) = 1 at h
    linarith
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact sum_nonneg fun i _ ↦ hP.nonneg i
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    exact sum_nonneg fun i _ ↦ hQ.nonneg i
  have hCP_nonneg : 0 ≤ ∑ x ∈ C, P x := sum_nonneg fun i _ ↦ hP.nonneg i
  have hCQ_nonneg : 0 ≤ ∑ x ∈ C, Q x := sum_nonneg fun i _ ↦ hQ.nonneg i
  have ha_le : a ≤ 1 := by linarith [hCP]
  have hb_le : b ≤ 1 := by linarith [hCQ]
  have hab_nonneg : 0 ≤ a - b := by
    change 0 ≤ (∑ x ∈ A, P x) - ∑ x ∈ A, Q x
    rw [← sum_sub_distrib]
    exact sum_nonneg fun i hi ↦ by
      have hi' : Q i < P i := by simpa [A] using hi
      exact sub_nonneg.mpr hi'.le
  have hAdiff : ∑ x ∈ A, (P x - Q x) = a - b := by
    dsimp [a, b]
    rw [sum_sub_distrib]
  have hCdiff : ∑ x ∈ C, (Q x - P x) = a - b := by
    rw [sum_sub_distrib, hCQ, hCP]
    ring
  have habs : ∑ x, |P x - Q x| = 2 * (a - b) := by
    calc
      (∑ x, |P x - Q x|) =
          (∑ x ∈ A, |P x - Q x|) + (∑ x ∈ C, |P x - Q x|) :=
            (hpartition fun x ↦ |P x - Q x|).symm
      _ = (∑ x ∈ A, (P x - Q x)) + (∑ x ∈ C, (Q x - P x)) := by
        congr 1
        · apply sum_congr rfl
          intro i hi
          have hi' : Q i < P i := by simpa [A] using hi
          rw [abs_of_pos (sub_pos.mpr hi')]
        · apply sum_congr rfl
          intro i hi
          have hi' : P i ≤ Q i := by
            have : ¬Q i < P i := by simpa [C] using hi
            exact le_of_not_gt this
          rw [abs_of_nonpos (sub_nonpos.mpr hi')]
          ring
      _ = 2 * (a - b) := by rw [hAdiff, hCdiff]; ring
  have htv : tvDist P Q = a - b := by
    rw [tvDist, habs]
    ring
  by_cases hab : a = b
  · have hkl := KL_nonneg hP hQ hac
    rw [htv, hab]
    norm_num
    exact hkl
  have hab_pos : 0 < a - b := lt_of_le_of_ne hab_nonneg (Ne.symm (sub_ne_zero.mpr hab))
  have hb_ne : b ≠ 0 := by
    intro hb0
    have hQzero : ∀ i ∈ A, Q i = 0 := by
      apply (sum_eq_zero_iff_of_nonneg fun i _ ↦ hQ.nonneg i).mp
      simpa [b] using hb0
    have hPzero : ∀ i ∈ A, P i = 0 := fun i hi ↦ hac i (hQzero i hi)
    have ha0 : a = 0 := by
      dsimp [a]
      exact sum_eq_zero hPzero
    linarith
  have hb_pos : 0 < b := lt_of_le_of_ne hb_nonneg (Ne.symm hb_ne)
  have hba : b ≤ a := by linarith
  have hlogA := log_sum_le A hP.nonneg hQ.nonneg hac (by linarith) hb_pos
  change a * Real.log (a / b) ≤ ∑ i ∈ A, P i * Real.log (P i / Q i) at hlogA
  have hsplitKL := hpartition (fun i ↦ P i * Real.log (P i / Q i))
  have hdata :
      a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b)) ≤
        ∑ i, P i * Real.log (P i / Q i) := by
    by_cases ha1 : a = 1
    · have hPzero : ∀ i ∈ C, P i = 0 := by
        apply (sum_eq_zero_iff_of_nonneg fun i _ ↦ hP.nonneg i).mp
        rw [hCP, ha1]
        norm_num
      have hzero : ∑ i ∈ C, P i * Real.log (P i / Q i) = 0 := by
        apply sum_eq_zero
        intro i hi
        simp [hPzero i hi]
      rw [ha1] at hlogA ⊢
      norm_num at hlogA ⊢
      rw [← hsplitKL, hzero, add_zero]
      exact hlogA
    · have ha_lt : a < 1 := lt_of_le_of_ne ha_le ha1
      have hca_pos : 0 < 1 - a := sub_pos.mpr ha_lt
      have hcb_pos : 0 < 1 - b := by linarith
      have hlogC := log_sum_le C hP.nonneg hQ.nonneg hac
        (by simpa [hCP] using hca_pos) (by simpa [hCQ] using hcb_pos)
      rw [hCP, hCQ] at hlogC
      calc
        a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b)) ≤
            (∑ i ∈ A, P i * Real.log (P i / Q i)) +
              ∑ i ∈ C, P i * Real.log (P i / Q i) := add_le_add hlogA hlogC
        _ = ∑ i, P i * Real.log (P i / Q i) := hsplitKL
  have hbinary := binary_pinsker_of_le hb_pos hba ha_le
  have hnats : 2 * (a - b) ^ 2 ≤ ∑ i, P i * Real.log (P i / Q i) :=
    hbinary.trans hdata
  have hKL : KL P Q = (∑ i, P i * Real.log (P i / Q i)) / Real.log 2 := by
    rw [KL]
    change (∑ i, P i * (Real.log (P i / Q i) / Real.log 2)) = _
    simp_rw [← mul_div_assoc]
    rw [← sum_div]
  rw [htv, hKL]
  calc
    2 / Real.log 2 * (a - b) ^ 2 = (2 * (a - b) ^ 2) / Real.log 2 := by ring
    _ ≤ (∑ i, P i * Real.log (P i / Q i)) / Real.log 2 :=
      (div_le_div_iff_of_pos_right (Real.log_pos (by norm_num))).2 hnats

/-- **(T3)** Bhattacharyya, first half:
`min_r [D(r‖P) + D(r‖Q)] = −2 lg BC(P,Q)`. Only `≥` is used (Thm 9.1). -/
theorem bhattacharyya_le {P Q : ω → ℝ} (hP : IsPMF P) (hQ : IsPMF Q)
    {r : ω → ℝ} (hr : IsPMF r) (hacP : AbsCont r P) (hacQ : AbsCont r Q) :
    -2 * lg (BC P Q) ≤ KL r P + KL r Q := by
  let B : ℝ := BC P Q
  let S : ω → ℝ := fun a ↦ Real.sqrt (P a * Q a) / B
  obtain ⟨a₀, ha₀⟩ : ∃ a, 0 < r a := by
    have hsum : 0 < ∑ a, r a := by
      rw [← mass, hr.total]
      norm_num
    rcases (Finset.sum_pos_iff_of_nonneg (fun a _ ↦ hr.nonneg a)).mp hsum with
      ⟨a, _, ha⟩
    exact ⟨a, ha⟩
  have hPa₀ : 0 < P a₀ := by
    have hne : P a₀ ≠ 0 := fun h ↦ ha₀.ne' (hacP a₀ h)
    exact lt_of_le_of_ne (hP.nonneg a₀) (Ne.symm hne)
  have hQa₀ : 0 < Q a₀ := by
    have hne : Q a₀ ≠ 0 := fun h ↦ ha₀.ne' (hacQ a₀ h)
    exact lt_of_le_of_ne (hQ.nonneg a₀) (Ne.symm hne)
  have hB : 0 < B := by
    dsimp [B, BC]
    apply Finset.sum_pos'
    · intro a _
      exact Real.sqrt_nonneg _
    · exact ⟨a₀, Finset.mem_univ _, Real.sqrt_pos.2 (mul_pos hPa₀ hQa₀)⟩
  have hS : IsPMF S := by
    constructor
    · intro a
      dsimp [S]
      exact div_nonneg (Real.sqrt_nonneg _) hB.le
    · dsimp [mass, S]
      rw [← sum_div]
      exact div_self hB.ne'
  have hacS : AbsCont r S := by
    intro a hSa
    by_cases hPa : P a = 0
    · exact hacP a hPa
    by_cases hQa : Q a = 0
    · exact hacQ a hQa
    have hPa_pos : 0 < P a := lt_of_le_of_ne (hP.nonneg a) (Ne.symm hPa)
    have hQa_pos : 0 < Q a := lt_of_le_of_ne (hQ.nonneg a) (Ne.symm hQa)
    have hSa_pos : 0 < S a := by
      dsimp [S]
      exact div_pos (Real.sqrt_pos.2 (mul_pos hPa_pos hQa_pos)) hB
    exact (hSa_pos.ne' hSa).elim
  have hnonneg : 0 ≤ KL r S := KL_nonneg hr hS hacS
  have hterm : ∀ a : ω,
      2 * (r a * lg (r a / S a)) =
        r a * lg (r a / P a) + r a * lg (r a / Q a) + r a * (2 * lg B) := by
    intro a
    by_cases hra : r a = 0
    · simp [hra]
    · have hra_pos : 0 < r a := lt_of_le_of_ne (hr.nonneg a) (Ne.symm hra)
      have hPa : P a ≠ 0 := fun h ↦ hra (hacP a h)
      have hQa : Q a ≠ 0 := fun h ↦ hra (hacQ a h)
      have hPa_pos : 0 < P a := lt_of_le_of_ne (hP.nonneg a) (Ne.symm hPa)
      have hQa_pos : 0 < Q a := lt_of_le_of_ne (hQ.nonneg a) (Ne.symm hQa)
      have hS_pos : 0 < S a := by
        dsimp [S]
        exact div_pos (Real.sqrt_pos.2 (mul_pos hPa_pos hQa_pos)) hB
      change 2 * (r a * (Real.log (r a / S a) / Real.log 2)) =
        r a * (Real.log (r a / P a) / Real.log 2) +
          r a * (Real.log (r a / Q a) / Real.log 2) +
            r a * (2 * (Real.log B / Real.log 2))
      rw [Real.log_div hra hS_pos.ne', Real.log_div hra hPa, Real.log_div hra hQa,
        show Real.log (S a) =
            (Real.log (P a) + Real.log (Q a)) / 2 - Real.log B by
          dsimp [S]
          rw [Real.log_div (Real.sqrt_pos.2 (mul_pos hPa_pos hQa_pos)).ne' hB.ne',
            Real.log_sqrt (mul_nonneg (hP.nonneg a) (hQ.nonneg a)),
            Real.log_mul hPa hQa]]
      field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2)
        (by norm_num : (2 : ℝ) ≠ 1)]
      ring
  have hid : 2 * KL r S = KL r P + KL r Q + 2 * lg B := by
    rw [KL, KL, KL, mul_sum]
    calc
      (∑ a, 2 * (r a * lg (r a / S a))) =
          ∑ a, (r a * lg (r a / P a) + r a * lg (r a / Q a) +
            r a * (2 * lg B)) := by
              apply sum_congr rfl
              intro a _
              exact hterm a
      _ = (∑ a, r a * lg (r a / P a)) + (∑ a, r a * lg (r a / Q a)) +
          (∑ a, r a) * (2 * lg B) := by
            rw [sum_add_distrib, sum_add_distrib, ← sum_mul]
      _ = (∑ a, r a * lg (r a / P a)) + (∑ a, r a * lg (r a / Q a)) +
          2 * lg B := by
            have hsumr : ∑ a, r a = 1 := by simpa [mass] using hr.total
            rw [hsumr, one_mul]
  have htwice : 0 ≤ 2 * KL r S := mul_nonneg (by norm_num) hnonneg
  rw [hid] at htwice
  change -2 * lg B ≤ KL r P + KL r Q
  linarith

/-- **(T3)** second half: `TV(P,Q) ≤ √(1 − BC(P,Q)²)`. -/
theorem tv_le_bhattacharyya {P Q : ω → ℝ} (hP : IsPMF P) (hQ : IsPMF Q) :
    tvDist P Q ≤ Real.sqrt (1 - BC P Q ^ 2) := by
  let u : ω → ℝ := fun a ↦ |Real.sqrt (P a) - Real.sqrt (Q a)|
  let v : ω → ℝ := fun a ↦ Real.sqrt (P a) + Real.sqrt (Q a)
  have hfactor : ∀ a : ω, |P a - Q a| = u a * v a := by
    intro a
    dsimp [u, v]
    calc
      |P a - Q a| =
          |(Real.sqrt (P a) - Real.sqrt (Q a)) *
            (Real.sqrt (P a) + Real.sqrt (Q a))| := by
              congr 1
              calc
                P a - Q a = Real.sqrt (P a) ^ 2 - Real.sqrt (Q a) ^ 2 := by
                  rw [Real.sq_sqrt (hP.nonneg a), Real.sq_sqrt (hQ.nonneg a)]
                _ = (Real.sqrt (P a) - Real.sqrt (Q a)) *
                    (Real.sqrt (P a) + Real.sqrt (Q a)) := by ring
      _ = |Real.sqrt (P a) - Real.sqrt (Q a)| *
          |Real.sqrt (P a) + Real.sqrt (Q a)| := abs_mul _ _
      _ = |Real.sqrt (P a) - Real.sqrt (Q a)| *
          (Real.sqrt (P a) + Real.sqrt (Q a)) := by
            rw [abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have hu_term : ∀ a : ω,
      u a ^ 2 = P a + Q a - 2 * Real.sqrt (P a * Q a) := by
    intro a
    dsimp [u]
    rw [sq_abs]
    calc
      (Real.sqrt (P a) - Real.sqrt (Q a)) ^ 2 =
          Real.sqrt (P a) ^ 2 + Real.sqrt (Q a) ^ 2 -
            2 * (Real.sqrt (P a) * Real.sqrt (Q a)) := by ring
      _ = P a + Q a - 2 * Real.sqrt (P a * Q a) := by
        rw [Real.sq_sqrt (hP.nonneg a), Real.sq_sqrt (hQ.nonneg a),
          Real.sqrt_mul (hP.nonneg a)]
  have hv_term : ∀ a : ω,
      v a ^ 2 = P a + Q a + 2 * Real.sqrt (P a * Q a) := by
    intro a
    dsimp [v]
    calc
      (Real.sqrt (P a) + Real.sqrt (Q a)) ^ 2 =
          Real.sqrt (P a) ^ 2 + Real.sqrt (Q a) ^ 2 +
            2 * (Real.sqrt (P a) * Real.sqrt (Q a)) := by ring
      _ = P a + Q a + 2 * Real.sqrt (P a * Q a) := by
        rw [Real.sq_sqrt (hP.nonneg a), Real.sq_sqrt (hQ.nonneg a),
          Real.sqrt_mul (hP.nonneg a)]
  have hsumP : ∑ a, P a = 1 := by simpa [mass] using hP.total
  have hsumQ : ∑ a, Q a = 1 := by simpa [mass] using hQ.total
  have hu_sum : ∑ a, u a ^ 2 = 2 - 2 * BC P Q := by
    calc
      (∑ a, u a ^ 2) = ∑ a, (P a + Q a - 2 * Real.sqrt (P a * Q a)) := by
        apply sum_congr rfl
        intro a _
        exact hu_term a
      _ = (∑ a, P a) + (∑ a, Q a) - 2 * ∑ a, Real.sqrt (P a * Q a) := by
        rw [sum_sub_distrib, sum_add_distrib, ← mul_sum]
      _ = 2 - 2 * BC P Q := by rw [hsumP, hsumQ, BC]; norm_num
  have hv_sum : ∑ a, v a ^ 2 = 2 + 2 * BC P Q := by
    calc
      (∑ a, v a ^ 2) = ∑ a, (P a + Q a + 2 * Real.sqrt (P a * Q a)) := by
        apply sum_congr rfl
        intro a _
        exact hv_term a
      _ = (∑ a, P a) + (∑ a, Q a) + 2 * ∑ a, Real.sqrt (P a * Q a) := by
        rw [sum_add_distrib, sum_add_distrib, ← mul_sum]
      _ = 2 + 2 * BC P Q := by rw [hsumP, hsumQ, BC]; norm_num
  have huv_sum : ∑ a, u a * v a = ∑ a, |P a - Q a| := by
    apply sum_congr rfl
    intro a _
    exact (hfactor a).symm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ω) u v
  rw [huv_sum, hu_sum, hv_sum] at hcs
  have hsq : ((∑ a, |P a - Q a|) / 2) ^ 2 ≤ 1 - BC P Q ^ 2 := by
    nlinarith
  exact Real.le_sqrt_of_sq_le hsq

/-! ### Analytic preparation for (T4) -/

/-- A mesh of width `1 / (N + 1)` partitions the nonnegative half-line. -/
private lemma mesh_iUnion (N : ℕ) :
    ⋃ k : ℕ, Set.Ico ((k : ℝ) / ((N : ℝ) + 1))
      (((k : ℝ) + 1) / ((N : ℝ) + 1)) = Set.Ici 0 := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ico, Set.mem_Ici]
  constructor
  · rintro ⟨k, hk⟩
    exact (div_nonneg (Nat.cast_nonneg k) (by positivity)).trans hk.1
  · intro hx
    let k : ℕ := ⌊(((N : ℝ) + 1) * x)⌋₊
    have hden : 0 < (N : ℝ) + 1 := by positivity
    have hprod : 0 ≤ ((N : ℝ) + 1) * x := mul_nonneg hden.le hx
    refine ⟨k, ?_, ?_⟩
    · apply (div_le_iff₀ hden).2
      simpa [k, mul_comm] using Nat.floor_le hprod
    · apply (lt_div_iff₀ hden).2
      simpa [k, mul_comm] using Nat.lt_floor_add_one (((N : ℝ) + 1) * x)

private lemma mesh_pairwise (N : ℕ) :
    Pairwise (Function.onFun Disjoint fun k : ℕ ↦
      Set.Ico ((k : ℝ) / ((N : ℝ) + 1))
        (((k : ℝ) + 1) / ((N : ℝ) + 1))) := by
  intro i j hij
  apply Set.disjoint_left.2
  intro x hxi hxj
  have hden : 0 ≤ (N : ℝ) + 1 := by positivity
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hc : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr hij
    have hd : ((i : ℝ) + 1) / ((N : ℝ) + 1) ≤
        (j : ℝ) / ((N : ℝ) + 1) := div_le_div_of_nonneg_right hc hden
    exact (not_lt_of_ge (hd.trans hxj.1)) hxi.2
  · have hc : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr hji
    have hd : ((j : ℝ) + 1) / ((N : ℝ) + 1) ≤
        (i : ℝ) / ((N : ℝ) + 1) := div_le_div_of_nonneg_right hc hden
    exact (not_lt_of_ge (hd.trans hxi.1)) hxj.2

/-- Upper Riemann sums for `exp (-x)` on the nonnegative half-line. -/
private lemma exp_neg_Ici_lintegral_mesh_bound (N : ℕ) :
    (∫⁻ x : ℝ in Set.Ici 0, ENNReal.ofReal (Real.exp (-x))) ≤
      ENNReal.ofReal (((N : ℝ) + 1)⁻¹ *
        (1 - Real.exp (-((N : ℝ) + 1)⁻¹))⁻¹) := by
  let q : ℝ := Real.exp (-((N : ℝ) + 1)⁻¹)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    simp only [q, Real.exp_lt_one_iff]
    exact neg_lt_zero.mpr (inv_pos.mpr (by positivity))
  have hsum : Summable fun k : ℕ ↦ ((N : ℝ) + 1)⁻¹ * q ^ k :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  rw [← mesh_iUnion N,
    lintegral_iUnion (fun _ ↦ measurableSet_Ico) (mesh_pairwise N)]
  calc
    (∑' k : ℕ, ∫⁻ x : ℝ in
        Set.Ico ((k : ℝ) / ((N : ℝ) + 1)) (((k : ℝ) + 1) / ((N : ℝ) + 1)),
          ENNReal.ofReal (Real.exp (-x))) ≤
        ∑' k : ℕ, ENNReal.ofReal (((N : ℝ) + 1)⁻¹ * q ^ k) := by
      apply ENNReal.tsum_le_tsum
      intro k
      calc
        (∫⁻ x : ℝ in
            Set.Ico ((k : ℝ) / ((N : ℝ) + 1)) (((k : ℝ) + 1) / ((N : ℝ) + 1)),
              ENNReal.ofReal (Real.exp (-x))) ≤
            ∫⁻ _x : ℝ in
              Set.Ico ((k : ℝ) / ((N : ℝ) + 1)) (((k : ℝ) + 1) / ((N : ℝ) + 1)),
                ENNReal.ofReal (Real.exp (-((k : ℝ) / ((N : ℝ) + 1)))) := by
          apply setLIntegral_mono measurable_const
          intro x hx
          apply ENNReal.ofReal_le_ofReal
          exact Real.exp_le_exp.mpr (neg_le_neg hx.1)
        _ = ENNReal.ofReal (((N : ℝ) + 1)⁻¹ * q ^ k) := by
          rw [setLIntegral_const, Real.volume_Ico]
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
          congr 1
          rw [← Real.exp_nat_mul]
          field_simp
          ring
    _ = ENNReal.ofReal (∑' k : ℕ, ((N : ℝ) + 1)⁻¹ * q ^ k) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun k ↦ mul_nonneg (by positivity) (pow_nonneg hq0 k))
        hsum).symm
    _ = ENNReal.ofReal (((N : ℝ) + 1)⁻¹ *
        (1 - Real.exp (-((N : ℝ) + 1)⁻¹))⁻¹) := by
      congr 1
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]

private lemma exp_mesh_bound_tendsto :
    Tendsto (fun N : ℕ ↦ ((N : ℝ) + 1)⁻¹ *
      (1 - Real.exp (-((N : ℝ) + 1)⁻¹))⁻¹) atTop (𝓝 1) := by
  let u : ℕ → ℝ := fun N ↦ ((N : ℝ) + 1)⁻¹
  have hu : Tendsto u atTop (𝓝 0) := by
    simpa only [u, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hu_pos : ∀ N, 0 < u N := fun N ↦ by
    simp only [u]
    positivity
  have hu_within : Tendsto u atTop (𝓝[>] (0 : ℝ)) := by
    rw [nhdsWithin]
    exact tendsto_inf.2 ⟨hu, tendsto_principal.2 (Eventually.of_forall hu_pos)⟩
  have hd : HasDerivAt (fun t : ℝ ↦ 1 - Real.exp (-t)) 1 0 := by
    simpa only [neg_zero, Real.exp_zero, one_mul, neg_neg] using
      (hasDerivAt_neg (0 : ℝ)).exp.const_sub 1
  have hs := hd.tendsto_slope_zero_right.comp hu_within
  have hsi := hs.inv₀ one_ne_zero
  convert hsi using 1
  · funext N
    dsimp [u]
    simp only [zero_add, neg_zero, Real.exp_zero, sub_self, sub_zero]
    field_simp
  · norm_num

private lemma exp_neg_Ici_lintegral_le_one :
    (∫⁻ x : ℝ in Set.Ici 0, ENNReal.ofReal (Real.exp (-x))) ≤ 1 := by
  let L : ℝ≥0∞ := lintegral (volume.restrict (Set.Ici 0))
    (fun x : ℝ ↦ ENNReal.ofReal (Real.exp (-x)))
  have hfinite : L ≠ ∞ := by
    have h := exp_neg_Ici_lintegral_mesh_bound 0
    change L ≤ _ at h
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hreal (N : ℕ) : L.toReal ≤ ((N : ℝ) + 1)⁻¹ *
      (1 - Real.exp (-((N : ℝ) + 1)⁻¹))⁻¹ := by
    have he : Real.exp (-((N : ℝ) + 1)⁻¹) < 1 := by
      rw [Real.exp_lt_one_iff]
      exact neg_lt_zero.mpr (inv_pos.mpr (by positivity))
    have hB : 0 ≤ ((N : ℝ) + 1)⁻¹ *
        (1 - Real.exp (-((N : ℝ) + 1)⁻¹))⁻¹ :=
      mul_nonneg (inv_nonneg.mpr (by positivity)) (inv_nonneg.mpr (sub_nonneg.mpr he.le))
    have h := (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).2
      (exp_neg_Ici_lintegral_mesh_bound N)
    rwa [ENNReal.toReal_ofReal hB] at h
  have hL : L.toReal ≤ 1 := ge_of_tendsto exp_mesh_bound_tendsto
    (Eventually.of_forall hreal)
  rw [← ENNReal.toReal_le_toReal hfinite (by simp)]
  simpa using hL

private lemma exp_neg_abs_lintegral_le_two :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-|x|))) ≤ 2 := by
  let F : ℝ → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (Real.exp (-|x|))
  have hpos : (∫⁻ x : ℝ in Set.Ici 0, F x) ≤ 1 := by
    calc
      (∫⁻ x : ℝ in Set.Ici 0, F x) =
          ∫⁻ x : ℝ in Set.Ici 0, ENNReal.ofReal (Real.exp (-x)) := by
        apply setLIntegral_congr_fun measurableSet_Ici
        intro x hx
        simp only [F, abs_of_nonneg (Set.mem_Ici.mp hx)]
      _ ≤ 1 := exp_neg_Ici_lintegral_le_one
  have hsymm : (∫⁻ x : ℝ in Set.Iio 0, F x) = ∫⁻ x : ℝ in Set.Ioi 0, F x := by
    calc
      (∫⁻ x : ℝ in Set.Iio 0, F x) =
          ∫⁻ x : ℝ, (Set.Iio 0).indicator F x :=
        (lintegral_indicator measurableSet_Iio F).symm
      _ = ∫⁻ x : ℝ, (Set.Iio 0).indicator F x
          ∂Measure.map (fun x : ℝ ↦ -x) volume := by
        have hmap : Measure.map (fun x : ℝ ↦ -x) volume = volume := by
          convert Real.map_volume_mul_left (a := (-1 : ℝ)) (by norm_num) using 1 <;>
            norm_num
        rw [hmap]
      _ = ∫⁻ x : ℝ, (Set.Iio 0).indicator F (-x) := by
        simpa using lintegral_map_equiv ((Set.Iio 0).indicator F)
          (MeasurableEquiv.neg ℝ)
      _ = ∫⁻ x : ℝ, (Set.Ioi 0).indicator F x := by
        apply lintegral_congr
        intro x
        simp only [Set.indicator]
        by_cases hx : x ∈ Set.Ioi (0 : ℝ)
        · rw [if_pos (by simpa using hx), if_pos hx]
          simp only [F, abs_neg]
        · rw [if_neg (by simpa using hx), if_neg hx]
      _ = ∫⁻ x : ℝ in Set.Ioi 0, F x := lintegral_indicator measurableSet_Ioi F
  have hneg : (∫⁻ x : ℝ in Set.Iio 0, F x) ≤ 1 := by
    rw [hsymm]
    exact (lintegral_mono' (Measure.restrict_mono Set.Ioi_subset_Ici_self le_rfl) le_rfl).trans
      hpos
  change (∫⁻ x : ℝ, F x) ≤ 2
  calc
    (∫⁻ x : ℝ, F x) =
        (∫⁻ x : ℝ in Set.Ici 0, F x) + ∫⁻ x : ℝ in Set.Iio 0, F x := by
      simpa using (lintegral_add_compl F measurableSet_Ici).symm
    _ ≤ 1 + 1 := add_le_add hpos hneg
    _ = 2 := by norm_num

/-- Scaling the previous bound gives the mass bound for the unnormalized
Laplace kernel. -/
private lemma laplace_kernel_lintegral_le {m : ℝ} (hm : 0 < m) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-|x| / m))) ≤ ENNReal.ofReal (2 * m) := by
  let F : ℝ → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (Real.exp (-|x|))
  let Fm : ℝ → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (Real.exp (-|x| / m))
  have hmap : Measure.map (fun x : ℝ ↦ m⁻¹ * x) volume =
      ENNReal.ofReal m • volume := by
    convert Real.map_volume_mul_left (a := m⁻¹) (inv_ne_zero hm.ne') using 1
    simp only [inv_inv, abs_of_pos hm]
  have hscale : (∫⁻ x : ℝ, Fm x) = ENNReal.ofReal m * ∫⁻ x : ℝ, F x := by
    symm
    calc
      ENNReal.ofReal m * (∫⁻ x : ℝ, F x) =
          ∫⁻ x : ℝ, F x ∂(ENNReal.ofReal m • volume) := by
        rw [lintegral_smul_measure]
        rfl
      _ = ∫⁻ x : ℝ, F x ∂Measure.map (fun x : ℝ ↦ m⁻¹ * x) volume := by
        rw [hmap]
      _ = ∫⁻ x : ℝ, F (m⁻¹ * x) := by
        simpa using lintegral_map_equiv F
          (Homeomorph.mulLeft₀ m⁻¹ (inv_ne_zero hm.ne')).toMeasurableEquiv
      _ = ∫⁻ x : ℝ, Fm x := by
        apply lintegral_congr
        intro x
        simp only [F, Fm, abs_mul, abs_inv, abs_of_pos hm, div_eq_mul_inv]
        rw [mul_comm m⁻¹ |x|]
        rw [neg_mul]
  change (∫⁻ x : ℝ, Fm x) ≤ ENNReal.ofReal (2 * m)
  rw [hscale]
  calc
    ENNReal.ofReal m * (∫⁻ x : ℝ, F x) ≤ ENNReal.ofReal m * 2 :=
      mul_le_mul_of_nonneg_left exp_neg_abs_lintegral_le_two zero_le
    _ = ENNReal.ofReal m * ENNReal.ofReal (2 : ℝ) := by norm_num
    _ = ENNReal.ofReal (m * 2) := (ENNReal.ofReal_mul hm.le).symm
    _ = ENNReal.ofReal (2 * m) := by
      congr 1
      ring

private lemma laplace_density_lintegral_le_one {m : ℝ} (hm : 0 < m) :
    (∫⁻ x : ℝ, ENNReal.ofReal ((2 * m)⁻¹ * Real.exp (-|x| / m))) ≤ 1 := by
  have hc : 0 ≤ (2 * m)⁻¹ := inv_nonneg.mpr (mul_nonneg (by norm_num) hm.le)
  calc
    (∫⁻ x : ℝ, ENNReal.ofReal ((2 * m)⁻¹ * Real.exp (-|x| / m))) =
        ∫⁻ x : ℝ, ENNReal.ofReal ((2 * m)⁻¹) *
          ENNReal.ofReal (Real.exp (-|x| / m)) := by
      apply lintegral_congr
      intro x
      rw [ENNReal.ofReal_mul hc]
    _ = ENNReal.ofReal ((2 * m)⁻¹) *
        ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-|x| / m)) := by
      rw [lintegral_const_mul]
      fun_prop
    _ ≤ ENNReal.ofReal ((2 * m)⁻¹) * ENNReal.ofReal (2 * m) :=
      mul_le_mul_of_nonneg_left (laplace_kernel_lintegral_le hm) zero_le
    _ = 1 := by
      rw [← ENNReal.ofReal_mul hc]
      have h2m : 2 * m ≠ 0 := mul_ne_zero (by norm_num) hm.ne'
      rw [inv_mul_cancel₀ h2m, ENNReal.ofReal_one]

private lemma laplace_density_integrable {m : ℝ} (hm : 0 < m) :
    Integrable (fun x : ℝ ↦ (2 * m)⁻¹ * Real.exp (-|x| / m)) := by
  constructor
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · rw [hasFiniteIntegral_iff_norm]
    have hlin := laplace_density_lintegral_le_one hm
    have heq : (fun x : ℝ ↦ ENNReal.ofReal ‖(2 * m)⁻¹ * Real.exp (-|x| / m)‖) =
        fun x : ℝ ↦ ENNReal.ofReal ((2 * m)⁻¹ * Real.exp (-|x| / m)) := by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact mul_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) hm.le)) (Real.exp_pos _).le
    rw [heq]
    exact hlin.trans_lt (by simp)

private lemma laplace_density_integral_le_one {m : ℝ} (hm : 0 < m) :
    (∫ x : ℝ, (2 * m)⁻¹ * Real.exp (-|x| / m)) ≤ 1 := by
  let g : ℝ → ℝ := fun x ↦ (2 * m)⁻¹ * Real.exp (-|x| / m)
  have hg_nonneg : ∀ x, 0 ≤ g x := fun x ↦
    mul_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) hm.le)) (Real.exp_pos _).le
  have hgsm : AEStronglyMeasurable g := (laplace_density_integrable hm).1
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg_nonneg) hgsm]
  have hlin : (∫⁻ x : ℝ, ENNReal.ofReal (g x)) ≤ 1 := laplace_density_lintegral_le_one hm
  have hfinite : (∫⁻ x : ℝ, ENNReal.ofReal (g x)) ≠ ∞ :=
    ne_top_of_le_ne_top (by simp) hlin
  rw [← ENNReal.toReal_one]
  exact (ENNReal.toReal_le_toReal hfinite (by simp)).2 hlin

/-- Scalar Gibbs inequality, rearranged as a pointwise upper bound on
`negMulLog`. -/
private lemma negMulLog_le_cross {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    Real.negMulLog a ≤ -a * Real.log b - a + b := by
  by_cases ha0 : a = 0
  · simp [ha0, hb.le]
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hlog := Real.log_le_sub_one_of_pos (div_pos hb ha_pos)
    have hmul := mul_le_mul_of_nonneg_left hlog ha
    have hlog_eq : Real.log (b / a) = -Real.log (a / b) := by
      rw [Real.log_div hb.ne' ha0, Real.log_div ha0 hb.ne']
      ring
    have hKL : a - b ≤ a * Real.log (a / b) := by
      calc
        a - b = -(b - a) := by ring
        _ = -(a * (b / a - 1)) := by field_simp
        _ ≤ -(a * Real.log (b / a)) := neg_le_neg hmul
        _ = a * Real.log (a / b) := by rw [hlog_eq]; ring
    rw [Real.negMulLog]
    rw [Real.log_div ha0 hb.ne'] at hKL
    ring_nf at hKL ⊢
    linarith

/-- Differential entropy in **nats** of a real law given by the Lebesgue density
`f`: `h(f) := −∫ f ln f = ∫ negMulLog ∘ f`. -/
noncomputable def diffEntropy (f : ℝ → ℝ) : ℝ := ∫ x, Real.negMulLog (f x)

/-- **(T4)** max-entropy bound: a real random variable with
density `f` and `E|W| ≤ m` has `h(W) ≤ ln(2em)` nats.

The proof starts from `0 ≤ D(f ‖ Laplace(0,m))`.

The integrability hypotheses are essential in Lean: without `hent` and
`habsint`, the junk value of a divergent integral falsifies the claim for
`m < 1/(2e)` (and for heavy-tailed `f`).  The §8 application, a finite mixture
of shifted log-Exp densities, discharges both. -/
theorem diffEntropy_le_of_abs_le {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hint : Integrable f) (hnorm : ∫ x, f x = 1)
    (hent : Integrable fun x => Real.negMulLog (f x))
    (habsint : Integrable fun x => |x| * f x)
    {m : ℝ} (hm : 0 < m) (habs : ∫ x, |x| * f x ≤ m) :
    diffEntropy f ≤ Real.log (2 * Real.exp 1 * m) := by
  let g : ℝ → ℝ := fun x ↦ (2 * m)⁻¹ * Real.exp (-|x| / m)
  let R : ℝ → ℝ := fun x ↦
    -f x + g x + Real.log (2 * m) * f x + m⁻¹ * (|x| * f x)
  have hg_pos (x : ℝ) : 0 < g x := by
    dsimp [g]
    exact mul_pos (inv_pos.mpr (mul_pos (by norm_num) hm)) (Real.exp_pos _)
  have hlogg (x : ℝ) : Real.log (g x) = -Real.log (2 * m) - |x| / m := by
    dsimp [g]
    rw [Real.log_mul (inv_ne_zero (mul_ne_zero (by norm_num) hm.ne')) (Real.exp_ne_zero _),
      Real.log_inv, Real.log_exp]
    ring
  have hpw (x : ℝ) : Real.negMulLog (f x) ≤ R x := by
    have h := negMulLog_le_cross (hf x) (hg_pos x)
    rw [hlogg x] at h
    dsimp [R]
    ring_nf at h ⊢
    exact h
  have hgint : Integrable g := by
    simpa only [g] using laplace_density_integrable hm
  have hg_le : (∫ x, g x) ≤ 1 := by
    simpa only [g] using laplace_density_integral_le_one hm
  have hlogf : Integrable fun x ↦ Real.log (2 * m) * f x := hint.const_mul _
  have habsscaled : Integrable fun x ↦ m⁻¹ * (|x| * f x) := habsint.const_mul _
  have hR : Integrable R := by
    exact (((hint.neg.add hgint).add hlogf).add habsscaled).congr
      (ae_of_all _ fun x ↦ by rfl)
  have hmono : (∫ x, Real.negMulLog (f x)) ≤ ∫ x, R x :=
    integral_mono hent hR hpw
  have habs_scaled : m⁻¹ * (∫ x, |x| * f x) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left habs (inv_nonneg.mpr hm.le)
    rwa [inv_mul_cancel₀ hm.ne'] at h
  have hR_bound : (∫ x, R x) ≤ Real.log (2 * m) + 1 := by
    have hR_eq : (∫ x, R x) =
        -(∫ x, f x) + (∫ x, g x) + Real.log (2 * m) * (∫ x, f x) +
          m⁻¹ * (∫ x, |x| * f x) := by
      have hadd_outer :
          (∫ x, (((-f + g) + (fun x ↦ Real.log (2 * m) * f x)) +
            (fun x ↦ m⁻¹ * (|x| * f x))) x) =
            (∫ x, ((-f + g) + (fun x ↦ Real.log (2 * m) * f x)) x) +
              ∫ x, m⁻¹ * (|x| * f x) := by
        simpa only [Pi.add_apply] using
          integral_add (((hint.neg.add hgint).add hlogf)) habsscaled
      have hadd_mid :
          (∫ x, ((-f + g) + (fun x ↦ Real.log (2 * m) * f x)) x) =
            (∫ x, (-f + g) x) + ∫ x, Real.log (2 * m) * f x := by
        simpa only [Pi.add_apply] using integral_add (hint.neg.add hgint) hlogf
      have hadd_inner : (∫ x, (-f + g) x) = (∫ x, (-f) x) + ∫ x, g x := by
        simpa only [Pi.add_apply] using integral_add hint.neg hgint
      have hneg_eq : (∫ x, (-f) x) = -(∫ x, f x) := by
        simpa only [Pi.neg_apply] using integral_neg f
      have hlog_eq : (∫ x, Real.log (2 * m) * f x) =
          Real.log (2 * m) * (∫ x, f x) := integral_const_mul _ _
      have habs_eq : (∫ x, m⁻¹ * (|x| * f x)) =
          m⁻¹ * (∫ x, |x| * f x) := integral_const_mul _ _
      calc
        (∫ x, R x) = ∫ x, (((-f + g) + (fun x ↦ Real.log (2 * m) * f x)) +
            (fun x ↦ m⁻¹ * (|x| * f x))) x := by rfl
        _ = (∫ x, ((-f + g) + (fun x ↦ Real.log (2 * m) * f x)) x) +
            ∫ x, m⁻¹ * (|x| * f x) := hadd_outer
        _ = ((∫ x, (-f + g) x) + ∫ x, Real.log (2 * m) * f x) +
            ∫ x, m⁻¹ * (|x| * f x) := by
          exact congrArg (fun z ↦ z + ∫ x, m⁻¹ * (|x| * f x)) hadd_mid
        _ = (((∫ x, (-f) x) + ∫ x, g x) + ∫ x, Real.log (2 * m) * f x) +
            ∫ x, m⁻¹ * (|x| * f x) := by
          exact congrArg (fun z ↦ (z + ∫ x, Real.log (2 * m) * f x) +
            ∫ x, m⁻¹ * (|x| * f x)) hadd_inner
        _ = -(∫ x, f x) + (∫ x, g x) + Real.log (2 * m) * (∫ x, f x) +
            m⁻¹ * (∫ x, |x| * f x) := by
          rw [hneg_eq, hlog_eq, habs_eq]
    rw [hR_eq, hnorm]
    linarith
  have hlog : Real.log (2 * Real.exp 1 * m) = Real.log (2 * m) + 1 := by
    rw [show 2 * Real.exp 1 * m = (2 * m) * Real.exp 1 by ring,
      Real.log_mul (mul_ne_zero (by norm_num) hm.ne') (Real.exp_ne_zero 1), Real.log_exp]
  rw [diffEntropy, hlog]
  exact hmono.trans hR_bound

end stoch_to_det
