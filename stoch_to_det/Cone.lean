import stoch_to_det.Scalar

/-!
# §10. The cone bound


`cone = I(X*₋B ; Z ∣ B, C₀, U) ≤ d` in **nats** — the whole losing vector,
priced against a single product reference, with **no** face, loser, rank or
spacing approximation.

The statement of Theorem 10.1 is the `RaceQuantities.cone_le_nats`
obligation; this module keeps its shifted-exponential ingredients and the
`Korth` assembly bound.

## Proof structure

Three steps:

1. **One product reference.** For a unit exponential
   shifted by `a ≥ 0`, the density ratio on the shifted support is the constant
   `eᵃ`, so `D(Law(a+E) ‖ Law(E)) = a` **exactly**. KL is additive over
   products, hence
   `D(P_z^{(u,b)} ‖ Q₀) = u ∑_{c≠b} r_c(z) = u (1/s_z − 1)`  — the coordinate
   sum collapses algebraically.
2. **Information radius.** The golden formula against the
   true conditional output mixture, discarding `D(P_out ‖ Q) ≥ 0`; this is
   packaged by the race construction in `stoch_to_det.Race`.
3. **Integrate the exact joint** against `q_g(z)e^{−u/s_z}du`
   using `∫₀^∞ u e^{−u/s} du = s²`, collapsing to
   `E_p[1 − ∑_b σ_b(Z)²] = d` by Lemma 7.2(d).

The analytic content is `shifted_exp_klDiv` and the elementary integral
`exp_integral_sq`; the rest is `Finset.sum` algebra. `cone` conditions on the
continuous `U`, so its definition depends on the modelling question described
in `stoch_to_det.Quotient`.
-/

namespace stoch_to_det

open Finset MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable {p : α × β → ℝ} {D : SeedSetup p} {K : Clustering D}

private theorem klDiv_smul_restrict {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (s : Set Ω) (hs : MeasurableSet s)
    (c : ℝ≥0) [IsProbabilityMeasure (c • ν.restrict s)] :
    (klDiv (c • ν.restrict s) ν).toReal = Real.log (c : ℝ) := by
  let μ : Measure Ω := c • ν.restrict s
  have hμν : μ ≪ ν := Measure.absolutelyContinuous_restrict.smul_left c
  have hrn : μ.rnDeriv ν =ᵐ[ν]
      (fun x => c • s.indicator (fun _ => (1 : ℝ≥0∞)) x) := by
    exact (Measure.rnDeriv_smul_left (ν.restrict s) ν c).trans
      ((Measure.rnDeriv_restrict_self ν hs).const_smul c)
  have hmem : ∀ᵐ x ∂μ, x ∈ s := by
    exact Measure.ae_smul_measure (ae_restrict_mem hs) c
  have hllr : llr μ ν =ᵐ[μ] fun _ => Real.log (c : ℝ) := by
    filter_upwards [hμν.ae_le hrn, hmem] with x hx hxs
    rw [llr, hx]
    simp [Set.indicator_of_mem hxs]
  rw [toReal_klDiv_of_measure_eq hμν (by simp [μ]), integral_congr_ae hllr]
  simp

private theorem map_expMeasure_add_eq_smul_restrict {a : ℝ} (ha : 0 ≤ a) :
    (expMeasure 1).map (fun x => a + x) =
      Real.toNNReal (Real.exp a) • (expMeasure 1).restrict (Set.Ioi a) := by
  let ν : Measure ℝ := expMeasure 1
  let c : ℝ≥0 := Real.toNNReal (Real.exp a)
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_expMeasure (by norm_num)
  apply Measure.ext_of_Iic
  intro x
  have hpre : (fun y : ℝ => a + y) ⁻¹' Set.Iic x = Set.Iic (x - a) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iic]
    constructor <;> intro h <;> linarith
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic, hpre]
  change ν (Set.Iic (x - a)) = (c • ν.restrict (Set.Ioi a)) (Set.Iic x)
  rw [Measure.coe_nnreal_smul_apply, Measure.restrict_apply measurableSet_Iic]
  simp only [Set.inter_comm (Set.Iic x), Set.Ioi_inter_Iic]
  by_cases hx : a ≤ x
  · have hxa : 0 ≤ x - a := sub_nonneg.mpr hx
    have hx0 : 0 ≤ x := ha.trans hx
    have hIoc : ν (Set.Ioc a x) = ENNReal.ofReal (cdf ν x - cdf ν a) := by
      calc
        ν (Set.Ioc a x) = (cdf ν).measure (Set.Ioc a x) := by rw [measure_cdf]
        _ = ENNReal.ofReal (cdf ν x - cdf ν a) :=
          StieltjesFunction.measure_Ioc (cdf ν) a x
    rw [← ofReal_cdf ν (x - a), hIoc]
    dsimp [ν, c]
    rw [cdf_expMeasure_eq (by norm_num), cdf_expMeasure_eq (by norm_num),
      cdf_expMeasure_eq (by norm_num)]
    simp only [if_pos hxa, if_pos hx0, if_pos ha]
    simp only [one_mul]
    rw [show -(x - a) = a - x by ring]
    rw [← ENNReal.ofReal_coe_nnreal]
    rw [Real.coe_toNNReal _ (Real.exp_nonneg a)]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg a)]
    congr 1
    have haa : Real.exp a * Real.exp (-a) = 1 := by
      rw [← Real.exp_add]
      simp
    have hax : Real.exp a * Real.exp (-x) = Real.exp (a - x) := by
      rw [← Real.exp_add]
      congr 1
    simp only [mul_sub]
    rw [haa, hax]
    ring
  · have hxa : x < a := lt_of_not_ge hx
    have hneg : x - a < 0 := sub_neg.mpr hxa
    have hempty : Set.Ioc a x = ∅ := Set.Ioc_eq_empty (not_lt.mpr hxa.le)
    rw [hempty, measure_empty]
    simp only [mul_zero]
    rw [← ofReal_cdf ν (x - a)]
    dsimp [ν]
    rw [cdf_expMeasure_eq (by norm_num)]
    rw [if_neg (not_le.mpr hneg)]
    simp

/-- **Step 1**: a unit exponential shifted by `a ≥ 0` has
`D(Law(a+E) ‖ Law(E)) = a` exactly, in nats.

The density ratio on the shifted support is the *constant* `eᵃ`, which is why
the coordinate sum in (10.1) collapses with no slack. -/
theorem shifted_exp_klDiv {a : ℝ} (ha : 0 ≤ a) :
    (klDiv ((expMeasure 1).map (fun x => a + x)) (expMeasure 1)).toReal = a := by
  let c : ℝ≥0 := Real.toNNReal (Real.exp a)
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have hmap := map_expMeasure_add_eq_smul_restrict ha
  letI : IsProbabilityMeasure
      (c • (expMeasure 1).restrict (Set.Ioi a)) := by
    rw [← hmap]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  rw [hmap, klDiv_smul_restrict (expMeasure 1) (Set.Ioi a) measurableSet_Ioi c]
  simp [c, Real.coe_toNNReal _ (Real.exp_nonneg a)]

/-- **(10.1)**: additivity of KL over the product of
shifted exponentials, `D(P_z^{(u,b)} ‖ Q₀) = u ∑_{c≠b} r_c(z) = u(1/s_z − 1)`. -/
theorem product_shift_klDiv (b : K.κ) {z : α × β} (hz : z ∈ support p)
    {u : ℝ} (hu : 0 ≤ u) :
    ∑ c ∈ univ.erase b, u * (K.sigma c z / K.sigma b z)
      = u * (1 / K.sigma b z - 1) := by
  have hpz : p z ≠ 0 := by
    simpa [support] using hz
  have hsigma : ∑ c, K.sigma c z = 1 := by
    calc
      ∑ c, K.sigma c z = ∑ ℓ, D.post ℓ z := by
        unfold Clustering.sigma
        simpa using
          (Finset.sum_fiberwise (univ : Finset D.L.ι) K.cl (fun ℓ => D.post ℓ z))
      _ = (∑ ℓ, D.L.prior ℓ * D.L.comp ℓ z) / p z := by
        simp only [SeedSetup.post, Finset.sum_div]
      _ = p z / p z := by rw [D.L.mixture]
      _ = 1 := div_self hpz
  have hsb : K.sigma b z ≠ 0 := (K.sigma_pos b z hz).ne'
  have herase : ∑ c ∈ univ.erase b, K.sigma c z = 1 - K.sigma b z := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ b), hsigma]
  calc
    ∑ c ∈ univ.erase b, u * (K.sigma c z / K.sigma b z) =
        u / K.sigma b z * ∑ c ∈ univ.erase b, K.sigma c z := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c _
          field_simp
    _ = u / K.sigma b z * (1 - K.sigma b z) := by rw [herase]
    _ = u * (1 / K.sigma b z - 1) := by field_simp

/-- The elementary integral of **Step 3**:
`∫₀^∞ u e^{−u/s} du = s²` for `s > 0`. -/
theorem exp_integral_sq {s : ℝ} (hs : 0 < s) :
    ∫ u in Set.Ioi (0 : ℝ), u * Real.exp (-u / s) = s ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : ℝ)) (r := 1 / s) (by norm_num) (one_div_pos.mpr hs)
  simpa [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
    div_eq_mul_inv, hs.ne', mul_comm] using h

/-- **Theorem 10.1**, bits form:
`cone ≤ d/ln 2 ≤ K_orth (M + S)`, using Theorem 9.1. -/
theorem cone_bound_Korth (R : RaceQuantities D K) :
    R.cone ≤ Korth * (D.M + K.Sinfo) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    R.cone ≤ K.dMis / Real.log 2 := (le_div_iff₀ hlog).2 R.cone_le_nats
    _ ≤ Korth * (D.M + K.Sinfo) := mismatch_charge_Korth K

end stoch_to_det
