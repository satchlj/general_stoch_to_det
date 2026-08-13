import stoch_to_det.Main1771

/-!
# A rational certificate for `Cdagger1771 < 1771`

All numerical comparisons in this module are exact rational arithmetic.
Transcendental quantities are bounded by proved Taylor, integral, and
Euler--Mascheroni inequalities; no floating-point evaluator is used.
-/

namespace stoch_to_det

open MeasureTheory Set Finset

/-- The elementary logarithmic moments on `(0,1]`. -/
theorem integral_neg_log_mul_pow (m : ℕ) :
    (∫ t : ℝ in Set.Ioc 0 1, (-Real.log t) * t ^ m) =
      1 / (m + 1 : ℝ) ^ 2 := by
  let f : ℝ → ℝ := fun x => Real.exp (-x)
  let g : ℝ → ℝ := fun t => (-Real.log t) * t ^ m
  have himage : f '' Set.Ioi 0 = Set.Ioo (0 : ℝ) 1 := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      constructor
      · exact Real.exp_pos _
      · exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)
    · intro ht
      refine ⟨-Real.log t, ?_, ?_⟩
      · have hlog : Real.log t < 0 := Real.log_neg ht.1 ht.2
        simpa using neg_pos.mpr hlog
      · dsimp [f]
        rw [neg_neg, Real.exp_log ht.1]
  have hderiv (x : ℝ) : HasDerivAt f (-Real.exp (-x)) x := by
    simpa [f, Function.comp_def] using
      (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg' (x := x))
  have hinj : Set.InjOn f (Set.Ioi 0) := by
    intro x _ y _ hxy
    dsimp [f] at hxy
    have := Real.exp_injective hxy
    linarith
  have hchange := integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioi (0 : ℝ)) (f := f)
    (f' := fun x => -Real.exp (-x)) measurableSet_Ioi
    (fun x _ => (hderiv x).hasDerivWithinAt) hinj g
  rw [himage] at hchange
  have haeeq :
      (∫ t : ℝ in Set.Ioc 0 1, g t) =
        ∫ t : ℝ in Set.Ioo 0 1, g t := by
    rw [restrict_Ioo_eq_restrict_Ioc]
  rw [haeeq, hchange]
  have hvalue := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : ℝ)) (r := (m + 1 : ℝ)) (by norm_num) (by positivity)
  calc
    (∫ x : ℝ in Set.Ioi 0,
        |-Real.exp (-x)| • g (f x)) =
        ∫ x : ℝ in Set.Ioi 0,
          x * Real.exp (-(m + 1 : ℝ) * x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx0 : 0 < x := hx
      simp only [abs_neg, abs_of_pos (Real.exp_pos _), smul_eq_mul]
      dsimp [f, g]
      rw [Real.log_exp]
      rw [← Real.exp_nat_mul]
      calc
        Real.exp (-x) * (- -x * Real.exp (↑m * -x)) =
            x * (Real.exp (-x) * Real.exp (↑m * -x)) := by ring
        _ = x * Real.exp (-x + ↑m * -x) := by rw [Real.exp_add]
        _ = x * Real.exp (-(↑m + 1) * x) := by congr 1 <;> ring
    _ = 1 / (m + 1 : ℝ) ^ 2 := by
      calc
        (∫ x : ℝ in Set.Ioi 0,
            x * Real.exp (-(m + 1 : ℝ) * x)) =
            (1 / (m + 1 : ℝ)) ^ 2 * Real.Gamma 2 := by
          simpa only [show (2 : ℝ) - 1 = 1 by norm_num,
            Real.rpow_one, Real.rpow_two, neg_mul] using hvalue
        _ = 1 / (m + 1 : ℝ) ^ 2 := by
          rw [Real.Gamma_two, mul_one, div_pow]
          norm_num

/-- The low-half logarithmic moment used in the Taylor certificate. -/
noncomputable def lowLogMoment1771 : ℝ :=
  ∫ t : ℝ in Set.Ioc 0 1, (-Real.log t) * Real.exp (-t)

/-- Splitting the signed and absolute logarithmic moments at `1`. -/
theorem logExpAbsMoment_eq_low :
    logExpAbsMoment =
      2 * lowLogMoment1771 - Real.eulerMascheroniConstant := by
  let fa : ℝ → ℝ := fun t => |Real.log t| * Real.exp (-t)
  let fs : ℝ → ℝ := fun t => Real.log t * Real.exp (-t)
  let fl : ℝ → ℝ := fun t => (-Real.log t) * Real.exp (-t)
  have hfa : IntegrableOn fa (Set.Ioi 0) := by
    simpa [fa] using integrableOn_abs_log_mul_exp_neg_Ioi_1771
  have hfs_meas : StronglyMeasurable fs := by
    dsimp [fs]
    exact (Real.measurable_log.mul
      (Real.measurable_exp.comp measurable_id.neg)).stronglyMeasurable
  have hfs : IntegrableOn fs (Set.Ioi 0) := by
    refine hfa.congr' hfs_meas.aestronglyMeasurable.restrict ?_
    filter_upwards with t
    dsimp [fa, fs]
    simp only [Real.norm_eq_abs, abs_mul,
      abs_abs, abs_of_nonneg (Real.exp_nonneg _)]
  have hfaLow : IntegrableOn fa (Set.Ioc 0 1) :=
    hfa.mono_set (by intro t ht; exact ht.1)
  have hfaHigh : IntegrableOn fa (Set.Ioi 1) :=
    hfa.mono_set (by
      intro t ht
      exact zero_lt_one.trans (show (1 : ℝ) < t from ht))
  have hfsLow : IntegrableOn fs (Set.Ioc 0 1) :=
    hfs.mono_set (by intro t ht; exact ht.1)
  have hfsHigh : IntegrableOn fs (Set.Ioi 1) :=
    hfs.mono_set (by
      intro t ht
      exact zero_lt_one.trans (show (1 : ℝ) < t from ht))
  have habsSplit : logExpAbsMoment =
      (∫ t : ℝ in Set.Ioc 0 1, fa t) +
        ∫ t : ℝ in Set.Ioi 1, fa t := by
    unfold logExpAbsMoment
    change (∫ t : ℝ in Set.Ioi 0, fa t) = _
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        hfaLow hfaHigh]
  have hsignedSplit : -Real.eulerMascheroniConstant =
      (∫ t : ℝ in Set.Ioc 0 1, fs t) +
        ∫ t : ℝ in Set.Ioi 1, fs t := by
    rw [← integral_log_mul_exp_neg_Ioi]
    change (∫ t : ℝ in Set.Ioi 0, fs t) = _
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        hfsLow hfsHigh]
  have habsLow : (∫ t : ℝ in Set.Ioc 0 1, fa t) =
      lowLogMoment1771 := by
    unfold lowLogMoment1771
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have hlog : Real.log t ≤ 0 := Real.log_nonpos ht.1.le ht.2
    dsimp [fa, fl]
    rw [abs_of_nonpos hlog]
  have habsHigh : (∫ t : ℝ in Set.Ioi 1, fa t) =
      ∫ t : ℝ in Set.Ioi 1, fs t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hlog : 0 ≤ Real.log t := Real.log_nonneg ht.le
    dsimp [fa, fs]
    rw [abs_of_nonneg hlog]
  have hsignedLow : (∫ t : ℝ in Set.Ioc 0 1, fs t) =
      -lowLogMoment1771 := by
    calc
      (∫ t : ℝ in Set.Ioc 0 1, fs t) =
          ∫ t : ℝ in Set.Ioc 0 1, -fl t := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t _
        dsimp [fs, fl]
        ring
      _ = -(∫ t : ℝ in Set.Ioc 0 1, fl t) := by rw [integral_neg]
      _ = -lowLogMoment1771 := by rfl
  rw [habsLow, habsHigh] at habsSplit
  rw [hsignedLow] at hsignedSplit
  linarith

/-- The degree-seven Taylor polynomial for `exp (-t)`. -/
noncomputable def expNegTaylor7 (t : ℝ) : ℝ :=
  ∑ m ∈ Finset.range 8, (-t) ^ m / (m.factorial : ℝ)

lemma exp_neg_le_taylor7 (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp (-t) ≤ expNegTaylor7 t + t ^ 8 / 35840 := by
  have hb := Real.exp_bound (x := -t) (n := 8)
    (by simpa [abs_neg, abs_of_nonneg ht0] using ht1) (by norm_num)
  have hub := (abs_le.mp hb).2
  rw [abs_neg, abs_of_nonneg ht0] at hub
  change Real.exp (-t) - expNegTaylor7 t ≤ _ at hub
  norm_num at hub ⊢
  linarith

/-- Integrability of all logarithmic moments used to integrate the Taylor
polynomial. -/
lemma integrableOn_neg_log_mul_pow (m : ℕ) :
    IntegrableOn (fun t : ℝ => (-Real.log t) * t ^ m) (Set.Ioc 0 1) := by
  have hlog : IntegrableOn (fun t : ℝ => -Real.log t) (Set.Ioc 0 1) := by
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      intervalIntegral.intervalIntegrable_log').neg
  have hmeas : StronglyMeasurable (fun t : ℝ => (-Real.log t) * t ^ m) := by
    exact (Real.measurable_log.neg.mul
      (continuous_pow m).measurable).stronglyMeasurable
  refine Integrable.mono_nonneg hlog hmeas.aestronglyMeasurable.restrict ?_ ?_
  · rw [ae_restrict_iff' measurableSet_Ioc]
    exact ae_of_all _ fun t ht =>
      mul_nonneg (neg_nonneg.mpr (Real.log_nonpos ht.1.le ht.2))
        (pow_nonneg ht.1.le m)
  · rw [ae_restrict_iff' measurableSet_Ioc]
    exact ae_of_all _ fun t ht => by
      have hneglog : 0 ≤ -Real.log t :=
        neg_nonneg.mpr (Real.log_nonpos ht.1.le ht.2)
      have hpow : t ^ m ≤ 1 := pow_le_one₀ ht.1.le ht.2
      exact mul_le_of_le_one_right hneglog hpow

/-- Exact rational upper certificate for the low logarithmic moment. -/
theorem lowLogMoment1771_le :
    lowLogMoment1771 ≤ (10117453 : ℝ) / 12700800 := by
  let term : ℕ → ℝ → ℝ := fun m t =>
    (-Real.log t) * ((-t) ^ m / (m.factorial : ℝ))
  let rem : ℝ → ℝ := fun t =>
    (-Real.log t) * (t ^ 8 / 35840)
  let major : ℝ → ℝ := fun t =>
    (-Real.log t) * (expNegTaylor7 t + t ^ 8 / 35840)
  have hterm (m : ℕ) : IntegrableOn (term m) (Set.Ioc 0 1) := by
    have h := (integrableOn_neg_log_mul_pow m).const_mul
      (((-1 : ℝ) ^ m) / (m.factorial : ℝ))
    refine h.congr (ae_of_all _ fun t => ?_)
    dsimp [term]
    rw [neg_pow]
    ring
  have hpoly : IntegrableOn
      (fun t : ℝ => (-Real.log t) * expNegTaylor7 t) (Set.Ioc 0 1) := by
    have hsum := integrable_finsetSum (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
      (Finset.range 8) (fun m _ => hterm m)
    refine hsum.congr (ae_of_all _ fun t => ?_)
    simp only [term, expNegTaylor7, Finset.mul_sum]
  have hrem : IntegrableOn rem (Set.Ioc 0 1) := by
    have h := (integrableOn_neg_log_mul_pow 8).const_mul ((1 : ℝ) / 35840)
    refine h.congr (ae_of_all _ fun t => ?_)
    dsimp [rem]
    ring
  have hmajor : IntegrableOn major (Set.Ioc 0 1) := by
    have hadd := hpoly.add hrem
    refine hadd.congr (ae_of_all _ fun t => ?_)
    change (-Real.log t) * expNegTaylor7 t + rem t = major t
    dsimp [major, rem]
    ring
  have hactual : IntegrableOn
      (fun t : ℝ => (-Real.log t) * Real.exp (-t)) (Set.Ioc 0 1) := by
    have habs := integrableOn_abs_log_mul_exp_neg_Ioi_1771.mono_set
      (show Set.Ioc (0 : ℝ) 1 ⊆ Set.Ioi 0 by intro t ht; exact ht.1)
    refine habs.congr (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
    have hlog : Real.log t ≤ 0 := Real.log_nonpos ht.1.le ht.2
    change |Real.log t| * Real.exp (-t) =
      (-Real.log t) * Real.exp (-t)
    rw [abs_of_nonpos hlog]
  have hpoint (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
      (-Real.log t) * Real.exp (-t) ≤ major t := by
    have hlog : 0 ≤ -Real.log t :=
      neg_nonneg.mpr (Real.log_nonpos ht.1.le ht.2)
    dsimp [major]
    exact mul_le_mul_of_nonneg_left
      (exp_neg_le_taylor7 t ht.1.le ht.2) hlog
  have hle : lowLogMoment1771 ≤
      ∫ t : ℝ in Set.Ioc 0 1, major t := by
    unfold lowLogMoment1771
    exact setIntegral_mono_on hactual hmajor measurableSet_Ioc hpoint
  have htermValue (m : ℕ) :
      (∫ t : ℝ in Set.Ioc 0 1, term m t) =
        ((-1 : ℝ) ^ m / (m.factorial : ℝ)) *
          (1 / (m + 1 : ℝ) ^ 2) := by
    calc
      (∫ t : ℝ in Set.Ioc 0 1, term m t) =
          ∫ t : ℝ in Set.Ioc 0 1,
            (((-1 : ℝ) ^ m / (m.factorial : ℝ)) *
              ((-Real.log t) * t ^ m)) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t _
        dsimp [term]
        rw [neg_pow]
        ring
      _ = ((-1 : ℝ) ^ m / (m.factorial : ℝ)) *
          (∫ t : ℝ in Set.Ioc 0 1, (-Real.log t) * t ^ m) := by
        rw [integral_const_mul]
      _ = ((-1 : ℝ) ^ m / (m.factorial : ℝ)) *
          (1 / (m + 1 : ℝ) ^ 2) := by rw [integral_neg_log_mul_pow]
  have hpolyValue :
      (∫ t : ℝ in Set.Ioc 0 1,
        (-Real.log t) * expNegTaylor7 t) =
      ∑ m ∈ Finset.range 8,
        ((-1 : ℝ) ^ m / (m.factorial : ℝ)) *
          (1 / (m + 1 : ℝ) ^ 2) := by
    calc
      (∫ t : ℝ in Set.Ioc 0 1,
          (-Real.log t) * expNegTaylor7 t) =
          ∫ t : ℝ in Set.Ioc 0 1, ∑ m ∈ Finset.range 8, term m t := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t _
        simp only [term, expNegTaylor7, Finset.mul_sum]
      _ = ∑ m ∈ Finset.range 8,
          ∫ t : ℝ in Set.Ioc 0 1, term m t := by
        rw [integral_finsetSum (Finset.range 8) (fun m _ => hterm m)]
      _ = ∑ m ∈ Finset.range 8,
          ((-1 : ℝ) ^ m / (m.factorial : ℝ)) *
            (1 / (m + 1 : ℝ) ^ 2) := by
        apply Finset.sum_congr rfl
        intro m _
        exact htermValue m
  have hremValue :
      (∫ t : ℝ in Set.Ioc 0 1, rem t) =
        (1 / 35840 : ℝ) * (1 / (8 + 1 : ℝ) ^ 2) := by
    calc
      (∫ t : ℝ in Set.Ioc 0 1, rem t) =
          (1 / 35840 : ℝ) *
            (∫ t : ℝ in Set.Ioc 0 1, (-Real.log t) * t ^ 8) := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t _
        dsimp [rem]
        ring
      _ = (1 / 35840 : ℝ) * (1 / (8 + 1 : ℝ) ^ 2) := by
        rw [integral_neg_log_mul_pow]
        norm_num
  have hmajorValue :
      (∫ t : ℝ in Set.Ioc 0 1, major t) =
        (10117453 : ℝ) / 12700800 := by
    calc
      (∫ t : ℝ in Set.Ioc 0 1, major t) =
          (∫ t : ℝ in Set.Ioc 0 1,
            (-Real.log t) * expNegTaylor7 t) +
          ∫ t : ℝ in Set.Ioc 0 1, rem t := by
        rw [← integral_add hpoly hrem]
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t _
        dsimp [major, rem]
        ring
      _ = (10117453 : ℝ) / 12700800 := by
        rw [hpolyValue, hremValue]
        norm_num [Finset.sum_range_succ]
  rw [hmajorValue] at hle
  exact hle

section

set_option maxRecDepth 10000

/-- A certified lower bound for Euler's constant, obtained from the same
harmonic-sequence argument as the historical constant audit. -/
theorem eulerMascheroni_lower_1771 :
    (5770052 : ℝ) / 10000000 < Real.eulerMascheroniConstant := by
  have hlog2500 : Real.log 2500 = 2 * Real.log 2 + 4 * Real.log 5 := by
    calc
      Real.log 2500 = Real.log (((2 : ℝ) ^ 2) * ((5 : ℝ) ^ 4)) := by
        norm_num
      _ = Real.log ((2 : ℝ) ^ 2) + Real.log ((5 : ℝ) ^ 4) :=
        Real.log_mul (by norm_num) (by norm_num)
      _ = 2 * Real.log 2 + 4 * Real.log 5 := by
        rw [Real.log_pow, Real.log_pow]
        norm_num only [Nat.cast_ofNat]
  have hgamma := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 2499
  have hlog2 := Real.log_two_lt_d9
  have hlog5 := Real.log_five_lt_d9
  rw [Real.eulerMascheroniSeq] at hgamma
  norm_num only [Nat.cast_ofNat] at hgamma
  rw [hlog2500] at hgamma
  norm_num [harmonic] at hgamma hlog2 hlog5 ⊢
  nlinarith

end

/-- Seven Taylor terms already certify `2/e < 0.7359`. -/
theorem two_div_exp_one_lt_1771 :
    2 / Real.exp 1 < (7359 : ℝ) / 10000 := by
  have hsum := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) 7
  have hexp : 0 < Real.exp 1 := Real.exp_pos 1
  apply (div_lt_iff₀ hexp).2
  norm_num [Finset.sum_range_succ] at hsum ⊢
  nlinarith

/-- Rational envelope for `alpha1771`. -/
noncomputable def alphaBar1771 : ℝ :=
  (7359 : ℝ) / 10000 +
    2 * ((10117453 : ℝ) / 12700800) -
    (5770052 : ℝ) / 10000000

lemma alpha1771_lt_alphaBar1771 : alpha1771 < alphaBar1771 := by
  have hA := lowLogMoment1771_le
  have hγ := eulerMascheroni_lower_1771
  have he := two_div_exp_one_lt_1771
  have habs := logExpAbsMoment_eq_low
  unfold alpha1771 alphaBar1771
  linarith

/-- The rational exponent used to bound `log (2 alpha)`. -/
noncomputable def x01771 : ℝ :=
  (5770052 : ℝ) / 10000000 + (677 : ℝ) / 1000

lemma two_mul_alpha1771_lt_exp_x01771 :
    2 * alpha1771 < Real.exp x01771 := by
  have hxnonneg : 0 ≤ x01771 := by norm_num [x01771]
  have hsum := Real.sum_le_exp_of_nonneg hxnonneg 9
  have hrat : 2 * alphaBar1771 <
      ∑ i ∈ Finset.range 9, x01771 ^ i / (i.factorial : ℝ) := by
    norm_num [alphaBar1771, x01771, Finset.sum_range_succ]
  have hα := alpha1771_lt_alphaBar1771
  exact (by nlinarith : 2 * alpha1771 < 2 * alphaBar1771) |>.trans
    (hrat.trans_le hsum)

/-- The exact scalar charge satisfies the sharp rational envelope used by
the final ledger. -/
theorem cOff1771_lt : cOff1771 < (677 : ℝ) / 1000 := by
  have hαpos : 0 < 2 * alpha1771 := by
    nlinarith [one_lt_alpha1771]
  have hlog : Real.log (2 * alpha1771) < x01771 :=
    (Real.log_lt_iff_lt_exp hαpos).2 two_mul_alpha1771_lt_exp_x01771
  have hγ := eulerMascheroni_lower_1771
  unfold x01771 at hlog
  unfold cOff1771
  linarith

/-- The second-order lower Taylor bound for `-log (1-u)`. -/
lemma neg_log_one_sub_ge_quadratic {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    u + u ^ 2 / 2 ≤ -Real.log (1 - u) := by
  let f : ℝ → ℝ := fun x =>
    -Real.log (1 - x) - x - x ^ 2 / 2
  have hfderiv (x : ℝ) (hx : x < 1) :
      HasDerivAt f (x ^ 2 / (1 - x)) x := by
    have hone : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      have hraw := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
      refine (hraw.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with y
        rfl
      · norm_num
    have hlog := hone.log (by linarith : 1 - x ≠ 0)
    have hsq : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
      have hraw := ((hasDerivAt_id x).pow 2).div_const 2
      refine (hraw.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with y
        rfl
      · norm_num
    have hraw := hlog.neg.sub (hasDerivAt_id x) |>.sub hsq
    have hraw' : HasDerivAt f (-(-1 / (1 - x)) - 1 - x) x := by
      refine hraw.congr_of_eventuallyEq ?_
      filter_upwards with y
      rfl
    have hne : 1 - x ≠ 0 := by linarith
    refine hraw'.congr_deriv ?_
    field_simp [hne]
    ring
  have hdiff : DifferentiableOn ℝ f (Set.Icc 0 u) := by
    intro x hx
    exact (hfderiv x (lt_of_le_of_lt hx.2 hu1)).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn f (Set.Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) u) hdiff.continuousOn
      (hdiff.mono interior_subset)
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) u := interior_subset hx
    have hxlt : x < 1 := lt_of_le_of_lt hxIcc.2 hu1
    rw [(hfderiv x hxlt).deriv]
    exact div_nonneg (sq_nonneg x) (sub_nonneg.mpr hxlt.le)
  have hle := hmono (show (0 : ℝ) ∈ Set.Icc 0 u by exact ⟨le_rfl, hu0⟩)
    (show u ∈ Set.Icc (0 : ℝ) u by exact ⟨hu0, le_rfl⟩) hu0
  dsimp [f] at hle
  norm_num at hle
  linarith

/-- The exact information floor dominates a rational expression in
`u = chi/2`. -/
theorem infoFloor1771_lower :
    (2 * (chi1771 / 2) + (chi1771 / 2) ^ 2) / Real.log 2 ≤
      infoFloor1771 := by
  let u : ℝ := chi1771 / 2
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact div_nonneg chi1771_pos.le (by norm_num)
  have hu1 : u < 1 := by dsimp [u]; linarith [chi1771_lt_two]
  have hquad := neg_log_one_sub_ge_quadratic hu0 hu1
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hfloorMul : infoFloor1771 * Real.log 2 =
      -2 * Real.log (1 - chi1771 / 2) := by
    unfold infoFloor1771
    rw [lg_eq_log_div]
    field_simp [hlog2.ne']
  apply (div_le_iff₀ hlog2).2
  rw [hfloorMul]
  dsimp [u] at hquad ⊢
  nlinarith

/-! ### Rational envelopes for the closing ledger -/

noncomputable def u1771 : ℝ := chi1771 / 2

noncomputable def v1771 : ℝ := 2 * u1771 + u1771 ^ 2

noncomputable def KMbar1771 : ℝ :=
  ((2677 : ℝ) / 1000) / v1771

noncomputable def KSbar1771 : ℝ :=
  2 + 2 * ((2677 : ℝ) / 1000) / delta1771

lemma u1771_pos : 0 < u1771 := by
  unfold u1771
  exact div_pos chi1771_pos (by norm_num)

lemma v1771_pos : 0 < v1771 := by
  unfold v1771
  nlinarith [u1771_pos, sq_nonneg u1771]

lemma beta1771_mul_log_two :
    beta1771 * Real.log 2 = 2 + cOff1771 := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  unfold beta1771
  field_simp [hlog]

theorem KM1771_lt_bar : KM1771 < KMbar1771 := by
  let a : ℝ := 2 + cOff1771
  let b : ℝ := (2677 : ℝ) / 1000
  let L : ℝ := Real.log 2
  let F : ℝ := infoFloor1771
  let v : ℝ := v1771
  have hL : 0 < L := by dsimp [L]; exact Real.log_pos one_lt_two
  have hF : 0 < F := by dsimp [F]; exact infoFloor1771_pos
  have hv : 0 < v := by dsimp [v]; exact v1771_pos
  have ha : 0 < a := by
    have h := mul_pos beta1771_pos hL
    dsimp [a, L] at h ⊢
    rw [beta1771_mul_log_two] at h
    exact h
  have hab : a < b := by
    dsimp [a, b]
    linarith [cOff1771_lt]
  have hfloor : v / L ≤ F := by
    dsimp [v, L, F, v1771, u1771]
    exact infoFloor1771_lower
  have hvLF : v ≤ L * F := by
    have h := (div_le_iff₀ hL).1 hfloor
    simpa [mul_comm] using h
  have hden : 0 < L * F := mul_pos hL hF
  calc
    KM1771 = a / (L * F) := by
      dsimp [a, L, F]
      unfold KM1771 beta1771
      field_simp [hL.ne', hF.ne']
    _ ≤ a / v := by
      exact (div_le_div_iff₀ hden hv).2
        (mul_le_mul_of_nonneg_left hvLF ha.le)
    _ < b / v := (div_lt_div_iff_of_pos_right hv).2 hab
    _ = KMbar1771 := by rfl

theorem KS1771_lt_bar : KS1771 < KSbar1771 := by
  let a : ℝ := 2 + cOff1771
  let b : ℝ := (2677 : ℝ) / 1000
  have hab : a < b := by
    dsimp [a, b]
    linarith [cOff1771_lt]
  have hδ : 0 < delta1771 := delta1771_pos
  have hdiv : a / delta1771 < b / delta1771 :=
    (div_lt_div_iff_of_pos_right hδ).2 hab
  calc
    KS1771 = 2 + 2 * (a / delta1771) := by
      dsimp [a]
      unfold KS1771 beta1771
      have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
      field_simp [hlog]
    _ < 2 + 2 * (b / delta1771) := by nlinarith
    _ = KSbar1771 := by
      dsimp [b]
      unfold KSbar1771
      ring

lemma three_KMbar1771_lt_1770 : 3 * KMbar1771 < (1770 : ℝ) := by
  norm_num [KMbar1771, v1771, u1771, chi1771, chi1771Q,
    rho1771Q, eta1771Q]

lemma six_KSbar1771_add_two_lt_1770 :
    6 * KSbar1771 + 2 < (1770 : ℝ) := by
  norm_num [KSbar1771, delta1771, delta1771Q, eta1771Q]

theorem KD1771_lt_1770 : KD1771 < (1770 : ℝ) := by
  have hM : 3 * KM1771 < (1770 : ℝ) :=
    (mul_lt_mul_of_pos_left KM1771_lt_bar (by norm_num)).trans
      three_KMbar1771_lt_1770
  have hS : 6 * KS1771 + 2 < (1770 : ℝ) := by
    nlinarith [KS1771_lt_bar, six_KSbar1771_add_two_lt_1770]
  unfold KD1771
  exact (max_lt_iff).2 ⟨hM, hS⟩

/-- Rounded finite-latent theorem. -/
theorem T_le_1771
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {p : α × β → ℝ} (hp : IsPMF p) :
    T p ≤ (1771 : ℝ) * tau p := by
  have hCdagger : Cdagger1771 < (1771 : ℝ) := by
    unfold Cdagger1771
    linarith [KD1771_lt_1770]
  calc
    T p ≤ Cdagger1771 * tau p := T_le_Cdagger1771 hp
    _ ≤ (1771 : ℝ) * tau p :=
      mul_le_mul_of_nonneg_right (le_of_lt hCdagger)
        (tau_nonneg p)

end stoch_to_det
