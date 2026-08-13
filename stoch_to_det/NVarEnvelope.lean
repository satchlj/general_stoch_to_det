import stoch_to_det.NVar
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Attainment for the n-variable envelope

This file ports the finite-dimensional concave-envelope and attainment layer of
`Envelope.lean` from a product cell space to an arbitrary finite cell space
`Ω`, with payoff `nPhi f g` and score `NLatent.score f g`.
-/

namespace stoch_to_det

open Finset

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
variable {p : Ω → ℝ}
variable {n : ℕ} {κ γ : Fin n → Type}
  [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
  [∀ i, Fintype (γ i)] [∀ i, DecidableEq (γ i)]
variable (f : ∀ i, Ω → κ i) (g : ∀ i, Ω → γ i)

/-- The infimum of the n-variable score over all finite latents. -/
noncomputable def nTau (p : Ω → ℝ) : ℝ :=
  ⨅ V : NLatent p, V.score f g

namespace NLatent

/-- The one-point latent, used to inhabit `NLatent p` when `p` is a PMF. -/
noncomputable def const (hp : IsPMF p) : NLatent p where
  ι := Unit
  fin := inferInstance
  dec := inferInstance
  prior := fun _ => 1
  comp := fun _ => p
  prior_isPMF := by
    constructor
    · intro _
      norm_num
    · simp [mass]
  comp_isPMF := fun _ => hp
  mixture := by simp

end NLatent

/-- The upper concave envelope of `nPhi f g` on the probability simplex,
written as the supremum over all finite mixture representations of `p`. -/
noncomputable def concaveEnvelopeNPhi (p : Ω → ℝ) : ℝ :=
  ⨆ V : NLatent p, ∑ v, V.prior v * nPhi f g (V.comp v)

noncomputable def nContinuousEntropy {δ : Type*} [Fintype δ]
    (m : δ → ℝ) : ℝ :=
  (∑ a, Real.negMulLog (m a)) / Real.log 2

lemma H_eq_nContinuousEntropy {δ : Type*} [Fintype δ]
    {m : δ → ℝ} (hm : IsPMF m) : H m = nContinuousEntropy m := by
  have h := H_eq_negMulLog hm.isFinMeas
  rw [hm.total, Real.log_one, mul_zero, zero_add] at h
  apply (eq_div_iff (Real.log_pos one_lt_two).ne').2
  rw [mul_comm]
  exact h

lemma continuous_nContinuousEntropy {δ : Type*} [Fintype δ] :
    Continuous (nContinuousEntropy : (δ → ℝ) → ℝ) := by
  unfold nContinuousEntropy
  fun_prop

lemma continuous_push_map_n {δ ε : Type*} [Fintype δ] [Fintype ε]
    [DecidableEq ε] (h : δ → ε) :
    Continuous (fun m : δ → ℝ => push h m) := by
  apply continuous_pi
  intro c
  unfold push
  fun_prop

noncomputable def continuousNPhi (q : Ω → ℝ) : ℝ :=
  ((n : ℝ) + 1) * nContinuousEntropy q
    - ∑ i, nContinuousEntropy (push (f i) q)
    - ∑ i, nContinuousEntropy (push (g i) q)

lemma continuous_continuousNPhi :
    Continuous (continuousNPhi f g : (Ω → ℝ) → ℝ) := by
  unfold continuousNPhi
  have hq : Continuous (fun q : Ω → ℝ => nContinuousEntropy q) :=
    continuous_nContinuousEntropy
  have hf : ∀ i : Fin n,
      Continuous (fun q : Ω → ℝ => nContinuousEntropy (push (f i) q)) :=
    fun i => continuous_nContinuousEntropy.comp (continuous_push_map_n (f i))
  have hg : ∀ i : Fin n,
      Continuous (fun q : Ω → ℝ => nContinuousEntropy (push (g i) q)) :=
    fun i => continuous_nContinuousEntropy.comp (continuous_push_map_n (g i))
  fun_prop

lemma nPhi_eq_continuousNPhi {q : Ω → ℝ} (hq : IsPMF q) :
    nPhi f g q = continuousNPhi f g q := by
  unfold nPhi continuousNPhi Hvar
  rw [H_eq_nContinuousEntropy hq]
  simp_rw [H_eq_nContinuousEntropy (isPMF_push hq)]

def nPmfSet : Set (Ω → ℝ) := {q | IsPMF q}

noncomputable def nPhiGraph : Set ((Ω → ℝ) × ℝ) :=
  (fun q => (q, nPhi f g q)) '' nPmfSet

lemma isCompact_nPmfSet : IsCompact (nPmfSet : Set (Ω → ℝ)) := by
  have heq : (nPmfSet : Set (Ω → ℝ)) = stdSimplex ℝ Ω := by
    ext q
    constructor
    · intro hq
      exact ⟨hq.nonneg, by simpa [mass] using hq.total⟩
    · rintro ⟨hq, htotal⟩
      exact ⟨hq, by simpa [mass] using htotal⟩
  rw [heq]
  exact isCompact_stdSimplex ℝ Ω

lemma isCompact_nPhiGraph :
    IsCompact (nPhiGraph f g : Set ((Ω → ℝ) × ℝ)) := by
  let graphMap : (Ω → ℝ) → (Ω → ℝ) × ℝ :=
    fun q => (q, continuousNPhi f g q)
  have hgraphMap : Continuous graphMap :=
    continuous_id.prodMk (continuous_continuousNPhi f g)
  have heq : nPhiGraph f g = graphMap '' nPmfSet := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, by simp [graphMap, nPhi_eq_continuousNPhi f g hq]⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, by simp [graphMap, nPhi_eq_continuousNPhi f g hq]⟩
  rw [heq]
  exact isCompact_nPmfSet.image hgraphMap

/-- The fixed Carathéodory support size used for the graph in
`(Ω → ℝ) × ℝ`. -/
noncomputable def nEnvelopeSize : ℕ :=
  Module.finrank ℝ ((Ω → ℝ) × ℝ) + 1

lemma nEnvelopeSize_eq_card_add_two :
    nEnvelopeSize (Ω := Ω) = Fintype.card Ω + 2 := by
  simp [nEnvelopeSize]

private noncomputable def nEnvelopeBarycenter
    (a : (Fin (nEnvelopeSize (Ω := Ω)) → ℝ) ×
      (Fin (nEnvelopeSize (Ω := Ω)) → (Ω → ℝ) × ℝ)) :
    (Ω → ℝ) × ℝ :=
  ∑ i, a.1 i • a.2 i

private noncomputable def nEnvelopeParams :
    Set ((Fin (nEnvelopeSize (Ω := Ω)) → ℝ) ×
      (Fin (nEnvelopeSize (Ω := Ω)) → (Ω → ℝ) × ℝ)) :=
  stdSimplex ℝ (Fin (nEnvelopeSize (Ω := Ω))) ×ˢ
    Set.pi (Set.univ : Set (Fin (nEnvelopeSize (Ω := Ω))))
      (fun _ => nPhiGraph f g)

private lemma continuous_nEnvelopeBarycenter :
    Continuous (nEnvelopeBarycenter (Ω := Ω)) := by
  unfold nEnvelopeBarycenter
  fun_prop

private lemma isCompact_nEnvelopeParams :
    IsCompact (nEnvelopeParams f g) := by
  unfold nEnvelopeParams
  apply IsCompact.prod (isCompact_stdSimplex ℝ _)
  exact isCompact_univ_pi fun _ => isCompact_nPhiGraph f g

private lemma isCompact_nEnvelopeBarycenter_image :
    IsCompact (nEnvelopeBarycenter (Ω := Ω) '' nEnvelopeParams f g) :=
  (isCompact_nEnvelopeParams f g).image continuous_nEnvelopeBarycenter

private lemma nEnvelopeBarycenter_image_subset_convexHull :
    nEnvelopeBarycenter (Ω := Ω) '' nEnvelopeParams f g ⊆
      convexHull ℝ (nPhiGraph f g : Set ((Ω → ℝ) × ℝ)) := by
  rintro x ⟨a, ha, rfl⟩
  rcases ha with ⟨hw, hq⟩
  apply mem_convexHull_of_exists_fintype a.1 a.2
  · exact hw.1
  · exact hw.2
  · intro i
    exact hq i (Set.mem_univ i)
  · rfl

private lemma convexHull_subset_nEnvelopeBarycenter_image (hp : IsPMF p) :
    convexHull ℝ (nPhiGraph f g : Set ((Ω → ℝ) × ℝ)) ⊆
      nEnvelopeBarycenter (Ω := Ω) '' nEnvelopeParams f g := by
  intro x hx
  rw [convexHull_eq_union] at hx
  simp only [Set.mem_iUnion, exists_prop] at hx
  rcases hx with ⟨t, htGraph, htIndependent, hxt⟩
  have htcard : Fintype.card t ≤ nEnvelopeSize (Ω := Ω) := by
    calc
      Fintype.card t ≤
          Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → (Ω → ℝ) × ℝ))) + 1 :=
        htIndependent.card_le_finrank_succ
      _ ≤ Module.finrank ℝ ((Ω → ℝ) × ℝ) + 1 :=
        Nat.add_le_add_right (Submodule.finrank_le _) 1
      _ = nEnvelopeSize (Ω := Ω) := rfl
  let e : t ↪ Fin (nEnvelopeSize (Ω := Ω)) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using htcard))
  rcases (Finset.mem_convexHull'.mp hxt) with ⟨w, hw_nonneg, hw_sum, hw_center⟩
  let weights : Fin (nEnvelopeSize (Ω := Ω)) → ℝ :=
    fun j => ∑ i : t, if e i = j then w i.1 else 0
  let points : Fin (nEnvelopeSize (Ω := Ω)) → (Ω → ℝ) × ℝ :=
    fun j => if h : ∃ i : t, e i = j then (Classical.choose h).1 else (p, nPhi f g p)
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
  have hpoints (j : Fin (nEnvelopeSize (Ω := Ω))) : points j ∈ nPhiGraph f g := by
    by_cases hj : ∃ i : t, e i = j
    · rw [show points j = (Classical.choose hj).1 by simp [points, hj]]
      exact htGraph (Classical.choose hj).2
    · rw [show points j = (p, nPhi f g p) by simp [points, hj]]
      exact ⟨p, hp, rfl⟩
  have hterm (j : Fin (nEnvelopeSize (Ω := Ω))) :
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
  have hbary : nEnvelopeBarycenter (weights, points) = x := by
    calc
      nEnvelopeBarycenter (weights, points) = ∑ j, weights j • points j := rfl
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

private lemma convexHull_nPhiGraph_eq_barycenter_image (hp : IsPMF p) :
    convexHull ℝ (nPhiGraph f g : Set ((Ω → ℝ) × ℝ)) =
      nEnvelopeBarycenter (Ω := Ω) '' nEnvelopeParams f g :=
  Set.Subset.antisymm (convexHull_subset_nEnvelopeBarycenter_image f g hp)
    (nEnvelopeBarycenter_image_subset_convexHull f g)

lemma isCompact_convexHull_nPhiGraph (hp : IsPMF p) :
    IsCompact (convexHull ℝ (nPhiGraph f g : Set ((Ω → ℝ) × ℝ))) := by
  rw [convexHull_nPhiGraph_eq_barycenter_image f g hp]
  exact isCompact_nEnvelopeBarycenter_image f g

private lemma NLatent.graphMixture_mem_convexHull (V : NLatent p) :
    (p, ∑ v, V.prior v * nPhi f g (V.comp v)) ∈
      convexHull ℝ (nPhiGraph f g : Set ((Ω → ℝ) × ℝ)) := by
  apply mem_convexHull_of_exists_fintype V.prior
    (fun v => (V.comp v, nPhi f g (V.comp v)))
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

/-- Every point of the graph convex hull has a representing latent whose
alphabet is the fixed Carathéodory alphabet. -/
lemma exists_bounded_latent_of_mem_convexHull_nPhiGraph (hp : IsPMF p) {r : ℝ}
    (h : (p, r) ∈ convexHull ℝ (nPhiGraph f g : Set ((Ω → ℝ) × ℝ))) :
    ∃ V : NLatent p,
      Fintype.card V.ι ≤ nEnvelopeSize (Ω := Ω) ∧
      (∑ v, V.prior v * nPhi f g (V.comp v)) = r := by
  rw [convexHull_nPhiGraph_eq_barycenter_image f g hp] at h
  rcases h with ⟨a, ha, hcenter⟩
  rcases ha with ⟨hw, hz⟩
  have hz' : ∀ i, ∃ q : Ω → ℝ, IsPMF q ∧ (q, nPhi f g q) = a.2 i := by
    intro i
    rcases hz i (Set.mem_univ i) with ⟨q, hq, hqz⟩
    exact ⟨q, hq, hqz⟩
  choose q hq hqz using hz'
  have hcenter' : ∑ i, a.1 i • (q i, nPhi f g (q i)) = (p, r) := by
    calc
      _ = ∑ i, a.1 i • a.2 i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hqz i]
      _ = (p, r) := hcenter
  have hfirst : ∑ i, a.1 i • q i = p := by
    have hfst := congrArg Prod.fst hcenter'
    simpa only [Prod.fst_sum, Prod.smul_fst] using hfst
  have hmixture : ∀ z, ∑ i, a.1 i * q i z = p z := by
    intro z
    have ha := congrFun hfirst z
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using ha
  have hpayoff : ∑ i, a.1 i * nPhi f g (q i) = r := by
    have hr := congrArg Prod.snd hcenter'
    simpa only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul] using hr
  let V : NLatent p :=
    { ι := Fin (nEnvelopeSize (Ω := Ω))
      fin := inferInstance
      dec := inferInstance
      prior := a.1
      comp := q
      prior_isPMF := ⟨hw.1, by simpa [mass] using hw.2⟩
      comp_isPMF := hq
      mixture := hmixture }
  refine ⟨V, ?_, ?_⟩
  · simp [V]
  · exact hpayoff

/-- The infimum defining `nTau` is attained by a finite latent, with the
Carathéodory support bound inherited from the ambient graph space. -/
theorem exists_nTau_optimal_latent [Nonempty Ω] (hp : IsPMF p)
    (hinj : ∀ i, Function.Injective (fun z => (f i z, g i z))) :
    ∃ V : NLatent p,
      Fintype.card V.ι ≤ Fintype.card Ω + 2 ∧
      V.score f g = nTau f g p := by
  let slice : Set ((Ω → ℝ) × ℝ) :=
    convexHull ℝ (nPhiGraph f g : Set ((Ω → ℝ) × ℝ)) ∩ {x | x.1 = p}
  have hslice_compact : IsCompact slice := by
    apply (isCompact_convexHull_nPhiGraph f g hp).inter_right
    exact isClosed_eq continuous_fst continuous_const
  have hbase_graph : (p, nPhi f g p) ∈ (nPhiGraph f g : Set ((Ω → ℝ) × ℝ)) :=
    ⟨p, hp, rfl⟩
  have hslice_nonempty : slice.Nonempty := by
    refine ⟨(p, nPhi f g p), ?_, rfl⟩
    exact subset_convexHull ℝ _ hbase_graph
  obtain ⟨x, hx_slice, hx_max⟩ :=
    hslice_compact.exists_isMaxOn hslice_nonempty continuous_snd.continuousOn
  have hx_eq : (p, x.2) = x := by
    apply Prod.ext
    · exact hx_slice.2.symm
    · rfl
  have hx_hull : (p, x.2) ∈
      convexHull ℝ (nPhiGraph f g : Set ((Ω → ℝ) × ℝ)) := by
    rw [hx_eq]
    exact hx_slice.1
  obtain ⟨V, hVcard, hVpayoff⟩ :=
    exists_bounded_latent_of_mem_convexHull_nPhiGraph f g hp hx_hull
  have hVmin : ∀ W : NLatent p, V.score f g ≤ W.score f g := by
    intro W
    have hW_slice :
        (p, ∑ v, W.prior v * nPhi f g (W.comp v)) ∈ slice :=
      ⟨NLatent.graphMixture_mem_convexHull f g W, rfl⟩
    have hpayoff_le :
        (∑ v, W.prior v * nPhi f g (W.comp v)) ≤ x.2 := hx_max hW_slice
    rw [NLatent.score_eq hp V hinj, NLatent.score_eq hp W hinj, hVpayoff]
    linarith
  have hVcard' : Fintype.card V.ι ≤ Fintype.card Ω + 2 := by
    simpa [nEnvelopeSize_eq_card_add_two (Ω := Ω)] using hVcard
  refine ⟨V, hVcard', ?_⟩
  letI : Nonempty (NLatent p) := ⟨NLatent.const hp⟩
  have hscore_bdd : BddBelow (Set.range fun W : NLatent p => W.score f g) :=
    ⟨V.score f g, by
      rintro _ ⟨W, rfl⟩
      exact hVmin W⟩
  apply le_antisymm
  · unfold nTau
    exact le_ciInf hVmin
  · unfold nTau
    exact ciInf_le hscore_bdd V

/-- `nTau = nPsi -` the upper concave envelope of `nPhi`. -/
theorem nTau_eq [Nonempty Ω] (hp : IsPMF p)
    (hinj : ∀ i, Function.Injective (fun z => (f i z, g i z))) :
    nTau f g p = nPsi f g p - concaveEnvelopeNPhi f g p := by
  let payoff : NLatent p → ℝ :=
    fun V => ∑ v, V.prior v * nPhi f g (V.comp v)
  let C : ℝ := ((n : ℝ) + 1) * lg (Fintype.card Ω)
  letI : Nonempty (NLatent p) := ⟨NLatent.const hp⟩
  have hscore (V : NLatent p) : V.score f g = nPsi f g p - payoff V := by
    simpa [payoff] using NLatent.score_eq hp V hinj
  have hnPhi_le (q : Ω → ℝ) (hq : IsPMF q) : nPhi f g q ≤ C := by
    have hf_nonneg : 0 ≤ ∑ i, Hvar (f i) q := by
      apply Finset.sum_nonneg
      intro i _
      unfold Hvar
      exact H_nonneg_of_isPMF (isPMF_push hq)
    have hg_nonneg : 0 ≤ ∑ i, Hvar (g i) q := by
      apply Finset.sum_nonneg
      intro i _
      unfold Hvar
      exact H_nonneg_of_isPMF (isPMF_push hq)
    calc
      nPhi f g q ≤ ((n : ℝ) + 1) * H q := by
        unfold nPhi
        linarith
      _ ≤ C := by
        dsimp [C]
        exact mul_le_mul_of_nonneg_left (H_le_card hq) (by positivity)
  have hpayoff_upper (V : NLatent p) : payoff V ≤ C := by
    calc
      payoff V ≤ ∑ v, V.prior v * C := by
        dsimp [payoff]
        apply Finset.sum_le_sum
        intro v _
        exact mul_le_mul_of_nonneg_left (hnPhi_le (V.comp v) (V.comp_isPMF v))
          (V.prior_isPMF.nonneg v)
      _ = C := by
        rw [← Finset.sum_mul]
        have htotal : ∑ v, V.prior v = 1 := by
          simpa [mass] using V.prior_isPMF.total
        rw [htotal, one_mul]
  have hscore_bdd : BddBelow (Set.range fun V : NLatent p => V.score f g) :=
    ⟨nPsi f g p - C, by
      rintro _ ⟨V, rfl⟩
      change nPsi f g p - C ≤ V.score f g
      rw [hscore V]
      linarith [hpayoff_upper V]⟩
  have hpayoff_bdd : BddAbove (Set.range payoff) :=
    ⟨C, by
      rintro _ ⟨V, rfl⟩
      exact hpayoff_upper V⟩
  unfold nTau concaveEnvelopeNPhi
  change (⨅ V : NLatent p, V.score f g) =
    nPsi f g p - ⨆ V : NLatent p, payoff V
  apply le_antisymm
  · have hsup :
        (⨆ V : NLatent p, payoff V) ≤
          nPsi f g p - ⨅ V : NLatent p, V.score f g := by
      refine ciSup_le fun V => ?_
      have hinf : (⨅ W : NLatent p, W.score f g) ≤ V.score f g :=
        ciInf_le hscore_bdd V
      rw [hscore V] at hinf
      linarith
    linarith
  · refine le_ciInf fun V => ?_
    have hle : payoff V ≤ ⨆ W : NLatent p, payoff W := le_ciSup hpayoff_bdd V
    rw [hscore V]
    linarith

/-! ## Hard-code attainment -/

private noncomputable def nConditionedComp {δ : Type} [Fintype δ] [DecidableEq δ]
    (Γ : Ω → δ) (c : δ) : Ω → ℝ :=
  fun z =>
    if push Γ p c = 0 then p z
    else if Γ z = c then (push Γ p c)⁻¹ * p z else 0

private lemma nConditionedComp_isPMF {δ : Type} [Fintype δ] [DecidableEq δ]
    (hp : IsPMF p) (Γ : Ω → δ) (c : δ) :
    IsPMF (nConditionedComp (p := p) Γ c) := by
  classical
  by_cases hc : push Γ p c = 0
  · have hcomp : nConditionedComp (p := p) Γ c = p := by
      funext z
      simp [nConditionedComp, hc]
    rw [hcomp]
    exact hp
  · have hprior_nonneg : 0 ≤ push Γ p c := (isPMF_push hp).nonneg c
    constructor
    · intro z
      simp only [nConditionedComp, hc, if_false]
      split
      · exact mul_nonneg (inv_nonneg.mpr hprior_nonneg) (hp.nonneg z)
      · exact le_rfl
    · unfold mass nConditionedComp
      simp only [hc, if_false]
      calc
        (∑ z, if Γ z = c then (push Γ p c)⁻¹ * p z else 0) =
            (push Γ p c)⁻¹ * ∑ z ∈ univ.filter (fun z => Γ z = c), p z := by
              rw [Finset.mul_sum, Finset.sum_filter]
        _ = (push Γ p c)⁻¹ * push Γ p c := by rfl
        _ = 1 := inv_mul_cancel₀ hc

private lemma push_mul_nConditionedComp {δ : Type} [Fintype δ] [DecidableEq δ]
    (hp : IsPMF p) (Γ : Ω → δ) (c : δ) (z : Ω) :
    push Γ p c * nConditionedComp (p := p) Γ c z =
      if Γ z = c then p z else 0 := by
  classical
  by_cases hΓc : Γ z = c
  · subst c
    have hz_le : p z ≤ push Γ p (Γ z) := by
      unfold push
      exact Finset.single_le_sum (fun w _ => hp.nonneg w) (by simp)
    by_cases hc : push Γ p (Γ z) = 0
    · have hz : p z = 0 := le_antisymm (by simpa [hc] using hz_le) (hp.nonneg z)
      simp [nConditionedComp, hc, hz]
    · rw [show nConditionedComp (p := p) Γ (Γ z) z =
          (push Γ p (Γ z))⁻¹ * p z by simp [nConditionedComp, hc]]
      rw [if_pos rfl]
      field_simp [hc]
  · by_cases hc : push Γ p c = 0
    · simp [nConditionedComp, hΓc, hc]
    · simp [nConditionedComp, hΓc, hc]

/-- The `NLatent` induced by a deterministic hard code. -/
noncomputable def NLatent.ofFunction {δ : Type} [Fintype δ] [DecidableEq δ]
    (hp : IsPMF p) (Γ : Ω → δ) : NLatent p where
  ι := δ
  fin := inferInstance
  dec := inferInstance
  prior := push Γ p
  comp := nConditionedComp (p := p) Γ
  prior_isPMF := isPMF_push hp
  comp_isPMF := nConditionedComp_isPMF hp Γ
  mixture := by
    intro z
    calc
      (∑ c, push Γ p c * nConditionedComp (p := p) Γ c z) =
          ∑ c, if Γ z = c then p z else 0 := by
            apply Finset.sum_congr rfl
            intro c _
            exact push_mul_nConditionedComp hp Γ c z
      _ = p z := by
        have hsingle :
            (∑ c, if Γ z = c then p z else 0) =
              (if Γ z = Γ z then p z else 0) := by
          apply Finset.sum_eq_single (Γ z)
          · intro c _ hne
            simp [hne, Ne.symm hne]
          · simp
        simpa using hsingle

/-- The joint law of a deterministic `NLatent` is the pushforward along the
graph of its code. -/
theorem NLatent.ofFunction_joint_eq_push
    {δ : Type} [Fintype δ] [DecidableEq δ]
    (hp : IsPMF p) (Γ : Ω -> δ) :
    (NLatent.ofFunction hp Γ).joint =
      push (fun z : Ω => (Γ z, z)) p := by
  classical
  change (fun w : δ × Ω =>
      push Γ p w.1 * nConditionedComp (p := p) Γ w.1 w.2) = _
  funext w
  rcases w with ⟨c, z⟩
  change push Γ p c * nConditionedComp (p := p) Γ c z =
    push (fun x : Ω => (Γ x, x)) p (c, z)
  rw [push_mul_nConditionedComp hp Γ c z]
  unfold push
  rw [Finset.sum_filter]
  have hsum :
      (∑ x, if (Γ x, x) = (c, z) then p x else 0) =
        (if (Γ z, z) = (c, z) then p z else 0) := by
    apply Finset.sum_eq_single z
    · intro x _ hx
      by_cases hpair : (Γ x, x) = (c, z)
      · exact (hx (congrArg Prod.snd hpair)).elim
      · simp [hpair]
    · simp
  calc
    (if Γ z = c then p z else 0) =
        (if (Γ z, z) = (c, z) then p z else 0) := by simp
    _ = ∑ x, if (Γ x, x) = (c, z) then p x else 0 := hsum.symm
    _ = ∑ x, if (fun a => (Γ a, a)) x = (c, z) then p x else 0 := rfl

/-- A conditioned component of a deterministic code vanishes away from its
code fiber. -/
@[simp] lemma NLatent.ofFunction_comp_eq_zero_of_ne
    {δ : Type} [Fintype δ] [DecidableEq δ]
    (hp : IsPMF p) (Γ : Ω → δ) {c : δ} {z : Ω}
    (hc : push Γ p c ≠ 0) (hz : Γ z ≠ c) :
    (NLatent.ofFunction hp Γ).comp c z = 0 := by
  simp [NLatent.ofFunction, nConditionedComp, hc, hz]

/-- The hard-code functional. For non-PMF inputs it is set to zero; all
substantive statements carry `IsPMF p`. -/
noncomputable def nT (p : Ω → ℝ) : ℝ := by
  classical
  exact if hp : IsPMF p then
    ⨅ Γ : Ω → Fin (Fintype.card Ω), (NLatent.ofFunction hp Γ).score f g
  else 0

/-- The infimum over hard codes is attained, since the fixed code space is
finite. -/
theorem exists_nT_optimal_code [Nonempty Ω] (hp : IsPMF p) :
    ∃ Γ : Ω → Fin (Fintype.card Ω),
      (NLatent.ofFunction hp Γ).score f g = nT (f := f) (g := g) p := by
  let Code := Ω → Fin (Fintype.card Ω)
  let scoreOf : Code → ℝ := fun Γ => (NLatent.ofFunction hp Γ).score f g
  have hcodes : (univ : Finset Code).Nonempty := by
    let Γ₀ : Code := fun z => Fintype.equivFin Ω z
    exact ⟨Γ₀, Finset.mem_univ _⟩
  obtain ⟨Γ₀, _hΓ₀, hΓ₀min⟩ :=
    Finset.exists_min_image (univ : Finset Code) scoreOf hcodes
  refine ⟨Γ₀, ?_⟩
  rw [nT, dif_pos hp]
  apply le_antisymm
  · refine le_ciInf fun Γ => ?_
    exact hΓ₀min Γ (Finset.mem_univ _)
  · have hb : BddBelow (Set.range scoreOf) := by
      refine ⟨scoreOf Γ₀, ?_⟩
      rintro _ ⟨Γ, rfl⟩
      exact hΓ₀min Γ (Finset.mem_univ _)
    exact ciInf_le hb Γ₀

end stoch_to_det
