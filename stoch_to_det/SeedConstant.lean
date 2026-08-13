import stoch_to_det.Cone

/-!
# §11. The seed-two-replica constant


`H(A ∣ ε, L₀) ≤ C₀ [M + I(L₁,L₂; Z ∣ L₀)]`, with `C₀ = K_sc + K_orth + 1`.

## Proof structure

Given §§8-10 there is no new mathematics here — the argument is four lines of
inequality chaining:

```
D = scalar + cone                       (Lemma 7.5, chain_split)
  ≤ (K_sc + K_orth)(M + S)              (Thm 8.1, Thm 10.1)
H(A ∣ ε,L₀) = S + D                     (Lemma 7.3, winner_entropy_identity)
  ≤ (K_sc + K_orth + 1)(M + S)
  ≤ C₀ [M + I(L₁,L₂;Z ∣ L₀)]            (S ≤ I(L₁,L₂;Z ∣ L₀), monotonicity)
```

Everything it needs from §§8 and 10 arrives through the `RaceQuantities`
interface of `stoch_to_det.Quotient`.

The same argument also gives the sharper
single-replica form `H(A ∣ ε,L₀) ≤ C₀[M + b_Z]`, recorded below as
`seed_constant_single`; the pair form follows because
`I(L₁;Z ∣ L₀) ≤ I(L₁,L₂;Z ∣ L₀)`. The single form yields the final constant
`6C₀+3` rather than `108C₀+3`; see `stoch_to_det.Main.T_le_Cstar_sharpest`.
-/

namespace stoch_to_det

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable {p : α × β → ℝ} {D : SeedSetup p} {K : Clustering D}

private theorem seed_M_nonneg (D : SeedSetup p) : 0 ≤ D.M := by
  exact condMI_nonneg D.L.joint_isPMF
    (fun q => q.2.1) (fun q => q.2.2) (fun q => q.1)

private theorem push_comp_equiv_eq {Ω γ : Type*} [Fintype Ω] [Fintype γ]
    [DecidableEq γ] (m : Ω → ℝ) (e : Ω ≃ Ω) (hm : ∀ x, m (e x) = m x)
    (f : Ω → γ) : push (f ∘ e) m = push f m := by
  funext y
  unfold push
  simp only [Finset.sum_filter, Function.comp_apply]
  calc
    (∑ x, if f (e x) = y then m x else 0) =
        (∑ x, if f (e x) = y then m (e x) else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hm x]
    _ = (∑ x, if f x = y then m x else 0) := by
      simpa using e.sum_comp (fun x => if f x = y then m x else 0)

private theorem Hvar_comp_equiv_eq {Ω γ : Type*} [Fintype Ω] [Fintype γ]
    [DecidableEq γ] (m : Ω → ℝ) (e : Ω ≃ Ω) (hm : ∀ x, m (e x) = m x)
    (f : Ω → γ) : Hvar (f ∘ e) m = Hvar f m := by
  unfold Hvar
  rw [push_comp_equiv_eq m e hm f]

private theorem condMI_comp_equiv_eq {Ω γ δ ε : Type*} [Fintype Ω]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    [Fintype ε] [DecidableEq ε] (m : Ω → ℝ) (e : Ω ≃ Ω)
    (hm : ∀ x, m (e x) = m x) (f : Ω → γ) (g : Ω → δ) (h : Ω → ε) :
    condMI (f ∘ e) (g ∘ e) (h ∘ e) m = condMI f g h m := by
  have hfh := Hvar_comp_equiv_eq m e hm (fun x => (f x, h x))
  have hgh := Hvar_comp_equiv_eq m e hm (fun x => (g x, h x))
  have hfgh := Hvar_comp_equiv_eq m e hm (fun x => (f x, g x, h x))
  have hh := Hvar_comp_equiv_eq m e hm h
  unfold condMI
  change Hvar ((fun x => (f x, h x)) ∘ e) m +
      Hvar ((fun x => (g x, h x)) ∘ e) m -
      Hvar ((fun x => (f x, g x, h x)) ∘ e) m - Hvar (h ∘ e) m = _
  rw [hfh, hgh, hfgh, hh]

private theorem condMI_pair_left_eq {Ω γ κ δ ε : Type*} [Fintype Ω]
    [Fintype γ] [DecidableEq γ] [Fintype κ] [DecidableEq κ]
    [Fintype δ] [DecidableEq δ] [Fintype ε] [DecidableEq ε]
    {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → γ) (k : Ω → κ)
    (g : Ω → δ) (h : Ω → ε) :
    condMI (fun x => (f x, k x)) g h m =
      condMI f g h m + condMI k g (fun x => (f x, h x)) m := by
  let e₁ : κ × (γ × ε) ≃ (γ × κ) × ε :=
    { toFun := fun x => ((x.2.1, x.1), x.2.2)
      invFun := fun x => (x.1.2, (x.1.1, x.2))
      left_inv := by rintro ⟨k, f, h⟩; rfl
      right_inv := by rintro ⟨⟨f, k⟩, h⟩; rfl }
  let e₂ : δ × (γ × ε) ≃ γ × (δ × ε) :=
    { toFun := fun x => (x.2.1, (x.1, x.2.2))
      invFun := fun x => (x.2.1, (x.1, x.2.2))
      left_inv := by rintro ⟨g, f, h⟩; rfl
      right_inv := by rintro ⟨f, g, h⟩; rfl }
  let e₃ : κ × (δ × (γ × ε)) ≃ (γ × κ) × (δ × ε) :=
    { toFun := fun x => ((x.2.2.1, x.1), (x.2.1, x.2.2.2))
      invFun := fun x => (x.1.2, (x.2.1, (x.1.1, x.2.2)))
      left_inv := by rintro ⟨k, g, f, h⟩; rfl
      right_inv := by rintro ⟨⟨f, k⟩, g, h⟩; rfl }
  have h₁ : Hvar (fun x => ((f x, k x), h x)) m =
      Hvar (fun x => (k x, f x, h x)) m := by
    simpa [e₁, Function.comp_def] using
      Hvar_equiv hm (fun x => (k x, f x, h x)) e₁
  have h₂ : Hvar (fun x => (f x, g x, h x)) m =
      Hvar (fun x => (g x, f x, h x)) m := by
    simpa [e₂, Function.comp_def] using
      Hvar_equiv hm (fun x => (g x, f x, h x)) e₂
  have h₃ : Hvar (fun x => ((f x, k x), g x, h x)) m =
      Hvar (fun x => (k x, g x, (f x, h x))) m := by
    simpa [e₃, Function.comp_def] using
      Hvar_equiv hm (fun x => (k x, g x, (f x, h x))) e₃
  unfold condMI
  rw [← h₁, ← h₂, ← h₃]
  ring

private def replicaSwap (D : SeedSetup p) :
    D.L.ι × D.L.ι × D.L.ι × (α × β) ≃ D.L.ι × D.L.ι × D.L.ι × (α × β) where
  toFun u := (u.2.1, u.1, u.2.2.1, u.2.2.2)
  invFun u := (u.2.1, u.1, u.2.2.1, u.2.2.2)
  left_inv := by rintro ⟨l₀, l₁, l₂, z⟩; rfl
  right_inv := by rintro ⟨l₀, l₁, l₂, z⟩; rfl

private theorem replicaLaw_swap (D : SeedSetup p)
    (u : D.L.ι × D.L.ι × D.L.ι × (α × β)) :
    replicaLaw D (replicaSwap D u) = replicaLaw D u := by
  rcases u with ⟨l₀, l₁, l₂, z⟩
  change replicaLaw D (l₁, l₀, l₂, z) = replicaLaw D (l₀, l₁, l₂, z)
  simp only [replicaLaw]
  ring

private theorem bZ_le_pair (D : SeedSetup p) :
    bZ D ≤ condMI (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2)
      (fun u => u.1) (replicaLaw D) := by
  have hswap := condMI_comp_equiv_eq (replicaLaw D) (replicaSwap D)
    (replicaLaw_swap D) (fun u => u.1) (fun u => u.2.2.2) (fun u => u.2.1)
  have heq : condMI (fun u => u.2.1) (fun u => u.2.2.2) (fun u => u.1)
      (replicaLaw D) = bZ D := by
    simpa [replicaSwap, Function.comp_def, bZ] using hswap
  have hchain := condMI_pair_left_eq (replicaLaw_isPMF D)
    (fun u => u.2.1) (fun u => u.2.2.1) (fun u => u.2.2.2) (fun u => u.1)
  have hnonneg := condMI_nonneg (replicaLaw_isPMF D)
    (fun u => u.2.2.1) (fun u => u.2.2.2) (fun u => (u.2.1, u.1))
  rw [heq] at hchain
  linarith

/-- The seed leak is bounded by `(K_sc + K_orth)(M + S)`,
from `chain_split`, `scalar_bound_Ksc` and `cone_bound_Korth`. -/
theorem seedLeak_bound (R : RaceQuantities D K) :
    R.seedLeak ≤ (Ksc + Korth) * (D.M + K.Sinfo) := by
  calc
    R.seedLeak = R.scalar + R.cone := R.chain_split
    _ ≤ Ksc * (D.M + K.Sinfo) + Korth * (D.M + K.Sinfo) :=
      add_le_add (scalar_bound_Ksc R) (cone_bound_Korth R)
    _ = (Ksc + Korth) * (D.M + K.Sinfo) := by ring

/-- **Theorem 11.1**, single-replica form (Remark 12.3(b)):
`H(A ∣ ε, L₀) ≤ C₀ [M + b_Z]`. -/
theorem seed_constant_single (R : RaceQuantities D K) :
    R.winnerEntropy ≤ C0 * (D.M + bZ D) := by
  have hle := seedLeak_bound R
  rw [K.Sinfo_eq_bZ] at hle
  rw [R.winner_entropy_identity, K.Sinfo_eq_bZ]
  calc
    bZ D + R.seedLeak ≤ bZ D + (Ksc + Korth) * (D.M + bZ D) :=
      by simpa [add_comm] using add_le_add_left hle (bZ D)
    _ ≤ C0 * (D.M + bZ D) := by
      rw [C0]
      nlinarith [seed_M_nonneg D]

/-- **Theorem 11.1** (*seed-two-replica-constant-bound*):
`H(A ∣ ε, L₀) ≤ C₀ [M + I(L₁,L₂; Z ∣ L₀)]`. -/
theorem seed_constant (R : RaceQuantities D K) :
    R.winnerEntropy
      ≤ C0 * (D.M + condMI (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2)
                      (fun u => u.1) (replicaLaw D)) := by
  apply (seed_constant_single R).trans
  apply mul_le_mul_of_nonneg_left _ C0_pos.le
  simpa [add_comm] using add_le_add_left (bZ_le_pair D) D.M

end stoch_to_det
