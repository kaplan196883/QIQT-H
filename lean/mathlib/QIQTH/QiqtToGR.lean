import QIQTH.ClausiusToPernull
import QIQTH.DifferentialAreaLaw
import QIQTH.Raychaudhuri

/-!
# Assembling QIQT-H + Bekenstein ⇒ GR: the per-null tensor premise from the DERIVED modular relation

`DifferentialAreaLaw.differential_area_law` DERIVES the modular first-law relation `δ⟨K⟩ = η δA`
(`k' = η·a'`) from QIQT-H's own capacity bound + saturation + Klein positivity.  This file turns that
relation, per null direction `v`, into Jacobson's **pointwise** per-null premise
`BL(a·T − Ric) v = 0` — the exact hypothesis `pernull` that `jacobson_einstein_equation_of_state`
consumes — using only two clearly-labelled CITED inputs (Mathlib has no AQFT/Lorentzian-GR):

* `hFlux`  — Bisognano–Wichmann + boost heat flux: `δ⟨K⟩ = (2π/ℏ)·BL(T) v`  (the modular energy is the
  boost-energy flux `T_kk`);
* `hFocus` — Raychaudhuri (leading order): the area first-variation rate `a' = BL(Ric) v` (the focusing
  scalar `R_kk`).

The modular relation `hModular` is DERIVED from QIQT-H; only `hFlux`/`hFocus` are cited, and they are kept
SEPARATE from each other and from the area law — neither presupposes Einstein.  This isolates the *exact*
physics surface (the Type III₁ wedge-modular identification + Raychaudhuri focusing) that cannot be
Lean-proved, while everything QIQT-H supplies is derived.
-/

namespace QIQTH.QiqtToGR

open QIQTH.EinsteinEOS QIQTH.Curvature QIQTH.DifferentialAreaLaw
open Filter Topology

/-- **★ The `hFocus` input DERIVED from the machine-checked Raychaudhuri equation — only the area↔θ
    modelling identification remains.**  `hFocus` (input #3 of `qiqt_gr_from_wedge_kms`) demands that the area
    first-variation rate `ad` equals the contracted Ricci `R_kk = BL(Ric) v`.  Given the equilibrium condition
    `hequil` (the shear–expansion quadratic vanishes — a stationary/bifurcation horizon, Jacobson's setup) and
    the single **modelling identification** `harea` (the abstract area rate is minus the congruence expansion
    rate `−V^ν∂_νθ`), `raychaudhuri_focusing_at_equilibrium` *derives* `ad = R_kk`.  So the geometric content of
    `hFocus` is machine-checked (the kinematics of null congruences, no Einstein presupposed); the only
    remaining labelled step is the area-vs-`θ` identification `harea`.  Mirrors `wedge_hBoostCharge_of_smooth`
    for input #1.  Axiom-free. -/
theorem hFocus_of_raychaudhuri
    (g gi : Point 4 → Fin 4 → Fin 4 → ℝ) (hsymm : ∀ y a b, g y a b = g y b a)
    (V : Point 4 → Fin 4 → ℝ)
    (hVC : ∀ μ, ContDiff ℝ ⊤ (fun y => V y μ))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (hgeo : ∀ y μ, ∑ ν, V y ν * covDerivVec g gi V ν μ y = 0)
    (x : Point 4)
    (hequil : (∑ μ, ∑ ν, covDerivVec g gi V μ ν x * covDerivVec g gi V ν μ x) = 0)
    (ad : ℝ)
    (harea : ad = - ∑ ν, V x ν * pd (fun y => expansion g gi V y) ν x) :
    ad = BL (fun i j => ricci g gi i j x) (V x) := by
  rw [harea, raychaudhuri_focusing_at_equilibrium g gi hsymm V hVC hC hgeo x hequil, neg_neg, BL,
    Finset.sum_comm]

/-- **The pointwise per-null premise from the derived modular relation + cited AQFT/geometry.**
    From `δ⟨K⟩ = η δA` (`hModular`, DERIVED) together with the cited boost-flux (`hFlux`,
    Bisognano–Wichmann) and Raychaudhuri focusing (`hFocus`), with `a = 2π/(ℏη)`, the heat tensor
    `a·T − Ric` vanishes on the null vector `v`: `BL(a·T − Ric) v = 0`.  This is exactly Jacobson's
    `pernull` premise for the direction `v`. -/
theorem bl_pernull_of_modular (T Ric : Fin 4 → Fin 4 → ℝ) (v : Fin 4 → ℝ)
    {k' a' η hbar a : ℝ}
    (hbar0 : hbar ≠ 0) (heta : η ≠ 0) (ha : a = 2 * Real.pi / (hbar * η))
    (hModular : k' = η * a')
    (hFlux : k' = 2 * Real.pi / hbar * BL T v)
    (hFocus : a' = BL Ric v) :
    BL (fun i j => a * T i j - Ric i j) v = 0 := by
  have h1 : η * a' = 2 * Real.pi / hbar * BL T v := hModular.symm.trans hFlux
  have hkey : a * BL T v = BL Ric v := by
    rw [ha, ← hFocus]
    have key : 2 * Real.pi / (hbar * η) * BL T v = η⁻¹ * (2 * Real.pi / hbar * BL T v) := by
      field_simp
    rw [key, ← h1, ← mul_assoc, inv_mul_cancel₀ heta, one_mul]
  rw [BL_smul_sub a T Ric v, hkey, sub_self]

/-- **The per-null premise DERIVED from QIQT-H content + the two cited inputs.**  Composes
    `differential_area_law_of_relEntropy` (QIQT-H ⇒ `δ⟨K⟩ = η δA`) with `bl_pernull_of_modular`, so the
    only non-derived inputs are the labelled cited physics (`hFlux`, `hFocus`).

    QIQT-H content (along the deformation path `t` at this point/null direction):
    * `hbound` — the capacity **bound** `S ≤ η·A` (QIQT-H's `shannon_le_log_card`);
    * `hsat`   — saturation at the reference `S 0 = η·A 0` (`shannon_uniform_eq_log_card`);
    * `hDnn`,`hD0` — relative-entropy positivity `KE − S ≥ 0`, `= 0` at the reference (Klein,
      `relEntropy_nonneg`);
    * differentiability of `S, KE, A`.
    Cited (Mathlib-unprovable, kept SEPARATE): `hFlux` (Bisognano–Wichmann boost flux), `hFocus`
    (Raychaudhuri focusing).

    Conclusion: `BL(a·T − Ric) v = 0` — Jacobson's per-null premise.  No hypothesis is the area law or
    `BL(a·T − Ric) v = 0` itself; the area law is *derived* from the bound + saturation + Klein. -/
theorem bl_pernull_of_qiqt (T Ric : Fin 4 → Fin 4 → ℝ) (v : Fin 4 → ℝ)
    {S KE A : ℝ → ℝ} {s' k' a' η hbar a : ℝ}
    (hbar0 : hbar ≠ 0) (heta : η ≠ 0) (ha : a = 2 * Real.pi / (hbar * η))
    (hS : HasDerivAt S s' 0) (hK : HasDerivAt KE k' 0) (hA : HasDerivAt A a' 0)
    (hbound : ∀ᶠ t in 𝓝 0, S t ≤ η * A t) (hsat : S 0 = η * A 0)
    (hDnn : ∀ t, 0 ≤ KE t - S t) (hD0 : KE 0 - S 0 = 0)
    (hFlux : k' = 2 * Real.pi / hbar * BL T v)
    (hFocus : a' = BL Ric v) :
    BL (fun i j => a * T i j - Ric i j) v = 0 :=
  bl_pernull_of_modular T Ric v hbar0 heta ha
    (differential_area_law_of_relEntropy hS hK hA hbound hsat hDnn hD0).2 hFlux hFocus

/-- **★★★ THE END-TO-END THEOREM — QIQT-H + (cited Bisognano–Wichmann & Raychaudhuri) ⇒ the Einstein
    field equations.**  Assembles the whole chain into one theorem.  Along each local null generator
    `(x, v)` (with `v` metric-null), QIQT-H's content — the capacity **bound** `S ≤ η·A`
    (`shannon_le_log_card`), saturation at the reference (`shannon_uniform_eq_log_card`), and
    relative-entropy positivity (Klein, `relEntropy_nonneg`) — DERIVES the differential area law / modular
    relation, which with the two **cited** inputs (`hFlux` = Bisognano–Wichmann boost flux, `hFocus` =
    Raychaudhuri focusing) gives Jacobson's per-null premise; `jacobson_einstein_equation_of_state` then
    yields `a·T = G + Λ·g` with genuine Einstein tensor and constant `Λ`.

    HONEST SCOPE.  This is **not** a from-nothing derivation:
    * QIQT-H supplies (as *theorems*, not assumptions): the entropy bound, its saturation, Klein
      positivity — i.e. the *inequality* side of the area law.  The differential law `δS = η δA` is
      *derived* from these (no hypothesis asserts `S = ηA`).
    * **Cited (Mathlib cannot prove these — they are explicit labelled hypotheses, never Lean axioms):**
      `hFlux` (the wedge-modular = boost identification, Bisognano–Wichmann, Type III₁) and `hFocus`
      (Raychaudhuri leading-order focusing); plus the standard structural inputs (Lorentzian congruence
      `g = Pᵀ·η·P`, `∇·T = 0`, `f`-regularity) and the per-generator path-differentiability (a modelling
      choice).
    All geometry (Bianchi, `∇·G = 0`, null-cone→tensor, constant `Λ`) is machine-checked axiom-free.
    So: *modulo the two cited AQFT/geometry facts and the standard structural inputs, QIQT-H's own
    capacity bound + Klein positivity DERIVE the Einstein field equations.* -/
theorem qiqt_bekenstein_gives_gr
    (g gi : Point 4 → Fin 4 → Fin 4 → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hCgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (T : Point 4 → Fin 4 → Fin 4 → ℝ) (η hbar a : ℝ)
    (hbar0 : hbar ≠ 0) (heta : η ≠ 0) (ha : a = 2 * Real.pi / (hbar * η))
    (hT_symm : ∀ x a' b, T x a' b = T x b a')
    (hric_symm : ∀ x a' b, ricci g gi a' b x = ricci g gi b a' x)
    (P Pinv : Point 4 → Fin 4 → Fin 4 → ℝ)
    (hPP : ∀ x i j, (∑ k, P x i k * Pinv x k j) = if i = j then (1 : ℝ) else 0)
    (hPP' : ∀ x i j, (∑ k, Pinv x i k * P x k j) = if i = j then (1 : ℝ) else 0)
    (hcong : ∀ x i j, g x i j = ∑ k, ∑ l, P x k i * gm k l * P x l j)
    -- QIQT-H content along each null generator (S = entropy, KE = modular energy ⟨K⟩, A = area):
    (S KE A : Point 4 → (Fin 4 → ℝ) → ℝ → ℝ) (sd kd ad : Point 4 → (Fin 4 → ℝ) → ℝ)
    (hS : ∀ x v, BL (g x) v = 0 → HasDerivAt (S x v) (sd x v) 0)
    (hK : ∀ x v, BL (g x) v = 0 → HasDerivAt (KE x v) (kd x v) 0)
    (hA : ∀ x v, BL (g x) v = 0 → HasDerivAt (A x v) (ad x v) 0)
    (hbound : ∀ x v, BL (g x) v = 0 → ∀ᶠ t in 𝓝 0, S x v t ≤ η * A x v t)
    (hsat : ∀ x v, BL (g x) v = 0 → S x v 0 = η * A x v 0)
    (hDnn : ∀ x v, BL (g x) v = 0 → ∀ t, 0 ≤ KE x v t - S x v t)
    (hD0 : ∀ x v, BL (g x) v = 0 → KE x v 0 - S x v 0 = 0)
    -- CITED (Mathlib-unprovable, kept SEPARATE): Bisognano–Wichmann boost flux + Raychaudhuri focusing:
    (hFlux : ∀ x v, BL (g x) v = 0 → kd x v = 2 * Real.pi / hbar * BL (T x) v)
    (hFocus : ∀ x v, BL (g x) v = 0 → ad x v = BL (fun i j => ricci g gi i j x) v)
    (hreg : ∀ f : Point 4 → ℝ,
        (∀ y a' b, a * T y a' b = ricci g gi a' b y + f y * g y a' b) →
        (∀ x ρ, PdiffAt f ρ x) ∧
          Differentiable ℝ (fun y => f y + (1 / 2 : ℝ) * scalarCurv g gi y))
    (conserv : ∀ x ν, div02 g gi (fun y a' b => a * T y a' b) ν x = 0) :
    ∃ Λ : ℝ, ∀ x μ ν, a * T x μ ν = einsteinTensor g gi μ ν x + Λ * g x μ ν := by
  have pernull : ∀ (x : Point 4) (v : Fin 4 → ℝ),
      BL (g x) v = 0 → BL (fun a' b => a * T x a' b - ricci g gi a' b x) v = 0 := by
    intro x v hnull
    exact bl_pernull_of_qiqt (T x) (fun i j => ricci g gi i j x) v hbar0 heta ha
      (hS x v hnull) (hK x v hnull) (hA x v hnull) (hbound x v hnull) (hsat x v hnull)
      (hDnn x v hnull) (hD0 x v hnull) (hFlux x v hnull) (hFocus x v hnull)
  exact jacobson_einstein_equation_of_state g gi hsymm hsymm_gi hinv hCg hCgi hC T a hT_symm
    hric_symm P Pinv hPP hPP' hcong pernull hreg conserv

end QIQTH.QiqtToGR
