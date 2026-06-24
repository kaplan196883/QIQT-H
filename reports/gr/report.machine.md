# Track state — GR field equations
*Target 3 — QIQT-H gives the GR field equations (Jacobson route, free KG field)*

_Generated 2026-06-24 09:49 UTC · git `7233ca0` · 14 theorems · tool lean_track_ · provenance: [L]=Lean fact [P]=Lean-checked prober [D]=derived [C]=curation_

## Axiom status  [L]
- Project-specific (non-standard) axioms: **0**
- All policy-clean (axioms ⊆ allowed `propext, Classical.choice, Quot.sound`): **YES**
- All *literally* axiom-free (no axioms at all): **NO**

## Assumption surface (capstone)  [P]/[D]

**`QIQTH.WedgeKMSToGR.qiqt_gr_freefield_complete`** — 28 surface items (28 distinct after dedup; conclusion: `∃ Λ,
  ∀ (x : QIQTH.Curvature.Point 4) (μ ν : Fin 4),
    a * QIQTH.Curvature.kgStress m φ`):
  - `inst._@.QIQTH.QiqtGrComplete.4163739781._hygCtx._hyg.6` : `Nonempty ι`
  - `hsymm` : `∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), g y a b = g y b a` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants, record-law normalization** [C:regularity]
  - `hsymm_gi` : `∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), gi y a b = gi y b a` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants, record-law normalization** [C:regularity]
  - `hinv` : `∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), ∑ σ, g y a σ * gi y σ b = if a = b then 1 else 0` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants, record-law normalization** [C:regularity]
  - `hCg` : `∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => g y a b` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants, record-law normalization** [C:regularity]
  - `hCgi` : `∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => gi y a b` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants, record-law normalization** [C:regularity]
  - `hbar0` : `hbar ≠ 0` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants, record-law normalization** [C:regularity]
  - `hbar_pos` : `0 < hbar` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants, record-law normalization** [C:regularity]
  - `heta` : `η ≠ 0` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants, record-law normalization** [C:regularity]
  - `ha` : `a = 2 * Real.pi / (hbar * η)` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants, record-law normalization** [C:regularity]
  - `hφ` : `ContDiff ℝ ⊤ φ` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants, record-law normalization** [C:regularity]
  - `hKG` : `∀ (x : QIQTH.Curvature.Point 4), QIQTH.Curvature.boxField φ g gi x = m ^ 2 * φ x` · **PHYSICS — genuine input (EOM / Clausius / focusing / localization / FQ capacity)** [C:physics-floor]
  - `hPP` : `∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, P x i k * Pinv x k j = if i = j then 1 else 0` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants, record-law normalization** [C:regularity]
  - `hPP'` : `∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, Pinv x i k * P x k j = if i = j then 1 else 0` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants, record-law normalization** [C:regularity]
  - `hcong` : `∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), g x i j = ∑ k, ∑ l, P x k i * QIQTH.EinsteinEOS.gm k l * P x l j` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants, record-law normalization** [C:regularity]
  - `hpp_nn` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (t : ℝ) (r : ι), 0 ≤ pp x v t r` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants, record-law normalization** [C:regularity]
  - `hpp1` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (t : ℝ), ∑ r, pp x v t r = 1` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants, record-law normalization** [C:regularity]
  - `hpp0` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), pp x v 0 = fun x => (↑(Fintype.card ι))⁻¹` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants, record-law normalization** [C:regularity]
  - `hcap` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), η * A x v 0 = Real.log ↑(Fintype.card ι)` · **PHYSICS — genuine input (EOM / Clausius / focusing / localization / FQ capacity)** [C:physics-floor]
  - `hWx` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → W x v x = v` · **SETUP — per-generator derivative existence / null-congruence kinematics** [C:setup]
  - `hWC` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (μ : Fin 4), ContDiff ℝ ⊤ fun y => W x v y μ` · **SETUP — per-generator derivative existence / null-congruence kinematics** [C:setup]
  - `hWgeo` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (y : QIQTH.Curvature.Point 4) (μ : Fin 4),
  ∑ ν, W x v y ν * QIQTH.Curvature.covDerivVec g gi (W x v) ν μ y = 0` · **SETUP — per-generator derivative existence / null-congruence kinematics** [C:setup]
  - `hWequil` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    ∑ μ, ∑ ν, QIQTH.Curvature.covDerivVec g gi (W x v) μ ν x * QIQTH.Curvature.covDerivVec g gi (W x v) ν μ x = 0` · **SETUP — per-generator derivative existence / null-congruence kinematics** [C:setup]
  - `hS` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (fun t => QIQTH.BranchLedger.Shannon Finset.univ (pp x v t)) (sd x v) 0` · **SETUP — per-generator derivative existence / null-congruence kinematics** [C:setup]
  - `hK` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    HasDerivAt
      (fun t =>
        QIQTH.BranchLedger.Shannon Finset.univ (pp x v t) + QIQTH.RelEntPositivity.KL Finset.univ (pp x v t) (pp x v 0))
      (2 * Real.pi / hbar * QIQTH.EinsteinEOS.BL (QIQTH.Curvature.kgStress m φ g gi x) v) 0` · **SETUP — per-generator derivative existence / null-congruence kinematics** [C:setup]
  - `hA` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    HasDerivAt (A x v) (-∑ ν, W x v x ν * QIQTH.Curvature.pd (fun y => QIQTH.Curvature.expansion g gi (W x v) y) ν x) 0` · **SETUP — per-generator derivative existence / null-congruence kinematics** [C:setup]
  - `hbound` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    ∀ᶠ (t : ℝ) in nhds 0, QIQTH.BranchLedger.Shannon Finset.univ (pp x v t) ≤ η * A x v t` · **PHYSICS — genuine input (EOM / Clausius / focusing / localization / FQ capacity)** [C:physics-floor]
  - `hmw` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), 0 < mw x v` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants, record-law normalization** [C:regularity]

## Curated piles  [C] *(author labels — NOT a Lean fact)*

**PHYSICS — genuine input (EOM / Clausius / focusing / localization / FQ capacity)** (17 distinct)
  - `2 * Real.pi / hbar * Tkk = (-(2 * ↑Real.pi * ∫ (θ : ℝ), (starRingEnd ℂ) (f θ) * f' θ)).im`
  - `HasDerivAt
  (fun t =>
    inner ℂ (MeasureTheory.MemLp.toLp f hf2)
      ((QIQTH.StandardSubspaceModular.modUnitary (QIQTH.Fock.BoostKMS.niceWedgeStandardSubspace m ⋯ ⋯) t)
        (MeasureTheory.MemLp.toLp f hf2)))
  (Complex.I * ↑kd) 0`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    2 * Real.pi / hbar * (∑ b, v b * QIQTH.Curvature.pd φ b x) ^ 2 =
      (-(2 * ↑Real.pi * ∫ (θ : ℝ), (starRingEnd ℂ) (ff x v θ) * ff' x v θ)).im`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    2 * Real.pi / hbar * QIQTH.EinsteinEOS.BL (QIQTH.Curvature.kgStress m φ g gi x) v =
      (-(2 * ↑Real.pi * ∫ (θ : ℝ), (starRingEnd ℂ) (ff x v θ) * ff' x v θ)).im`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    HasDerivAt
      (fun t =>
        inner ℂ (MeasureTheory.MemLp.toLp (ff x v) ⋯)
          ((QIQTH.StandardSubspaceModular.modUnitary (QIQTH.Fock.BoostKMS.niceWedgeStandardSubspace (mw x v) ⋯ ⋯) t)
            (MeasureTheory.MemLp.toLp (ff x v) ⋯)))
      (Complex.I * ↑(kd x v)) 0`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    ∀ᶠ (t : ℝ) in nhds 0, QIQTH.BranchLedger.Shannon Finset.univ (pp x v t) ≤ η * A x v t`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ad x v = QIQTH.EinsteinEOS.BL (fun i j => QIQTH.Curvature.ricci g gi i j x) v`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ᶠ (t : ℝ) in nhds 0, S x v t ≤ η * A x v t`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ᶠ (t : ℝ) in nhds 0, Sf x v t ≤ η * A x v t`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → KE x v 0 - S x v 0 = 0`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → KE x v 0 - Sf x v 0 = 0`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → S x v 0 = η * A x v 0`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → Sf x v 0 = η * A x v 0`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ (t : ℝ), 0 ≤ KE x v t - S x v t`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ (t : ℝ), 0 ≤ KE x v t - Sf x v t`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), η * A x v 0 = Real.log ↑(Fintype.card ι)`
  - `∀ (x : QIQTH.Curvature.Point 4), QIQTH.Curvature.boxField φ g gi x = m ^ 2 * φ x`

**PHYSICS — genuine input (EOM / Clausius / focusing / localization)** (2 distinct)
  - `QIQTH.WedgeKMSToGR.WedgeKMSFlux_complete g (QIQTH.Curvature.kgStress m φ g gi) kd hbar`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → kd x v = 2 * Real.pi / hbar * QIQTH.EinsteinEOS.BL (T x) v`

**REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants, record-law normalization** (32 distinct)
  - `0 < hbar`
  - `0 < m`
  - `ContDiff ℝ ⊤ φ`
  - `MeasureTheory.AEStronglyMeasurable f' MeasureTheory.volume`
  - `MeasureTheory.Integrable f MeasureTheory.volume`
  - `MeasureTheory.MemLp f 2 MeasureTheory.volume`
  - `a = 2 * Real.pi / (hbar * η)`
  - `hbar ≠ 0`
  - `η ≠ 0`
  - `∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => g y a b`
  - `∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => gi y a b`
  - `∀ (f : QIQTH.Curvature.Point 4 → ℝ),
  (∀ (y : QIQTH.Curvature.Point 4) (a' b : Fin 4), a * T y a' b = QIQTH.Curvature.ricci g gi a' b y + f y * g y a' b) →
    (∀ (x : QIQTH.Curvature.Point 4) (ρ : Fin 4), QIQTH.Curvature.PdiffAt f ρ x) ∧
      Differentiable ℝ fun y => f y + 1 / 2 * QIQTH.Curvature.scalarCurv g gi y`
  - `∀ (t : ℝ) (x : ↥(MeasureTheory.Lp ℂ 2 MeasureTheory.volume)),
  (V t) x = (QIQTH.Fock.OneParticle.boostUnitary (2 * Real.pi * t)) x`
  - `∀ (x : QIQTH.Curvature.Point 4) (a' b : Fin 4), T x a' b = T x b a'`
  - `∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), g x i j = ∑ k, ∑ l, P x k i * QIQTH.EinsteinEOS.gm k l * P x l j`
  - `∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, P x i k * Pinv x k j = if i = j then 1 else 0`
  - `∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, Pinv x i k * P x k j = if i = j then 1 else 0`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (t : ℝ) (r : ι), 0 ≤ pp x v t r`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (t : ℝ), ∑ r, pp x v t r = 1`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (θ : ℝ), HasDerivAt (ff x v) (ff' x v θ) θ`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (θ : ℝ), ‖ff' x v θ‖ ≤ Bd x v`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), 0 < mw x v`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.AEStronglyMeasurable (ff' x v) MeasureTheory.volume`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.Integrable (ff x v) MeasureTheory.volume`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.MemLp (ff x v) 2 MeasureTheory.volume`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), pp x v 0 = fun x => (↑(Fintype.card ι))⁻¹`
  - `∀ (x : QIQTH.Curvature.Point 4) (ν : Fin 4), QIQTH.Curvature.div02 g gi (fun y a' b => a * T y a' b) ν x = 0`
  - `∀ (x : ℝ), HasDerivAt f (f' x) x`
  - `∀ (x : ℝ), ‖f' x‖ ≤ B`
  - `∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), g y a b = g y b a`
  - `∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), gi y a b = gi y b a`
  - `∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), ∑ σ, g y a σ * gi y σ b = if a = b then 1 else 0`

**SETUP — per-generator derivative existence / null-congruence kinematics** (12 distinct)
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (y : QIQTH.Curvature.Point 4) (μ : Fin 4),
  ∑ ν, W x v y ν * QIQTH.Curvature.covDerivVec g gi (W x v) ν μ y = 0`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (μ : Fin 4), ContDiff ℝ ⊤ fun y => W x v y μ`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    HasDerivAt
      (fun t =>
        QIQTH.BranchLedger.Shannon Finset.univ (pp x v t) + QIQTH.RelEntPositivity.KL Finset.univ (pp x v t) (pp x v 0))
      (2 * Real.pi / hbar * QIQTH.EinsteinEOS.BL (QIQTH.Curvature.kgStress m φ g gi x) v) 0`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    HasDerivAt (A x v) (-∑ ν, W x v x ν * QIQTH.Curvature.pd (fun y => QIQTH.Curvature.expansion g gi (W x v) y) ν x) 0`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    HasDerivAt (KE x v) (2 * Real.pi / hbar * QIQTH.EinsteinEOS.BL (QIQTH.Curvature.kgStress m φ g gi x) v) 0`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    ∑ μ, ∑ ν, QIQTH.Curvature.covDerivVec g gi (W x v) μ ν x * QIQTH.Curvature.covDerivVec g gi (W x v) ν μ x = 0`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (fun t => QIQTH.BranchLedger.Shannon Finset.univ (pp x v t)) (sd x v) 0`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (A x v) (ad x v) 0`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (KE x v) (kd x v) 0`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (S x v) (sd x v) 0`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (Sf x v) (sd x v) 0`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → W x v x = v`

**(uncategorised surface hypotheses — 2)** *(no rule matched)*
  - `Nonempty ι`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    ad x v = -∑ ν, W x v x ν * QIQTH.Curvature.pd (fun y => QIQTH.Curvature.expansion g gi (W x v) y) ν x`

## Per-theorem facts  [L]/[P]/[D]

### `QIQTH.WedgeKMSToGR.qiqt_gr_freefield_complete`  ·  *capstone*
- policy-clean · uses-spine: `qiqt_gr_freefield_thermo` · kind=thm  [L]
- **conclusion:**
```
∃ Λ,
  ∀ (x : QIQTH.Curvature.Point 4) (μ ν : Fin 4),
    a * QIQTH.Curvature.kgStress m φ g gi x μ ν = QIQTH.Curvature.einsteinTensor g gi μ ν x + Λ * g x μ ν
```
- **hypotheses (28)** — name : status [P]/[D]:
```
1. inst._@.QIQTH.QiqtGrComplete.4163739781._hygCtx._hyg.6 [surface] : Nonempty ι
2. hsymm [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), g y a b = g y b a
3. hsymm_gi [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), gi y a b = gi y b a
4. hinv [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), ∑ σ, g y a σ * gi y σ b = if a = b then 1 else 0
5. hCg [surface] : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => g y a b
6. hCgi [surface] : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => gi y a b
7. hbar0 [surface] : hbar ≠ 0
8. hbar_pos [surface] : 0 < hbar
9. heta [surface] : η ≠ 0
10. ha [surface] : a = 2 * Real.pi / (hbar * η)
11. hφ [surface] : ContDiff ℝ ⊤ φ
12. hKG [surface] : ∀ (x : QIQTH.Curvature.Point 4), QIQTH.Curvature.boxField φ g gi x = m ^ 2 * φ x
13. hPP [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, P x i k * Pinv x k j = if i = j then 1 else 0
14. hPP' [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, Pinv x i k * P x k j = if i = j then 1 else 0
15. hcong [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), g x i j = ∑ k, ∑ l, P x k i * QIQTH.EinsteinEOS.gm k l * P x l j
16. hpp_nn [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (t : ℝ) (r : ι), 0 ≤ pp x v t r
17. hpp1 [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (t : ℝ), ∑ r, pp x v t r = 1
18. hpp0 [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), pp x v 0 = fun x => (↑(Fintype.card ι))⁻¹
19. hcap [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), η * A x v 0 = Real.log ↑(Fintype.card ι)
20. hWx [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → W x v x = v
21. hWC [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (μ : Fin 4), ContDiff ℝ ⊤ fun y => W x v y μ
22. hWgeo [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (y : QIQTH.Curvature.Point 4) (μ : Fin 4),
  ∑ ν, W x v y ν * QIQTH.Curvature.covDerivVec g gi (W x v) ν μ y = 0
23. hWequil [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    ∑ μ, ∑ ν, QIQTH.Curvature.covDerivVec g gi (W x v) μ ν x * QIQTH.Curvature.covDerivVec g gi (W x v) ν μ x = 0
24. hS [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (fun t => QIQTH.BranchLedger.Shannon Finset.univ (pp x v t)) (sd x v) 0
25. hK [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    HasDerivAt
      (fun t =>
        QIQTH.BranchLedger.Shannon Finset.univ (pp x v t) + QIQTH.RelEntPositivity.KL Finset.univ (pp x v t) (pp x v 0))
      (2 * Real.pi / hbar * QIQTH.EinsteinEOS.BL (QIQTH.Curvature.kgStress m φ g gi x) v) 0
26. hA [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    HasDerivAt (A x v) (-∑ ν, W x v x ν * QIQTH.Curvature.pd (fun y => QIQTH.Curvature.expansion g gi (W x v) y) ν x) 0
27. hbound [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    ∀ᶠ (t : ℝ) in nhds 0, QIQTH.BranchLedger.Shannon Finset.univ (pp x v t) ≤ η * A x v t
28. hmw [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), 0 < mw x v
```
- **data binders (15):** `ι`, `g`, `gi`, `φ`, `m`, `η`, `hbar`, `a`, `P`, `Pinv`, `A`, `sd`, `pp`, `W`, `mw`

### `QIQTH.WedgeKMSToGR.qiqt_gr_freefield_gaussian`  ·  *spine*
- policy-clean · uses-spine: `qiqt_gr_freefield_nullEnergy` · kind=thm  [L]
- **conclusion:**
```
∃ Λ,
  ∀ (x : QIQTH.Curvature.Point 4) (μ ν : Fin 4),
    a * QIQTH.Curvature.kgStress m φ g gi x μ ν = QIQTH.Curvature.einsteinTensor g gi μ ν x + Λ * g x μ ν
```
- **hypotheses (27)** — name : status [P]/[D]:
```
1. hsymm [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), g y a b = g y b a
2. hsymm_gi [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), gi y a b = gi y b a
3. hinv [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), ∑ σ, g y a σ * gi y σ b = if a = b then 1 else 0
4. hCg [surface] : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => g y a b
5. hCgi [surface] : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => gi y a b
6. hbar0 [surface] : hbar ≠ 0
7. hbar_pos [surface] : 0 < hbar
8. heta [surface] : η ≠ 0
9. ha [surface] : a = 2 * Real.pi / (hbar * η)
10. hφ [surface] : ContDiff ℝ ⊤ φ
11. hKG [surface] : ∀ (x : QIQTH.Curvature.Point 4), QIQTH.Curvature.boxField φ g gi x = m ^ 2 * φ x
12. hPP [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, P x i k * Pinv x k j = if i = j then 1 else 0
13. hPP' [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, Pinv x i k * P x k j = if i = j then 1 else 0
14. hcong [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), g x i j = ∑ k, ∑ l, P x k i * QIQTH.EinsteinEOS.gm k l * P x l j
15. hS [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (Sf x v) (sd x v) 0
16. hK [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    HasDerivAt (KE x v) (2 * Real.pi / hbar * QIQTH.EinsteinEOS.BL (QIQTH.Curvature.kgStress m φ g gi x) v) 0
17. hA [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (A x v) (ad x v) 0
18. hbound [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ᶠ (t : ℝ) in nhds 0, Sf x v t ≤ η * A x v t
19. hsat [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → Sf x v 0 = η * A x v 0
20. hDnn [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ (t : ℝ), 0 ≤ KE x v t - Sf x v t
21. hD0 [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → KE x v 0 - Sf x v 0 = 0
22. hmw [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), 0 < mw x v
23. hWx [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → W x v x = v
24. hWC [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (μ : Fin 4), ContDiff ℝ ⊤ fun y => W x v y μ
25. hWgeo [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (y : QIQTH.Curvature.Point 4) (μ : Fin 4),
  ∑ ν, W x v y ν * QIQTH.Curvature.covDerivVec g gi (W x v) ν μ y = 0
26. hWequil [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    ∑ μ, ∑ ν, QIQTH.Curvature.covDerivVec g gi (W x v) μ ν x * QIQTH.Curvature.covDerivVec g gi (W x v) ν μ x = 0
27. hWarea [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    ad x v = -∑ ν, W x v x ν * QIQTH.Curvature.pd (fun y => QIQTH.Curvature.expansion g gi (W x v) y) ν x
```
- **data binders (16):** `g`, `gi`, `φ`, `m`, `η`, `hbar`, `a`, `P`, `Pinv`, `Sf`, `KE`, `A`, `sd`, `ad`, `mw`, `W`

### `QIQTH.WedgeKMSToGR.qiqt_gr_freefield_thermo`  ·  *spine*
- policy-clean · uses-spine: `qiqt_gr_freefield_geom` · kind=thm  [L]
- **conclusion:**
```
∃ Λ,
  ∀ (x : QIQTH.Curvature.Point 4) (μ ν : Fin 4),
    a * QIQTH.Curvature.kgStress m φ g gi x μ ν = QIQTH.Curvature.einsteinTensor g gi μ ν x + Λ * g x μ ν
```
- **hypotheses (33)** — name : status [P]/[D]:
```
1. inst._@.QIQTH.QiqtGrThermo.1369663628._hygCtx._hyg.6 [surface] : Nonempty ι
2. hsymm [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), g y a b = g y b a
3. hsymm_gi [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), gi y a b = gi y b a
4. hinv [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), ∑ σ, g y a σ * gi y σ b = if a = b then 1 else 0
5. hCg [surface] : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => g y a b
6. hCgi [surface] : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => gi y a b
7. hbar0 [surface] : hbar ≠ 0
8. heta [surface] : η ≠ 0
9. ha [surface] : a = 2 * Real.pi / (hbar * η)
10. hφ [surface] : ContDiff ℝ ⊤ φ
11. hKG [surface] : ∀ (x : QIQTH.Curvature.Point 4), QIQTH.Curvature.boxField φ g gi x = m ^ 2 * φ x
12. hPP [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, P x i k * Pinv x k j = if i = j then 1 else 0
13. hPP' [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, Pinv x i k * P x k j = if i = j then 1 else 0
14. hcong [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), g x i j = ∑ k, ∑ l, P x k i * QIQTH.EinsteinEOS.gm k l * P x l j
15. hpp_nn [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (t : ℝ) (r : ι), 0 ≤ pp x v t r
16. hpp1 [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (t : ℝ), ∑ r, pp x v t r = 1
17. hpp0 [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), pp x v 0 = fun x => (↑(Fintype.card ι))⁻¹
18. hcap [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), η * A x v 0 = Real.log ↑(Fintype.card ι)
19. hWx [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → W x v x = v
20. hWC [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (μ : Fin 4), ContDiff ℝ ⊤ fun y => W x v y μ
21. hWgeo [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (y : QIQTH.Curvature.Point 4) (μ : Fin 4),
  ∑ ν, W x v y ν * QIQTH.Curvature.covDerivVec g gi (W x v) ν μ y = 0
22. hWequil [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    ∑ μ, ∑ ν, QIQTH.Curvature.covDerivVec g gi (W x v) μ ν x * QIQTH.Curvature.covDerivVec g gi (W x v) ν μ x = 0
23. hS [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (fun t => QIQTH.BranchLedger.Shannon Finset.univ (pp x v t)) (sd x v) 0
24. hK [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    HasDerivAt
      (fun t =>
        QIQTH.BranchLedger.Shannon Finset.univ (pp x v t) + QIQTH.RelEntPositivity.KL Finset.univ (pp x v t) (pp x v 0))
      (2 * Real.pi / hbar * QIQTH.EinsteinEOS.BL (QIQTH.Curvature.kgStress m φ g gi x) v) 0
25. hA [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    HasDerivAt (A x v) (-∑ ν, W x v x ν * QIQTH.Curvature.pd (fun y => QIQTH.Curvature.expansion g gi (W x v) y) ν x) 0
26. hbound [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    ∀ᶠ (t : ℝ) in nhds 0, QIQTH.BranchLedger.Shannon Finset.univ (pp x v t) ≤ η * A x v t
27. hmw [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), 0 < mw x v
28. hf2 [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.MemLp (ff x v) 2 MeasureTheory.volume
29. hf_int [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.Integrable (ff x v) MeasureTheory.volume
30. hfd [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (θ : ℝ), HasDerivAt (ff x v) (ff' x v θ) θ
31. hf'_meas [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.AEStronglyMeasurable (ff' x v) MeasureTheory.volume
32. hB [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (θ : ℝ), ‖ff' x v θ‖ ≤ Bd x v
33. hTkk [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    2 * Real.pi / hbar * (∑ b, v b * QIQTH.Curvature.pd φ b x) ^ 2 =
      (-(2 * ↑Real.pi * ∫ (θ : ℝ), (starRingEnd ℂ) (ff x v θ) * ff' x v θ)).im
```
- **data binders (18):** `ι`, `g`, `gi`, `φ`, `m`, `η`, `hbar`, `a`, `P`, `Pinv`, `A`, `sd`, `pp`, `W`, `mw`, `ff`, `ff'`, `Bd`

### `QIQTH.WedgeKMSToGR.qiqt_gr_freefield_geom`  ·  *spine*
- policy-clean · uses-spine: `qiqt_gr_freefield_nullEnergy` · kind=thm  [L]
- **conclusion:**
```
∃ Λ,
  ∀ (x : QIQTH.Curvature.Point 4) (μ ν : Fin 4),
    a * QIQTH.Curvature.kgStress m φ g gi x μ ν = QIQTH.Curvature.einsteinTensor g gi μ ν x + Λ * g x μ ν
```
- **hypotheses (31)** — name : status [P]/[D]:
```
1. hsymm [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), g y a b = g y b a
2. hsymm_gi [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), gi y a b = gi y b a
3. hinv [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), ∑ σ, g y a σ * gi y σ b = if a = b then 1 else 0
4. hCg [surface] : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => g y a b
5. hCgi [surface] : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => gi y a b
6. hbar0 [surface] : hbar ≠ 0
7. heta [surface] : η ≠ 0
8. ha [surface] : a = 2 * Real.pi / (hbar * η)
9. hφ [surface] : ContDiff ℝ ⊤ φ
10. hKG [surface] : ∀ (x : QIQTH.Curvature.Point 4), QIQTH.Curvature.boxField φ g gi x = m ^ 2 * φ x
11. hPP [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, P x i k * Pinv x k j = if i = j then 1 else 0
12. hPP' [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, Pinv x i k * P x k j = if i = j then 1 else 0
13. hcong [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), g x i j = ∑ k, ∑ l, P x k i * QIQTH.EinsteinEOS.gm k l * P x l j
14. hWx [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → W x v x = v
15. hWC [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (μ : Fin 4), ContDiff ℝ ⊤ fun y => W x v y μ
16. hWgeo [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (y : QIQTH.Curvature.Point 4) (μ : Fin 4),
  ∑ ν, W x v y ν * QIQTH.Curvature.covDerivVec g gi (W x v) ν μ y = 0
17. hWequil [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    ∑ μ, ∑ ν, QIQTH.Curvature.covDerivVec g gi (W x v) μ ν x * QIQTH.Curvature.covDerivVec g gi (W x v) ν μ x = 0
18. hS [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (Sf x v) (sd x v) 0
19. hK [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    HasDerivAt (KE x v) (2 * Real.pi / hbar * QIQTH.EinsteinEOS.BL (QIQTH.Curvature.kgStress m φ g gi x) v) 0
20. hA [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    HasDerivAt (A x v) (-∑ ν, W x v x ν * QIQTH.Curvature.pd (fun y => QIQTH.Curvature.expansion g gi (W x v) y) ν x) 0
21. hbound [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ᶠ (t : ℝ) in nhds 0, Sf x v t ≤ η * A x v t
22. hsat [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → Sf x v 0 = η * A x v 0
23. hDnn [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ (t : ℝ), 0 ≤ KE x v t - Sf x v t
24. hD0 [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → KE x v 0 - Sf x v 0 = 0
25. hmw [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), 0 < mw x v
26. hf2 [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.MemLp (ff x v) 2 MeasureTheory.volume
27. hf_int [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.Integrable (ff x v) MeasureTheory.volume
28. hfd [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (θ : ℝ), HasDerivAt (ff x v) (ff' x v θ) θ
29. hf'_meas [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.AEStronglyMeasurable (ff' x v) MeasureTheory.volume
30. hB [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (θ : ℝ), ‖ff' x v θ‖ ≤ Bd x v
31. hTkk [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    2 * Real.pi / hbar * (∑ b, v b * QIQTH.Curvature.pd φ b x) ^ 2 =
      (-(2 * ↑Real.pi * ∫ (θ : ℝ), (starRingEnd ℂ) (ff x v θ) * ff' x v θ)).im
```
- **data binders (18):** `g`, `gi`, `φ`, `m`, `η`, `hbar`, `a`, `P`, `Pinv`, `Sf`, `KE`, `A`, `sd`, `W`, `mw`, `ff`, `ff'`, `Bd`

### `QIQTH.WedgeKMSToGR.qiqt_gr_freefield_nullEnergy`  ·  *spine*
- policy-clean · uses-spine: `qiqt_gr_freefield_localized'` · kind=thm  [L]
- **conclusion:**
```
∃ Λ,
  ∀ (x : QIQTH.Curvature.Point 4) (μ ν : Fin 4),
    a * QIQTH.Curvature.kgStress m φ g gi x μ ν = QIQTH.Curvature.einsteinTensor g gi μ ν x + Λ * g x μ ν
```
- **hypotheses (32)** — name : status [P]/[D]:
```
1. hsymm [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), g y a b = g y b a
2. hsymm_gi [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), gi y a b = gi y b a
3. hinv [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), ∑ σ, g y a σ * gi y σ b = if a = b then 1 else 0
4. hCg [surface] : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => g y a b
5. hCgi [surface] : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => gi y a b
6. hbar0 [surface] : hbar ≠ 0
7. heta [surface] : η ≠ 0
8. ha [surface] : a = 2 * Real.pi / (hbar * η)
9. hφ [surface] : ContDiff ℝ ⊤ φ
10. hKG [surface] : ∀ (x : QIQTH.Curvature.Point 4), QIQTH.Curvature.boxField φ g gi x = m ^ 2 * φ x
11. hPP [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, P x i k * Pinv x k j = if i = j then 1 else 0
12. hPP' [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, Pinv x i k * P x k j = if i = j then 1 else 0
13. hcong [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), g x i j = ∑ k, ∑ l, P x k i * QIQTH.EinsteinEOS.gm k l * P x l j
14. hS [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (Sf x v) (sd x v) 0
15. hK [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    HasDerivAt (KE x v) (2 * Real.pi / hbar * QIQTH.EinsteinEOS.BL (QIQTH.Curvature.kgStress m φ g gi x) v) 0
16. hA [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (A x v) (ad x v) 0
17. hbound [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ᶠ (t : ℝ) in nhds 0, Sf x v t ≤ η * A x v t
18. hsat [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → Sf x v 0 = η * A x v 0
19. hDnn [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ (t : ℝ), 0 ≤ KE x v t - Sf x v t
20. hD0 [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → KE x v 0 - Sf x v 0 = 0
21. hmw [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), 0 < mw x v
22. hf2 [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.MemLp (ff x v) 2 MeasureTheory.volume
23. hf_int [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.Integrable (ff x v) MeasureTheory.volume
24. hfd [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (θ : ℝ), HasDerivAt (ff x v) (ff' x v θ) θ
25. hf'_meas [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.AEStronglyMeasurable (ff' x v) MeasureTheory.volume
26. hB [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (θ : ℝ), ‖ff' x v θ‖ ≤ Bd x v
27. hTkk [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    2 * Real.pi / hbar * (∑ b, v b * QIQTH.Curvature.pd φ b x) ^ 2 =
      (-(2 * ↑Real.pi * ∫ (θ : ℝ), (starRingEnd ℂ) (ff x v θ) * ff' x v θ)).im
28. hWx [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → W x v x = v
29. hWC [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (μ : Fin 4), ContDiff ℝ ⊤ fun y => W x v y μ
30. hWgeo [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (y : QIQTH.Curvature.Point 4) (μ : Fin 4),
  ∑ ν, W x v y ν * QIQTH.Curvature.covDerivVec g gi (W x v) ν μ y = 0
31. hWequil [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    ∑ μ, ∑ ν, QIQTH.Curvature.covDerivVec g gi (W x v) μ ν x * QIQTH.Curvature.covDerivVec g gi (W x v) ν μ x = 0
32. hWarea [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    ad x v = -∑ ν, W x v x ν * QIQTH.Curvature.pd (fun y => QIQTH.Curvature.expansion g gi (W x v) y) ν x
```
- **data binders (19):** `g`, `gi`, `φ`, `m`, `η`, `hbar`, `a`, `P`, `Pinv`, `Sf`, `KE`, `A`, `sd`, `ad`, `mw`, `ff`, `ff'`, `Bd`, `W`

### `QIQTH.WedgeKMSToGR.qiqt_gr_freefield_localized'`  ·  *spine*
- policy-clean · uses-spine: `qiqt_gr_freefield_localized` · kind=thm  [L]
- **conclusion:**
```
∃ Λ,
  ∀ (x : QIQTH.Curvature.Point 4) (μ ν : Fin 4),
    a * QIQTH.Curvature.kgStress m φ g gi x μ ν = QIQTH.Curvature.einsteinTensor g gi μ ν x + Λ * g x μ ν
```
- **hypotheses (32)** — name : status [P]/[D]:
```
1. hsymm [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), g y a b = g y b a
2. hsymm_gi [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), gi y a b = gi y b a
3. hinv [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), ∑ σ, g y a σ * gi y σ b = if a = b then 1 else 0
4. hCg [surface] : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => g y a b
5. hCgi [surface] : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => gi y a b
6. hbar0 [surface] : hbar ≠ 0
7. heta [surface] : η ≠ 0
8. ha [surface] : a = 2 * Real.pi / (hbar * η)
9. hφ [surface] : ContDiff ℝ ⊤ φ
10. hKG [surface] : ∀ (x : QIQTH.Curvature.Point 4), QIQTH.Curvature.boxField φ g gi x = m ^ 2 * φ x
11. hPP [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, P x i k * Pinv x k j = if i = j then 1 else 0
12. hPP' [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, Pinv x i k * P x k j = if i = j then 1 else 0
13. hcong [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), g x i j = ∑ k, ∑ l, P x k i * QIQTH.EinsteinEOS.gm k l * P x l j
14. hS [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (Sf x v) (sd x v) 0
15. hK [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    HasDerivAt (KE x v) (2 * Real.pi / hbar * QIQTH.EinsteinEOS.BL (QIQTH.Curvature.kgStress m φ g gi x) v) 0
16. hA [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (A x v) (ad x v) 0
17. hbound [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ᶠ (t : ℝ) in nhds 0, Sf x v t ≤ η * A x v t
18. hsat [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → Sf x v 0 = η * A x v 0
19. hDnn [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ (t : ℝ), 0 ≤ KE x v t - Sf x v t
20. hD0 [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → KE x v 0 - Sf x v 0 = 0
21. hmw [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), 0 < mw x v
22. hf2 [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.MemLp (ff x v) 2 MeasureTheory.volume
23. hf_int [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.Integrable (ff x v) MeasureTheory.volume
24. hfd [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (θ : ℝ), HasDerivAt (ff x v) (ff' x v θ) θ
25. hf'_meas [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.AEStronglyMeasurable (ff' x v) MeasureTheory.volume
26. hB [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (θ : ℝ), ‖ff' x v θ‖ ≤ Bd x v
27. hTkk [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    2 * Real.pi / hbar * QIQTH.EinsteinEOS.BL (QIQTH.Curvature.kgStress m φ g gi x) v =
      (-(2 * ↑Real.pi * ∫ (θ : ℝ), (starRingEnd ℂ) (ff x v θ) * ff' x v θ)).im
28. hWx [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → W x v x = v
29. hWC [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (μ : Fin 4), ContDiff ℝ ⊤ fun y => W x v y μ
30. hWgeo [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (y : QIQTH.Curvature.Point 4) (μ : Fin 4),
  ∑ ν, W x v y ν * QIQTH.Curvature.covDerivVec g gi (W x v) ν μ y = 0
31. hWequil [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    ∑ μ, ∑ ν, QIQTH.Curvature.covDerivVec g gi (W x v) μ ν x * QIQTH.Curvature.covDerivVec g gi (W x v) ν μ x = 0
32. hWarea [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    ad x v = -∑ ν, W x v x ν * QIQTH.Curvature.pd (fun y => QIQTH.Curvature.expansion g gi (W x v) y) ν x
```
- **data binders (19):** `g`, `gi`, `φ`, `m`, `η`, `hbar`, `a`, `P`, `Pinv`, `Sf`, `KE`, `A`, `sd`, `ad`, `mw`, `ff`, `ff'`, `Bd`, `W`

### `QIQTH.WedgeKMSToGR.qiqt_gr_freefield_localized`  ·  *spine*
- policy-clean · uses-spine: `qiqt_gr_freefield`, `freeField_oneParticle_hFlux` · kind=thm  [L]
- **conclusion:**
```
∃ Λ,
  ∀ (x : QIQTH.Curvature.Point 4) (μ ν : Fin 4),
    a * QIQTH.Curvature.kgStress m φ g gi x μ ν = QIQTH.Curvature.einsteinTensor g gi μ ν x + Λ * g x μ ν
```
- **hypotheses (28)** — name : status [P]/[D]:
```
1. hsymm [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), g y a b = g y b a
2. hsymm_gi [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), gi y a b = gi y b a
3. hinv [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), ∑ σ, g y a σ * gi y σ b = if a = b then 1 else 0
4. hCg [surface] : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => g y a b
5. hCgi [surface] : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => gi y a b
6. hbar0 [surface] : hbar ≠ 0
7. heta [surface] : η ≠ 0
8. ha [surface] : a = 2 * Real.pi / (hbar * η)
9. hφ [surface] : ContDiff ℝ ⊤ φ
10. hKG [surface] : ∀ (x : QIQTH.Curvature.Point 4), QIQTH.Curvature.boxField φ g gi x = m ^ 2 * φ x
11. hPP [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, P x i k * Pinv x k j = if i = j then 1 else 0
12. hPP' [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, Pinv x i k * P x k j = if i = j then 1 else 0
13. hcong [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), g x i j = ∑ k, ∑ l, P x k i * QIQTH.EinsteinEOS.gm k l * P x l j
14. hS [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (Sf x v) (sd x v) 0
15. hK [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    HasDerivAt (KE x v) (2 * Real.pi / hbar * QIQTH.EinsteinEOS.BL (QIQTH.Curvature.kgStress m φ g gi x) v) 0
16. hA [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (A x v) (ad x v) 0
17. hbound [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ᶠ (t : ℝ) in nhds 0, Sf x v t ≤ η * A x v t
18. hsat [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → Sf x v 0 = η * A x v 0
19. hDnn [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ (t : ℝ), 0 ≤ KE x v t - Sf x v t
20. hD0 [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → KE x v 0 - Sf x v 0 = 0
21. hmw [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), 0 < mw x v
22. hf2 [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.MemLp (ff x v) 2 MeasureTheory.volume
23. hf_int [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.Integrable (ff x v) MeasureTheory.volume
24. hfd [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (θ : ℝ), HasDerivAt (ff x v) (ff' x v θ) θ
25. hf'_meas [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.AEStronglyMeasurable (ff' x v) MeasureTheory.volume
26. hB [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (θ : ℝ), ‖ff' x v θ‖ ≤ Bd x v
27. hTkk [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    2 * Real.pi / hbar * QIQTH.EinsteinEOS.BL (QIQTH.Curvature.kgStress m φ g gi x) v =
      (-(2 * ↑Real.pi * ∫ (θ : ℝ), (starRingEnd ℂ) (ff x v θ) * ff' x v θ)).im
28. hFocus [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ad x v = QIQTH.EinsteinEOS.BL (fun i j => QIQTH.Curvature.ricci g gi i j x) v
```
- **data binders (18):** `g`, `gi`, `φ`, `m`, `η`, `hbar`, `a`, `P`, `Pinv`, `Sf`, `KE`, `A`, `sd`, `ad`, `mw`, `ff`, `ff'`, `Bd`

### `QIQTH.WedgeKMSToGR.qiqt_gr_freefield`  ·  *spine*
- policy-clean · uses-spine: `qiqt_gr_from_flux_complete` · kind=thm  [L]
- **conclusion:**
```
∃ Λ,
  ∀ (x : QIQTH.Curvature.Point 4) (μ ν : Fin 4),
    a * QIQTH.Curvature.kgStress m φ g gi x μ ν = QIQTH.Curvature.einsteinTensor g gi μ ν x + Λ * g x μ ν
```
- **hypotheses (29)** — name : status [P]/[D]:
```
1. hsymm [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), g y a b = g y b a
2. hsymm_gi [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), gi y a b = gi y b a
3. hinv [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), ∑ σ, g y a σ * gi y σ b = if a = b then 1 else 0
4. hCg [surface] : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => g y a b
5. hCgi [surface] : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => gi y a b
6. hbar0 [surface] : hbar ≠ 0
7. heta [surface] : η ≠ 0
8. ha [surface] : a = 2 * Real.pi / (hbar * η)
9. hφ [surface] : ContDiff ℝ ⊤ φ
10. hKG [surface] : ∀ (x : QIQTH.Curvature.Point 4), QIQTH.Curvature.boxField φ g gi x = m ^ 2 * φ x
11. hPP [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, P x i k * Pinv x k j = if i = j then 1 else 0
12. hPP' [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, Pinv x i k * P x k j = if i = j then 1 else 0
13. hcong [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), g x i j = ∑ k, ∑ l, P x k i * QIQTH.EinsteinEOS.gm k l * P x l j
14. hS [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (Sf x v) (sd x v) 0
15. hK [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (KE x v) (kd x v) 0
16. hA [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (A x v) (ad x v) 0
17. hbound [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ᶠ (t : ℝ) in nhds 0, Sf x v t ≤ η * A x v t
18. hsat [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → Sf x v 0 = η * A x v 0
19. hDnn [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ (t : ℝ), 0 ≤ KE x v t - Sf x v t
20. hD0 [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → KE x v 0 - Sf x v 0 = 0
21. hmw [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), 0 < mw x v
22. hf2 [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.MemLp (ff x v) 2 MeasureTheory.volume
23. hf_int [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.Integrable (ff x v) MeasureTheory.volume
24. hfd [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (θ : ℝ), HasDerivAt (ff x v) (ff' x v θ) θ
25. hf'_meas [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.AEStronglyMeasurable (ff' x v) MeasureTheory.volume
26. hB [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (θ : ℝ), ‖ff' x v θ‖ ≤ Bd x v
27. hTkk [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    2 * Real.pi / hbar * QIQTH.EinsteinEOS.BL (QIQTH.Curvature.kgStress m φ g gi x) v =
      (-(2 * ↑Real.pi * ∫ (θ : ℝ), (starRingEnd ℂ) (ff x v θ) * ff' x v θ)).im
28. hbridge [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    HasDerivAt
      (fun t =>
        inner ℂ (MeasureTheory.MemLp.toLp (ff x v) ⋯)
          ((QIQTH.StandardSubspaceModular.modUnitary (QIQTH.Fock.BoostKMS.niceWedgeStandardSubspace (mw x v) ⋯ ⋯) t)
            (MeasureTheory.MemLp.toLp (ff x v) ⋯)))
      (Complex.I * ↑(kd x v)) 0
29. hFocus [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ad x v = QIQTH.EinsteinEOS.BL (fun i j => QIQTH.Curvature.ricci g gi i j x) v
```
- **data binders (19):** `g`, `gi`, `φ`, `m`, `η`, `hbar`, `a`, `P`, `Pinv`, `Sf`, `KE`, `A`, `sd`, `kd`, `ad`, `mw`, `ff`, `ff'`, `Bd`

### `QIQTH.WedgeKMSToGR.qiqt_gr_explicit_kg`  ·  *spine*
- policy-clean · kind=thm  [L]
- **conclusion:**
```
∃ Λ,
  ∀ (x : QIQTH.Curvature.Point 4) (μ ν : Fin 4),
    a * QIQTH.Curvature.kgStress m φ g gi x μ ν = QIQTH.Curvature.einsteinTensor g gi μ ν x + Λ * g x μ ν
```
- **hypotheses (22)** — name : status [P]/[D]:
```
1. hsymm [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), g y a b = g y b a
2. hsymm_gi [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), gi y a b = gi y b a
3. hinv [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), ∑ σ, g y a σ * gi y σ b = if a = b then 1 else 0
4. hCg [surface] : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => g y a b
5. hCgi [surface] : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => gi y a b
6. hbar0 [surface] : hbar ≠ 0
7. heta [surface] : η ≠ 0
8. ha [surface] : a = 2 * Real.pi / (hbar * η)
9. hφ [surface] : ContDiff ℝ ⊤ φ
10. hKG [surface] : ∀ (x : QIQTH.Curvature.Point 4), QIQTH.Curvature.boxField φ g gi x = m ^ 2 * φ x
11. hPP [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, P x i k * Pinv x k j = if i = j then 1 else 0
12. hPP' [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, Pinv x i k * P x k j = if i = j then 1 else 0
13. hcong [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), g x i j = ∑ k, ∑ l, P x k i * QIQTH.EinsteinEOS.gm k l * P x l j
14. hS [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (Sf x v) (sd x v) 0
15. hK [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (KE x v) (kd x v) 0
16. hA [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (A x v) (ad x v) 0
17. hbound [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ᶠ (t : ℝ) in nhds 0, Sf x v t ≤ η * A x v t
18. hsat [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → Sf x v 0 = η * A x v 0
19. hDnn [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ (t : ℝ), 0 ≤ KE x v t - Sf x v t
20. hD0 [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → KE x v 0 - Sf x v 0 = 0
21. hKMS [surface] : QIQTH.WedgeKMSToGR.WedgeKMSFlux_complete g (QIQTH.Curvature.kgStress m φ g gi) kd hbar
22. hFocus [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ad x v = QIQTH.EinsteinEOS.BL (fun i j => QIQTH.Curvature.ricci g gi i j x) v
```
- **data binders (15):** `g`, `gi`, `φ`, `m`, `η`, `hbar`, `a`, `P`, `Pinv`, `Sf`, `KE`, `A`, `sd`, `kd`, `ad`

### `QIQTH.WedgeKMSToGR.qiqt_gr_from_flux_complete`  ·  *spine*
- policy-clean · uses-spine: `qiqt_bekenstein_gives_gr` · kind=thm  [L]
- **conclusion:**
```
∃ Λ,
  ∀ (x : QIQTH.Curvature.Point 4) (μ ν : Fin 4), a * T x μ ν = QIQTH.Curvature.einsteinTensor g gi μ ν x + Λ * g x μ ν
```
- **hypotheses (23)** — name : status [P]/[D]:
```
1. hsymm [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), g y a b = g y b a
2. hsymm_gi [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), gi y a b = gi y b a
3. hinv [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), ∑ σ, g y a σ * gi y σ b = if a = b then 1 else 0
4. hCg [surface] : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => g y a b
5. hCgi [surface] : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => gi y a b
6. hbar0 [surface] : hbar ≠ 0
7. heta [surface] : η ≠ 0
8. ha [surface] : a = 2 * Real.pi / (hbar * η)
9. hT_symm [surface] : ∀ (x : QIQTH.Curvature.Point 4) (a' b : Fin 4), T x a' b = T x b a'
10. hPP [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, P x i k * Pinv x k j = if i = j then 1 else 0
11. hPP' [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, Pinv x i k * P x k j = if i = j then 1 else 0
12. hcong [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), g x i j = ∑ k, ∑ l, P x k i * QIQTH.EinsteinEOS.gm k l * P x l j
13. hS [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (Sf x v) (sd x v) 0
14. hK [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (KE x v) (kd x v) 0
15. hA [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (A x v) (ad x v) 0
16. hbound [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ᶠ (t : ℝ) in nhds 0, Sf x v t ≤ η * A x v t
17. hsat [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → Sf x v 0 = η * A x v 0
18. hDnn [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ (t : ℝ), 0 ≤ KE x v t - Sf x v t
19. hD0 [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → KE x v 0 - Sf x v 0 = 0
20. hflux [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → kd x v = 2 * Real.pi / hbar * QIQTH.EinsteinEOS.BL (T x) v
21. hFocus [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ad x v = QIQTH.EinsteinEOS.BL (fun i j => QIQTH.Curvature.ricci g gi i j x) v
22. hreg [surface] : ∀ (f : QIQTH.Curvature.Point 4 → ℝ),
  (∀ (y : QIQTH.Curvature.Point 4) (a' b : Fin 4), a * T y a' b = QIQTH.Curvature.ricci g gi a' b y + f y * g y a' b) →
    (∀ (x : QIQTH.Curvature.Point 4) (ρ : Fin 4), QIQTH.Curvature.PdiffAt f ρ x) ∧
      Differentiable ℝ fun y => f y + 1 / 2 * QIQTH.Curvature.scalarCurv g gi y
23. conserv [surface] : ∀ (x : QIQTH.Curvature.Point 4) (ν : Fin 4), QIQTH.Curvature.div02 g gi (fun y a' b => a * T y a' b) ν x = 0
```
- **data binders (14):** `g`, `gi`, `T`, `η`, `hbar`, `a`, `P`, `Pinv`, `Sf`, `KE`, `A`, `sd`, `kd`, `ad`

### `QIQTH.QiqtToGR.qiqt_bekenstein_gives_gr`  ·  *spine*
- policy-clean · kind=thm  [L]
- **conclusion:**
```
∃ Λ,
  ∀ (x : QIQTH.Curvature.Point 4) (μ ν : Fin 4), a * T x μ ν = QIQTH.Curvature.einsteinTensor g gi μ ν x + Λ * g x μ ν
```
- **hypotheses (23)** — name : status [P]/[D]:
```
1. hsymm [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), g y a b = g y b a
2. hsymm_gi [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), gi y a b = gi y b a
3. hinv [surface] : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), ∑ σ, g y a σ * gi y σ b = if a = b then 1 else 0
4. hCg [surface] : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => g y a b
5. hCgi [surface] : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => gi y a b
6. hbar0 [surface] : hbar ≠ 0
7. heta [surface] : η ≠ 0
8. ha [surface] : a = 2 * Real.pi / (hbar * η)
9. hT_symm [surface] : ∀ (x : QIQTH.Curvature.Point 4) (a' b : Fin 4), T x a' b = T x b a'
10. hPP [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, P x i k * Pinv x k j = if i = j then 1 else 0
11. hPP' [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, Pinv x i k * P x k j = if i = j then 1 else 0
12. hcong [surface] : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), g x i j = ∑ k, ∑ l, P x k i * QIQTH.EinsteinEOS.gm k l * P x l j
13. hS [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (S x v) (sd x v) 0
14. hK [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (KE x v) (kd x v) 0
15. hA [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (A x v) (ad x v) 0
16. hbound [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ᶠ (t : ℝ) in nhds 0, S x v t ≤ η * A x v t
17. hsat [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → S x v 0 = η * A x v 0
18. hDnn [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ (t : ℝ), 0 ≤ KE x v t - S x v t
19. hD0 [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → KE x v 0 - S x v 0 = 0
20. hFlux [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → kd x v = 2 * Real.pi / hbar * QIQTH.EinsteinEOS.BL (T x) v
21. hFocus [surface] : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ad x v = QIQTH.EinsteinEOS.BL (fun i j => QIQTH.Curvature.ricci g gi i j x) v
22. hreg [surface] : ∀ (f : QIQTH.Curvature.Point 4 → ℝ),
  (∀ (y : QIQTH.Curvature.Point 4) (a' b : Fin 4), a * T y a' b = QIQTH.Curvature.ricci g gi a' b y + f y * g y a' b) →
    (∀ (x : QIQTH.Curvature.Point 4) (ρ : Fin 4), QIQTH.Curvature.PdiffAt f ρ x) ∧
      Differentiable ℝ fun y => f y + 1 / 2 * QIQTH.Curvature.scalarCurv g gi y
23. conserv [surface] : ∀ (x : QIQTH.Curvature.Point 4) (ν : Fin 4), QIQTH.Curvature.div02 g gi (fun y a' b => a * T y a' b) ν x = 0
```
- **data binders (14):** `g`, `gi`, `T`, `η`, `hbar`, `a`, `P`, `Pinv`, `S`, `KE`, `A`, `sd`, `kd`, `ad`

### `QIQTH.Fock.CyclicWitness.oneParticleBW_niceWedge_unconditional`  ·  *spine*
- policy-clean · kind=thm  [L]
- **conclusion:**
```
QIQTH.StandardSubspaceModular.modUnitary (QIQTH.Fock.BoostKMS.niceWedgeStandardSubspace m ⋯ ⋯) t = V t
```
- **hypotheses (2)** — name : status [P]/[D]:
```
1. hm [surface] : 0 < m
2. hVboost [surface] : ∀ (t : ℝ) (x : ↥(MeasureTheory.Lp ℂ 2 MeasureTheory.volume)),
  (V t) x = (QIQTH.Fock.OneParticle.boostUnitary (2 * Real.pi * t)) x
```
- **data binders (3):** `m`, `V`, `t`

### `QIQTH.Fock.freeField_oneParticle_hFlux`  ·  *spine*
- policy-clean · kind=thm  [L]
- **conclusion:**
```
HasDerivAt
  (fun t =>
    inner ℂ (MeasureTheory.MemLp.toLp f hf2)
      ((QIQTH.StandardSubspaceModular.modUnitary (QIQTH.Fock.BoostKMS.niceWedgeStandardSubspace m ⋯ ⋯) t)
        (MeasureTheory.MemLp.toLp f hf2)))
  (Complex.I * ↑(2 * Real.pi / hbar * Tkk)) 0
```
- **hypotheses (7)** — name : status [P]/[D]:
```
1. hm [surface] : 0 < m
2. hf2 [surface] : MeasureTheory.MemLp f 2 MeasureTheory.volume
3. hf_int [surface] : MeasureTheory.Integrable f MeasureTheory.volume
4. hfd [surface] : ∀ (x : ℝ), HasDerivAt f (f' x) x
5. hf'_meas [surface] : MeasureTheory.AEStronglyMeasurable f' MeasureTheory.volume
6. hB [surface] : ∀ (x : ℝ), ‖f' x‖ ≤ B
7. hTkk [surface] : 2 * Real.pi / hbar * Tkk = (-(2 * ↑Real.pi * ∫ (θ : ℝ), (starRingEnd ℂ) (f θ) * f' θ)).im
```
- **data binders (6):** `m`, `f`, `f'`, `B`, `hbar`, `Tkk`

### `QIQTH.Fock.freeField_component_hFlux`  ·  *spine*
- policy-clean · uses-spine: `freeField_oneParticle_hFlux` · kind=thm  [L]
- **conclusion:**
```
kd = 2 * Real.pi / hbar * Tkk
```
- **hypotheses (8)** — name : status [P]/[D]:
```
1. hm [surface] : 0 < m
2. hf2 [surface] : MeasureTheory.MemLp f 2 MeasureTheory.volume
3. hf_int [surface] : MeasureTheory.Integrable f MeasureTheory.volume
4. hfd [surface] : ∀ (x : ℝ), HasDerivAt f (f' x) x
5. hf'_meas [surface] : MeasureTheory.AEStronglyMeasurable f' MeasureTheory.volume
6. hB [surface] : ∀ (x : ℝ), ‖f' x‖ ≤ B
7. hTkk [surface] : 2 * Real.pi / hbar * Tkk = (-(2 * ↑Real.pi * ∫ (θ : ℝ), (starRingEnd ℂ) (f θ) * f' θ)).im
8. hbridge [surface] : HasDerivAt
  (fun t =>
    inner ℂ (MeasureTheory.MemLp.toLp f hf2)
      ((QIQTH.StandardSubspaceModular.modUnitary (QIQTH.Fock.BoostKMS.niceWedgeStandardSubspace m ⋯ ⋯) t)
        (MeasureTheory.MemLp.toLp f hf2)))
  (Complex.I * ↑kd) 0
```
- **data binders (7):** `m`, `f`, `f'`, `B`, `hbar`, `kd`, `Tkk`
