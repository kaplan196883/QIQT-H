# Track state — GR field equations
*Target 3 — QIQT-H gives the GR field equations (Jacobson route, free KG field)*

_Generated 2026-06-24 02:33 UTC · git `1559a17` · 7 theorems · tool lean_track_ · provenance: [L]=Lean fact [P]=Lean-checked prober [D]=derived [C]=curation_

## Axiom status  [L]
- Project-specific (non-standard) axioms: **0**
- All policy-clean (axioms ⊆ allowed `propext, Classical.choice, Quot.sound`): **YES**
- All *literally* axiom-free (no axioms at all): **NO**

## Assumption surface (capstone)  [P]/[D]

**`QIQTH.WedgeKMSToGR.qiqt_gr_freefield`** — 29 surface items (29 distinct after dedup; conclusion: `∃ Λ,
  ∀ (x : QIQTH.Curvature.Point 4) (μ ν : Fin 4),
    a * QIQTH.Curvature.kgStress m φ`):
  - `hsymm` : `∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), g y a b = g y b a` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants** [C:regularity]
  - `hsymm_gi` : `∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), gi y a b = gi y b a` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants** [C:regularity]
  - `hinv` : `∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), ∑ σ, g y a σ * gi y σ b = if a = b then 1 else 0` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants** [C:regularity]
  - `hCg` : `∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => g y a b` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants** [C:regularity]
  - `hCgi` : `∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => gi y a b` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants** [C:regularity]
  - `hbar0` : `hbar ≠ 0` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants** [C:regularity]
  - `heta` : `η ≠ 0` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants** [C:regularity]
  - `ha` : `a = 2 * Real.pi / (hbar * η)` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants** [C:regularity]
  - `hφ` : `ContDiff ℝ ⊤ φ` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants** [C:regularity]
  - `hKG` : `∀ (x : QIQTH.Curvature.Point 4), QIQTH.Curvature.boxField φ g gi x = m ^ 2 * φ x` · **PHYSICS — genuine input (EOM / Clausius / focusing / localization)** [C:physics-floor]
  - `hPP` : `∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, P x i k * Pinv x k j = if i = j then 1 else 0` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants** [C:regularity]
  - `hPP'` : `∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, Pinv x i k * P x k j = if i = j then 1 else 0` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants** [C:regularity]
  - `hcong` : `∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), g x i j = ∑ k, ∑ l, P x k i * QIQTH.EinsteinEOS.gm k l * P x l j` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants** [C:regularity]
  - `hS` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (Sf x v) (sd x v) 0` · **SETUP — per-generator derivative existence / null-congruence kinematics** [C:setup]
  - `hK` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (KE x v) (kd x v) 0` · **SETUP — per-generator derivative existence / null-congruence kinematics** [C:setup]
  - `hA` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (A x v) (ad x v) 0` · **SETUP — per-generator derivative existence / null-congruence kinematics** [C:setup]
  - `hbound` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ᶠ (t : ℝ) in nhds 0, Sf x v t ≤ η * A x v t` · **PHYSICS — genuine input (EOM / Clausius / focusing / localization)** [C:physics-floor]
  - `hsat` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → Sf x v 0 = η * A x v 0` · **PHYSICS — genuine input (EOM / Clausius / focusing / localization)** [C:physics-floor]
  - `hDnn` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ (t : ℝ), 0 ≤ KE x v t - Sf x v t` · **PHYSICS — genuine input (EOM / Clausius / focusing / localization)** [C:physics-floor]
  - `hD0` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → KE x v 0 - Sf x v 0 = 0` · **PHYSICS — genuine input (EOM / Clausius / focusing / localization)** [C:physics-floor]
  - `hmw` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), 0 < mw x v` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants** [C:regularity]
  - `hf2` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.MemLp (ff x v) 2 MeasureTheory.volume` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants** [C:regularity]
  - `hf_int` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.Integrable (ff x v) MeasureTheory.volume` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants** [C:regularity]
  - `hfd` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (θ : ℝ), HasDerivAt (ff x v) (ff' x v θ) θ` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants** [C:regularity]
  - `hf'_meas` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.AEStronglyMeasurable (ff' x v) MeasureTheory.volume` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants** [C:regularity]
  - `hB` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (θ : ℝ), ‖ff' x v θ‖ ≤ Bd x v` · **REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants** [C:regularity]
  - `hTkk` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    2 * Real.pi / hbar * QIQTH.EinsteinEOS.BL (QIQTH.Curvature.kgStress m φ g gi x) v =
      (-(2 * ↑Real.pi * ∫ (θ : ℝ), (starRingEnd ℂ) (ff x v θ) * ff' x v θ)).im` · **PHYSICS — genuine input (EOM / Clausius / focusing / localization)** [C:physics-floor]
  - `hbridge` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    HasDerivAt
      (fun t =>
        inner ℂ (MeasureTheory.MemLp.toLp (ff x v) ⋯)
          ((QIQTH.StandardSubspaceModular.modUnitary (QIQTH.Fock.BoostKMS.niceWedgeStandardSubspace (mw x v) ⋯ ⋯) t)
            (MeasureTheory.MemLp.toLp (ff x v) ⋯)))
      (Complex.I * ↑(kd x v)) 0` · **PHYSICS — genuine input (EOM / Clausius / focusing / localization)** [C:physics-floor]
  - `hFocus` : `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ad x v = QIQTH.EinsteinEOS.BL (fun i j => QIQTH.Curvature.ricci g gi i j x) v` · **PHYSICS — genuine input (EOM / Clausius / focusing / localization)** [C:physics-floor]

## Curated piles  [C] *(author labels — NOT a Lean fact)*

**PHYSICS — genuine input (EOM / Clausius / focusing / localization)** (14 distinct)
  - `2 * Real.pi / hbar * Tkk = (-(2 * ↑Real.pi * ∫ (θ : ℝ), (starRingEnd ℂ) (f θ) * f' θ)).im`
  - `HasDerivAt
  (fun t =>
    inner ℂ (MeasureTheory.MemLp.toLp f hf2)
      ((QIQTH.StandardSubspaceModular.modUnitary (QIQTH.Fock.BoostKMS.niceWedgeStandardSubspace m ⋯ ⋯) t)
        (MeasureTheory.MemLp.toLp f hf2)))
  (Complex.I * ↑kd) 0`
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
  - `∀ (x : QIQTH.Curvature.Point 4), QIQTH.Curvature.boxField φ g gi x = m ^ 2 * φ x`

**REGULARITY/BACKGROUND — metric, frame, mode, smoothness, constants** (26 distinct)
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
  - `∀ (x : QIQTH.Curvature.Point 4) (a' b : Fin 4), T x a' b = T x b a'`
  - `∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), g x i j = ∑ k, ∑ l, P x k i * QIQTH.EinsteinEOS.gm k l * P x l j`
  - `∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, P x i k * Pinv x k j = if i = j then 1 else 0`
  - `∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, Pinv x i k * P x k j = if i = j then 1 else 0`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (θ : ℝ), HasDerivAt (ff x v) (ff' x v θ) θ`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (θ : ℝ), ‖ff' x v θ‖ ≤ Bd x v`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), 0 < mw x v`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.AEStronglyMeasurable (ff' x v) MeasureTheory.volume`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.Integrable (ff x v) MeasureTheory.volume`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.MemLp (ff x v) 2 MeasureTheory.volume`
  - `∀ (x : QIQTH.Curvature.Point 4) (ν : Fin 4), QIQTH.Curvature.div02 g gi (fun y a' b => a * T y a' b) ν x = 0`
  - `∀ (x : ℝ), HasDerivAt f (f' x) x`
  - `∀ (x : ℝ), ‖f' x‖ ≤ B`
  - `∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), g y a b = g y b a`
  - `∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), gi y a b = gi y b a`
  - `∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), ∑ σ, g y a σ * gi y σ b = if a = b then 1 else 0`

**SETUP — per-generator derivative existence / null-congruence kinematics** (4 distinct)
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (A x v) (ad x v) 0`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (KE x v) (kd x v) 0`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (S x v) (sd x v) 0`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (Sf x v) (sd x v) 0`

**(uncategorised surface hypotheses — 4)** *(no rule matched)*
  - `0 < m`
  - `QIQTH.WedgeKMSToGR.WedgeKMSFlux_complete g (QIQTH.Curvature.kgStress m φ g gi) kd hbar`
  - `∀ (t : ℝ) (x : ↥(MeasureTheory.Lp ℂ 2 MeasureTheory.volume)),
  (V t) x = (QIQTH.Fock.OneParticle.boostUnitary (2 * Real.pi * t)) x`
  - `∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → kd x v = 2 * Real.pi / hbar * QIQTH.EinsteinEOS.BL (T x) v`

## Per-theorem facts  [L]/[P]/[D]

### `QIQTH.WedgeKMSToGR.qiqt_gr_freefield`  ·  *capstone*
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
