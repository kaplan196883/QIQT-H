# QIQT-H state report — GR
*Target 3 — QIQT-H gives the GR field equations (Jacobson route, free KG field)*

_Generated 2026-06-23 21:24 UTC · git `fd82276` · 7 theorems_

## Axiom status
- **Project-specific axioms: 0** (target 0)
- All theorems axiom-free (only `propext`, `Classical.choice`, `Quot.sound`): **YES**

| theorem | axioms |
|---|---|
| `QIQTH.WedgeKMSToGR.qiqt_gr_freefield` | ✓ standard-3 only |
| `QIQTH.WedgeKMSToGR.qiqt_gr_explicit_kg` | ✓ standard-3 only |
| `QIQTH.WedgeKMSToGR.qiqt_gr_from_flux_complete` | ✓ standard-3 only |
| `QIQTH.QiqtToGR.qiqt_bekenstein_gives_gr` | ✓ standard-3 only |
| `QIQTH.Fock.CyclicWitness.oneParticleBW_niceWedge_unconditional` | ✓ standard-3 only |
| `QIQTH.Fock.freeField_oneParticle_hFlux` | ✓ standard-3 only |
| `QIQTH.Fock.freeField_component_hFlux` | ✓ standard-3 only |

## Theorems — facts from Lean

### `QIQTH.WedgeKMSToGR.qiqt_gr_freefield`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
∃ Λ,
  ∀ (x : QIQTH.Curvature.Point 4) (μ ν : Fin 4),
    a * QIQTH.Curvature.kgStress m φ g gi x μ ν = QIQTH.Curvature.einsteinTensor g gi μ ν x + Λ * g x μ ν
```
- **hypotheses (29):**
```
1. hsymm : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), g y a b = g y b a
2. hsymm_gi : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), gi y a b = gi y b a
3. hinv : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), ∑ σ, g y a σ * gi y σ b = if a = b then 1 else 0
4. hCg : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => g y a b
5. hCgi : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => gi y a b
6. hbar0 : hbar ≠ 0
7. heta : η ≠ 0
8. ha : a = 2 * Real.pi / (hbar * η)
9. hφ : ContDiff ℝ ⊤ φ
10. hKG : ∀ (x : QIQTH.Curvature.Point 4), QIQTH.Curvature.boxField φ g gi x = m ^ 2 * φ x
11. hPP : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, P x i k * Pinv x k j = if i = j then 1 else 0
12. hPP' : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, Pinv x i k * P x k j = if i = j then 1 else 0
13. hcong : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), g x i j = ∑ k, ∑ l, P x k i * QIQTH.EinsteinEOS.gm k l * P x l j
14. hS : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (Sf x v) (sd x v) 0
15. hK : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (KE x v) (kd x v) 0
16. hA : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (A x v) (ad x v) 0
17. hbound : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ᶠ (t : ℝ) in nhds 0, Sf x v t ≤ η * A x v t
18. hsat : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → Sf x v 0 = η * A x v 0
19. hDnn : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ (t : ℝ), 0 ≤ KE x v t - Sf x v t
20. hD0 : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → KE x v 0 - Sf x v 0 = 0
21. hmw : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), 0 < mw x v
22. hf2 : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.MemLp (ff x v) 2 MeasureTheory.volume
23. hf_int : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.Integrable (ff x v) MeasureTheory.volume
24. hfd : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (θ : ℝ), HasDerivAt (ff x v) (ff' x v θ) θ
25. hf'_meas : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), MeasureTheory.AEStronglyMeasurable (ff' x v) MeasureTheory.volume
26. hB : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ) (θ : ℝ), ‖ff' x v θ‖ ≤ Bd x v
27. hTkk : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    2 * Real.pi / hbar * QIQTH.EinsteinEOS.BL (QIQTH.Curvature.kgStress m φ g gi x) v =
      (-(2 * ↑Real.pi * ∫ (θ : ℝ), (starRingEnd ℂ) (ff x v θ) * ff' x v θ)).im
28. hbridge : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 →
    HasDerivAt
      (fun t =>
        inner ℂ (MeasureTheory.MemLp.toLp (ff x v) ⋯)
          ((QIQTH.StandardSubspaceModular.modUnitary (QIQTH.Fock.BoostKMS.niceWedgeStandardSubspace (mw x v) ⋯ ⋯) t)
            (MeasureTheory.MemLp.toLp (ff x v) ⋯)))
      (Complex.I * ↑(kd x v)) 0
29. hFocus : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ad x v = QIQTH.EinsteinEOS.BL (fun i j => QIQTH.Curvature.ricci g gi i j x) v
```
- **data binders (19):** `g`, `gi`, `φ`, `m`, `η`, `hbar`, `a`, `P`, `Pinv`, `Sf`, `KE`, `A`, `sd`, `kd`, `ad`, `mw`, `ff`, `ff'`, `Bd`

### `QIQTH.WedgeKMSToGR.qiqt_gr_explicit_kg`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
∃ Λ,
  ∀ (x : QIQTH.Curvature.Point 4) (μ ν : Fin 4),
    a * QIQTH.Curvature.kgStress m φ g gi x μ ν = QIQTH.Curvature.einsteinTensor g gi μ ν x + Λ * g x μ ν
```
- **hypotheses (22):**
```
1. hsymm : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), g y a b = g y b a
2. hsymm_gi : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), gi y a b = gi y b a
3. hinv : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), ∑ σ, g y a σ * gi y σ b = if a = b then 1 else 0
4. hCg : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => g y a b
5. hCgi : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => gi y a b
6. hbar0 : hbar ≠ 0
7. heta : η ≠ 0
8. ha : a = 2 * Real.pi / (hbar * η)
9. hφ : ContDiff ℝ ⊤ φ
10. hKG : ∀ (x : QIQTH.Curvature.Point 4), QIQTH.Curvature.boxField φ g gi x = m ^ 2 * φ x
11. hPP : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, P x i k * Pinv x k j = if i = j then 1 else 0
12. hPP' : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, Pinv x i k * P x k j = if i = j then 1 else 0
13. hcong : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), g x i j = ∑ k, ∑ l, P x k i * QIQTH.EinsteinEOS.gm k l * P x l j
14. hS : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (Sf x v) (sd x v) 0
15. hK : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (KE x v) (kd x v) 0
16. hA : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (A x v) (ad x v) 0
17. hbound : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ᶠ (t : ℝ) in nhds 0, Sf x v t ≤ η * A x v t
18. hsat : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → Sf x v 0 = η * A x v 0
19. hDnn : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ (t : ℝ), 0 ≤ KE x v t - Sf x v t
20. hD0 : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → KE x v 0 - Sf x v 0 = 0
21. hKMS : QIQTH.WedgeKMSToGR.WedgeKMSFlux_complete g (QIQTH.Curvature.kgStress m φ g gi) kd hbar
22. hFocus : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ad x v = QIQTH.EinsteinEOS.BL (fun i j => QIQTH.Curvature.ricci g gi i j x) v
```
- **data binders (15):** `g`, `gi`, `φ`, `m`, `η`, `hbar`, `a`, `P`, `Pinv`, `Sf`, `KE`, `A`, `sd`, `kd`, `ad`

### `QIQTH.WedgeKMSToGR.qiqt_gr_from_flux_complete`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
∃ Λ,
  ∀ (x : QIQTH.Curvature.Point 4) (μ ν : Fin 4), a * T x μ ν = QIQTH.Curvature.einsteinTensor g gi μ ν x + Λ * g x μ ν
```
- **hypotheses (23):**
```
1. hsymm : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), g y a b = g y b a
2. hsymm_gi : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), gi y a b = gi y b a
3. hinv : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), ∑ σ, g y a σ * gi y σ b = if a = b then 1 else 0
4. hCg : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => g y a b
5. hCgi : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => gi y a b
6. hbar0 : hbar ≠ 0
7. heta : η ≠ 0
8. ha : a = 2 * Real.pi / (hbar * η)
9. hT_symm : ∀ (x : QIQTH.Curvature.Point 4) (a' b : Fin 4), T x a' b = T x b a'
10. hPP : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, P x i k * Pinv x k j = if i = j then 1 else 0
11. hPP' : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, Pinv x i k * P x k j = if i = j then 1 else 0
12. hcong : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), g x i j = ∑ k, ∑ l, P x k i * QIQTH.EinsteinEOS.gm k l * P x l j
13. hS : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (Sf x v) (sd x v) 0
14. hK : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (KE x v) (kd x v) 0
15. hA : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (A x v) (ad x v) 0
16. hbound : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ᶠ (t : ℝ) in nhds 0, Sf x v t ≤ η * A x v t
17. hsat : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → Sf x v 0 = η * A x v 0
18. hDnn : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ (t : ℝ), 0 ≤ KE x v t - Sf x v t
19. hD0 : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → KE x v 0 - Sf x v 0 = 0
20. hflux : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → kd x v = 2 * Real.pi / hbar * QIQTH.EinsteinEOS.BL (T x) v
21. hFocus : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ad x v = QIQTH.EinsteinEOS.BL (fun i j => QIQTH.Curvature.ricci g gi i j x) v
22. hreg : ∀ (f : QIQTH.Curvature.Point 4 → ℝ),
  (∀ (y : QIQTH.Curvature.Point 4) (a' b : Fin 4), a * T y a' b = QIQTH.Curvature.ricci g gi a' b y + f y * g y a' b) →
    (∀ (x : QIQTH.Curvature.Point 4) (ρ : Fin 4), QIQTH.Curvature.PdiffAt f ρ x) ∧
      Differentiable ℝ fun y => f y + 1 / 2 * QIQTH.Curvature.scalarCurv g gi y
23. conserv : ∀ (x : QIQTH.Curvature.Point 4) (ν : Fin 4), QIQTH.Curvature.div02 g gi (fun y a' b => a * T y a' b) ν x = 0
```
- **data binders (14):** `g`, `gi`, `T`, `η`, `hbar`, `a`, `P`, `Pinv`, `Sf`, `KE`, `A`, `sd`, `kd`, `ad`

### `QIQTH.QiqtToGR.qiqt_bekenstein_gives_gr`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
∃ Λ,
  ∀ (x : QIQTH.Curvature.Point 4) (μ ν : Fin 4), a * T x μ ν = QIQTH.Curvature.einsteinTensor g gi μ ν x + Λ * g x μ ν
```
- **hypotheses (23):**
```
1. hsymm : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), g y a b = g y b a
2. hsymm_gi : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), gi y a b = gi y b a
3. hinv : ∀ (y : QIQTH.Curvature.Point 4) (a b : Fin 4), ∑ σ, g y a σ * gi y σ b = if a = b then 1 else 0
4. hCg : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => g y a b
5. hCgi : ∀ (a b : Fin 4), ContDiff ℝ ⊤ fun y => gi y a b
6. hbar0 : hbar ≠ 0
7. heta : η ≠ 0
8. ha : a = 2 * Real.pi / (hbar * η)
9. hT_symm : ∀ (x : QIQTH.Curvature.Point 4) (a' b : Fin 4), T x a' b = T x b a'
10. hPP : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, P x i k * Pinv x k j = if i = j then 1 else 0
11. hPP' : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), ∑ k, Pinv x i k * P x k j = if i = j then 1 else 0
12. hcong : ∀ (x : QIQTH.Curvature.Point 4) (i j : Fin 4), g x i j = ∑ k, ∑ l, P x k i * QIQTH.EinsteinEOS.gm k l * P x l j
13. hS : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (S x v) (sd x v) 0
14. hK : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (KE x v) (kd x v) 0
15. hA : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → HasDerivAt (A x v) (ad x v) 0
16. hbound : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ᶠ (t : ℝ) in nhds 0, S x v t ≤ η * A x v t
17. hsat : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → S x v 0 = η * A x v 0
18. hDnn : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → ∀ (t : ℝ), 0 ≤ KE x v t - S x v t
19. hD0 : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ), QIQTH.EinsteinEOS.BL (g x) v = 0 → KE x v 0 - S x v 0 = 0
20. hFlux : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → kd x v = 2 * Real.pi / hbar * QIQTH.EinsteinEOS.BL (T x) v
21. hFocus : ∀ (x : QIQTH.Curvature.Point 4) (v : Fin 4 → ℝ),
  QIQTH.EinsteinEOS.BL (g x) v = 0 → ad x v = QIQTH.EinsteinEOS.BL (fun i j => QIQTH.Curvature.ricci g gi i j x) v
22. hreg : ∀ (f : QIQTH.Curvature.Point 4 → ℝ),
  (∀ (y : QIQTH.Curvature.Point 4) (a' b : Fin 4), a * T y a' b = QIQTH.Curvature.ricci g gi a' b y + f y * g y a' b) →
    (∀ (x : QIQTH.Curvature.Point 4) (ρ : Fin 4), QIQTH.Curvature.PdiffAt f ρ x) ∧
      Differentiable ℝ fun y => f y + 1 / 2 * QIQTH.Curvature.scalarCurv g gi y
23. conserv : ∀ (x : QIQTH.Curvature.Point 4) (ν : Fin 4), QIQTH.Curvature.div02 g gi (fun y a' b => a * T y a' b) ν x = 0
```
- **data binders (14):** `g`, `gi`, `T`, `η`, `hbar`, `a`, `P`, `Pinv`, `S`, `KE`, `A`, `sd`, `kd`, `ad`

### `QIQTH.Fock.CyclicWitness.oneParticleBW_niceWedge_unconditional`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
QIQTH.StandardSubspaceModular.modUnitary (QIQTH.Fock.BoostKMS.niceWedgeStandardSubspace m ⋯ ⋯) t = V t
```
- **hypotheses (2):**
```
1. hm : 0 < m
2. hVboost : ∀ (t : ℝ) (x : ↥(MeasureTheory.Lp ℂ 2 MeasureTheory.volume)),
  (V t) x = (QIQTH.Fock.OneParticle.boostUnitary (2 * Real.pi * t)) x
```
- **data binders (3):** `m`, `V`, `t`

### `QIQTH.Fock.freeField_oneParticle_hFlux`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
HasDerivAt
  (fun t =>
    inner ℂ (MeasureTheory.MemLp.toLp f hf2)
      ((QIQTH.StandardSubspaceModular.modUnitary (QIQTH.Fock.BoostKMS.niceWedgeStandardSubspace m ⋯ ⋯) t)
        (MeasureTheory.MemLp.toLp f hf2)))
  (Complex.I * ↑(2 * Real.pi / hbar * Tkk)) 0
```
- **hypotheses (7):**
```
1. hm : 0 < m
2. hf2 : MeasureTheory.MemLp f 2 MeasureTheory.volume
3. hf_int : MeasureTheory.Integrable f MeasureTheory.volume
4. hfd : ∀ (x : ℝ), HasDerivAt f (f' x) x
5. hf'_meas : MeasureTheory.AEStronglyMeasurable f' MeasureTheory.volume
6. hB : ∀ (x : ℝ), ‖f' x‖ ≤ B
7. hTkk : 2 * Real.pi / hbar * Tkk = (-(2 * ↑Real.pi * ∫ (θ : ℝ), (starRingEnd ℂ) (f θ) * f' θ)).im
```
- **data binders (6):** `m`, `f`, `f'`, `B`, `hbar`, `Tkk`

### `QIQTH.Fock.freeField_component_hFlux`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
kd = 2 * Real.pi / hbar * Tkk
```
- **hypotheses (8):**
```
1. hm : 0 < m
2. hf2 : MeasureTheory.MemLp f 2 MeasureTheory.volume
3. hf_int : MeasureTheory.Integrable f MeasureTheory.volume
4. hfd : ∀ (x : ℝ), HasDerivAt f (f' x) x
5. hf'_meas : MeasureTheory.AEStronglyMeasurable f' MeasureTheory.volume
6. hB : ∀ (x : ℝ), ‖f' x‖ ≤ B
7. hTkk : 2 * Real.pi / hbar * Tkk = (-(2 * ↑Real.pi * ∫ (θ : ℝ), (starRingEnd ℂ) (f θ) * f' θ)).im
8. hbridge : HasDerivAt
  (fun t =>
    inner ℂ (MeasureTheory.MemLp.toLp f hf2)
      ((QIQTH.StandardSubspaceModular.modUnitary (QIQTH.Fock.BoostKMS.niceWedgeStandardSubspace m ⋯ ⋯) t)
        (MeasureTheory.MemLp.toLp f hf2)))
  (Complex.I * ↑kd) 0
```
- **data binders (7):** `m`, `f`, `f'`, `B`, `hbar`, `kd`, `Tkk`

## Current state (factual)
- Theorems present: **7/7**
- All axiom-free: **YES**
- Total Prop-hypotheses across the spine: **114**
- Per-theorem hypothesis counts: `qiqt_gr_freefield`=29, `qiqt_gr_explicit_kg`=22, `qiqt_gr_from_flux_complete`=23, `qiqt_bekenstein_gives_gr`=23, `oneParticleBW_niceWedge_unconditional`=2, `freeField_oneParticle_hFlux`=7, `freeField_component_hFlux`=8
