# QIQT-H state report — LORENTZ
*Target 2 — QIQT-H compatible with Lorentz (covariance spine + selector no-go)*

_Generated 2026-06-23 21:26 UTC · git `fd82276` · 11 theorems_

## Axiom status
- **Project-specific axioms: 0** (target 0)
- All theorems axiom-free (only `propext`, `Classical.choice`, `Quot.sound`): **YES**

| theorem | axioms |
|---|---|
| `QIQTH.LorentzSelection.evaluation_covariance` | ✓ standard-3 only |
| `QIQTH.LorentzSelectionStrong.group_evaluation_covariance` | ✓ standard-3 only |
| `QIQTH.LorentzSelectionStrong.upvm_covariant_probability` | ✓ standard-3 only |
| `QIQTH.FreeFieldTypicality.freeFieldMeasure_boost_invariant` | ✓ standard-3 only |
| `QIQTH.BHTypicalityMeasure.bh_typicalityMeasure_exists` | ✓ standard-3 only |
| `QIQTH.Fock.fock_typicalityMeasure_exists` | ✓ standard-3 only |
| `QIQTH.ContinuumSelection.continuum_volume_selects` | ✓ standard-3 only |
| `QIQTH.Theorem7.Setup.no_signaling` | ✓ standard-3 only |
| `QIQTH.NoSignalingGeneral.bipartite_no_signaling` | ✓ standard-3 only |
| `QIQTH.CovariantGluing.no_covariant_selector` | ✓ standard-3 only |
| `QIQTH.CovariantGluing.bool_swap_no_selector` | ✓ standard-3 only |

## Theorems — facts from Lean

### `QIQTH.LorentzSelection.evaluation_covariance`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
QIQTH.LorentzSelection.selector (QIQTH.LorentzSelection.actSection g lam) (g.act D) =
  (g.γ D) (QIQTH.LorentzSelection.selector lam D)
```
- **hypotheses (0):**
  *(none)*
- **data binders (6):** `Diam`, `inst._@.QIQTH.LorentzSelection.2352432197._hygCtx._hyg.3`, `P`, `g`, `lam`, `D`

### `QIQTH.LorentzSelectionStrong.group_evaluation_covariance`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
QIQTH.LorentzSelection.selector (QIQTH.LorentzSelection.actSection (A.toPoincare g) lam) ((A.act g) D) =
  (A.γ g D) (QIQTH.LorentzSelection.selector lam D)
```
- **hypotheses (0):**
  *(none)*
- **data binders (9):** `Diam`, `inst._@.QIQTH.LorentzSelectionStrong.743728840._hygCtx._hyg.3`, `G`, `inst._@.QIQTH.LorentzSelectionStrong.743728840._hygCtx._hyg.7`, `P`, `A`, `lam`, `g`, `D`

### `QIQTH.LorentzSelectionStrong.upvm_covariant_probability`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
(∀ (x : P.X D), 0 ≤ QIQTH.LorentzSelectionStrong.ubornω B.toUniformBornData D x) ∧
  Finset.univ.sum (QIQTH.LorentzSelectionStrong.ubornω B.toUniformBornData D) = 1 ∧
    ∀ (x : P.X D),
      QIQTH.LorentzSelectionStrong.ubornω B.toUniformBornData ((A.act g) D) ((A.γ g D) x) =
        QIQTH.LorentzSelectionStrong.ubornω B.toUniformBornData D x
```
- **hypotheses (0):**
  *(none)*
- **data binders (10):** `Diam`, `inst._@.QIQTH.LorentzSelectionStrong.891917837._hygCtx._hyg.3`, `G`, `inst._@.QIQTH.LorentzSelectionStrong.891917837._hygCtx._hyg.7`, `P`, `A`, `B`, `C`, `g`, `D`

### `QIQTH.FreeFieldTypicality.freeFieldMeasure_boost_invariant`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
MeasureTheory.Measure.map (QIQTH.FreeFieldTypicality.diagBoost e) (QIQTH.FreeFieldTypicality.freeFieldMeasure ν) =
  QIQTH.FreeFieldTypicality.freeFieldMeasure ν
```
- **hypotheses (2):**
```
1. inst._@.QIQTH.FreeFieldTypicality.4290387588._hygCtx._hyg.15 : MeasureTheory.IsProbabilityMeasure ν
2. hν : MeasureTheory.Measure.map (QIQTH.FreeFieldTypicality.boostMap e) ν = ν
```
- **data binders (5):** `m`, `inst._@.QIQTH.FreeFieldTypicality.4290387588._hygCtx._hyg.3`, `inst._@.QIQTH.FreeFieldTypicality.4290387588._hygCtx._hyg.6`, `ν`, `e`

### `QIQTH.BHTypicalityMeasure.bh_typicalityMeasure_exists`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
∃ μ,
  MeasureTheory.IsProbabilityMeasure μ ∧
    (QIQTH.BHTypicalityMeasure.diagNet hb hp hsum hp1 g).toFiniteMarginals.IsLimit μ
```
- **hypotheses (8):**
```
1. inst._@.QIQTH.BHTypicalityMeasure.2998898123._hygCtx._hyg.36 : ∀ (i : ι), MeasurableSingletonClass (α i)
2. inst._@.QIQTH.BHTypicalityMeasure.2998898123._hygCtx._hyg.56 : CompleteSpace H
3. inst._@.QIQTH.BHTypicalityMeasure.2998898123._hygCtx._hyg.79 : ∀ (i : ι), DiscreteTopology (α i)
4. inst._@.QIQTH.BHTypicalityMeasure.2998898123._hygCtx._hyg.88 : ∀ (i : ι), Finite (α i)
5. hb : Orthonormal ℂ ⇑b
6. hp : ∀ (i : κ), 0 ≤ p i
7. hsum : Summable p
8. hp1 : ∑' (i : κ), p i = 1
```
- **data binders (14):** `ι`, `inst._@.QIQTH.BHTypicalityMeasure.2998898123._hygCtx._hyg.3`, `α`, `inst._@.QIQTH.BHTypicalityMeasure.2998898123._hygCtx._hyg.9`, `inst._@.QIQTH.BHTypicalityMeasure.2998898123._hygCtx._hyg.18`, `inst._@.QIQTH.BHTypicalityMeasure.2998898123._hygCtx._hyg.27`, `κ`, `H`, `inst._@.QIQTH.BHTypicalityMeasure.2998898123._hygCtx._hyg.47`, `inst._@.QIQTH.BHTypicalityMeasure.2998898123._hygCtx._hyg.50`, `b`, `p`, `inst._@.QIQTH.BHTypicalityMeasure.2998898123._hygCtx._hyg.70`, `g`

### `QIQTH.Fock.fock_typicalityMeasure_exists`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
∃ μ, MeasureTheory.IsProbabilityMeasure μ ∧ (QIQTH.Fock.fockVacuumNet g).toFiniteMarginals.IsLimit μ
```
- **hypotheses (3):**
```
1. inst._@.QIQTH.Fock.FockTypicality.377538603._hygCtx._hyg.36 : ∀ (i : ι), MeasurableSingletonClass (α i)
2. inst._@.QIQTH.Fock.FockTypicality.377538603._hygCtx._hyg.64 : ∀ (i : ι), DiscreteTopology (α i)
3. inst._@.QIQTH.Fock.FockTypicality.377538603._hygCtx._hyg.73 : ∀ (i : ι), Finite (α i)
```
- **data binders (11):** `ι`, `inst._@.QIQTH.Fock.FockTypicality.377538603._hygCtx._hyg.3`, `α`, `inst._@.QIQTH.Fock.FockTypicality.377538603._hygCtx._hyg.9`, `inst._@.QIQTH.Fock.FockTypicality.377538603._hygCtx._hyg.18`, `inst._@.QIQTH.Fock.FockTypicality.377538603._hygCtx._hyg.27`, `H`, `inst._@.QIQTH.Fock.FockTypicality.377538603._hygCtx._hyg.46`, `inst._@.QIQTH.Fock.FockTypicality.377538603._hygCtx._hyg.49`, `inst._@.QIQTH.Fock.FockTypicality.377538603._hygCtx._hyg.55`, `g`

### `QIQTH.ContinuumSelection.continuum_volume_selects`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
MeasureTheory.volume {seed | QIQTH.SelectionEvent.selects (QIQTH.ContinuumSelection.contWeights S ξ s) seed k} =
  ENNReal.ofReal (QIQTH.ContinuumSelection.contWeights S ξ s k)
```
- **hypotheses (1):**
```
1. inst._@.QIQTH.ContinuumSelection.1070711794._hygCtx._hyg.12 : CompleteSpace H
```
- **data binders (8):** `H`, `inst._@.QIQTH.ContinuumSelection.1070711794._hygCtx._hyg.3`, `inst._@.QIQTH.ContinuumSelection.1070711794._hygCtx._hyg.6`, `S`, `ξ`, `n`, `s`, `k`

### `QIQTH.Theorem7.Setup.no_signaling`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
S.P x a y = S.PAlice x a
```
- **hypotheses (0):**
  *(none)*
- **data binders (4):** `S`, `x`, `a`, `y`

### `QIQTH.NoSignalingGeneral.bipartite_no_signaling`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
∑ b, (ρ * Matrix.kroneckerMap (fun x1 x2 => x1 * x2) E (F b)).trace =
  (ρ * Matrix.kroneckerMap (fun x1 x2 => x1 * x2) E 1).trace
```
- **hypotheses (1):**
```
1. hF : ∑ b, F b = 1
```
- **data binders (11):** `d₁`, `d₂`, `inst._@.QIQTH.NoSignalingGeneral.2292800562._hygCtx._hyg.4`, `inst._@.QIQTH.NoSignalingGeneral.2292800562._hygCtx._hyg.7`, `inst._@.QIQTH.NoSignalingGeneral.2292800562._hygCtx._hyg.10`, `inst._@.QIQTH.NoSignalingGeneral.2292800562._hygCtx._hyg.13`, `β`, `inst._@.QIQTH.NoSignalingGeneral.2292800562._hygCtx._hyg.17`, `ρ`, `E`, `F`

### `QIQTH.CovariantGluing.no_covariant_selector`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
False
```
- **hypotheses (3):**
```
1. equiv : ∀ (Φ : State), σ (actS Φ) = actH (σ Φ)
2. hΦ : actS Φ = Φ
3. hno : ∀ (h : History), actH h ≠ h
```
- **data binders (6):** `State`, `History`, `actS`, `actH`, `σ`, `Φ`

### `QIQTH.CovariantGluing.bool_swap_no_selector`
- **axioms:** ✓ standard-3 only
- **conclusion:**
```
False
```
- **hypotheses (1):**
```
1. equiv : ∀ (u : Unit), σ u = !σ u
```
- **data binders (1):** `σ`

## Current state (factual)
- Theorems present: **11/11**
- All axiom-free: **YES**
- Total Prop-hypotheses across the spine: **19**
- Per-theorem hypothesis counts: `evaluation_covariance`=0, `group_evaluation_covariance`=0, `upvm_covariant_probability`=0, `freeFieldMeasure_boost_invariant`=2, `bh_typicalityMeasure_exists`=8, `fock_typicalityMeasure_exists`=3, `continuum_volume_selects`=1, `no_signaling`=0, `bipartite_no_signaling`=1, `no_covariant_selector`=3, `bool_swap_no_selector`=1
