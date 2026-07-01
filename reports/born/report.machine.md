# Track state — Born rule
*Target 1 — QIQT-H compatible with Born (spine + no-go audits)*

_Generated 2026-07-01 11:49 UTC · git `6196e02` · 13 theorems · tool lean_track_ · provenance: [L]=Lean fact [P]=Lean-checked prober [D]=derived [C]=curation_

## Axiom status  [L]
- Project-specific (non-standard) axioms: **0**
- All policy-clean (axioms ⊆ allowed `propext, Classical.choice, Quot.sound`): **YES**
- All *literally* axiom-free (no axioms at all): **NO**

## Assumption surface (capstone)  [P]/[D]

**`QIQTH.BornJoinGleason.finite_noCollapseBorn_fromNoncontextuality`** — 12 surface items (12 distinct after dedup; conclusion: `∃ ρ,
  ρ.PosSemidef ∧
    ρ.trace = 1 ∧
      (∀ (ω : E.Ω), ∃! h, ∀ (t : Fin n), ∃ r ∈ (E.`):
  - `E.p_nonneg` : `∀ (k : Fin m), 0 ≤ p k` · **BRIDGE — positivity / normalization / ray-certainty** [C:bridge-positivity-name]
  - `E.p_sum` : `∑ k, p k = 1` · **SETUP — independence / completeness / probability vector** [C:setup-type]
  - `E.oneSite` : `∀ (t : Fin n) (a : Fin m), P.massSet {ω | (V ω t).actualValue = a} = p a` · **BRIDGE — additivity / non-contextuality (the Born-strength premise)** [C:bridge-additivity-name]
  - `E.indep` : `∀ (h : Fin n → Fin m),
  P.massSet {ω | (fun t => (V ω t).actualValue) = h} = ∏ t, P.massSet {ω | (V ω t).actualValue = h t}` · **SETUP — independence / completeness / probability vector** [C:setup-type]
  - `M.normalized` : `μ 1 = 1` · **BRIDGE — positivity / normalization / ray-certainty** [C:bridge-positivity-name]
  - `M.nonneg` : `∀ (E : Matrix (Fin d) (Fin d) ℂ), QIQTH.EffectGleason.IsEffect E → 0 ≤ μ E` · **BRIDGE — positivity / normalization / ray-certainty** [C:bridge-positivity-name]
  - `M.additive` : `∀ (E F : Matrix (Fin d) (Fin d) ℂ),
  QIQTH.EffectGleason.IsEffect E →
    QIQTH.EffectGleason.IsEffect F → QIQTH.EffectGleason.IsEffect (E + F) → μ (E + F) = μ E + μ F` · **BRIDGE — additivity / non-contextuality (the Born-strength premise)** [C:bridge-additivity-name]
  - `hP` : `∀ (a : Fin m), QIQTH.EffectGleason.IsEffect (P a)`
  - `hcal` : `∀ (a : Fin m), M.μ (P a) = E.p a` · **BRIDGE — additivity / non-contextuality (the Born-strength premise)** [C:bridge-additivity-name]
  - `k.isLt` : `val < n`
  - `hε` : `0 < ε`
  - `hn` : `0 < n`

## Curated piles  [C] *(author labels — NOT a Lean fact)*

**BRIDGE — additivity / non-contextuality (the Born-strength premise)** (7 distinct)
  - `∀ (A B : Matrix n n ℂ), w (A + B) = w A + w B`
  - `∀ (E F : Matrix (Fin d) (Fin d) ℂ),
  QIQTH.EffectGleason.IsEffect E →
    QIQTH.EffectGleason.IsEffect F → QIQTH.EffectGleason.IsEffect (E + F) → μ (E + F) = μ E + μ F`
  - `∀ (a : Fin m), M.μ (P a) = E.p a`
  - `∀ (a : Fin n → Fin m) (S : Finset (Fin n → Fin m)), a ∉ S → μ (insert a S) = μ {a} + μ S`
  - `∀ (c : ℂ) (A : Matrix n n ℂ), w (c • A) = c * w A`
  - `∀ (t : Fin n) (a : Fin m), P.massSet {ω | (V ω t).actualValue = a} = p a`
  - `∀ (x y : M), toZeroHom.toFun (x + y) = toZeroHom.toFun x + toZeroHom.toFun y`

**BRIDGE — positivity / normalization / ray-certainty** (11 distinct)
  - `star ψ ⬝ᵥ ψ = 1`
  - `w (Matrix.vecMulVec ψ (star ψ)) = 1`
  - `w 1 = 1`
  - `μ 1 = 1`
  - `ρ.PosSemidef`
  - `∀ (A : Matrix n n ℂ), QIQTH.GleasonSelector.NonnegC (w (A.conjTranspose * A))`
  - `∀ (E : Matrix (Fin d) (Fin d) ℂ), QIQTH.EffectGleason.IsEffect E → 0 ≤ μ E`
  - `∀ (i : Fin m), 0 ≤ p i`
  - `∀ (k : Fin m), (E k).PosSemidef`
  - `∀ (k : Fin m), 0 ≤ p k`
  - `∀ (γ : Γ), 0 ≤ μ γ`

**SETUP — independence / completeness / probability vector** (7 distinct)
  - `∀ (h : Fin n → Fin m),
  P.massSet {ω | (fun t => (V ω t).actualValue) = h} = ∏ t, P.massSet {ω | (V ω t).actualValue = h t}`
  - `∀ (ω : Fin n → Fin m), μ {ω} = ∏ t, QIQTH.BornTypicalityQuantum.bornProb ρ E (ω t)`
  - `∑ i, p i = 1`
  - `∑ j, w j = 1`
  - `∑ k, c k ^ 2 = 1`
  - `∑ k, p k = 1`
  - `∑ γ, μ γ = 1`

**(uncategorised surface hypotheses — 11)** *(no rule matched)*
  - `0 < N`
  - `0 < n`
  - `0 < ε`
  - `Continuous ⇑f`
  - `Function.Surjective outcome`
  - `QIQTH.RecordGleason.Decoherent ψ C`
  - `c 0 ≠ 0`
  - `c 1 ≠ 0`
  - `f 1 ≠ 0`
  - `μ ∅ = 0`
  - `∀ (a : Fin m), QIQTH.EffectGleason.IsEffect (P a)`

## Per-theorem facts  [L]/[P]/[D]

### `QIQTH.BornJoinGleason.finite_noCollapseBorn_fromNoncontextuality`  ·  *capstone*
- policy-clean · uses-spine: `finite_noCollapseBornRepresentation` · kind=thm  [L]
- **conclusion:**
```
∃ ρ,
  ρ.PosSemidef ∧
    ρ.trace = 1 ∧
      (∀ (ω : E.Ω), ∃! h, ∀ (t : Fin n), ∃ r ∈ (E.V ω t).config.active, (E.V ω t).ctx.valueOf r = h t) ∧
        (∀ (a : Fin m), E.p a = (ρ * P a).trace.re) ∧
          (∀ (h : Fin n → Fin m), E.P.massSet {ω | E.actualHist ω = h} = QIQTH.BornTypicalityFinite.w E.p h) ∧
            E.P.massSet {ω | (↑n * ε) ^ 2 ≤ (QIQTH.BornTypicalityFinite.count k (E.actualHist ω) - ↑n * E.p k) ^ 2} ≤
              E.p k * (1 - E.p k) / (↑n * ε ^ 2)
```
- **hypotheses (4)** — name : status [P]/[D]:
```
1. hP [surface] : ∀ (a : Fin m), QIQTH.EffectGleason.IsEffect (P a)
2. hcal [surface] : ∀ (a : Fin m), M.μ (P a) = E.p a
3. hε [surface] : 0 < ε
4. hn [surface] : 0 < n
```
- **packed Prop fields (hidden assumptions inside data structures, 8)  [L]:**
```
E.p_nonneg : ∀ (k : Fin m), 0 ≤ p k
E.p_sum : ∑ k, p k = 1
E.oneSite : ∀ (t : Fin n) (a : Fin m), P.massSet {ω | (V ω t).actualValue = a} = p a
E.indep : ∀ (h : Fin n → Fin m),
  P.massSet {ω | (fun t => (V ω t).actualValue) = h} = ∏ t, P.massSet {ω | (V ω t).actualValue = h t}
M.normalized : μ 1 = 1
M.nonneg : ∀ (E : Matrix (Fin d) (Fin d) ℂ), QIQTH.EffectGleason.IsEffect E → 0 ≤ μ E
M.additive : ∀ (E F : Matrix (Fin d) (Fin d) ℂ),
  QIQTH.EffectGleason.IsEffect E →
    QIQTH.EffectGleason.IsEffect F → QIQTH.EffectGleason.IsEffect (E + F) → μ (E + F) = μ E + μ F
k.isLt : val < n
```
- **data binders (8):** `m`, `n`, `d`, `E`, `M`, `P`, `k`, `ε`

### `QIQTH.EffectGleason.EffectMeasure.finite_effect_gleason`  ·  *spine*
- policy-clean · kind=thm  [L]
- **conclusion:**
```
∃ ρ,
  ρ.PosSemidef ∧
    ρ.trace = 1 ∧ ∀ (E : Matrix (Fin d) (Fin d) ℂ), QIQTH.EffectGleason.IsEffect E → ↑(m.μ E) = (ρ * E).trace
```
- **hypotheses (0)** — name : status [P]/[D]:
  *(none)*
- **packed Prop fields (hidden assumptions inside data structures, 3)  [L]:**
```
m.normalized : μ 1 = 1
m.nonneg : ∀ (E : Matrix (Fin d) (Fin d) ℂ), QIQTH.EffectGleason.IsEffect E → 0 ≤ μ E
m.additive : ∀ (E F : Matrix (Fin d) (Fin d) ℂ),
  QIQTH.EffectGleason.IsEffect E →
    QIQTH.EffectGleason.IsEffect F → QIQTH.EffectGleason.IsEffect (E + F) → μ (E + F) = μ E + μ F
```
- **data binders (2):** `d`, `m`

### `QIQTH.GleasonSelector.positive_ray_certain_forces_born`  ·  *spine*
- policy-clean · kind=thm  [L]
- **conclusion:**
```
w E = QIQTH.GleasonSelector.born ψ E
```
- **hypotheses (6)** — name : status [P]/[D]:
```
1. hψ [surface] : star ψ ⬝ᵥ ψ = 1
2. hadd [surface] : ∀ (A B : Matrix n n ℂ), w (A + B) = w A + w B
3. hhom [surface] : ∀ (c : ℂ) (A : Matrix n n ℂ), w (c • A) = c * w A
4. hpsd [surface] : ∀ (A : Matrix n n ℂ), QIQTH.GleasonSelector.NonnegC (w (A.conjTranspose * A))
5. hray [surface] : w (Matrix.vecMulVec ψ (star ψ)) = 1
6. hone [surface] : w 1 = 1
```
- **data binders (4):** `n`, `ψ`, `w`, `E`

### `QIQTH.RefinementBorn.continuous_additive_fMeasure_eq_born`  ·  *spine*
- policy-clean · kind=thm  [L]
- **conclusion:**
```
QIQTH.RefinementBorn.fMeasure (⇑f) w k = w k
```
- **hypotheses (3)** — name : status [P]/[D]:
```
1. hf [surface] : Continuous ⇑f
2. h1 [surface] : f 1 ≠ 0
3. hsum [surface] : ∑ j, w j = 1
```
- **packed Prop fields (hidden assumptions inside data structures, 2)  [L]:**
```
f.map_add' : ∀ (x y : M), toZeroHom.toFun (x + y) = toZeroHom.toFun x + toZeroHom.toFun y
k.isLt : val < n
```
- **data binders (4):** `n`, `f`, `w`, `k`

### `QIQTH.RecordGleason.decoherent_partition_additive`  ·  *spine*
- policy-clean · kind=thm  [L]
- **conclusion:**
```
QIQTH.GleasonSelector.born ψ ((∑ a ∈ S, C a).conjTranspose * ∑ a ∈ S, C a) =
  ∑ a ∈ S, QIQTH.GleasonSelector.born ψ ((C a).conjTranspose * C a)
```
- **hypotheses (1)** — name : status [P]/[D]:
```
1. hdec [surface] : QIQTH.RecordGleason.Decoherent ψ C
```
- **packed Prop fields (hidden assumptions inside data structures, 1)  [L]:**
```
S.nodup : val.Nodup
```
- **data binders (5):** `n`, `ψ`, `ι`, `C`, `S`

### `QIQTH.BornJoin.ActualEnsemble.finite_noCollapseBornRepresentation`  ·  *spine*
- policy-clean · kind=thm  [L]
- **conclusion:**
```
(∀ (ω : E.Ω), ∃! h, ∀ (t : Fin n), ∃ r ∈ (E.V ω t).config.active, (E.V ω t).ctx.valueOf r = h t) ∧
  (∀ (h : Fin n → Fin m), E.P.massSet {ω | E.actualHist ω = h} = QIQTH.BornTypicalityFinite.w E.p h) ∧
    E.P.massSet {ω | (↑n * ε) ^ 2 ≤ (QIQTH.BornTypicalityFinite.count k (E.actualHist ω) - ↑n * E.p k) ^ 2} ≤
      E.p k * (1 - E.p k) / (↑n * ε ^ 2)
```
- **hypotheses (2)** — name : status [P]/[D]:
```
1. hε [surface] : 0 < ε
2. hn [surface] : 0 < n
```
- **packed Prop fields (hidden assumptions inside data structures, 5)  [L]:**
```
E.p_nonneg : ∀ (k : Fin m), 0 ≤ p k
E.p_sum : ∑ k, p k = 1
E.oneSite : ∀ (t : Fin n) (a : Fin m), P.massSet {ω | (V ω t).actualValue = a} = p a
E.indep : ∀ (h : Fin n → Fin m),
  P.massSet {ω | (fun t => (V ω t).actualValue) = h} = ∏ t, P.massSet {ω | (V ω t).actualValue = h t}
k.isLt : val < n
```
- **data binders (5):** `m`, `n`, `E`, `k`, `ε`

### `QIQTH.BornMeasureUniqueness.product_born_measure_unique`  ·  *spine*
- policy-clean · kind=thm  [L]
- **conclusion:**
```
μ S = ((QIQTH.BornTypicalityQuantum.kronN fun x => ρ) * QIQTH.BornTypicalityQuantum.eventEffect E S).trace.re
```
- **hypotheses (5)** — name : status [P]/[D]:
```
1. hρ [surface] : ρ.PosSemidef
2. hE [surface] : ∀ (k : Fin m), (E k).PosSemidef
3. hμ0 [surface] : μ ∅ = 0
4. hμins [surface] : ∀ (a : Fin n → Fin m) (S : Finset (Fin n → Fin m)), a ∉ S → μ (insert a S) = μ {a} + μ S
5. hpt [surface] : ∀ (ω : Fin n → Fin m), μ {ω} = ∏ t, QIQTH.BornTypicalityQuantum.bornProb ρ E (ω t)
```
- **packed Prop fields (hidden assumptions inside data structures, 1)  [L]:**
```
S.nodup : val.Nodup
```
- **data binders (7):** `n`, `d`, `m`, `ρ`, `E`, `μ`, `S`

### `QIQTH.BornTypicalityFinite.chebyshev_freq`  ·  *spine*
- policy-clean · kind=thm  [L]
- **conclusion:**
```
∑ ω with (↑N * ε) ^ 2 ≤ (QIQTH.BornTypicalityFinite.count k ω - ↑N * p k) ^ 2, QIQTH.BornTypicalityFinite.w p ω ≤
  p k * (1 - p k) / (↑N * ε ^ 2)
```
- **hypotheses (4)** — name : status [P]/[D]:
```
1. hp [surface] : ∀ (i : Fin m), 0 ≤ p i
2. hp1 [surface] : ∑ i, p i = 1
3. hε [surface] : 0 < ε
4. hN [surface] : 0 < N
```
- **packed Prop fields (hidden assumptions inside data structures, 1)  [L]:**
```
k.isLt : val < n
```
- **data binders (5):** `m`, `N`, `p`, `k`, `ε`

### `QIQTH.BornTypicality.qiqth_born_typicality_conditional`  ·  *spine*
- policy-clean · kind=thm  [L]
- **conclusion:**
```
QIQTH.BornTypicality.expectedIndicator outcome M.μ k = c k ^ 2
```
- **hypotheses (0)** — name : status [P]/[D]:
  *(none)*
- **packed Prop fields (hidden assumptions inside data structures, 3)  [L]:**
```
M.nn : ∀ (γ : Γ), 0 ≤ μ γ
M.sum_one : ∑ γ, μ γ = 1
M.born_marginal : ∀ (k : Outcome), QIQTH.NoBornFromNothing.outcomeMarginal outcome μ k = c k ^ 2
```
- **data binders (6):** `Γ`, `Outcome`, `outcome`, `c`, `M`, `k`

### `QIQTH.NoBornFromNothing.born_distribution_realizable_conditional`  ·  *nogo*
- policy-clean · kind=thm  [L]
- **conclusion:**
```
∃ μ,
  (∀ (γ : Γ), 0 ≤ μ γ) ∧ ∑ γ, μ γ = 1 ∧ ∀ (k : Outcome), QIQTH.NoBornFromNothing.outcomeMarginal outcome μ k = c k ^ 2
```
- **hypotheses (2)** — name : status [P]/[D]:
```
1. h_surj [surface] : Function.Surjective outcome
2. hc_norm [surface] : ∑ k, c k ^ 2 = 1
```
- **data binders (4):** `Γ`, `Outcome`, `outcome`, `c`

### `QIQTH.NoConcentration.decoherence_does_not_concentrate`  ·  *nogo*
- policy-clean · kind=thm  [L]
- **conclusion:**
```
0 < QIQTH.NoConcentration.branchWeight c 0 ∧ 0 < QIQTH.NoConcentration.branchWeight c 1
```
- **hypotheses (2)** — name : status [P]/[D]:
```
1. h0 [surface] : c 0 ≠ 0
2. h1 [surface] : c 1 ≠ 0
```
- **data binders (1):** `c`

### `QIQTH.EquivarianceGap.support_preservation_does_not_imply_measure_preservation`  ·  *nogo*
- policy-clean · kind=thm  [L]
- **conclusion:**
```
∃ T μ,
  Function.Bijective T ∧
    QIQTH.EquivarianceGap.SupportPreserving Set.univ T ∧ ¬QIQTH.EquivarianceGap.MeasurePreserving T μ
```
- **hypotheses (0)** — name : status [P]/[D]:
  *(none)*
- **data binders (0):** *(none)*

### `QIQTH.OperationalNoGo.operational_data_insufficient`  ·  *nogo*
- policy-clean · kind=thm  [L]
- **conclusion:**
```
∃ outcome ν₁ ν₂,
  (∀ (k : Fin 2), QIQTH.OperationalNoGo.marginal3to2 ν₁ outcome k = QIQTH.OperationalNoGo.marginal3to2 ν₂ outcome k) ∧
    ν₁ ≠ ν₂
```
- **hypotheses (0)** — name : status [P]/[D]:
  *(none)*
- **data binders (0):** *(none)*
