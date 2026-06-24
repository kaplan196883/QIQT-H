# Track state — Lorentz covariance
*Target 2 — QIQT-H compatible with Lorentz (covariance spine + selector no-go)*

_Generated 2026-06-24 09:51 UTC · git `7233ca0` · 11 theorems · tool lean_track_ · provenance: [L]=Lean fact [P]=Lean-checked prober [D]=derived [C]=curation_

## Axiom status  [L]
- Project-specific (non-standard) axioms: **0**
- All policy-clean (axioms ⊆ allowed `propext, Classical.choice, Quot.sound`): **YES**
- All *literally* axiom-free (no axioms at all): **NO**

## Assumption surface (capstone)  [P]/[D]

**`QIQTH.LorentzSelectionStrong.upvm_covariant_probability`** — 10 surface items (10 distinct after dedup; conclusion: `(∀ (x : P.X D), 0 ≤ QIQTH.LorentzSelectionStrong.ubornω B.toUniformBornData D x) ∧
  Finse`):
  - `P.restrict_id` : `∀ {D : Diam} (x : X D), restrict ⋯ x = x`
  - `P.restrict_comp` : `∀ {L K D : Diam} (hLK : L ≤ K) (hKD : K ≤ D) (x : X D), restrict hLK (restrict hKD x) = restrict ⋯ x`
  - `A.natural` : `∀ (g : G) {K D : Diam} (h : K ≤ D) (x : P.X D), P.restrict ⋯ ((γ g D) x) = (γ g K) (P.restrict h x)`
  - `A.act_one` : `act 1 = OrderIso.refl Diam` · **COVARIANCE — equivariance / unitary-transport premise** [C:covariance-premise]
  - `A.act_mul` : `∀ (g₁ g₂ : G), act (g₁ * g₂) = (act g₁).trans (act g₂)` · **COVARIANCE — equivariance / unitary-transport premise** [C:covariance-premise]
  - `B.proj_herm` : `∀ (D : Diam) (x : P.X D), (toUniformBornData.E D x).conjTranspose = toUniformBornData.E D x`
  - `B.proj_idem` : `∀ (D : Diam) (x : P.X D), toUniformBornData.E D x * toUniformBornData.E D x = toUniformBornData.E D x`
  - `C.U_unit` : `∀ (g : G) (D : Diam), (U g D).conjTranspose * U g D = 1`
  - `C.ψ_cov` : `∀ (g : G) (D : Diam), B.ψ ((A.act g) D) = (U g D).mulVec (B.ψ D)` · **COVARIANCE — equivariance / unitary-transport premise** [C:covariance-premise]
  - `C.E_cov` : `∀ (g : G) (D : Diam) (x : P.X D), B.E ((A.act g) D) ((A.γ g D) x) = U g D * B.E D x * (U g D).conjTranspose` · **COVARIANCE — equivariance / unitary-transport premise** [C:covariance-premise]

## Curated piles  [C] *(author labels — NOT a Lean fact)*

**COVARIANCE — equivariance / unitary-transport premise** (4 distinct)
  - `act 1 = OrderIso.refl Diam`
  - `∀ (g : G) (D : Diam) (x : P.X D), B.E ((A.act g) D) ((A.γ g D) x) = U g D * B.E D x * (U g D).conjTranspose`
  - `∀ (g : G) (D : Diam), B.ψ ((A.act g) D) = (U g D).mulVec (B.ψ D)`
  - `∀ (g₁ g₂ : G), act (g₁ * g₂) = (act g₁).trans (act g₂)`

**(uncategorised surface hypotheses — 15)** *(no rule matched)*
  - `CompleteSpace H`
  - `MeasureTheory.IsProbabilityMeasure ν`
  - `MeasureTheory.Measure.map (QIQTH.FreeFieldTypicality.boostMap e) ν = ν`
  - `Orthonormal ℂ ⇑b`
  - `Summable p`
  - `actS Φ = Φ`
  - `∀ (h : History), actH h ≠ h`
  - `∀ (i : ι), DiscreteTopology (α i)`
  - `∀ (i : ι), Finite (α i)`
  - `∀ (i : ι), MeasurableSingletonClass (α i)`
  - `∀ (i : κ), 0 ≤ p i`
  - `∀ (u : Unit), σ u = !σ u`
  - `∀ (Φ : State), σ (actS Φ) = actH (σ Φ)`
  - `∑ b, F b = 1`
  - `∑' (i : κ), p i = 1`

## Per-theorem facts  [L]/[P]/[D]

### `QIQTH.LorentzSelectionStrong.upvm_covariant_probability`  ·  *capstone*
- policy-clean · kind=thm  [L]
- **conclusion:**
```
(∀ (x : P.X D), 0 ≤ QIQTH.LorentzSelectionStrong.ubornω B.toUniformBornData D x) ∧
  Finset.univ.sum (QIQTH.LorentzSelectionStrong.ubornω B.toUniformBornData D) = 1 ∧
    ∀ (x : P.X D),
      QIQTH.LorentzSelectionStrong.ubornω B.toUniformBornData ((A.act g) D) ((A.γ g D) x) =
        QIQTH.LorentzSelectionStrong.ubornω B.toUniformBornData D x
```
- **hypotheses (0)** — name : status [P]/[D]:
  *(none)*
- **packed Prop fields (hidden assumptions inside data structures, 10)  [L]:**
```
P.restrict_id : ∀ {D : Diam} (x : X D), restrict ⋯ x = x
P.restrict_comp : ∀ {L K D : Diam} (hLK : L ≤ K) (hKD : K ≤ D) (x : X D), restrict hLK (restrict hKD x) = restrict ⋯ x
A.natural : ∀ (g : G) {K D : Diam} (h : K ≤ D) (x : P.X D), P.restrict ⋯ ((γ g D) x) = (γ g K) (P.restrict h x)
A.act_one : act 1 = OrderIso.refl Diam
A.act_mul : ∀ (g₁ g₂ : G), act (g₁ * g₂) = (act g₁).trans (act g₂)
B.proj_herm : ∀ (D : Diam) (x : P.X D), (toUniformBornData.E D x).conjTranspose = toUniformBornData.E D x
B.proj_idem : ∀ (D : Diam) (x : P.X D), toUniformBornData.E D x * toUniformBornData.E D x = toUniformBornData.E D x
C.U_unit : ∀ (g : G) (D : Diam), (U g D).conjTranspose * U g D = 1
C.ψ_cov : ∀ (g : G) (D : Diam), B.ψ ((A.act g) D) = (U g D).mulVec (B.ψ D)
C.E_cov : ∀ (g : G) (D : Diam) (x : P.X D), B.E ((A.act g) D) ((A.γ g D) x) = U g D * B.E D x * (U g D).conjTranspose
```
- **data binders (8):** `Diam`, `G`, `P`, `A`, `B`, `C`, `g`, `D`

### `QIQTH.LorentzSelection.evaluation_covariance`  ·  *spine*
- policy-clean · kind=thm  [L]
- **conclusion:**
```
QIQTH.LorentzSelection.selector (QIQTH.LorentzSelection.actSection g lam) (g.act D) =
  (g.γ D) (QIQTH.LorentzSelection.selector lam D)
```
- **hypotheses (0)** — name : status [P]/[D]:
  *(none)*
- **packed Prop fields (hidden assumptions inside data structures, 4)  [L]:**
```
P.restrict_id : ∀ {D : Diam} (x : X D), restrict ⋯ x = x
P.restrict_comp : ∀ {L K D : Diam} (hLK : L ≤ K) (hKD : K ≤ D) (x : X D), restrict hLK (restrict hKD x) = restrict ⋯ x
g.natural : ∀ {K D : Diam} (h : K ≤ D) (x : P.X D), P.restrict ⋯ ((γ D) x) = (γ K) (P.restrict h x)
lam.consistent : ∀ {K D : Diam} (h : K ≤ D), P.restrict h (val D) = val K
```
- **data binders (5):** `Diam`, `P`, `g`, `lam`, `D`

### `QIQTH.LorentzSelectionStrong.group_evaluation_covariance`  ·  *spine*
- policy-clean · uses-spine: `evaluation_covariance` · kind=thm  [L]
- **conclusion:**
```
QIQTH.LorentzSelection.selector (QIQTH.LorentzSelection.actSection (A.toPoincare g) lam) ((A.act g) D) =
  (A.γ g D) (QIQTH.LorentzSelection.selector lam D)
```
- **hypotheses (0)** — name : status [P]/[D]:
  *(none)*
- **packed Prop fields (hidden assumptions inside data structures, 6)  [L]:**
```
P.restrict_id : ∀ {D : Diam} (x : X D), restrict ⋯ x = x
P.restrict_comp : ∀ {L K D : Diam} (hLK : L ≤ K) (hKD : K ≤ D) (x : X D), restrict hLK (restrict hKD x) = restrict ⋯ x
A.natural : ∀ (g : G) {K D : Diam} (h : K ≤ D) (x : P.X D), P.restrict ⋯ ((γ g D) x) = (γ g K) (P.restrict h x)
A.act_one : act 1 = OrderIso.refl Diam
A.act_mul : ∀ (g₁ g₂ : G), act (g₁ * g₂) = (act g₁).trans (act g₂)
lam.consistent : ∀ {K D : Diam} (h : K ≤ D), P.restrict h (val D) = val K
```
- **data binders (7):** `Diam`, `G`, `P`, `A`, `lam`, `g`, `D`

### `QIQTH.FreeFieldTypicality.freeFieldMeasure_boost_invariant`  ·  *spine*
- policy-clean · kind=thm  [L]
- **conclusion:**
```
MeasureTheory.Measure.map (QIQTH.FreeFieldTypicality.diagBoost e) (QIQTH.FreeFieldTypicality.freeFieldMeasure ν) =
  QIQTH.FreeFieldTypicality.freeFieldMeasure ν
```
- **hypotheses (2)** — name : status [P]/[D]:
```
1. inst._@.QIQTH.FreeFieldTypicality.4290387588._hygCtx._hyg.15 [surface] : MeasureTheory.IsProbabilityMeasure ν
2. hν [surface] : MeasureTheory.Measure.map (QIQTH.FreeFieldTypicality.boostMap e) ν = ν
```
- **packed Prop fields (hidden assumptions inside data structures, 4)  [L]:**
```
ν.m_iUnion : ∀ ⦃f : ℕ → Set α⦄,
  (∀ (i : ℕ), MeasurableSet (f i)) →
    Pairwise (Function.onFun Disjoint f) → toOuterMeasure (⋃ i, f i) = ∑' (i : ℕ), toOuterMeasure (f i)
ν.trim_le : toOuterMeasure.trim ≤ toOuterMeasure
e.left_inv : autoParam (Function.LeftInverse invFun toFun) Equiv.left_inv._autoParam
e.right_inv : autoParam (Function.RightInverse invFun toFun) Equiv.right_inv._autoParam
```
- **data binders (3):** `m`, `ν`, `e`

### `QIQTH.BHTypicalityMeasure.bh_typicalityMeasure_exists`  ·  *spine*
- policy-clean · kind=thm  [L]
- **conclusion:**
```
∃ μ,
  MeasureTheory.IsProbabilityMeasure μ ∧
    (QIQTH.BHTypicalityMeasure.diagNet hb hp hsum hp1 g).toFiniteMarginals.IsLimit μ
```
- **hypotheses (8)** — name : status [P]/[D]:
```
1. inst._@.QIQTH.BHTypicalityMeasure.2998898123._hygCtx._hyg.36 [surface] : ∀ (i : ι), MeasurableSingletonClass (α i)
2. inst._@.QIQTH.BHTypicalityMeasure.2998898123._hygCtx._hyg.56 [surface] : CompleteSpace H
3. inst._@.QIQTH.BHTypicalityMeasure.2998898123._hygCtx._hyg.79 [surface] : ∀ (i : ι), DiscreteTopology (α i)
4. inst._@.QIQTH.BHTypicalityMeasure.2998898123._hygCtx._hyg.88 [surface] : ∀ (i : ι), Finite (α i)
5. hb [surface] : Orthonormal ℂ ⇑b
6. hp [surface] : ∀ (i : κ), 0 ≤ p i
7. hsum [surface] : Summable p
8. hp1 [surface] : ∑' (i : κ), p i = 1
```
- **data binders (7):** `ι`, `α`, `κ`, `H`, `b`, `p`, `g`

### `QIQTH.Fock.fock_typicalityMeasure_exists`  ·  *spine*
- policy-clean · kind=thm  [L]
- **conclusion:**
```
∃ μ, MeasureTheory.IsProbabilityMeasure μ ∧ (QIQTH.Fock.fockVacuumNet g).toFiniteMarginals.IsLimit μ
```
- **hypotheses (3)** — name : status [P]/[D]:
```
1. inst._@.QIQTH.Fock.FockTypicality.377538603._hygCtx._hyg.36 [surface] : ∀ (i : ι), MeasurableSingletonClass (α i)
2. inst._@.QIQTH.Fock.FockTypicality.377538603._hygCtx._hyg.64 [surface] : ∀ (i : ι), DiscreteTopology (α i)
3. inst._@.QIQTH.Fock.FockTypicality.377538603._hygCtx._hyg.73 [surface] : ∀ (i : ι), Finite (α i)
```
- **data binders (4):** `ι`, `α`, `H`, `g`

### `QIQTH.ContinuumSelection.continuum_volume_selects`  ·  *spine*
- policy-clean · kind=thm  [L]
- **conclusion:**
```
MeasureTheory.volume {seed | QIQTH.SelectionEvent.selects (QIQTH.ContinuumSelection.contWeights S ξ s) seed k} =
  ENNReal.ofReal (QIQTH.ContinuumSelection.contWeights S ξ s k)
```
- **hypotheses (1)** — name : status [P]/[D]:
```
1. inst._@.QIQTH.ContinuumSelection.1070711794._hygCtx._hyg.12 [surface] : CompleteSpace H
```
- **packed Prop fields (hidden assumptions inside data structures, 2)  [L]:**
```
S.IsSeparating : toClosedSubmodule ⊓ toClosedSubmodule.mulI = ⊥
S.IsCyclic : toClosedSubmodule ⊔ toClosedSubmodule.mulI = ⊤
```
- **data binders (6):** `H`, `S`, `ξ`, `n`, `s`, `k`

### `QIQTH.Theorem7.Setup.no_signaling`  ·  *spine*
- literal-axiom-free · kind=thm  [L]
- **conclusion:**
```
S.P x a y = S.PAlice x a
```
- **hypotheses (0)** — name : status [P]/[D]:
  *(none)*
- **packed Prop fields (hidden assumptions inside data structures, 2)  [L]:**
```
S.alice_effect_inA : ∀ (x : AliceSetting) (a : AliceOutcome), inA (E x a)
S.locality : ∀ (y : BobSetting) (X : Obs), inA X → Ψ y X = X
```
- **data binders (4):** `S`, `x`, `a`, `y`

### `QIQTH.NoSignalingGeneral.bipartite_no_signaling`  ·  *spine*
- policy-clean · kind=thm  [L]
- **conclusion:**
```
∑ b, (ρ * Matrix.kroneckerMap (fun x1 x2 => x1 * x2) E (F b)).trace =
  (ρ * Matrix.kroneckerMap (fun x1 x2 => x1 * x2) E 1).trace
```
- **hypotheses (1)** — name : status [P]/[D]:
```
1. hF [surface] : ∑ b, F b = 1
```
- **data binders (6):** `d₁`, `d₂`, `β`, `ρ`, `E`, `F`

### `QIQTH.CovariantGluing.no_covariant_selector`  ·  *nogo*
- literal-axiom-free · **no-go (concl = False)** · kind=thm  [L]
- **conclusion:**
```
False
```
- **hypotheses (3)** — name : status [P]/[D]:
```
1. equiv [surface] : ∀ (Φ : State), σ (actS Φ) = actH (σ Φ)
2. hΦ [surface] : actS Φ = Φ
3. hno [surface] : ∀ (h : History), actH h ≠ h
```
- **data binders (6):** `State`, `History`, `actS`, `actH`, `σ`, `Φ`

### `QIQTH.CovariantGluing.bool_swap_no_selector`  ·  *nogo*
- literal-axiom-free · **no-go (concl = False)** · uses-spine: `no_covariant_selector` · kind=thm  [L]
- **conclusion:**
```
False
```
- **hypotheses (1)** — name : status [P]/[D]:
```
1. equiv [surface] : ∀ (u : Unit), σ u = !σ u
```
- **data binders (1):** `σ`
