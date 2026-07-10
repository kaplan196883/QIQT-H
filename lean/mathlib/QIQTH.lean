-- QIQT-H Mathlib-rooted formalizations.
-- See standalone variants in ../Theorem*.lean for axiomatized counterparts.

import QIQTH.Theorem6
import QIQTH.Theorem7
import QIQTH.Resolution
import QIQTH.UnitarityLocality
import QIQTH.Donald
import QIQTH.DoubleSlit
-- Extensions added in the GPT-5.5 audit round:
import QIQTH.StateLevelNoSignaling
import QIQTH.KrausLocality
import QIQTH.ResolutionExt
import QIQTH.CapacityPacking
import QIQTH.RelEntPositivity
import QIQTH.QuantumRelativeEntropy
import QIQTH.Entropy.TraceConvexity
import QIQTH.Entropy.OperatorConvex
import QIQTH.Entropy.CStarMatrixBridge
import QIQTH.Entropy.MatrixOperatorMonotone
import QIQTH.Entropy.GeometricMean
import QIQTH.Entropy.WeightedMean
import QIQTH.Entropy.TensorMean
import QIQTH.Entropy.TensorPower
import QIQTH.Entropy.CommuteRpow
import QIQTH.Entropy.Lieb
import QIQTH.Entropy.RpowConj
import QIQTH.Entropy.RelEntropyConvex
import QIQTH.Entropy.RelEntropyDPI
import QIQTH.Entropy.OrderLimit
import QIQTH.Entropy.PartialTrace
import QIQTH.Entropy.WeylDesign
import QIQTH.Entropy.PartialTraceDPI
import QIQTH.Entropy.TensorLog
import QIQTH.Entropy.StrongSubadditivity
import QIQTH.HolevoCoarseGraining
import QIQTH.DPI
import QIQTH.ShannonFano
import QIQTH.OperationalCapacity
import QIQTH.MaxEntropyCapacity
import QIQTH.ModularEnergyBound
import QIQTH.InducedNewtonConstant
import QIQTH.ScopeAudit
import QIQTH.HolographicScreenCode
import QIQTH.EmergentDynamics
import QIQTH.GravitonQuantization
import QIQTH.OperatorEmergence
import QIQTH.BargmannPairing
import QIQTH.ModularTransport
import QIQTH.Keystone
import QIQTH.KeystoneOperator
import QIQTH.JoinInstance
import QIQTH.Embedding
import QIQTH.Dynamics
import QIQTH.CrossCheck
import QIQTH.Conjectures
import QIQTH.Decoupling.TruncatedCCR
import QIQTH.Decoupling.GibbsSingleMode
import QIQTH.Decoupling.EntropyRegimes
import QIQTH.Decoupling.ProductModes
import QIQTH.Rigidity.LogValuationReal
import QIQTH.Rigidity.FiniteCornerValuation
import QIQTH.Decoupling.DecouplingShadow
import QIQTH.Tower.AWFingerprint
import QIQTH.Tower.KroneckerDensity
import QIQTH.Tower.Centerpiece
import QIQTH.Tower.PowersGuard
import QIQTH.Tower.GibbsLimit
import QIQTH.Tower.NonAtomic
import QIQTH.Tower.CornerEmbed
import QIQTH.Tower.Checkpoint
import QIQTH.VonNeumann.InvariantProjection
import QIQTH.VonNeumann.GeneratedBy
import QIQTH.VonNeumann.DensityOne
import QIQTH.VonNeumann.Amplification
import QIQTH.VonNeumann.MatrixCommutant
import QIQTH.VonNeumann.DensityN
import QIQTH.VonNeumann.Bicommutant
import QIQTH.VonNeumann.CrossedProductClosure
import QIQTH.VonNeumann.DirectedUnionVN
import QIQTH.VonNeumann.WOTClosure
import QIQTH.VonNeumann.Checkpoint
import QIQTH.VonNeumann.SelfAdjointCriterion
import QIQTH.VonNeumann.GraphDecomposition
import QIQTH.VonNeumann.AdjointComp
import QIQTH.TowerGNS.EmbedTrans
import QIQTH.TowerGNS.StageInner
import QIQTH.TowerGNS.PreSpace
import QIQTH.TowerGNS.Germ
import QIQTH.TowerGNS.StageBound
import QIQTH.TowerGNS.LeftMul
import QIQTH.TowerGNS.Representation
import QIQTH.TowerGNS.CyclicVector
import QIQTH.TowerGNS.LimitVN
import QIQTH.TowerGNS.Checkpoint
import QIQTH.TowerGNS.FlowPre
import QIQTH.TowerGNS.Flow
import QIQTH.TowerGNS.FlowCovariance
import QIQTH.Rigidity.RegulatorRigidity
import QIQTH.HeatKernelOneD
import QIQTH.HeatKernelA1
import QIQTH.HeatKernelDDim
import QIQTH.SpeciesCrossCheck
import QIQTH.TowerGNS.FlowContinuity
import QIQTH.TowerGNS.Generator
import QIQTH.TowerGNS.RightMul
import QIQTH.TowerGNS.Separation
import QIQTH.TowerGNS.Tomita
import QIQTH.TowerGNS.ConjClosure
import QIQTH.TowerGNS.TomitaBar
import QIQTH.TowerGNS.ConjAdjoint
import QIQTH.TowerGNS.ModularOp
import QIQTH.TowerGNS.ModularSurjective
import QIQTH.TowerGNS.ModularSelfAdjoint
import QIQTH.TowerGNS.Resolvent
import QIQTH.TowerGNS.ResolventOrder
import QIQTH.TowerGNS.ModularUnitary
import QIQTH.TowerGNS.ModularUnitaryCont
import QIQTH.TowerGNS.ModularUnitaryComm
import QIQTH.TowerGNS.ModularEigenbasis
import QIQTH.TowerGNS.ModularEigenvectors
import QIQTH.TowerGNS.ModularUnitaryEigen
import QIQTH.TowerGNS.Identification
import QIQTH.TowerGNS.TomitaFirstHalf
import QIQTH.TowerGNS.JStage
import QIQTH.TowerGNS.JEmbed
import QIQTH.TowerGNS.ConjPre
import QIQTH.TowerGNS.ModularConj
import QIQTH.TowerGNS.PolarCore
import QIQTH.TowerGNS.ConjFlow
import QIQTH.TowerGNS.ConjImplements
import QIQTH.TowerGNS.TomitaSecondHalf
import QIQTH.TowerGNS.CommutationTheorem
import QIQTH.LinearizedEinstein
import QIQTH.MatterCoupling
import QIQTH.WedgeBoostClausius
import QIQTH.AreaEmergence
import QIQTH.SoftGraviton
import QIQTH.CHMKernel
import QIQTH.BallClausius
import QIQTH.CHMTransport
import QIQTH.BridgeAssembly
import QIQTH.CHMSymbolProbe
import QIQTH.FreeFieldWedgePackage
import QIQTH.AreaDecoder
import QIQTH.CalibratedAreaLaw
import QIQTH.CodeEquilibrium
import QIQTH.DeserRung
import QIQTH.FormalDeser
import QIQTH.DualAction
import QIQTH.LogClockWeight
import QIQTH.ZClockRegression
import QIQTH.MonomialTrace
import QIQTH.EigenCore
import QIQTH.TraceCapacityFromCore
import QIQTH.FiniteCornerEigen
import QIQTH.BellMarginal
import QIQTH.Bell
import QIQTH.Tsirelson
-- Central audits proposed by GPT-5.5-pro:
import QIQTH.H1H2Audit
import QIQTH.NoConcentration
-- Entropy-focused audits from second GPT-5.5-pro consultation:
import QIQTH.EntropyBridge
-- Araki relative entropy via the relative modular operator (Phase A foundation):
import QIQTH.ArakiEntropy
import QIQTH.ArakiModularEntropy
-- Non-commutative matrix function calculus (the matrix power/trace derivative Mathlib lacks):
import QIQTH.MatrixFunctionCalculus
import QIQTH.BranchLedger
import QIQTH.ArakiInterface
-- Final non-entropy audits proposed by GPT-5.5-pro:
import QIQTH.FQDynamicsNoGo
import QIQTH.CompressionLocality
-- Born-rule audits from fourth GPT-5.5-pro consultation:
import QIQTH.NoBornFromNothing
import QIQTH.EquivarianceGap
import QIQTH.BornTypicality
-- Born from symmetric equiprobability (audit candidate ii): the Zurek amplitude→count bridge:
import QIQTH.BornEquiprobable
-- Sub-theorems B, C for the Canonical IC Measure Principle (sub-theorem A — the content-free
-- `TypicalityMackeyGleason` placeholder — was DELETED 2026-06, superseded by `EffectGleason`):
import QIQTH.OperationalNoGo
import QIQTH.FQEquivarianceUniqueness
-- Concrete finite-dim Goldstein-Struyve (Steps 2, 4 proved; 1, 3 axiomatized):
import QIQTH.GoldsteinStruyveFinDim
import QIQTH.GoldsteinStruyveStep3
import QIQTH.GoldsteinStruyveKronecker
import QIQTH.GoldsteinStruyveStep1
-- Regression suite: positive (non-vacuity) + negative (countermodel) witnesses:
import QIQTH.GoldsteinStruyveModels
-- Finite Born-typicality (non-vacuous replacement for the LLN placeholder content):
import QIQTH.BornTypicalityFinite
-- Quantum bridge: product trace factorization connecting Born weights to the product measure:
import QIQTH.BornTypicalityQuantum
-- λ-identification: the product-history Born measure is the UNIQUE additive measure
-- carrying the Born marginals, and equals the trace functional tr(ρ^⊗ⁿ · F_S):
import QIQTH.BornMeasureUniqueness
-- A1 strengthening: locality discharged from equivariance + local dynamics:
import QIQTH.MarginalLocality
-- General bipartite no-signaling for an ARBITRARY (possibly entangled) state — strengthens the
-- product-state ("toy") no-signaling: the local marginal is independent of the remote POVM choice:
import QIQTH.NoSignalingGeneral
-- P1 of the covariant-μ plan: coarse-graining naturality — the Born measures on a directed system
-- of measurement contexts are Kolmogorov-consistent (coarse Born = pushforward of fine Born):
import QIQTH.CoarseGrainNaturality
-- P3: the cylinder typicality (pre)measure on a directed projective system of finite contexts — a
-- canonical finite-record covariant μ (consistent, normalized, covariant) bypassing the TT walls:
import QIQTH.CylinderTypicality
-- XL-step Phase A smoke test: the Finset ι projective-family shape validated against Mathlib's
-- Kolmogorov extension — i.i.d. case gets a genuine σ-additive limit measure μ∞ via infinitePi:
import QIQTH.FiniteMarginals
-- XL-step A0: the matrix Born law as a PMF (bornPMF); the i.i.d. quantum history measure on ℕ→α
-- (σ-additive, Born marginals) — the concrete quantum endpoint of the reachable part of Phase A:
import QIQTH.QuantumHistoryMeasure
-- XL-step A2b: the general (correlated/entangled) Kolmogorov extension for FINITE discrete fibers —
-- every consistent finite-fiber marginal family has a σ-additive projective-limit measure μ∞:
import QIQTH.KolmogorovFiniteFiber
-- XL-step Phase B (formalizable core): the typicality measure is STATE-AGNOSTIC — any positive
-- normalized linear state ω on a net of compatible effects yields μ∞ (Type III₁ realization cited):
import QIQTH.StateNetMeasure
import QIQTH.HolographyScaffolding
-- Phase B Part A (first brick): a genuine infinite-dim NORMAL STATE on B(H) — the diagonal density
-- operator ω(x)=∑ pₙ⟨eₙ,x eₙ⟩ (positive, normalized, additive), bypassing general Schatten theory:
import QIQTH.NormalState
-- Phase B Part A — CLOSING THE LOOP on B(H): the diagonal normal state drives the EffectStateNet →
-- σ-additive μ∞ pipeline end-to-end (first fully infinite-dimensional instance of the prize):
import QIQTH.BHTypicalityMeasure
-- Phase B Part A — general trace-class step (Simon §1.1): the operator absolute value |T|=√(T⋆T) via
-- cfc on the nonneg-spectrum T⋆T (|T| self-adjoint, |T|²=T⋆T, ‖|T|x‖=‖Tx‖) — foundation of trace-class:
import QIQTH.AbsoluteValue
-- Toward the prize: the FREE-FIELD (finite-mode) covariant typicality measure — μ∞ on occupation-sector
-- histories, INVARIANT under the (geometry-moving) mode-permutation boost (finite-mode Lorentz action):
import QIQTH.FreeFieldTypicality
-- A6 strengthening: minimality/independence table for Born premises:
import QIQTH.BornMinimalityTable
-- A4 strengthening: Chebyshev concentration upgrading Born means to frequencies:
import QIQTH.BornConcentration
-- Open Problem 3b (Lorentz covariance): discrete sheaf skeleton + covariance
-- one-liner proved; AQFT analytic inputs named as interface axioms:
import QIQTH.LorentzSelection
-- Finite-dimensional Tomita–Takesaki (modular flow σ_t, KMS) proved from
-- matrix algebra + trace cyclicity — engine for the free-field finite-mode
-- record instance; NO axioms beyond the standard three:
import QIQTH.FiniteModularTheory
-- λ's pointer law, finite (Type I) shadow of Takesaki's conditional-expectation
-- criterion: σ(P)=P ⟺ [ρ,P]=0 (exact decoherence), algebraic Born weights are a
-- probability, the dephasing map is the ω-preserving conditional expectation;
-- NO axioms beyond the standard three:
import QIQTH.LambdaPointer
-- The weak/strong split of state-supervenience: naturality is f-blind (cannot
-- force Born), the α-family witnesses it, refinement-additivity is the strong
-- discriminating premise that linearizes; NO axioms beyond the standard three:
import QIQTH.WeakStrongSplit
-- λ's selection-event constructor: an explicit inverse-CDF selector from an
-- actuality seed — exactly one record per seed (single-world consistency) and
-- the uniform seed measure pushes to Born; NO axioms beyond the standard three:
import QIQTH.SelectionEvent
-- A particular finite inverse-CDF sampler (correct axiom-free arithmetic). Its
-- interpretation as a physical "finite-information λ" is RETRACTED after red-team
-- (the grid is ordering-dependent and breaks QIQT-H's own envariance + no-signaling;
-- finite value-space λ reproduces Born exactly with no deviation). See its header:
import QIQTH.FiniteInfoLambda
-- The finite-information λ that SURVIVES: a finite INDEX over a finite record
-- space with the EXACT Born law (Born-transparent). Machine-checks the dividing
-- line: the index preserves marginals + equal-weights, while the grid provably
-- BREAKS envariance and no-signaling. NO axioms beyond the standard three:
import QIQTH.FiniteIndexLambda
-- (Φ,λ) in a VERY LIMITED information space: the one-bit universe (M=2, exact
-- Born (p,1-p); the grid distorts it to (1/2,1/2) at N=2) and the
-- pre-statistical→statistical transition (Born as finite-sample frequency,
-- 1/(4Kε²)→0 as the number of actual records K→∞). NO axioms beyond standard three:
import QIQTH.TinyUniverse
-- (Φ,λ) at TWO bits: the actuality factors into two sub-bits λ=(λ_A,λ_B). New structure:
-- entanglement (product Φ → independent bits, joint = product of marginals; Bell Φ →
-- perfectly correlated bits with uniform marginals, joint ≠ product) + marginal/no-signaling.
-- NO axioms beyond the standard three:
import QIQTH.TwoBitUniverse
-- (Φ,λ) in an EIGHT-record (three-qubit) world with 1/2/3 bits of actuality: the
-- resolution hierarchy (k bits → 2^k-block coarse-graining, exact partial Born; 3 bits =
-- full per-record law) + the GHZ entropy ceiling (8 records but supported on 2, so even a
-- 2/3-bit λ reveals 1 bit; dimension ≠ information). NO axioms beyond the standard three:
import QIQTH.ThreeQubitUniverse
-- The (Φ,λ) record/area CONTRACT (labeled scaffold, NOT new physics): the four explicit
-- inputs (factorization → einselection → area-cap → λ), coarse-graining as a capacity-
-- non-increasing pushforward, and the area bridge in BOTH versions (Bousso entropy vs the
-- stronger dim-capacity postulate, kept distinct), threading postulates as HYPOTHESES (no
-- axioms). Metaselector = einselection, NOT capacity; operationally = Everett. Standard three:
import QIQTH.RecordContract
import QIQTH.DifferentialAreaLaw
import QIQTH.QiqtToGR
import QIQTH.QiqtGrWitness
import QIQTH.WedgeKMSToGR
-- T3-1: the four Clausius/area-law premises (bound/saturation/positivity/tightness) are theorems of
-- the finite QIQT entropy model + the holographic area-capacity identification, not assumptions.
import QIQTH.ClausiusFiniteWitness
-- GR scaffolding: the capstone HasDerivAt facts hS/hK derived from smoothness of the finite record law
-- (Shannon/KL derivatives; KL flat at equilibrium ⟹ hK from hS) — pure analysis, not the physics floor.
import QIQTH.EntropyDeriv
-- T3-1 Stage 2: the thermodynamic free-field QIQT→GR capstone — entropy/heat built from a finite record
-- law, hsat/hDnn/hD0 discharged via the witness; only the dynamical FQ capacity bound stays labelled.
import QIQTH.QiqtGrThermo
-- T3-3 continuum: the localization mode from the field (ff = (v^a ∂_a φ)·g₀); the per-generator hTkk
-- reduces to ONE universal mode calibration (Im ∫ conj g₀ g₀' = −1/ℏ).
import QIQTH.LocalizedMode
-- T3-3-C2: the concrete calibrated profile — a Gaussian wave packet satisfies the mode calibration,
-- closing the last analytic input (hcal) of the localization map.
import QIQTH.GaussianMode
-- GR scaffolding C: the localization discharge is not specific to one Gaussian — a width-parametrized
-- family gaussModeA (a>0) hits the SAME calibration 2π/ℏ for every width (reuses integral_gaussian a).
import QIQTH.GaussianModeFamily
-- T3-3-C3: the free-field QIQT→GR capstone with the localization mode CONSTRUCTED from φ
-- (ff = field-gradient · Gaussian), hTkk discharged in the GR theorem itself.
import QIQTH.QiqtGrGaussian
-- The maximally-discharged capstone: combines T3-1 (entropy from a finite record law) and T3-3-C3
-- (mode from φ) — hbridge/hFocus/hWarea/hsat/hDnn/hD0/hTkk/ff-block all discharged.
import QIQTH.QiqtGrComplete
-- T3-GR-Raychaudhuri: the congruence premises hWgeo/hWequil from one condition (W covariantly
-- constant), discharged fully for a flat (constant) metric.
import QIQTH.RaychaudhuriCongruence
-- The complete capstone with hWgeo/hWequil collapsed to the single covariant-constancy condition.
import QIQTH.QiqtGrCovCong
-- BORN-A1: Actuality Projective Consistency — grounding the Born additivity bridge in selector
-- no-signaling under outcome-refinement (Stage 1: honest coarse-graining selectors satisfy APC).
import QIQTH.BornActualityConsistency
-- BORN-C: μ-selection grounded in refinement equivariance (quantum equilibrium) — equivariance ⟹
-- selector no-signaling ⟹ (via BORN-A1) Born; the canonical measure is equivariant.
import QIQTH.BornMuSelection
-- A1-ppwave: a non-flat (curved) witness for the Raychaudhuri congruence premises — the pp-wave
-- metric whose null field ∂_v is covariantly constant (Stage 1: metric, inverse, symmetry).
import QIQTH.PPWaveMetric
-- A1+A2 worked example: QIQT→GR for the explicit pp-wave spacetime — all geometry (metric, tetrad
-- congruence, smoothness) discharged concretely; FQ/realization + matter field carried (conditional).
import QIQTH.QiqtGrPPWave
-- The instantiated SHOWCASE: pp-wave QIQT→GR with the floor laid bare — geometry + area-derivative hA
-- (via area_hasDerivAt_of_covConst) + entropy bound hbound (via shannon_le_log_card) all discharged;
-- only EOM (hKG) + FQ capacity (hcap) + the localization map (hS/hK) carried.
import QIQTH.QiqtGrShowcase
-- Sakharov Stage C: the per-mode Gaussian entanglement entropy S(ν)=(ν+½)log(ν+½)−(ν−½)log(ν−½),
-- the Srednicki building block summed by the entropy area law. S(½)=0 (pure), increasing, nonneg.
import QIQTH.GaussianStateEntropy
-- SG1: grounds gaussModeEntropy in first principles — it IS the Shannon/von Neumann entropy −∑ₖ pₖ log pₖ
-- of the thermal geometric occupation distribution pₖ=(1−q)qᵏ at ν=thermalNu q=(1+q)/(2(1−q)).
import QIQTH.GaussModeEntropyDerived
-- SG2/SG3/SG5: the entanglement-entropy AREA LAW S∝A for an EXPLICIT boundary-local Gaussian model
-- (each of the 6L² boundary plaquettes carries the same Srednicki modes) — turns the previously-carried
-- assumption S∝A into a theorem; the volume-law guard (bulk L³ vs boundary 6L²) isolates the locality input.
import QIQTH.BoundaryGaussianAreaLaw
import QIQTH.WilliamsonNormalForm
-- The Sakharov/induced-gravity 1/4 RATIO (circularity-clean algebraic core): S_ent/(A/G_ind)=1/4 with the
-- matter coefficient + regulator cancelling; the geometric 4π/16π. Lean mirror of scripts/sakharov_kg.py.
import QIQTH.SakharovRatio
-- Born FROM PROJECTORS: the operator bridge grounding the record/area contract. For a
-- finite orthogonal PVM {P_r} and a normalized Φ, μ(r)=‖P_r Φ‖²=⟨Φ,P_rΦ⟩ is a genuine
-- RecordContract.RecordLaw — so the contract rests on Born-from-Φ, not a toy distribution.
-- First concrete piece of the decoherent record algebra. Standard three:
import QIQTH.BornProjBridge
-- SYMMETRY CANNOT BE THE METASELECTOR: the unitary group acts transitively on frameworks
-- (orthonormal bases), so any unitarily-invariant typicality score is CONSTANT — selects no
-- preferred framework. The continuous form of capacity_underdetermines_realm; closes the
-- "select the most typical framework by symmetry" route. The metaselector must be einselection.
import QIQTH.SymmetryNoGo
-- What DOES select the framework (the positive answer): EINSELECTION via Zurek's
-- commutativity criterion — a record commuting with the monitored observable A commutes with
-- the interaction A⊗B (decoherence-free); plus the finite-budget overlap floor (a holographic
-- dimension cap forces record overlap above D records). Complements the symmetry/capacity no-gos.
import QIQTH.MetaselectorSelection
-- STATE-ALONE no-go (completes the trilogy): a single projection P=|Φ⟩⟨Φ| generates only the
-- trivial framework {0,P,1−P,1} — a state alone cannot select a finer record basis. So neither
-- capacity, nor symmetry, nor Φ selects the framework: the metaselector is einselection.
import QIQTH.StateAloneNoGo
-- Continuum λ-law (Stage 1 of CONTINUUM_LAMBDA_ROADMAP): the modular automorphism
-- σ_t = Ad(Δ^{it}) on the genuine continuum modular flow, the continuum Takesaki
-- criterion, and continuum persistence (decoherence map commutes with σ_t ∀t,
-- unconditional for spectral pointers); NO axioms beyond the standard three:
import QIQTH.ContinuumLambda
-- Continuum λ-law Stage 2: the Type-independent algebraic Born rule via the
-- scalar spectral measure — the spectral measure of pointer Borel sets is a
-- genuine probability (no trace); NO axioms beyond the standard three:
import QIQTH.NaturalConeBorn
-- Continuum λ-law Stage 3: the continuum selection event — exactly one record per
-- actuality seed driven by the continuum Born weights, realizing Born; the
-- selection event is Type-blind (needs only the finite record structure). NO
-- axioms beyond the standard three:
import QIQTH.ContinuumSelection
-- Continuum λ-law Stage 4 capstone foundation: the second-quantized free-field
-- modular flow Γ(Δ^{it}) is a bijective isometry (vector-level unitarity), and
-- Weyl records on modular-fixed modes commute with it (Γ-level persistence); NO
-- axioms beyond the standard three:
import QIQTH.ContinuumLambdaFock
-- Γ(Δ^{it}) repackaged as a bounded operator on the Fock Hilbert space (the
-- ContinuousLinearMap one-parameter group), the substrate for field-level
-- Ad(Γ) persistence; NO axioms beyond the standard three:
import QIQTH.Fock.SecondQuantCLM
-- The continuum λ-persistence at the genuine FREE-FIELD level: the modular
-- automorphism σ_t = Ad(Γ(Δ^{it})), the field-level Takesaki criterion, and
-- field-level persistence (decoherence map commutes with σ_t ∀t) on the
-- second-quantized modular flow; NO axioms beyond the standard three:
import QIQTH.Fock.ContinuumLambdaField
-- The Born rule at the genuine free-field level: vacuum-state weights of a POVM
-- are a probability (instantiated at the Weyl-bit record POVM) — the Born layer
-- on the real Fock vacuum state; NO axioms beyond the standard three:
import QIQTH.Fock.FieldBorn
-- The selection event at the genuine free-field level: exactly one Weyl-bit
-- record per actuality seed, realizing the Fock-vacuum-state Born weights; NO
-- axioms beyond the standard three:
import QIQTH.Fock.FieldSelection
-- Free-field finite-mode instance: (a) holographic record count, (b) Gaussian
-- decoherence decay, (c) finite-mode Lorentz action — concrete theorems
-- instantiating parts of the LorentzSelection AQFT axioms; standard axioms only:
import QIQTH.FreeFieldRecord
-- Gleason-route μ construction (Open Problem 1): the deep finite-dim
-- effect-Gleason representation is one named axiom; the μ-is-Born history
-- corollary and the finite no-signaling marginal are PROVED from it:
import QIQTH.GleasonSelector
-- Strengthened Lorentz layer (GPT-5.5-pro A–G): externalized geometry (rigid
-- holographic bound + boundary), a real Poincaré GROUP action with covariance
-- ∀g, an equivariant-measure total-mass theorem that consumes covariance, and
-- the BORN LINK (normalization derived from GleasonSelector.born, not assumed).
-- Zero project axioms; turns the conditional interface rigid + connected:
import QIQTH.LorentzSelectionStrong
-- A CONCRETE NON-TRIVIAL model of the strengthened Lorentz interface: a genuine
-- 2-outcome PVM record system with Born weights (9/25, 16/25) — proves the
-- conditional interface is not vacuously satisfied only by the one-point net.
-- Does NOT touch the continuum realization (still open). Standard axioms only:
import QIQTH.LorentzWitness
-- Prize Stage 1 (PRIZE_EXECUTION_PLAN.md): a NON-TOY recorded-history net with genuine
-- marginalizing restriction and the product Born measure — the no-signaling marginal ω_marg is
-- a THEOREM about the product Born measure (vs LorentzWitness's trivial restriction). Axiom-free:
import QIQTH.FreeFieldNet
-- Prize Stage 1 (diamond-permuting action): a 2-atom diamond net (left,right ≤ top) whose
-- left↔right swap is a GENUINE non-trivial order-iso moving the geometry, exercising the
-- covariance machinery over a real orbit with a marginalizing restriction. Axiom-free:
import QIQTH.DiamondSwapNet
-- Prize Stage 2 (sheaf / gluing layer): global sections λ ∈ Γ(X) exist and are CLASSIFIED by the
-- top fibre for a poset directed to a greatest element — gluing unobstructed (Roberts–DHR cocycle
-- trivial for the product/finite case); selectors over the diamond net = joint records. Axiom-free:
import QIQTH.SheafSection
-- Phase 1 of the Tomita–Takesaki roadmap (TOMITA_TAKESAKI_ROADMAP.md): the
-- projection-valued-measure / bounded-spectral-theorem keystone. Structural PVM
-- content proved axiom-free; the analytic core (σ-additivity, bounded-Borel FC,
-- spectral theorem) is the named Phase-1 target. General Mathlib-bound material;
-- ZERO project axioms:
import QIQTH.Spectral.PVM
-- Phase 1.3 (bounded spectral theorem, in progress): PVM_of_selfAdjoint from a bounded self-adjoint
-- T via cfc + Riesz–Markov + boundedFC_mul. Begins by validating cfc fires on B(H) (CStarAlgebra
-- (H→L[ℂ]H) instance). Both earlier-feared blockers (cfc-on-B(H), RMK representation) absent in v4.30.
import QIQTH.Spectral.SpectralTheorem
-- Stone M1 (STONE_THEOREM_PLAN Phase 1 / P4_TO_GR_MASTER_PLAN M1): the unbounded functional calculus
-- ∫ f dE on a PVM — the domain D(∫f dE) = {x : ∫ f² dμ_x < ∞} as a ℂ-submodule (the keystone toward
-- K = ∫ log(r/(2−r)) dE_R as a self-adjoint operator). Builds on scalarMeasure + the parallelogram law.
import QIQTH.Spectral.UnboundedFC
import QIQTH.Spectral.MultiplicationOp
-- The POSITION PVM: E(A)=M_{𝟙_A} bundled as a genuine ProjectionValuedMeasure on L²(μ) (self-adjoint
-- idempotents, PV-content, strong HasSum σ-additivity). The route to the momentum PVM (Fourier) / boost gen.
import QIQTH.Spectral.PositionPVM
-- Unitary conjugation of a PVM: U E(A) U⁻¹ is again a PVM (the mechanism Fourier uses to carry the position
-- PVM to the momentum PVM). Unitary-generic, axiom-free.
import QIQTH.Spectral.PVMConj
-- The MOMENTUM PVM on L²(ℝ): Ê(A)=ℱ E(A) ℱ⁻¹, the Fourier–Plancherel conjugate of the position PVM (via
-- Mathlib's fourierTransformₗᵢ). A genuine ProjectionValuedMeasure, axiom-free — the spectral measure of P=ℱXℱ⁻¹.
import QIQTH.Spectral.MomentumPVM
-- The translation operator τ_t on L²(ℝ) ((τ_t f)(x)=f(x+t)): a ℂ-linear isometry, one-parameter group law
-- τ_s∘τ_t=τ_{s+t}. The unitary family whose generator is the momentum operator P (toward WedgeKMSFlux #5).
import QIQTH.Spectral.TranslationFlow
-- Translation-covariance of the position observable: conjugating the position PVM by τ_t shifts the Born
-- position distribution by t (the covariance making momentum the translation generator, conjugate to position).
import QIQTH.Spectral.PositionCovariance
-- The modulation operator e^{isX}=M_{e^{isx}} on L²(ℝ): a one-parameter UNITARY group (|e^{isx}|=1), generated by
-- the position operator X — the Fourier-dual of the translation group e^{itP}; the canonical pair behind the Weyl CCR.
import QIQTH.Spectral.ModulationFlow
-- STONE Phase 3.1 (P4-wall Phase 4.2): the infinitesimal generator A x=−i(d/dt U_t x)|₀ of a one-parameter operator
-- family, as an unbounded operator (LinearPMap) on the smooth domain. Self-adjointness (Cayley) is the frontier.
import QIQTH.Spectral.Stone
import QIQTH.Spectral.MomentumGenerator
-- CCR DUAL: the position operator X = stoneGen modulationLp = x· on L²(ℝ), the self-adjoint generator of the
-- modulation group e^{isX} — the Fourier-dual twin of momentumOp, completing the canonical CCR pair (P, X).
import QIQTH.Spectral.PositionGenerator
import QIQTH.Spectral.ModularGenerator
import QIQTH.Spectral.Garding
import QIQTH.Spectral.StoneProduct
import QIQTH.Spectral.StoneExp
import QIQTH.Spectral.PVMEigen
-- Prize Stage 3.1 (finite case): the matrix spectral theorem packaged as a PVM — eigenprojections
-- Pᵢ = U·diag(δᵢ)·U⋆ with ∑Pᵢ=1 (resolution of identity), Pᵢ²=Pᵢ, PᵢPⱼ=0, Pᵢ⋆=Pᵢ. The finite,
-- axiom-free case of the bounded-spectral-theorem target (continuum stays open). Standard axioms:
import QIQTH.SpectralPVM
-- Prize Stage 3′ (Track B): free-field / standard-subspace modular theory via the bounded-operator
-- approach of Rieffel–Van Daele (PJM 69, 1977). On Mathlib's StandardSubspace: the projections
-- P,Q onto 𝒦,i𝒦, R=P+Q, and RvD Prop 2.2(1) ⟪Rξ,ξ⟫=‖Pξ‖²+‖Qξ‖² (engine for R injective). Standard axioms:
import QIQTH.StandardSubspaceModular
-- Track B continuation: the CONTINUUM MODULAR FLOW Δ^{it}=u_t(R) of a standard subspace, via the
-- bounded BOREL functional calculus (boundedFC/PVM_of_selfAdjoint). u_t(r)=exp(it·log((2−r)/r)) is
-- discontinuous at the spectral endpoints r=0,2 (continuous cfc cannot reach it). One-parameter
-- unitary group: U_0=1, U_{s+t}=U_s·U_t, U_t⋆=U_{-t}, unitary. Standard axioms:
import QIQTH.StandardSubspaceModularFlow
-- P4-derivation Stage 1: the modular Hamiltonian K = −log Δ spectral function kFn(r)=log(r/(2−r)) and the
-- generator identity Δ^{it} = e^{−itK} (toward the JLMS route deriving the holographic capacity P4).
import QIQTH.ModularHamiltonian
-- Type II crossed product Increment 1a-0: the modular automorphism σ_t(a)=Δ^{it}aΔ^{-it} as a one-parameter
-- group of unital *-homomorphisms (the ℝ-action M ⋊_σ ℝ is built from) — toward an honest area operator.
import QIQTH.CrossedProduct
-- The Wall, Phase 1.1: measurability of the matter-rep fiber s ↦ σ_{-s}(a)(ξ s) on L²(ℝ;H) — toward π(a)
-- as an operator on the crossed-product Hilbert space (operator-valued Lp multiplication).
import QIQTH.CrossedProductRep
-- The Wall, Phase 2.1: the clock translation λ_t ξ = ξ(·+t) as a ℂ-linear isometry on L²(ℝ;H) — the L²(ℝ)
-- clock factor of the crossed product (via Mathlib compMeasurePreservingₗᵢ).
import QIQTH.CrossedProductTranslation
-- The Wall, Phase 3.1: the covariance λ_{-t} π(a) λ_t = π(σ_t a) — the defining identity of the crossed
-- product M ⋊_σ ℝ, joining the matter rep (Phase 1) and the clock group (Phase 2).
import QIQTH.CrossedProductCovariance
-- The Wall, Phase 4.1: strong continuity of the clock group λ_t — t ↦ λ_t ξ continuous in L²(ℝ;H), completing
-- "λ_t is a strongly-continuous one-parameter unitary group" (Stone's theorem hypothesis; X = the frontier).
import QIQTH.CrossedProductGenerator
import QIQTH.CrossedProductModularFlow
-- MODULAR RELATIVE ENTROPY (Phase B, one-particle / standard-subspace continuum object): the
-- Casini–Grillo–Pontello relative entropy of a coherent state vs vacuum, as the SCALAR spectral
-- integral S(ξ)=−∫log((2−r)/r)dμ^R_ξ over the bounded RvD operator R=P+Q (no unbounded log Δ).
-- entropyDensity = the modular-flow generator (modChar t r = exp(i t·g(r))); cgpEntropy + total
-- mass ‖ξ‖² + zero. Genuine continuum one-particle object (full vN-algebra needs Γ(Δ^{it}), cited).
import QIQTH.ModularRelativeEntropy
-- Stone M2: the modular Hamiltonian K = −log Δ as a GENUINE unbounded operator K = ∫ kFn dE_R (via the
-- unbounded FC), upgrading the spectral function; ⟨ξ,Kξ⟩ = cgpEntropy (operator-level JLMS first law).
import QIQTH.ModularHamiltonianOp
-- QIQT-H CORE (post-2026-06 GPT-5.5-pro strategic pivot): the conditional
-- representation theorem for single-outcome-without-collapse. The non-circular
-- finite-capacity exclusion (coactual_subsingleton) + actuality selector give
-- EXACTLY ONE actual record; collapse recovered as conditionalization. This —
-- NOT the Tomita–Takesaki tower — is the load-bearing part of the breakthrough:
import QIQTH.CoreNoCollapse
-- Capacity MODEL: DERIVES the finite-capacity bound (and the saturation premise)
-- of CoreNoCollapse from orthonormality of records in a finite-dim register
-- (∑ recDim ≤ D = finrank). Removes the "cost > Q_max/2" assumption for this model:
-- macroscopic_subsingleton is now a THEOREM. Grounds Strasberg et al. arXiv:2601.19703.
import QIQTH.CapacityModel
-- Grounding the subadditive core: pairwise overflow DERIVED from orthogonality of
-- distinct records (span-dimension joint cost; no additivity assumed):
import QIQTH.OrthogonalCapacity
-- Prize bridge C1: one actual RECORD → one actual VALUE (redundant same-value records
-- coexist; the experienced pointer value is unique), iterated to a unique value history:
import QIQTH.ValueSelection
-- Prize bridge C2: one-site Born — the prepared state's vector valuation on a PVM effect
-- IS the Born weight ‖Eᵣψ‖², packaged as a probability vector for the typicality layer:
import QIQTH.OneSiteBorn
-- THE PRIZE (C3+C4): join A and B — capacity-selected actual VALUE histories have the Born
-- PRODUCT law (from one-site calibration + independence) and are Born-typical; no collapse:
import QIQTH.BornJoin
-- Toward the REAL prize: DERIVE the single-trial Born law from NON-CONTEXTUALITY (effect-
-- Gleason) instead of assuming it — μ(Pₐ) = tr(ρ Pₐ) forced for any non-contextual assignment:
import QIQTH.OneSiteGleason
-- Wiring non-contextuality into the join: the ensemble's single-trial law p is FORCED Born
-- (no longer a free parameter); the representation with p DERIVED, only non-contextuality +
-- independence assumed:
import QIQTH.BornJoinGleason
-- Tier B (GPT-5.5-pro review): the BRIDGE theorem via Spectrum Broadcast Structures.
-- DERIVES the saturation premise cost>Q_max/2 from an objective record's redundancy +
-- an INFORMATION cost R·log n (tensor/log, fixing the rank-model flaw): distinguishability
-- ⇒ dimension (proved), broadcasting tensors spaces ⇒ dims multiply (proved), so a
-- macroscopic (redundant) record costs > half the capacity. Grounds arXiv:2007.04276 (SBS):
import QIQTH.SBSBridge
-- Discharging the ONE isolated physical input of the SBS chain (GPT-5.5-pro): the
-- per-collision distinguishability γ<1 is DERIVED from a concrete toy Hamiltonian
-- H_int = g σ_z^S ⊗ σ_x^E (Zurek collisional/QND monitoring). The branch-conditioned
-- records overlap by cos 2θ, so γ = |cos 2θ| < 1 for generic coupling; over L independent
-- collisions the overlap factorizes to γ^L → 0, feeding overlap_amplifies. Axiom-free.
import QIQTH.CollisionalGamma
-- Toward the PRIZE (PRIZE_ROADMAP.md, GPT-5.5-pro "be bold" plan): Stage 1 of the
-- Effect-Gleason route to the canonical covariant typicality measure μ. Extends the
-- single-state Gleason core (GleasonSelector.positive_ray_certain_forces_born) with the
-- two gaps the prize needs: Born tensor-multiplicativity (independent experiments factor)
-- and decoherent coarse-graining additivity (Born for ALL decoherent partitions). Axiom-free.
import QIQTH.RecordGleason
-- Toward the PRIZE, step G1 (GLEASON_SCOPE.md): finite-dimensional Busch/effect (POVM)
-- Gleason. Foundation installment — effect predicate + closure (0/1/smul/sub), μ 0 = 0,
-- monotonicity, scaling-additivity. Will discharge the finite-dim Mackey-Gleason axiom and
-- the Goldstein-Struyve Born-uniqueness axioms, and complete Stage 1. Axiom-free.
import QIQTH.EffectGleason
-- Prize Stage 1.2 (PRIZE_EXECUTION_PLAN.md): finite Covariant Record-Completeness, qubit case —
-- an explicit rational IC-POVM on ℂ² whose four record traces SEPARATE density matrices
-- (informationally complete), the finite case of the make-or-break lemma. Axiom-free:
import QIQTH.QubitIC
import QIQTH.Fock.OneParticle
import QIQTH.Fock.ExpKernel
import QIQTH.Fock.FockSpace
import QIQTH.Fock.VacuumState
import QIQTH.Fock.Weyl
import QIQTH.Fock.FockTypicality
import QIQTH.Fock.SecondQuant
import QIQTH.Fock.SecondQuantModularFlow
import QIQTH.Fock.OneParticleBW
import QIQTH.Fock.StressTensor.RapidityMomentum
import QIQTH.Fock.StressTensor.HorizonField
import QIQTH.Fock.StressTensor.NullStressFlux
import QIQTH.Fock.StressTensor.HorizonPlancherel
import QIQTH.Fock.StressTensor.HorizonFourier
import QIQTH.Fock.StressTensor.HorizonParseval
import QIQTH.Fock.StressTensor.L2Plancherel
import QIQTH.Fock.StressTensor.WedgeBoostWiring
import QIQTH.StripUniqueness
import QIQTH.KMSCorrelation
import QIQTH.Fock.RelativeModularFlow
import QIQTH.Fock.WeylOp
import QIQTH.Fock.WeylCovariance
import QIQTH.Fock.WeylCCR
import QIQTH.Fock.WeylBit
import QIQTH.Fock.WeylBitProcess
import QIQTH.Fock.WeylBitMeasure
import QIQTH.Fock.WeylBitConsistency
import QIQTH.Fock.WeylBitStrongDecoherence
import QIQTH.Fock.WeylBitBell
import QIQTH.Fock.WeylBitEffect
import QIQTH.Fock.WeylBitGeoCovariance
import QIQTH.Fock.LocalizationSkeleton
import QIQTH.Fock.WeylCLM
import QIQTH.Fock.BoostOrbit
import QIQTH.Fock.Localization
import QIQTH.Fock.WedgeAnalyticity
import QIQTH.Fock.BoostKMS
import QIQTH.Fock.SchwartzDecay
import QIQTH.Fock.PauliJordan
import QIQTH.Fock.LocalizedCovariance
import QIQTH.Fock.LocalizedWitness
import QIQTH.Fock.CyclicWitness
import QIQTH.Fock.FreeFieldHFlux
import QIQTH.Fock.FieldBWUnconditional
import QIQTH.Fock.TranslationCovariance
import QIQTH.Fock.Dirac.QuasiFreeEntropy
import QIQTH.Fock.Dirac.CAR
import QIQTH.Fock.Dirac.Parity
import QIQTH.Fock.Dirac.KleinTwist
import QIQTH.Fock.Dirac.KleinTwistUnitary
import QIQTH.Fock.Dirac.KleinTwistWitness
import QIQTH.Fock.Dirac.FermiDirac
import QIQTH.Fock.Dirac.EvenObservables
import QIQTH.Fock.Dirac.DiracGamma
import QIQTH.Fock.Dirac.LocalDifferentialSupport
import QIQTH.Fock.Dirac.FockKleinTwist
import QIQTH.Fock.Dirac.PhysLeanBridge
import QIQTH.Fock.Dirac.PhysLeanGammaBridge
import QIQTH.Fock.Dirac.ModularKMS
import QIQTH.Fock.Dirac.CARModularFlow
import QIQTH.Fock.Dirac.GradedCapacity

import QIQTH.Fock.Photon.PhotonFock
import QIQTH.Fock.Photon.PhotonCapacity
import QIQTH.Fock.Photon.PhotonUnruh
import QIQTH.Fock.Photon.PhotonModularFlow
import QIQTH.Fock.Photon.PhotonGaugeRecords
import QIQTH.Fock.Photon.PhotonEdgeModes
import QIQTH.Fock.Photon.PhotonFluxSectors
import QIQTH.Fock.Photon.PhotonBRST
import QIQTH.Fock.Photon.PhotonFieldStrength
import QIQTH.Fock.Photon.PhotonHelicity
import QIQTH.Fock.Photon.PhysLeanEMBridge

import QIQTH.RefinementBorn
import QIQTH.SBSBoolean
import QIQTH.SBSSuppression
import QIQTH.RedundancyCompressible
import QIQTH.CovariantGluing
import QIQTH.ContextualitySafe
import QIQTH.SelectorRefinement
import QIQTH.SelectionDynamics
import QIQTH.BornRoutes
import QIQTH.Envariance
import QIQTH.EnvarianceJustification
import QIQTH.StateSupervenience
import QIQTH.Relaxation
import QIQTH.RankCountNoGo
import QIQTH.BornChain
import QIQTH.RotationBorn
import QIQTH.SymmetrySquare
import QIQTH.RealmSelection
import QIQTH.EinsteinEquationOfState
import QIQTH.SpectralSum
import QIQTH.EntanglementFirstLaw
import QIQTH.Curvature
-- GEO1: the geodesic ODE of a component connection — local existence + uniqueness via Picard–Lindelöf
-- on the phase space Point n × Point n. Geodesic EXISTENCE only: NOT the exp-map / normal coordinates,
-- does NOT discharge the RNC gauge (gated on smooth dependence on IC, absent from Mathlib), NOT numerical-G.
import QIQTH.Geodesic
-- RNC1: the √det g atom of the Riemann-normal-coordinate 2nd-order expansion — √det g = 1 − ⅙R_{cd}x^cx^d,
-- CONDITIONAL on a carried tr∂∂g(0)=−⅔Ric (RNC3 discharges it). The ⅙ = source of the κ=1/6 conformal factor.
-- NOT numerical-G, NOT a curved heat kernel. Standard three axioms.
import QIQTH.RNCExpansion
-- exp-map campaign, first bricks: the STRICT derivative of the geodesic field at the equilibrium
-- e=(p,0) is the explicit A(ξ,η)=(η,0) (S2, HasStrictFDerivAt_geodesicField); the geodesic rescaling
-- γ_{p,sv}(t)=γ_{p,v}(st) as a property of any integral curve (S1, geodesic_rescale); and the flow
-- scaffolding (geodesicSol as a function + expMap). Groundwork toward HasStrictFDerivAt exp_p id 0 →
-- the RNC local diffeo; NOT yet exp_p's strict derivative, NOT the diffeo, NOT the RNC gauge, NOT
-- numerical-G. Axiom-free (standard three).
import QIQTH.ExpMap
import QIQTH.Polarization
import QIQTH.RNCGauge
import QIQTH.RNCGaugeExp
import QIQTH.EinsteinFieldEquation
import QIQTH.KGStressConservation
import QIQTH.QiqtGrExplicitKG
import QIQTH.QiqtGrFreeField
import QIQTH.HTkkPhysical
import QIQTH.KGSymplectic
import QIQTH.RicciSymm
import QIQTH.ChristoffelSmooth
import QIQTH.HregExplicitKG
import QIQTH.ManifoldCurvature
import QIQTH.ManifoldCommutator
import QIQTH.PseudoRiemannian
import QIQTH.LeviCivita
import QIQTH.ClausiusIntegral
import QIQTH.ClausiusToPernull
import QIQTH.Raychaudhuri
import QIQTH.Unruh
import QIQTH.FQBoundConditional
import QIQTH.FQBoundCGP
import QIQTH.FQBoundMicro
import QIQTH.GRFromMicro
import QIQTH.CodeCapacityBridge
import QIQTH.CornerConstruction
import QIQTH.EmergentSpacetime
import QIQTH.MetricFromState
import QIQTH.MetricRefinement
import QIQTH.MetricRefinement2D
import QIQTH.ContinuumLimit
import QIQTH.IsotropyNoGo
import QIQTH.StencilGraph
import QIQTH.StencilWalk
import QIQTH.StencilDistortion
import QIQTH.StencilGH
import QIQTH.StencilDimGraph
import QIQTH.StencilDimWalk
import QIQTH.StencilDimDistortion
import QIQTH.StencilDimGH
import QIQTH.StencilFromState
import QIQTH.TorusStencilGraph
import QIQTH.TorusStencilWalk
import QIQTH.TorusStencilGH
import QIQTH.TripodGH
import QIQTH.ConeMetric
import QIQTH.ConeGH
import QIQTH.TorusFromState
import QIQTH.TripodFromState
import QIQTH.SphereMetric
import QIQTH.SphereGH
import QIQTH.ConeIntrinsicGraph
import QIQTH.ConeIntrinsicWalk
import QIQTH.ConeIntrinsicGH
import QIQTH.ConeFromState
import QIQTH.ConeFlat
import QIQTH.HawkingWick
import QIQTH.MinkowskiDiamond
import QIQTH.CausalStencil
import QIQTH.DeSitterTime
import QIQTH.RecordChannel
import QIQTH.RecordEquilibrium
import QIQTH.RecordUnraveling
import QIQTH.InteractingChannel
import QIQTH.BellCutRank
import QIQTH.ReducedDensity
import QIQTH.RecordMincut
import QIQTH.RecordMincutMPS
import QIQTH.RecordMincutEntropy
import QIQTH.OneParticleMeasure
import QIQTH.WeightedL2
import QIQTH.PosFreqDomain
import QIQTH.OneParticleInner
import QIQTH.PosFreqInner
import QIQTH.OneParticleBoost
import QIQTH.OneParticleMap
import QIQTH.OneParticleFockBridge
import QIQTH.FreeFieldCorner
import QIQTH.QG.FinitePoincareNoGo
import QIQTH.QG.LatticeDispersionBound
import QIQTH.QG.CpsuvGate
import QIQTH.QG.DiamondTipGate
import QIQTH.QG.StateLevelLVGate
import QIQTH.QG.FiniteModularRecurrence
import QIQTH.QG.LatticeDispersion
import QIQTH.QG.FiniteTracePhase5
import QIQTH.QG.ExactRT
import QIQTH.QG.MaxFlowMinCut
import QIQTH.QG.MinCutRecords
import QIQTH.QG.WardSpeedSplitting
import QIQTH.QG.CpsuvEscape
import QIQTH.QG.FiniteMatterNoLorentz
import QIQTH.QG.EntropyNotCardinality
-- THE NON-TRACIALITY campaign, N1: the finite Gibbs state is genuinely non-tracial —
-- ω(E_{nm}·E_{mn}) = w_n ≠ w_m = ω(E_{mn}·E_{nm}) when the weights differ. HONEST SCOPE:
-- a state-level inequality, NOT a type classification (see the file header). Standard three:
import QIQTH.NonTracial.FiniteNonTrace
import QIQTH.NonTracial.TowerNonTrace
import QIQTH.NonTracial.ModularNonTrivial
import QIQTH.NonTracial.Checkpoint
import QIQTH.NonTracial.ModularDataComplete
