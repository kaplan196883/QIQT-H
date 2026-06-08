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
import QIQTH.HolevoCoarseGraining
import QIQTH.DPI
import QIQTH.ShannonFano
import QIQTH.BellMarginal
import QIQTH.Bell
import QIQTH.Tsirelson
-- Central audits proposed by GPT-5.5-pro:
import QIQTH.H1H2Audit
import QIQTH.NoConcentration
-- Entropy-focused audits from second GPT-5.5-pro consultation:
import QIQTH.EntropyBridge
import QIQTH.BranchLedger
import QIQTH.ArakiInterface
-- Final non-entropy audits proposed by GPT-5.5-pro:
import QIQTH.FQDynamicsNoGo
import QIQTH.CompressionLocality
-- Born-rule audits from fourth GPT-5.5-pro consultation:
import QIQTH.NoBornFromNothing
import QIQTH.EquivarianceGap
import QIQTH.BornTypicality
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
-- Prize Stage 3.1 (finite case): the matrix spectral theorem packaged as a PVM — eigenprojections
-- Pᵢ = U·diag(δᵢ)·U⋆ with ∑Pᵢ=1 (resolution of identity), Pᵢ²=Pᵢ, PᵢPⱼ=0, Pᵢ⋆=Pᵢ. The finite,
-- axiom-free case of the bounded-spectral-theorem target (continuum stays open). Standard axioms:
import QIQTH.SpectralPVM
-- Prize Stage 3′ (Track B): free-field / standard-subspace modular theory via the bounded-operator
-- approach of Rieffel–Van Daele (PJM 69, 1977). On Mathlib's StandardSubspace: the projections
-- P,Q onto 𝒦,i𝒦, R=P+Q, and RvD Prop 2.2(1) ⟪Rξ,ξ⟫=‖Pξ‖²+‖Qξ‖² (engine for R injective). Standard axioms:
import QIQTH.StandardSubspaceModular
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
import QIQTH.Fock.WeylOp
import QIQTH.Fock.WeylCovariance
import QIQTH.Fock.WeylCCR
import QIQTH.Fock.WeylBit
import QIQTH.Fock.WeylBitProcess
import QIQTH.Fock.WeylBitMeasure
