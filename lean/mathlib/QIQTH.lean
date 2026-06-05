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
-- Sub-theorems A, B, C for the Canonical IC Measure Principle:
import QIQTH.TypicalityMackeyGleason
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
-- Phase 1 of the Tomita–Takesaki roadmap (TOMITA_TAKESAKI_ROADMAP.md): the
-- projection-valued-measure / bounded-spectral-theorem keystone. Structural PVM
-- content proved axiom-free; the analytic core (σ-additivity, bounded-Borel FC,
-- spectral theorem) is the named Phase-1 target. General Mathlib-bound material;
-- ZERO project axioms:
import QIQTH.Spectral.PVM
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
