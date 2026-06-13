/-
SelectionDynamics.lean — scaffold for Gap-2 Phase 3c: the (Φ,λ) selection-dynamics model.

GOAL (multi-session program): derive selector EQUIVARIANCE `(R)_*μ = μ` — hence selector no-signaling
(`SelectorRefinement.equivariant_marg_invariant`) — from a concrete *microcausal* selection model over a
FIXED, Born-agnostic typicality measure `μ`, the Dürr–Goldstein–Zanghì-equivariance analogue. With local
Gleason + state-anchoring (paper_strategy/49_Born_Status.md §6) this would close Born.

THIS FILE = the scaffold (first increment): the model structure, the no-signaling wiring, and a non-vacuous
Born-agnostic equivariant instance (the uniform measure is preserved by ANY bijective remote action, so the
REMOTE no-signaling half is achievable WITHOUT assuming Born). The OPEN core — deriving equivariance for the
ACTUAL non-uniform dynamics, and showing the local marginals over `μ` are Born — is the frontier (§7). Honest
risk (GPT-5.5-pro): if the only equivariant `μ` is `|Ψ|²` itself the step is circular; the non-circular hope
is a Valentini-style relaxation of a Born-agnostic `μ` to equivariance under the dynamics.

HONEST SCOPE: finite; no `sorry`, no project axioms.
-/
import QIQTH.SelectorRefinement

namespace QIQTH.SelectionDynamics

open QIQTH.SelectorRefinement

/-- A finite selection-dynamics model: a microstate space `Ω` with a typicality measure `μ`, a deterministic
local selector (record readout) `sel`, a remote-refinement action `R` on the microstates, and the
equilibrium/equivariance condition `(R)_*μ = μ` (here as `μ (R ω) = μ ω`). -/
structure SelectionModel (Ω K : Type*) [Fintype Ω] [DecidableEq K] where
  /-- the fixed, Born-agnostic typicality measure on microstates -/
  μ : Ω → ℝ
  /-- the deterministic local readout (which record is actual) -/
  sel : Ω → K
  /-- the remote refinement acting as a bijection of the microstate space -/
  R : Ω ≃ Ω
  /-- equivariance: the remote refinement preserves the typicality measure -/
  equivariant : ∀ ω, μ (R ω) = μ ω

variable {Ω K : Type*} [Fintype Ω] [DecidableEq K]

/-- **Any equivariant selection model has selector no-signaling.** The local marginal is invariant under the
remote refinement — immediate from the equilibrium core `equivariant_marg_invariant`. So in this model class
the *entire* remaining Born content sits in two places: that `μ` is the genuine dynamical (equivariant)
measure, and that the local marginals `marg μ sel` are Born. -/
theorem SelectionModel.no_signaling (M : SelectionModel Ω K) (k : K) :
    marg M.μ (fun ω => M.sel (M.R ω)) k = marg M.μ M.sel k :=
  equivariant_marg_invariant M.μ M.sel M.R M.equivariant k

/-- **Born-agnostic equivariant instance (non-vacuity, and the remote half for free).** The uniform /
counting measure is preserved by ANY bijection, so any deterministic selector with any bijective remote
action over uniform `μ` is automatically equivariant. This witnesses that the REMOTE no-signaling half is
reachable with a measure that assumes *nothing* about Born — isolating the genuine open content as (i) the
local marginals being Born and (ii) equivariance for the actual non-uniform dynamical measure. -/
def uniformModel (sel : Ω → K) (R : Ω ≃ Ω) : SelectionModel Ω K where
  μ := fun _ => 1
  sel := sel
  R := R
  equivariant := fun _ => rfl

/-- The uniform model is inhabitable for any selector/action and has selector no-signaling. -/
theorem uniformModel_no_signaling (sel : Ω → K) (R : Ω ≃ Ω) (k : K) :
    marg (uniformModel sel R).μ (fun ω => sel (R ω)) k = marg (uniformModel sel R).μ sel k :=
  (uniformModel sel R).no_signaling k

end QIQTH.SelectionDynamics
