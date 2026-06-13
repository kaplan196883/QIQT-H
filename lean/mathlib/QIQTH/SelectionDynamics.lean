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

/-- **Equivariance ⇒ the martingale conservation law.** In an equivariant selection model the
μ-expectation of *every* observable `W` is conserved under one selection step `R`:
`E_μ[W ∘ R] = E_μ[W]`. This is exactly the martingale-increment condition that
`BornRoutes.born_from_martingale` takes as its Born-strength premise (`hmart`): so in this model class
the conservation needed for the optional-stopping Born derivation is **not an extra assumption** — it
is the equivariance of the typicality measure. The open content collapses to a single physical claim:
that the actual `(Φ,λ)` dynamics preserves a Born-agnostic `μ`. (Proof: rewrite the weight by
equivariance `μ ω = μ(R ω)` then reindex the sum by the bijection `R`.) -/
theorem SelectionModel.expectation_conserved (M : SelectionModel Ω K) (W : Ω → ℝ) :
    ∑ ω, M.μ ω * W (M.R ω) = ∑ ω, M.μ ω * W ω := by
  calc ∑ ω, M.μ ω * W (M.R ω)
      = ∑ ω, M.μ (M.R ω) * W (M.R ω) := by
        refine Finset.sum_congr rfl (fun ω _ => ?_); rw [M.equivariant ω]
    _ = ∑ ω, M.μ ω * W ω := Equiv.sum_comp M.R (fun ω => M.μ ω * W ω)

/-! ### First concrete instance where uniform typicality REPRODUCES Born (the Zurek envariance route)

Building on the scaffold: a model where the *Born-agnostic* uniform measure actually yields Born marginals.
The microstate space is fine-grained — outcome `k` is realised by some number of equal sub-records — and the
uniform marginal of `k` is just that count. If the fine-graining encodes the Born weights (count `= M·w_k`,
the rational-case envariance refinement), the normalised marginal equals `w_k`: **uniform counting reproduces
Born.** Combined with `equivariant_marg_invariant` (uniform `μ` is preserved by any permutation of the fine
records), this instance has BOTH Born marginals AND selector no-signaling, end-to-end, axiom-free.

HONEST residual: the premise `count = M·w_k` (the environment fine-grains outcome `k` into `M·w_k` equal
sub-records) is exactly the envariance / refinement-additivity premise proved necessary in
`RefinementBorn.lean` — it is NOT derived here. So this is the Zurek route realised as a selection model with
the residual made fully explicit and machine-checked, not a from-nothing derivation. -/

/-- Over the uniform (Born-agnostic) measure, the marginal of outcome `k` is exactly the number of fine
microstates selecting `k`. -/
theorem marg_uniform_eq_card (sel : Ω → K) (k : K) :
    marg (fun _ => (1 : ℝ)) sel k = ((Finset.univ.filter (fun ω => sel ω = k)).card : ℝ) := by
  simp only [marg, Finset.sum_boole]

/-- **Born from uniform typicality, given the envariance fine-graining.** If a deterministic selector over the
uniform measure on the fine microstates has exactly `M · w k` microstates selecting outcome `k`, then the
normalised uniform marginal equals the Born weight `w k`. Uniform counting reproduces Born; the residual is
exactly that the fine-graining encodes the weights. -/
theorem born_from_uniform (sel : Ω → K) (w : K → ℝ) (M : ℝ) (hM : M ≠ 0)
    (hfine : ∀ k, ((Finset.univ.filter (fun ω => sel ω = k)).card : ℝ) = M * w k) (k : K) :
    marg (fun _ => (1 : ℝ)) sel k / M = w k := by
  rw [marg_uniform_eq_card, hfine k, mul_comm, mul_div_assoc, div_self hM, mul_one]

/-- The explicit fine-grained microstate space: outcome `k` is realised by `m k` equal sub-records (a
microstate is a pair `(k, i)`, `i < m k`); the local selector is the first projection `Sigma.fst`. The fiber
of `Sigma.fst` over `k` has exactly `m k` microstates, so `born_from_uniform` applies once `m k = M·w k`
(the weight-encoding / envariance residual). Left as the natural next increment (the `Σ`-fiber cardinality
needs a short `Sigma.fst`-reduction lemma). -/
abbrev FineSpace {n : ℕ} (m : Fin n → ℕ) : Type := Σ k : Fin n, Fin (m k)

end QIQTH.SelectionDynamics
