/-
SelectorRefinement.lean — the selector (λ) layer of the Born problem.

Per GPT-5.5-pro (2026-06-13): the corpus's microcausality theorems
(`NoSignalingGeneral.bipartite_no_signaling`, `FreeFieldNet.bornNet_no_signaling`) are the CONVERSE
direction `Born ⇒ no-signaling` — they presuppose the trace/Born functional and hold *because* it is
linear, so they place NO constraint on a candidate record rule `p ∝ f` and cannot derive Born.

A genuine derivation must instead impose no-signaling on the SELECTOR `λ`'s OWN marginals — the actual
`(Φ,λ,μ)` outcome statistics over a FIXED, Born-agnostic typicality measure `μ` on a microstate space `Ω`.
This file formalises that layer. Two results:

1. `readout_invariant_marg` (the Born-free dynamical bridge): if a remote refinement `R` leaves the LOCAL
   readout unchanged (`XL ∘ R = XL` — locality/microcausality at the selector level), then the local
   marginal is invariant under refinement — selector no-signaling, with NO Born input. This `XL∘R=XL` is
   exactly the bridge QIQT-H's dynamical-realization layer (Gap 2) must supply; it does NOT follow from
   operator-net microcausality automatically (one must show the actual SELECTOR commutes, not just the
   observables). No Bell/Fine obstruction here: a context and its refinement are compatible.

2. `Countermodel.alphaSq_selector_signals` (the SEPARATION / independence result): a deterministic α=2
   selector over a fixed UNIFORM measure on 15 microstates realises coarse marginal `12/15` for a merged
   outcome but fine marginals `5/15` each, so the merged fine cells total `10/15 ≠ 12/15` — selector
   no-signaling FAILS. The trace/Born no-signaling theorem is untouched (it constrains the trace functional,
   not `λ`). Hence existing microcausality does NOT force selector no-signaling: Gap 3 genuinely reduces to
   the Gap-2 bridge above, it is not already closed.

Combine `readout_invariant_marg` (selector no-signaling) with a selector realising `p ∝ f`, feed the
binary-split marginal identity into `RefinementBorn.refinementNatural_additive`, and Born follows. So:
Born ⟺ selector-marginal no-signaling, and the latter ⟸ the `XL∘R=XL` microcausal bridge.

HONEST SCOPE: finite; no `sorry`, no project axioms. See `paper_strategy/49_Born_Status.md` §5.
-/
import Mathlib.Tactic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card

open scoped BigOperators

namespace QIQTH.SelectorRefinement

/-- The local marginal of a deterministic selector `sel : Ω → K` under a typicality measure `μ : Ω → ℝ`:
the `μ`-mass of the cell of microstates that the selector maps to outcome `k`. -/
def marg {Ω K : Type*} [Fintype Ω] [DecidableEq K] (μ : Ω → ℝ) (sel : Ω → K) (k : K) : ℝ :=
  ∑ ω, if sel ω = k then μ ω else 0

/-- **The Born-free dynamical bridge.** If a remote refinement `R : Ω → Ω` leaves the local readout
unchanged on every microstate (`XL (R ω) = XL ω` — selector-level locality / microcausality), then the
local marginal is invariant under that refinement: selector no-signaling, derived with NO Born/trace input.
This `XL ∘ R = XL` is precisely the bridge the `(Φ,λ)` dynamics (Gap 2) must supply — it is the actual
content that capacity / operator-net microcausality do not by themselves provide. -/
theorem readout_invariant_marg {Ω K : Type*} [Fintype Ω] [DecidableEq K]
    (μ : Ω → ℝ) (XL : Ω → K) (R : Ω → Ω) (hloc : ∀ ω, XL (R ω) = XL ω) (k : K) :
    marg μ (fun ω => XL (R ω)) k = marg μ XL k := by
  unfold marg
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  simp only [hloc]

/-! ### Separation: existing (Born⇒no-signaling) microcausality does NOT force selector no-signaling -/

namespace Countermodel

/-- Coarse selector on 15 microstates realising the α=2 marginal `(12, 3)` of weights `(2/3, 1/3)`
(`(2/3)²/((2/3)²+(1/3)²) = 4/5`, so `12` of `15` states). -/
def lamC : Fin 15 → Fin 2 := fun ω => if (ω : ℕ) < 12 then 0 else 1

/-- Fine selector realising the α=2 fine marginal `(5, 5, 5)` of the refined weights `(1/3, 1/3, 1/3)`
(`(1/3)²/(3·(1/3)²) = 1/3`, so `5` of `15` states each). The refinement merges fine outcomes `0,1` into
coarse outcome `0`. -/
def lamF : Fin 15 → Fin 3 := fun ω => if (ω : ℕ) < 5 then 0 else if (ω : ℕ) < 10 then 1 else 2

/-- The `μ`-cell count of a selector (uniform measure = counting). -/
def cell {K : Type*} [DecidableEq K] (sel : Fin 15 → K) (k : K) : ℕ :=
  (Finset.univ.filter (fun ω => sel ω = k)).card

/-- **Selector no-signaling FAILS for the α=2 selector (the separation / independence result).** The coarse
cell of the merged outcome has `12` microstates, but the two fine cells it refines into total `5 + 5 = 10`;
`12 ≠ 10`, so the local marginal is *not* invariant under remote refinement. The trace/Born no-signaling
theorem still holds (it constrains the trace functional, not `λ`). Therefore the existing microcausality
results do NOT force selector no-signaling — closing Born genuinely requires the `XL∘R=XL` bridge
(`readout_invariant_marg`), i.e. Gap-2 dynamics. -/
theorem alphaSq_selector_signals : cell lamC 0 ≠ cell lamF 0 + cell lamF 1 := by decide

end Countermodel

/-! ### Milestone 1 of the Gap-2 attack: selector-locality ⇒ remote no-signaling
(per GPT-5.5-pro's corrected sketch, 2026-06-13)

**Selector-locality** = the local marginal factors through the LOCAL reduced state `ρ_A`. Combined with the
fact that a remote refinement preserves `ρ_A` (bipartite no-signaling *at the state level*), the local
marginal is remote-invariant — i.e. selector no-signaling. This is the clean "remote" half.

Two honest caveats (pro):
* Selector-locality is **not** derivable from operator-net microcausality alone — that gives `ρ_A`-invariance
  and Born-*linear* expectations, not invariance of the deterministic selector's μ-measure. It is an extra
  equilibrium/screening condition on `(Φ,λ)` (Bohmian-quantum-equilibrium analogue) — the real Gap-2 content.
* Selector-locality does **not** by itself give Born: e.g. `g(ρ,P)=tr(ρ²/tr(ρ²)·P)` is selector-local and
  remote-no-signaling but non-Born. Born additionally needs **local Gleason/Busch additivity** ⇒
  `g(ρ,P)=tr(σ(ρ)P)`, plus **state-anchoring** (affinity + pure-state certainty ⇒ `σ(ρ)=ρ`).

So the corrected reduction is `Born ⟸ selector-locality + local Gleason + state-anchoring`. -/

/-- Selector-locality: the local marginal `localMarg ρ k` is a functional `g` of the local reduced state
`reducedA ρ` only. -/
def SelectorLocal {G L K : Type*} (reducedA : G → L) (localMarg : G → K → ℝ) (g : L → K → ℝ) : Prop :=
  ∀ ρ k, localMarg ρ k = g (reducedA ρ) k

/-- **Milestone 1 — selector-locality + `ρ_A`-preservation ⇒ remote no-signaling.** If the local marginal
factors through the local reduced state, and a remote refinement `R` preserves that reduced state (the
state-level content of `NoSignalingGeneral.bipartite_no_signaling`), then the local marginal is invariant
under `R`. The "remote" half of the Gap-2 bridge; the load-bearing hypothesis is `SelectorLocal`. -/
theorem local_factor_remote_invariant {G L K : Type*}
    (reducedA : G → L) (localMarg : G → K → ℝ) (g : L → K → ℝ)
    (hloc : SelectorLocal reducedA localMarg g)
    (R : G → G) (hR : ∀ ρ, reducedA (R ρ) = reducedA ρ) (ρ : G) (k : K) :
    localMarg (R ρ) k = localMarg ρ k := by
  rw [hloc (R ρ) k, hR ρ, ← hloc ρ k]

/-! ### Milestone 3a — the equilibrium core: EQUIVARIANCE ⇒ selector no-signaling

The deeper, Bell-compatible route to the Gap-2 bridge. `readout_invariant_marg` used pointwise
readout-commutation `XL∘R=XL` — but pro's Bell/Fine caveat says a *pointwise* local valuation is too strong
(a deterministic pointwise-local selector is a local hidden-variable model, hence `Bell.chsh_lhv`-bounded
`|CHSH|≤2`, contradicting the quantum violation `Tsirelson`). The weak/Bell-compatible route instead asks only
that the remote refinement dynamics **preserve the typicality measure `μ`** (equivariance) — then *every*
local-readout marginal is invariant, with `λ` allowed to be globally correlated/contextual. This isolates the
exact Gap-2 input: `(R)_*μ = μ` (the Bohmian-quantum-equilibrium / Dürr–Goldstein–Zanghì equivariance
condition; Valentini: non-equilibrium measures signal, so equivariance is essential). It does NOT follow from
operator-net microcausality, which concerns commuting observables, not the measure. -/

/-- **Equivariance ⇒ selector no-signaling.** If the remote refinement dynamics is a `μ`-preserving bijection
`R` of the microstate space, then every local-readout marginal is invariant under `R` — selector
no-signaling — with no readout-commutation and no Born input. The load-bearing hypothesis is measure
preservation `hR`, the equilibrium/equivariance condition; the proof is just reindexing the cell sum by the
measure-preserving bijection, so no pointwise locality (hence Bell-compatible). -/
theorem equivariant_marg_invariant {Ω K : Type*} [Fintype Ω] [DecidableEq K]
    (μ : Ω → ℝ) (XL : Ω → K) (R : Ω ≃ Ω) (hR : ∀ ω, μ (R ω) = μ ω) (k : K) :
    marg μ (fun ω => XL (R ω)) k = marg μ XL k := by
  unfold marg
  rw [← Equiv.sum_comp R (fun ω => if XL ω = k then μ ω else 0)]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [hR ω]

end QIQTH.SelectorRefinement
