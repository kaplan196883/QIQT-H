/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# PHOTON_FIELD_PLAN P8 — the centered (edge-mode) entropy decomposition

Per the PHOTON_FIELD_PLAN crux (§0, GPT-5.5-pro): for the photon, regional information across a cut is
generally a **centered flux-sector algebra** `𝒜_R ≃ ⊕_q 𝓑(𝓗_{R,q})`, with `q` the **boundary-flux
sectors** (the electric-center data `E_⊥|_{∂R}`) — the photon's local algebra is *not* a simple factor
because of the Gauss-law constraint.  The regional entanglement entropy then splits into a **bulk piece +
a Shannon piece over the boundary-flux superselection** — the **edge-mode / Kabat contact-term** structure:

  `S(ρ_R) = H(p_q) + Σ_q p_q S(ρ_{R,q})`,   `p_q` = the boundary-flux distribution.

This is the *same* centered/graded decomposition as the electron's charge/parity-graded capacity
(`QIQTH/Fock/Dirac/GradedCapacity.lean`) — only the superselection label changes from fermion *parity* to
**boundary flux**.  So P8 reuses that machinery verbatim (`gradedShannon_chain_rule`,
`gradedShannon_le_log_total`), relabelled, and adds the photon-specific facts:

* `photon_edge_entropy_decomp` — the centered decomposition `S = H(p_q) + Σ_q p_q S_q` (the edge-mode home).
* `photon_edge_term_nonneg` — the boundary-flux Shannon term `H(p_q) ≥ 0`: at finite cutoff the edge modes
  add **positively** to the entanglement entropy, vanishing exactly when the boundary flux is *definite*
  (a single sector = a factor, no edge contribution).
* `photon_edge_capacity_le` — the centered capacity bound `S ≤ log(Σ_q dim 𝓗_{R,q})`.

HONEST scope (GPT-5.5-pro): the "nontrivial center" is the *regulated/cut* statement; in continuum AQFT
nice contractible regions/wedges can be *factors* (single flux sector ⟹ `H(p)=0`, recovered here).  The
**Kabat contact-term sign** is a *continuum renormalization* subtlety — at finite cutoff the Shannon edge
term is positive (as proved here); the universal contact coefficient is NOT encoded as a naive positive
number.  The full Gauss-law boundary algebra + the heat-kernel contact determinant are the deferred
frontier P10.  Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.  Free Maxwell.
-/
import QIQTH.Fock.Dirac.GradedCapacity

namespace QIQTH.Fock.Photon

open Real
open scoped BigOperators

variable {Q : Type*} [Fintype Q] {I : Q → Type*} [∀ q, Fintype (I q)]

/-- **The photon centered (edge-mode) entropy decomposition** `S(ρ_R) = H(p_q) + Σ_q p_q S(ρ_{R,q})`.
For a boundary-flux distribution `p` over the sectors `Q` and a within-sector (bulk) state `w q` on each
sector `I q`, the regional record entropy splits into the **boundary-flux mixing entropy** `H(p_q)` (the
edge-mode / contact-term piece) plus the **average bulk entropy** `Σ_q p_q S(w_q)`.  This is the photon
analogue of the electron's `gradedShannon_chain_rule`, with the superselection label = boundary flux
(electric-center `E_⊥|_{∂R}`) rather than fermion parity. -/
theorem photon_edge_entropy_decomp (p : Q → ℝ) (w : ∀ q, I q → ℝ) (hw : ∀ q, ∑ i, w q i = 1) :
    ∑ q, ∑ i, Real.negMulLog (p q * w q i)
      = (∑ q, Real.negMulLog (p q)) + ∑ q, p q * ∑ i, Real.negMulLog (w q i) :=
  QIQTH.Fock.Dirac.gradedShannon_chain_rule p w hw

/-- **The edge-mode (boundary-flux) term is non-negative** `H(p_q) ≥ 0`.  For a boundary-flux probability
distribution (`0 ≤ p_q ≤ 1`), the Shannon mixing entropy over the flux sectors is non-negative: at finite
cutoff the **edge modes add positively** to the regional entanglement entropy.  It vanishes exactly when
the boundary flux is *definite* (`p` concentrated on one sector) — i.e. when the regional algebra is a
*factor* (no center, no edge contribution).  (HONEST: the continuum Kabat contact-term *sign* is a
renormalization subtlety beyond this finite-cutoff positivity — see the module header / P10.) -/
theorem photon_edge_term_nonneg (p : Q → ℝ) (hp0 : ∀ q, 0 ≤ p q) (hp1 : ∀ q, p q ≤ 1) :
    0 ≤ ∑ q, Real.negMulLog (p q) :=
  Finset.sum_nonneg fun q _ => Real.negMulLog_nonneg (hp0 q) (hp1 q)

variable [Nonempty Q] [∀ q, Nonempty (I q)]

/-- **The photon centered capacity bound** `S(ρ_R) ≤ log(Σ_q dim 𝓗_{R,q})`.  The centered (edge-mode)
regional record entropy is bounded by the log of the total dimension of the centered flux-sector algebra
`⊕_q 𝓑(𝓗_{R,q})` — combining the edge-mode decomposition, the per-sector (bulk) capacity, and the
Gibbs/log-sum collapse (the photon analogue of the electron's `gradedShannon_le_log_total`).  As always
for the bosonic photon, each `dim 𝓗_{R,q}` is finite only with a per-sector photon-number cutoff
(P2/P3). -/
theorem photon_edge_capacity_le (p : Q → ℝ) (w : ∀ q, I q → ℝ)
    (hp : ∀ q, 0 ≤ p q) (h1 : ∑ q, p q = 1) (hw0 : ∀ q i, 0 ≤ w q i) (hw : ∀ q, ∑ i, w q i = 1) :
    ∑ q, ∑ i, Real.negMulLog (p q * w q i) ≤ Real.log (∑ q, (Fintype.card (I q) : ℝ)) :=
  QIQTH.Fock.Dirac.gradedShannon_le_log_total p w hp h1 hw0 hw

end QIQTH.Fock.Photon
