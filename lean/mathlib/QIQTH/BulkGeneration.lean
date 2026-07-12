/-
  BULK GENERATION — a boundary evolution that MOVES the emergent metric, with an explicit
  evolution law (duality campaign, brick D4b).  The GENERATION half of D4a.

  D4a (`QIQTH/BulkRelaxation.lean`) proved the RC dephasing channel FREEZES the emergent bulk
  metric: the record LEDGER (the matrix diagonal) is invariant, so every area functional is a
  conserved charge and the decoded metric trajectory is CONSTANT (`bulk_metric_frozen`).  This
  brick is the complement: a boundary evolution that genuinely MOVES the ledger induces a
  nontrivial bulk metric TRAJECTORY, and we give its explicit evolution law.

  THE HONEST SOURCE OF LEDGER MOTION.  RC phase-dephasing fixes the diagonal (D4a), and so does
  the free/coherent flow (it only rotates phases).  The move that actually transports the
  diagonal is a classical POPULATION-TRANSFER / continuous-time Markov rate generator `Q` acting
  on the populations, `p'(s) = Q·p(s)`.  The bulk equation of motion is then the PUSHFORWARD of
  this boundary rate equation through the FIXED LINEAR area decoder `AreaMap.reconstruct`:

    • PART A — the abstract evolution law (`bulk_chain`, `bulk_eom`): for any linear
      `areaOfLedger : Ledger →ₗ AreaData` and linear `reconstruct' : AreaData →ₗ Metric`, the
      velocity of the decoded metric trajectory is the decoder pushforward of the ledger
      velocity — the composite-linear-decoder chain rule.  With `p'(s) = Q·p(s)` this reads
      `d/ds reconstruct'(areaOfLedger(p s)) = reconstruct'(areaOfLedger(Q·p(s)))`.  THIS is the
      load-bearing result.
    • PART B — the Markov generator and its exponential trajectory (`IsMarkovGeneratorCol`,
      `pExp`, `hasDerivAt_pExp`): the population trajectory `p(t) = exp(tQ)·p0` solves the rate
      equation, giving a concrete moving ledger to feed Part A.
    • PART C — grounding in the REAL decoder (`reconstructL`, the concrete `AreaMap.reconstruct`
      bundled as the linear map it is) and the honest nontriviality contrast with D4a
      (`frozen_of_velocity_ker`, `metric_moving_iff`).

  ⚠ MANDATORY FIREWALL (verifier-binding, honest).
  • D4b is the PUSHFORWARD of a SPECIFIED boundary Markov / population-transfer dynamics through
    the FIXED LINEAR area decoder.  It is NOT the RC/dephasing channel (which freezes the metric
    — D4a) and NOT the free flow (which also fixes the diagonal).  It is NOT yet an autonomous
    bulk gravitational equation of motion: the velocity depends on the boundary ledger data
    `p(s)`, not on the metric `h(s)` alone.  An autonomous bulk-only law would additionally
    require `ker(reconstruct ∘ areaOfLedger)` to be `Q`-invariant — NOT claimed here.
  • Nontriviality is a REAL hypothesis (`reconstruct'(areaOfLedger(Q·p s)) ≠ 0`); without it the
    ledger may move inside the decoder kernel and the metric still freezes — the D4a case
    recovered here as `frozen_of_velocity_ker`.
  • Finite-dimensional, linearized decoder, chosen basis (inherits `AreaDecoder`'s scope).  NOT
    the conjecture, NOT the strong holographic principle, NOT quantum gravity.
  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.AreaDecoder

namespace QIQTH.BulkGeneration

open QIQTH.AreaMap

-- Matrices carry no canonical norm; we fix the Frobenius normed ring/algebra (the QIQTH
-- convention) throughout, so the metric codomain `Matrix (Fin 4) (Fin 4) ℝ` is a genuine normed
-- space and the differentiability statements below are well-formed.  The choice of (equivalent)
-- norm is immaterial to the finite-dimensional derivative statements.
open scoped Matrix.Norms.Frobenius

/-- The boundary record populations — the classical/geometric ledger data. -/
abbrev Ledger (ι : Type*) := ι → ℝ

/-- The ray-probe area data `A(v) = δA_ray(v)(h)`, the decoder's input. -/
abbrev AreaData := (Fin 4 → ℝ) → ℝ

/-- The reconstructed bulk metric perturbation, the decoder's output. -/
abbrev Metric := Matrix (Fin 4) (Fin 4) ℝ

/-! ## Part A — the abstract evolution law (the composite-linear-decoder chain rule) -/

/-- **★★ THE BULK METRIC TRAJECTORY'S VELOCITY = the decoder pushforward of the ledger
    velocity.**  For any linear `areaOfLedger` and linear `reconstruct'`, if the ledger path `p`
    has velocity `v` at time `s`, then the decoded metric path
    `t ↦ reconstruct'(areaOfLedger(p t))` has velocity `reconstruct'(areaOfLedger v)`.  The chain
    rule for the (continuous, finite-dim) composite linear decoder. -/
theorem bulk_chain {ι : Type*} [Fintype ι]
    (areaOfLedger : Ledger ι →ₗ[ℝ] AreaData) (reconstruct' : AreaData →ₗ[ℝ] Metric)
    (p : ℝ → Ledger ι) (s : ℝ) (v : Ledger ι) (hp : HasDerivAt p v s) :
    HasDerivAt (fun t => reconstruct' (areaOfLedger (p t))) (reconstruct' (areaOfLedger v)) s := by
  let D : Ledger ι →L[ℝ] Metric := (reconstruct'.comp areaOfLedger).toContinuousLinearMap
  simpa [D] using
    (HasFDerivAt.comp_hasDerivAt_of_eq (f := p) (x := s) (D.hasFDerivAt (x := p s)) hp rfl)

/-- **★★ THE BULK EQUATION OF MOTION.**  With the ledger obeying the Markov rate equation
    `p'(s) = Q·p(s)`, the induced bulk metric velocity is `reconstruct'(areaOfLedger(Q·p(s)))` —
    the pushforward of the population rate through the decoder. -/
theorem bulk_eom {ι : Type*} [Fintype ι]
    (areaOfLedger : Ledger ι →ₗ[ℝ] AreaData) (reconstruct' : AreaData →ₗ[ℝ] Metric)
    (Q : Matrix ι ι ℝ) (p : ℝ → Ledger ι) (s : ℝ) (hp : HasDerivAt p (Q.mulVec (p s)) s) :
    HasDerivAt (fun t => reconstruct' (areaOfLedger (p t)))
      (reconstruct' (areaOfLedger (Q.mulVec (p s)))) s :=
  bulk_chain areaOfLedger reconstruct' p s (Q.mulVec (p s)) hp

/-! ## Part B — the Markov generator and the exponential trajectory -/

/-- A continuous-time Markov / rate generator in the column-sums-zero convention (matching the
    action `p ↦ Q·p` on populations): off-diagonal rates are nonnegative and each column sums to
    zero (probability conservation). -/
structure IsMarkovGeneratorCol {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℝ) : Prop where
  offdiag_nonneg : ∀ ⦃i j⦄, i ≠ j → 0 ≤ Q i j
  col_sum_zero : ∀ j, ∑ i, Q i j = 0

section Exponential

/-- The population trajectory `p(t) = exp(tQ)·p0` generated by the rate matrix `Q`. -/
noncomputable def pExp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (p0 : Ledger ι) : ℝ → Ledger ι :=
  fun t => (NormedSpace.exp (t • Q)).mulVec p0

/-- **★ THE EXPONENTIAL TRAJECTORY SOLVES THE RATE EQUATION**: `p(t) = exp(tQ)·p0` satisfies
    `p'(s) = Q·p(s)` — the concrete moving ledger fed to the bulk EOM.  Proved via the matrix
    exponential derivative `d/dt exp(t•Q) = Q · exp(t•Q)` (under the L∞ operator norm, whose
    topology agrees with the canonical matrix topology) pushed through the linear map
    `M ↦ M·p0`. -/
theorem hasDerivAt_pExp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (p0 : Ledger ι) (s : ℝ) :
    HasDerivAt (pExp Q p0) (Q.mulVec (pExp Q p0 s)) s := by
  -- derivative of the matrix exponential path: `d/ds exp(s•Q) = Q * exp(s•Q)`.
  have hexp : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • Q))
      (Q * NormedSpace.exp (s • Q)) s := hasDerivAt_exp_smul_const' Q s
  -- `M ↦ M·p0` is linear, hence (finite dim) a continuous linear map.
  let L : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ) :=
    { toFun := fun M => M.mulVec p0
      map_add' := fun M N => by ext i; simp [Matrix.add_mulVec]
      map_smul' := fun c M => by ext i; simp [Matrix.smul_mulVec] }
  let D : Matrix ι ι ℝ →L[ℝ] (ι → ℝ) := L.toContinuousLinearMap
  -- chain rule, then rewrite `(Q * exp(s•Q))·p0 = Q·(exp(s•Q)·p0)`.
  have key := HasFDerivAt.comp_hasDerivAt_of_eq (f := fun u : ℝ => NormedSpace.exp (u • Q)) (x := s)
    (D.hasFDerivAt (x := NormedSpace.exp (s • Q))) hexp rfl
  simpa [D, L, pExp, Function.comp, Matrix.mulVec_mulVec] using key

/-- **The bulk metric trajectory along the `exp(tQ)` boundary evolution.**  Composing the
    exponential-trajectory rate equation with the bulk EOM: the decoded metric moves with
    velocity `reconstruct'(areaOfLedger(Q·p(s)))` where `p = exp(·Q)·p0`. -/
theorem bulk_eom_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (areaOfLedger : Ledger ι →ₗ[ℝ] AreaData) (reconstruct' : AreaData →ₗ[ℝ] Metric)
    (Q : Matrix ι ι ℝ) (p0 : Ledger ι) (s : ℝ) :
    HasDerivAt (fun t => reconstruct' (areaOfLedger (pExp Q p0 t)))
      (reconstruct' (areaOfLedger (Q.mulVec (pExp Q p0 s)))) s :=
  bulk_eom areaOfLedger reconstruct' Q (pExp Q p0) s (hasDerivAt_pExp Q p0 s)

end Exponential

/-! ## Part C — grounding in the real decoder and the nontriviality contrast with D4a -/

/-- **The concrete E2 decoder `AreaMap.reconstruct` bundled as the LINEAR map it is.**  Each
    entry of the reconstructed metric is a fixed linear combination of area-data values, so
    reconstruction is linear in the area data. -/
noncomputable def reconstructL : AreaData →ₗ[ℝ] Metric where
  toFun := QIQTH.AreaMap.reconstruct
  map_add' := by
    intro A B; ext i j
    simp only [QIQTH.AreaMap.reconstruct, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
    split <;> ring
  map_smul' := by
    intro c A; ext i j
    simp only [QIQTH.AreaMap.reconstruct, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    split <;> ring

/-- `reconstructL` agrees with the held decoder `AreaMap.reconstruct`. -/
theorem reconstructL_apply (A : AreaData) : reconstructL A = QIQTH.AreaMap.reconstruct A := rfl

/-- **The D4a case recovered as the kernel case.**  If the decoded ledger-velocity lies in the
    decoder kernel (`reconstruct'(areaOfLedger(Q·p s)) = 0`), the bulk metric velocity is `0` —
    the metric is frozen even though the boundary populations move.  This is exactly the
    generation-free regime of D4a, here obtained as a corollary of the bulk EOM. -/
theorem frozen_of_velocity_ker {ι : Type*} [Fintype ι]
    (areaOfLedger : Ledger ι →ₗ[ℝ] AreaData) (reconstruct' : AreaData →ₗ[ℝ] Metric)
    (Q : Matrix ι ι ℝ) (p : ℝ → Ledger ι) (s : ℝ) (hp : HasDerivAt p (Q.mulVec (p s)) s)
    (hker : reconstruct' (areaOfLedger (Q.mulVec (p s))) = 0) :
    HasDerivAt (fun t => reconstruct' (areaOfLedger (p t))) 0 s := by
  have h := bulk_eom areaOfLedger reconstruct' Q p s hp
  rwa [hker] at h

/-- **★ NONTRIVIALITY / the honest contrast with D4a.**  If the decoded ledger-velocity is
    nonzero, the metric is GENUINELY MOVING — its trajectory does NOT have derivative `0` at `s`,
    so it is not the frozen D4a case.  (Combined with `frozen_of_velocity_ker`: zero decoded
    velocity ⇒ frozen; nonzero decoded velocity ⇒ genuine motion.) -/
theorem metric_moving_iff {ι : Type*} [Fintype ι]
    (areaOfLedger : Ledger ι →ₗ[ℝ] AreaData) (reconstruct' : AreaData →ₗ[ℝ] Metric)
    (Q : Matrix ι ι ℝ) (p : ℝ → Ledger ι) (s : ℝ) (hp : HasDerivAt p (Q.mulVec (p s)) s) :
    (reconstruct' (areaOfLedger (Q.mulVec (p s))) ≠ 0) →
      ¬ (∀ M, HasDerivAt (fun t => reconstruct' (areaOfLedger (p t))) M s → M = 0) := by
  intro hne hall
  exact hne (hall _ (bulk_eom areaOfLedger reconstruct' Q p s hp))

end QIQTH.BulkGeneration
