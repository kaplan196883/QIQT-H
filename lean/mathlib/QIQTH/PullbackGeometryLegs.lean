/-
  PullbackGeometryLegs — the three "pullback geometry legs" closing the derivable residue of the
  hGauss campaign: the RNC 1-jet of the pullback metric (L1), the local inverse / positivity of the
  pullback metric near the origin (L2), and the C∞-vs-C⁴ consumer verdict (L3).  (Brick J4-348 of the
  a₁ = R/6 heat-kernel tower.)

  ⚠ HONESTY FIREWALL (binding).  This file is **NOT** a proof of `a₁ = R/6`.  The a₁ = R/6 milestone
  remains CONDITIONAL: `hGauss` (and the still-open `hpd2` radial-contraction identity) are labelled
  inputs of the downstream consumers.  This file only surfaces / completes the *geometry data* of the
  exp-pullback metric near the origin.  Nothing here builds normal coordinates from scratch, moves
  numerical-G, or closes a₁ = R/6.

  ─────────────────────────────────────────────────────────────────────────────────────────────
  BANKED-JET INVENTORY (what already exists in `QIQTH/PullbackMetric.lean`, do NOT re-prove)
  ─────────────────────────────────────────────────────────────────────────────────────────────
  The F4 verdict of `GaussLemmaFlowData` recorded legs (iii) `∂g̃(0)=0` and (iv) inverse/positivity as
  "🔶 derivable-with-work".  In fact BOTH are already largely banked (this is a "don't under-credit the
  repo" situation).  The load-bearing banked facts, all axiom-clean:
    • `expPullbackMetric_at_zero`        : `g̃(0)_{ij} = g(p)_{ij}`  (RNC value jet).
    • `fderiv_expMap_zero`               : `D exp_p 0 = id`.
    • `pd_jacobian_expMap_zero`          : `∂_l(D exp_p·e_i)_a(0) = ½(−Γ^a_{il} − Γ^a_{li})` — the D²exp
      1-jet in closed Christoffel form (the classical `exp_p(x)=p+x−½Γ(x,x)+O(x³)` content, extracted
      from the little-o one-jet via `hasFDerivAt_fderiv_expMap_zero`).  This is the "D²exp jet" the
      mission worried might resist extraction — it is BANKED, so L1 needs no new exp-jet work.
    • `pd_expPullbackMetric_at_zero`     : `∂_l g̃_{ij}(0) = 0` — **L1 already fully proved**, via the
      christoffel_lower (metric-compat) cancellation against the Jacobian 1-jet.
    • `christoffel_expPullbackMetric_zero` : `Γ̃(0) = 0`.
    • `expPullbackMetric_symm`           : `g̃` symmetric.
    • `expPullbackMetricInv` (def)       : the smooth pullback inverse `g̃⁻¹` via `Ring.inverse` of the
      operator `matToCLM (g̃ x)`; with `expPullbackMetricInv_zero` (`g̃⁻¹(0) = gi p`),
      `expPullbackMetricInv_differentiableAt` / `expPullbackMetricInv_contDiffAt_one`.
    • `metricCLMUnit0`                   : `matToCLM (g̃ 0)` is a unit of the operator ring (inverse
      `matToCLM (gi p)`), with `matToCLM_apply` / `matToCLM_mul_eq_one` / `ringInverse_metricCLM_zero`.
    • `contDiffAt2_expPullbackMetric_zero` : `g̃` is `C²` at `0` (each component).

  ─────────────────────────────────────────────────────────────────────────────────────────────
  DELIVERED HERE (fully derived, axiom-free, no `sorry`)
  ─────────────────────────────────────────────────────────────────────────────────────────────
  • L1  `expPullbackMetric_one_jet_zero` — a clean named re-export of the banked `∂g̃(0)=0`, recording
      that the RNC 1-jet leg is DONE (leg (iii) of the F4 verdict).
  • L2  the local inverse / positivity package near `0` (the new content):
      - `matToCLM_isUnit_eventually`      : `∀ᶠ x in 𝓝 0, IsUnit (matToCLM (g̃ x))` — invertibility of
        the pullback metric operator on a neighbourhood of `0` (open-condition: units are open in the
        operator Banach algebra, `Units.isOpen`, and `matToCLM (g̃ ·)` is continuous with `matToCLM
        (g̃ 0)` a unit via `metricCLMUnit0`).
      - `expPullbackMetric_rightInverse_eventually` : `∀ᶠ x in 𝓝 0, ∀ i c,
          ∑ b, g̃(x)_{ib}·g̃⁻¹(x)_{bc} = δ_{ic}` — the genuine matrix-inverse identity for the BANKED
        partner `expPullbackMetricInv`, from `Ring.mul_inverse_cancel` on the unit.
      - `expPullbackMetric_det_pos_eventually` : under the orthonormal frame `g_p = δ`,
          `∀ᶠ x in 𝓝 0, 0 < det (g̃ x)` — positive determinant near `0` (continuity of `det` + `det
        (g̃ 0) = det I = 1 > 0`), the open-condition positivity leg (iv).
  • L3  the consumer-binder verdict — in this header (see below); no code beyond L1/L2.

  ─────────────────────────────────────────────────────────────────────────────────────────────
  L3 — THE C∞-vs-C⁴ CONSUMER VERDICT (complete and honest)
  ─────────────────────────────────────────────────────────────────────────────────────────────
  There are TWO distinct a₁-consumers in the tree, and the pullback route feeds the FINITE-order one:

    (A) `QIQTH.RNCExpansion.heat_a1_of_gauge_c2` — the FINITE-order, LOCAL consumer.  Its smoothness
        binders are `hg2 : ContDiffAt ℝ 2 g̃ 0` and `hgi1 : ContDiffAt ℝ 1 g̃⁻¹ 0`, and it needs the
        geometry ONLY at `0` (value/inverse-value/1-jet/gauge), NOT global positivity.  This consumer
        is ALREADY instantiated at the exp-pullback metric — `PullbackMetric.kappa_eq_one_sixth_
        expPullback_of_hpd2` discharges every one of its binders from the banked pullback lemmas
        (`contDiffAt2_expPullbackMetric_zero`, `expPullbackMetricInv_contDiffAt_one`,
        `expPullbackMetric_at_zero`, `expPullbackMetricInv_zero`, `pd_expPullbackMetric_at_zero`,
        `expPullbackMetric_symm`, and the gauge from `hpd2`).  Because the binder is `C²`/`C¹`, the
        provable `C²` regularity of `g̃` MEETS it exactly — there is NO C∞-vs-C⁴ wall for consumer (A).
        The pullback route's sole residue at this consumer is the labelled `hpd2` (the pure `∂²g̃(0)`
        radial-contraction identity), NOT smoothness.

    (B) `QIQTH.A1R6FromLabelled.a1_R6_from_labelled` — the GLOBAL, labelled façade.  Its binders demand
        `hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b)` (C∞-in-the-point), `hgiC : ∀ a b, ContDiff ℝ ⊤ …`
        (C∞ inverse), and `hgpos : ∀ v, 0 < det (g v)` (GLOBAL positive determinant, all `v`).  These
        are the binders the F4 verdict flagged as residue (i).  Instantiating THIS façade directly at
        `g := g̃` is a TYPE MISMATCH, and doubly so:
          – smoothness: `g̃` is provably only `C²`/`C⁴`-ish (`fderiv exp_p` sheds an order), never a
            provable `C∞`, so the `⊤` binder is unmeetable by a provable fact; and
          – positivity: `hgpos` demands det > 0 EVERYWHERE, which is FALSE for a pullback metric (exp
            is a chart only near `0`) — this file's `expPullbackMetric_det_pos_eventually` is LOCAL
            (`∀ᶠ x in 𝓝 0`), which is the honest and correct positivity for a normal-coordinate metric.
        So façade (B) is a DIFFERENT (global, C∞) packaging, NOT the pullback's intended consumer.

    RECOMMENDATION (option analysis of the mission's (a)/(b)/(c)):
      • (c) is the operative truth: the CORRECT pullback consumer (A) is ALREADY finite-order (`C²`/`C¹`)
        and ALREADY wired to `g̃`; the pullback route carries NO C∞-of-pullback labelled input.  The
        F4 "genuine labelled residue (i)" is an artefact of pointing at façade (B); against consumer
        (A) it dissolves.
      • Neither (a) (adding a labelled C∞-of-pullback input) nor (b) (a C⁴-binder façade refactor) is
        needed to close the pullback route through consumer (A).  IF one insists on routing through the
        GLOBAL façade (B), then (b) — refactoring (B) to a finite `C^k`-binder AND to a LOCAL positivity
        binder — is the right move, but that is a future façade campaign about (B)'s own derivative
        accounting, orthogonal to the pullback geometry.  It is explicitly NOT attempted here.

    NET after this brick: the hGauss-route surface is — the germ `hGauss` (delivered by
    `GaussInteriorMVT.hGauss_pullback_concrete`), the value/1-jet/gauge/inverse geometry (all banked +
    surfaced here), local invertibility & positivity (delivered here) — leaving the labelled `hpd2`
    radial-contraction identity as the ONE genuine open analytic residue of the pullback route to the
    finite-order consumer (A).  This is STILL NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.Geodesic
import QIQTH.ExpMap
import QIQTH.PullbackMetric

namespace QIQTH.PullbackGeometryLegs

open QIQTH.Curvature QIQTH.Geodesic QIQTH.ExpMap
open QIQTH.PullbackMetric
open Finset Topology Filter

variable {n : ℕ}

/-! ### L1 — the RNC 1-jet `∂g̃(0) = 0` (banked; surfaced here as a named leg). -/

/-- **L1 — `expPullbackMetric_one_jet_zero`.**  The Riemann-normal-coordinate first-derivative
    (1-jet) of the exp-pullback metric vanishes at the origin: `∂_l g̃_{ij}(0) = 0`, for ANY ambient
    symmetric metric `g` with inverse `gi` at `p` (no ambient gauge needed).  This is leg (iii) of the
    `GaussLemmaFlowData` F4 verdict; it is ALREADY fully proved in `PullbackMetric` as
    `pd_expPullbackMetric_at_zero` (the classical cancellation `∂g = Γg+Γg` of metric compatibility
    against the `−½Γ`-jet of `exp`, via `pd_jacobian_expMap_zero` + `christoffel_lower`).  We record it
    here under a leg-name to mark the leg DONE.  ⚠ NOT a₁ = R/6. -/
theorem expPullbackMetric_one_jet_zero
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ a b, (∑ σ, g p a σ * gi p σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (i j l : Fin n) :
    pd (fun x => expPullbackMetric g gi hC p x i j) l 0 = 0 :=
  pd_expPullbackMetric_at_zero g gi hC p hsymm hinv hg i j l

/-! ### L2 — the local inverse / positivity of `g̃` near `0` (the new content). -/

/-- **L2a — `matToCLM_isUnit_eventually`.**  The pullback-metric operator `matToCLM (g̃ x)` is a UNIT
    of the endomorphism ring `Point n →L[ℝ] Point n` for all `x` in a neighbourhood of `0`.  Open-
    condition argument: the units are an open set in the operator Banach algebra (`Units.isOpen`), the
    field `x ↦ matToCLM (g̃ x)` is continuous at `0` (its matrix entries are `C²` at `0`,
    `contDiffAt2_expPullbackMetric_zero`), and `matToCLM (g̃ 0)` is a unit (`metricCLMUnit0`, since
    `g̃(0) = g(p)` is invertible with inverse `gi p`).  ⚠ NOT a₁ = R/6. -/
theorem matToCLM_isUnit_eventually
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hinv : ∀ a b, (∑ σ, g p a σ * gi p σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) :
    ∀ᶠ x in 𝓝 (0 : Point n),
      IsUnit (matToCLM (fun a b => expPullbackMetric g gi hC p x a b)) := by
  -- `matToCLM : (Fin n → Fin n → ℝ) → (Point n →L[ℝ] Point n)` is continuous (a finite ℝ-combination
  -- of the constant matrix units `elemCLM a b`).
  have hmatToCLM_cont : Continuous (fun M : Fin n → Fin n → ℝ => matToCLM M) := by
    show Continuous (fun M : Fin n → Fin n → ℝ => ∑ a, ∑ b, M a b • elemCLM a b)
    refine continuous_finsetSum _ (fun a _ => continuous_finsetSum _ (fun b _ => ?_))
    exact (((continuous_apply b).comp (continuous_apply a)).smul continuous_const)
  -- the matrix field `x ↦ g̃ x` is continuous at `0` (entrywise `C²`).
  have hgtilde_cont : ContinuousAt
      (fun x : Point n => (fun a b => expPullbackMetric g gi hC p x a b : Fin n → Fin n → ℝ)) 0 :=
    continuousAt_pi.mpr (fun a => continuousAt_pi.mpr (fun b =>
      (contDiffAt2_expPullbackMetric_zero g gi hC p hg a b).continuousAt))
  -- the operator field is continuous at `0`.
  have hmatCont : ContinuousAt
      (fun x => matToCLM (fun a b => expPullbackMetric g gi hC p x a b)) 0 :=
    (hmatToCLM_cont.continuousAt).comp hgtilde_cont
  -- `matToCLM (g̃ 0)` is a unit.
  have hunit0 : IsUnit (matToCLM (fun a b => expPullbackMetric g gi hC p 0 a b)) :=
    ⟨metricCLMUnit0 g gi hC p hinv, rfl⟩
  -- open-condition: units are open, so the preimage under the continuous field is a nhds of `0`.
  exact hmatCont.eventually (Units.isOpen.mem_nhds hunit0)

/-- **L2b — `expPullbackMetric_rightInverse_eventually`.**  On a neighbourhood of `0`, the BANKED
    pullback inverse `g̃⁻¹ = expPullbackMetricInv` is a genuine (right) matrix inverse of `g̃`:
    `∑_b g̃(x)_{ib}·g̃⁻¹(x)_{bc} = δ_{ic}`.  From `matToCLM_isUnit_eventually` and
    `Ring.mul_inverse_cancel` (the operator times its `Ring.inverse` is `1` on the unit locus), read
    off componentwise via `matToCLM_apply`.  ⚠ NOT a₁ = R/6. -/
theorem expPullbackMetric_rightInverse_eventually
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hinv : ∀ a b, (∑ σ, g p a σ * gi p σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) :
    ∀ᶠ x in 𝓝 (0 : Point n), ∀ i c,
      (∑ b, expPullbackMetric g gi hC p x i b * expPullbackMetricInv g gi hC p x b c)
        = if i = c then (1 : ℝ) else 0 := by
  filter_upwards [matToCLM_isUnit_eventually g gi hC p hinv hg] with x hx i c
  have key := Ring.mul_inverse_cancel
    (matToCLM (fun a b => expPullbackMetric g gi hC p x a b)) hx
  have happ := congrArg (fun T : Point n →L[ℝ] Point n => T (Pi.single c 1) i) key
  simp only [ContinuousLinearMap.mul_apply, matToCLM_apply, ContinuousLinearMap.one_apply,
    Pi.single_apply] at happ
  simpa only [expPullbackMetricInv] using happ

/-- **L2c — `expPullbackMetric_det_pos_eventually`.**  Under the orthonormal frame `g_p = δ`
    (satisfiable — the standard RNC frame gauge), the pullback metric has POSITIVE determinant on a
    neighbourhood of `0`: `∀ᶠ x in 𝓝 0, 0 < det (g̃ x)`.  Open-condition: `det (g̃ ·)` is continuous at
    `0` (continuity of the determinant composed with the entrywise-`C²` matrix field), and `det (g̃ 0)
    = det (g_p) = det I = 1 > 0`.  This is the honest LOCAL positivity leg (iv) — a pullback metric
    cannot be globally positive-definite (exp is a chart only near `0`).  ⚠ NOT a₁ = R/6. -/
theorem expPullbackMetric_det_pos_eventually
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgauge : ∀ a b, g p a b = if a = b then 1 else 0) :
    ∀ᶠ x in 𝓝 (0 : Point n), 0 < Matrix.det (expPullbackMetric g gi hC p x) := by
  -- entrywise continuity at `0` of the matrix field.
  have hentry_cont : ContinuousAt
      (fun x : Point n => (expPullbackMetric g gi hC p x : Fin n → Fin n → ℝ)) 0 :=
    continuousAt_pi.mpr (fun a => continuousAt_pi.mpr (fun b =>
      (contDiffAt2_expPullbackMetric_zero g gi hC p hg a b).continuousAt))
  -- determinant is continuous at `0`.
  have hdetCont : ContinuousAt (fun x => Matrix.det (expPullbackMetric g gi hC p x)) 0 :=
    (Continuous.matrix_det continuous_id).continuousAt.comp hentry_cont
  -- value at `0`: `g̃(0) = g_p = I`, so `det = 1`.
  have hf0 : Matrix.det (expPullbackMetric g gi hC p 0) = 1 := by
    have hM : (Matrix.of fun i j => expPullbackMetric g gi hC p 0 i j)
        = (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      rw [Matrix.of_apply, expPullbackMetric_at_zero, hgauge, Matrix.one_apply]
    calc Matrix.det (expPullbackMetric g gi hC p 0)
        = Matrix.det (Matrix.of fun i j => expPullbackMetric g gi hC p 0 i j) := rfl
      _ = Matrix.det (1 : Matrix (Fin n) (Fin n) ℝ) := by rw [hM]
      _ = 1 := Matrix.det_one
  have hmem : Matrix.det (expPullbackMetric g gi hC p 0) ∈ Set.Ioi (0 : ℝ) := by
    rw [Set.mem_Ioi, hf0]; norm_num
  filter_upwards [hdetCont.eventually (isOpen_Ioi.eventually_mem hmem)] with x hx
  exact hx

end QIQTH.PullbackGeometryLegs

section AxiomChecks
open QIQTH.PullbackGeometryLegs
#print axioms expPullbackMetric_one_jet_zero
#print axioms matToCLM_isUnit_eventually
#print axioms expPullbackMetric_rightInverse_eventually
#print axioms expPullbackMetric_det_pos_eventually
end AxiomChecks
