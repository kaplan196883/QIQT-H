/-
  GaussInteriorMVTGeneral — the GENERAL-base-point (no `g_p = I` gauge) exp-pullback Gauss lemma germ
  (corrected-hpull program, item (1); a sub-brick of the a₁ = R/6 heat-kernel tower).

  ⚠ HONESTY FIREWALL (binding).  This file is **NOT** a proof of `a₁ = R/6`.  The a₁ = R/6 milestone
  remains CONDITIONAL on {hDuhamel, hDConv, hCConv}; `hGauss` is one of the labelled inputs of
  `a1_R6_from_labelled`.  This file discharges item (1) of the corrected-`hpull` program: it produces
  the exp-pullback Gauss germ WITHOUT the base-point normalization `g_p = I`, i.e. in the general
  curved-metric form where `g` at the base point `p` is an arbitrary (symmetric, invertible) matrix,
  not necessarily the identity.  Nothing here builds normal coordinates, moves numerical-G, or closes
  a₁ = R/6.

  ─────────────────────────────────────────────────────────────────────────────────────────────
  WHY THIS IS A THIN ALGEBRAIC UN-NORMALIZATION (not new analysis)
  ─────────────────────────────────────────────────────────────────────────────────────────────
  The interior first-variation Gauss identity `gauss_interior_identity` (J4-347, `GaussInteriorMVT`)
  is ALREADY stated and proved for a general base-point metric: its RHS is
    `∑ a, ∑ b, g p a b · w^a · v^b   =   g_p(w, v)`,
  NOT `⟨w, v⟩`.  The MVT/interior-derivative closure (`E' = W`, `W' = 0`, Lagrange MVT) never uses
  `g_p = I` in ANY proof step — the base gauge is used ONLY in the downstream germ-shaping wrapper
  `hGauss_pullback_concrete` (via `gauss_coordinate_contraction_gauge`) to collapse the coordinate RHS
  `∑ b, g_p(i,b)·v^b` to the clean `v^i`.  Likewise the coordinate contraction
  `gauss_coordinate_contraction` (A3, `GaussLemmaAssembly`) is ALREADY general:
    `∑_j g̃_ij(v)·v^j = ∑_b g_p(i,b)·v^b`   (the gauge lemma A3′ only post-composes `g_p = I`).
  So the general germ is obtained by feeding the SAME banked ball-family `hgball_concrete` through the
  UN-gauged contraction `gauss_coordinate_contraction` and the SAME `Metric.eventually_nhds_iff`
  neighbourhood witness — no new analytic content whatsoever.

  ─────────────────────────────────────────────────────────────────────────────────────────────
  DELIVERED (fully derived, axiom-free, no `sorry`)
  ─────────────────────────────────────────────────────────────────────────────────────────────
   • G1  `hGauss_pullback_general` — the germ shape at a GENERAL base metric, from an abstract ball
       family of per-point Gauss identities:
         `∀ i, (fun x => ∑ j, expPullbackMetric g gi hC p x i j · x^j)
                 =ᶠ[𝓝 0] (fun x => ∑ b, g p i b · x^b)`.
       (RHS is the base metric applied to the radial vector; NO `hgauge` hypothesis.)
   • G2  `hGauss_pullback_general_concrete` — G1 with the ball family DISCHARGED by
       `gauss_interior_identity`/`hgball_concrete`.  Surviving hypotheses are ONLY the metric geometry
       `hsymm/hinv/hg` (all satisfiable); NO base gauge `g_p = I`.
   • G3  `expPullbackMetric_zero_general` — the un-gauged capstone center value `g̃(0) = g_p` (the
       general analog of `expPullbackMetric_zero_gauge`), a thin wrapper over
       `expPullbackMetric_at_zero`.
   • G4  `hGauss_pullback_gauge_of_general` — the REGRESSION check: the banked gauged germ
       (`hGauss_pullback`, RHS `x^i`) is recovered from G1 by the purely algebraic collapse
       `∑ b, g_p(i,b)·x^b = x^i` under `g_p = I`.  Confirms G1 strictly generalizes the banked brick.

  NET: item (1) of the corrected-`hpull` program is delivered.  The `g_p = I` assumption was found to
  be a STATEMENT normalization only, absent from every proof step; the general germ is a thin
  un-normalization of already-banked, axiom-free machinery.  This is STILL NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.Geodesic
import QIQTH.ExpMap
import QIQTH.PullbackMetric
import QIQTH.GaussLemmaAssembly
import QIQTH.GaussInteriorMVT

namespace QIQTH.GaussInteriorMVTGeneral

open QIQTH.Curvature QIQTH.Geodesic QIQTH.ExpMap
open QIQTH.GaussLemmaAssembly QIQTH.GaussInteriorMVT
open QIQTH.PullbackMetric
open Finset Topology

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-! ### G1 — the general-base-metric germ from an abstract ball family. -/

/-- **G1 — `hGauss_pullback_general`.**  The exp-pullback Gauss germ at a GENERAL base metric (no
    `g_p = I` gauge): from the ball family `hgball` of per-point first-variation Gauss identities on
    `ball 0 expRho`, each fed through the UN-gauged coordinate contraction
    `gauss_coordinate_contraction` (A3),
      `∀ i, (fun x => ∑ j, expPullbackMetric g gi hC p x i j · x^j)
              =ᶠ[𝓝 0] (fun x => ∑ b, g p i b · x^b)`.
    The RHS is the base metric `g_p` contracted with the radial vector `x`; it collapses to `x^i`
    exactly when `g_p = I` (leg G4).  Same `Metric.eventually_nhds_iff` witness as the gauged
    `hGauss_pullback`; the only change is dropping `hgauge` and keeping the honest `g_p` RHS.
    ⚠ NOT a₁ = R/6. -/
theorem hGauss_pullback_general
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n)
    (hgball : ∀ v : Point n, ‖v‖ < expRho g gi hC p → ∀ i,
        (∑ a, ∑ b, g (expMap g gi hC p v) a b
          * (fderiv ℝ (expMap g gi hC p) v) (Pi.single i 1) a * (expTube g gi hC p v 1).2 b)
        = ∑ a, ∑ b, g p a b * (Pi.single i 1 : Point n) a * v b) :
    ∀ i, (fun x => ∑ j, expPullbackMetric g gi hC p x i j * x j)
      =ᶠ[𝓝 (0 : Point n)] (fun x => ∑ b, g p i b * x b) := by
  intro i
  refine Metric.eventually_nhds_iff.mpr ⟨expRho g gi hC p, expRho_pos g gi hC p, fun {x} hx => ?_⟩
  have hnorm : ‖x‖ < expRho g gi hC p := by rwa [dist_zero_right] at hx
  exact gauss_coordinate_contraction g gi hC p x hnorm i (hgball x hnorm i)

/-! ### G2 — the general germ with the ball family discharged by the interior MVT. -/

/-- **G2 — `hGauss_pullback_general_concrete`.**  Item (1) of the corrected-`hpull` program: the germ
    shape of the exp-pullback Gauss lemma at a GENERAL base metric, with the per-point first-variation
    Gauss carry DISCHARGED (fed by `hgball_concrete`/`gauss_interior_identity`):
      `∀ i, (fun x => ∑ j, expPullbackMetric g gi hC p x i j · x^j)
              =ᶠ[𝓝 0] (fun x => ∑ b, g p i b · x^b)`.
    Surviving hypotheses: ONLY the metric geometry `hsymm/hinv/hg` (all satisfiable).  Crucially there
    is NO base gauge `g_p = I` — this is precisely the generalization of the banked
    `hGauss_pullback_concrete` off the base-normalized coordinates.  ⚠ NOT a₁ = R/6. -/
theorem hGauss_pullback_general_concrete
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (p : Point n) :
    ∀ i, (fun x => ∑ j, expPullbackMetric g gi hC p x i j * x j)
      =ᶠ[𝓝 (0 : Point n)] (fun x => ∑ b, g p i b * x b) :=
  hGauss_pullback_general g gi hC p (hgball_concrete g gi hC hsymm hinv hg p)

/-! ### G3 — the un-gauged capstone center value `g̃(0) = g_p`. -/

/-- **G3 — `expPullbackMetric_zero_general`.**  The un-gauged center value of the pullback metric:
    `g̃(0)_{ij} = g_p(i,j)` — the general analog of `expPullbackMetric_zero_gauge` (which specializes
    `g_p = I` to get `δ_{ij}`).  A thin wrapper over `expPullbackMetric_at_zero`.  ⚠ NOT a₁ = R/6. -/
theorem expPullbackMetric_zero_general
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (i j : Fin n) :
    expPullbackMetric g gi hC p 0 i j = g p i j :=
  expPullbackMetric_at_zero g gi hC p i j

/-! ### G4 — regression: the banked gauged germ is recovered under `g_p = I`. -/

/-- **G4 — `hGauss_pullback_gauge_of_general`.**  Regression / consistency check: the banked gauged
    germ (`GaussLemmaFlowData.hGauss_pullback`, RHS `x^i`) is recovered from the general germ G1 by the
    purely algebraic collapse `∑ b, g_p(i,b)·x^b = x^i` under the base gauge `g_p = I` (`hgauge`).
    This confirms G1/G2 STRICTLY GENERALIZE the base-normalized bricks — the `g_p = I` assumption was a
    statement normalization, recoverable by post-composition, never used in any proof step.
    ⚠ NOT a₁ = R/6. -/
theorem hGauss_pullback_gauge_of_general
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n)
    (hgauge : ∀ a b, g p a b = if a = b then 1 else 0)
    (hgball : ∀ v : Point n, ‖v‖ < expRho g gi hC p → ∀ i,
        (∑ a, ∑ b, g (expMap g gi hC p v) a b
          * (fderiv ℝ (expMap g gi hC p) v) (Pi.single i 1) a * (expTube g gi hC p v 1).2 b)
        = ∑ a, ∑ b, g p a b * (Pi.single i 1 : Point n) a * v b) :
    ∀ i, (fun x => ∑ j, expPullbackMetric g gi hC p x i j * x j)
      =ᶠ[𝓝 (0 : Point n)] (fun x => x i) := by
  intro i
  have hrhs : (fun x : Point n => ∑ b, g p i b * x b) = (fun x : Point n => x i) := by
    funext x
    rw [Finset.sum_congr rfl (fun b _ => by rw [hgauge i b] :
        ∀ b ∈ (Finset.univ : Finset (Fin n)), g p i b * x b = (if i = b then 1 else 0) * x b)]
    simp [Finset.sum_ite_eq]
  rw [← hrhs]
  exact hGauss_pullback_general g gi hC p hgball i

end QIQTH.GaussInteriorMVTGeneral

section AxiomChecks
open QIQTH.GaussInteriorMVTGeneral
#print axioms hGauss_pullback_general
#print axioms hGauss_pullback_general_concrete
#print axioms expPullbackMetric_zero_general
#print axioms hGauss_pullback_gauge_of_general
end AxiomChecks
