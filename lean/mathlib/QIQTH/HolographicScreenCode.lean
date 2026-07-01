/-
  The toy holographic-screen code — a kinematic INTERFACE, NOT gravity.

  ★ SCOPE (read first). This is the honest, tractable "toy Stage 1" from the GPT-5.5-pro mechanism consult
    (`HOLOGRAPHIC_SCREEN_CODE_PLAN.md`). It does **NOT** make QIQT-H a quantum gravity theory and does **NOT**
    close the "mechanism gap". It turns the regional capacity from a *postulate* into a *theorem — GIVEN a local
    packing constraint + the code/min-cut structure*: a genuine reduction (regional area law ⟸ local packing),
    and exactly the "precise interface into which a real microscopic model could plug" the consult named as
    QIQT-H's one genuine piece of leverage. Kinematic scaffolding, not gravity. ★

  TWO CORRECTIONS FROM THE CONSULT, enforced in every theorem:
  (1) **Area is an INDEPENDENT charge, never `log dim`.** Defining `A := 4G·log(dim)` and then "proving"
      `log dim = A/4G` is a tautology. Here each screen link carries TWO independent labels — a log-dimension
      `logDim e` and an area weight `areaWt e` — related only by a *carried* local constraint. The independence
      guard `area_dim_independent` (large area, zero code dimension) certifies they are not the same quantity.
  (2) **A `≤` BOUND with horizon saturation, not exact `e^{A/4G}`.** Gravity gives `S ≤ A/4G` saturated by
      horizons; exact equality for every region is too strong. We prove `≤`, with saturation separate.

  FRONTIERS THIS DOES NOT TOUCH (cite, never claim): dynamical Einstein + propagating gravitons (Stage 3 — the
  serious wall, fatal to any code-only proposal); background independence (the screen/cuts here are FIXED/supplied
  — a fixed-graph toy, NOT background-independent); non-circular `G` (the `1/4G` is CARRIED in the packing
  constraint, never derived); deriving the area charge `areaWt` from a substrate. The `(Φ,λ)` selector gives no
  leverage here (interpretational, not a gravity mechanism) and is absent.
-/
import Mathlib

namespace QIQTH.ScreenCode

open scoped BigOperators

variable {ι : Type*}

/-- A **finite holographic-screen cut**: a region's boundary screen is a `Finset` of links, each carrying **two
    independent** labels — `logDim e ≥ 0` (the log Hilbert dimension the link can carry) and `areaWt e ≥ 0` (its
    **independent** area charge). The two are NOT identified (see `area_dim_independent`). -/
structure ScreenCut (ι : Type*) where
  /-- the links crossing the boundary screen `∂R` -/
  links : Finset ι
  /-- log Hilbert dimension carried by each link (`≥ 0`) -/
  logDim : ι → ℝ
  /-- the **independent** area weight of each link (`≥ 0`) — NOT `logDim` -/
  areaWt : ι → ℝ
  logDim_nonneg : ∀ e, 0 ≤ logDim e
  areaWt_nonneg : ∀ e, 0 ≤ areaWt e

/-- **Code capacity (single-cut bound)** `codeCap(∂R) = Σ_{e∈∂R} logDim e` — the holographic-code property that a
    boundary cut upper-bounds the encodable logical dimension, `log dim C_R ≤ Σ_cut log D_e`. -/
noncomputable def codeCap (S : ScreenCut ι) : ℝ := ∑ e ∈ S.links, S.logDim e

/-- **Screen area (the independent charge)** `screenArea(∂R) = Σ_{e∈∂R} areaWt e`. -/
noncomputable def screenArea (S : ScreenCut ι) : ℝ := ∑ e ∈ S.links, S.areaWt e

/-- `codeCap ≥ 0` (a sum of nonneg log-dimensions). -/
lemma codeCap_nonneg (S : ScreenCut ι) : 0 ≤ codeCap S :=
  Finset.sum_nonneg (fun e _ => S.logDim_nonneg e)

/-- `screenArea ≥ 0` (a sum of nonneg area weights). -/
lemma screenArea_nonneg (S : ScreenCut ι) : 0 ≤ screenArea S :=
  Finset.sum_nonneg (fun e _ => S.areaWt_nonneg e)

/-- **S1a — the independence guard (NOT a tautology).** The screen area and the code capacity are **provably
    distinct** quantities: there is a screen with strictly positive area but **zero** code dimension. So we did
    NOT set `area := log dim`; they are independent labels related only by the (carried) local packing constraint.
    This is the holographic-screen analogue of `EntropyNotCardinality` / `svn_underdetermines_smax`. -/
theorem area_dim_independent : ∃ S : ScreenCut Unit, 0 < screenArea S ∧ codeCap S = 0 := by
  refine ⟨⟨{()}, fun _ => 0, fun _ => 1, fun _ => le_refl 0, fun _ => zero_le_one⟩, ?_, ?_⟩
  · simp [screenArea]
  · simp [codeCap]

/-- The **local holographic packing constraint** (the microscopic postulate — CARRIED, with the `1/4G`): every
    screen link's log-dimension is bounded by its independent area weight in Planck units, `logDim e ≤ areaWt e/(4G)`. -/
def Packing (S : ScreenCut ι) (G : ℝ) : Prop := ∀ e ∈ S.links, S.logDim e ≤ S.areaWt e / (4 * G)

/-- **S1b — the linchpin: local packing ⟹ regional area law.** From the *local* packing constraint on each screen
    link plus the code (single-cut) structure, the *regional* holographic bound follows:
    `codeCap(∂R) ≤ screenArea(∂R)/(4G)`. This turns the capacity **postulate** into a **theorem given a local
    postulate** — the regional area law is reduced to a *local* packing law. Area is an INDEPENDENT charge
    (`screenArea`, not `codeCap`); the `1/4G` is carried in `Packing`, never derived. A `≤` bound (saturation
    separate, S1c). NOT gravity: no dynamics, no gravitons, fixed screen. -/
theorem area_law_of_packing (S : ScreenCut ι) (G : ℝ) (hG : 0 < G) (h : Packing S G) :
    codeCap S ≤ screenArea S / (4 * G) := by
  unfold codeCap screenArea
  rw [Finset.sum_div]
  exact Finset.sum_le_sum h

/-- **S1c — horizon saturation (the bound is tight).** In the horizon-like sector where the local packing is
    *saturated* on every cut link (`logDim e = areaWt e/(4G)`), the area law is an **equality**
    `codeCap(∂R) = screenArea(∂R)/(4G)` — the microstate count saturates the area, as for a black-hole horizon. -/
theorem area_law_saturation (S : ScreenCut ι) (G : ℝ)
    (hsat : ∀ e ∈ S.links, S.logDim e = S.areaWt e / (4 * G)) :
    codeCap S = screenArea S / (4 * G) := by
  unfold codeCap screenArea
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl hsat

end QIQTH.ScreenCode
