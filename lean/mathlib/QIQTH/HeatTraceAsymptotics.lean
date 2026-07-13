/-
  HEAT-TRACE SHORT-TIME ASYMPTOTIC-SHAPE INTERFACE — the Phase-4 instance obligation of the
  heat-kernel gap plan, isolated (`HEAT_KERNEL_GAP_PLAN.md`, §4 extension).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  MANDATORY FIREWALL (binding, honest scope).

  • This file ADDS the asymptotic-SHAPE layer to the deferred Seeley–DeWitt interface
    (`QIQTH.SeeleyDeWittInterface`).  The `asymptotic` field — the short-time expansion
    `Tr e^{−tP} = (4πt)^{−d/2} (a₀ + a₁ t + o(t))` as `t → 0⁺` — is the DEFERRED Phase-4 heat-kernel
    fact, CARRIED as a structure field (in difference-quotient form), NEVER proved here (and never a
    Lean `axiom`).

  • What is PROVED here is only the coefficient-EXTRACTION from the carried asymptotic: the
    normalized trace `N(t) = (4πt)^{d/2}·Tr e^{−tP}` tends to `a₀ = 1` (the leading Seeley–DeWitt
    normalization, recovered as a genuine limit), and its subleading slope `(N(t)−1)/t → R/6 + tr E`
    (the carried `a₁`).  This shows the interface is NON-VACUOUS — the coefficients are determined
    by the trace — and isolates Phase 4's instance obligation.

  • It does NOT build the heat semigroup, the kernel, or the asymptotic expansion (Phases 1/3/4 —
    the Riemannian-heat-kernel wall, absent from every proof assistant).  `a₁ = R/6` remains CARRIED
    (option (b)).  NOT the conjecture, NOT the strong holographic principle, NOT quantum gravity.
    No axioms, no `sorry`.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.SeeleyDeWittInterface

noncomputable section

namespace QIQTH.HeatTraceAsymptotics

open QIQTH.SeeleyDeWittInterface QIQTH.CorrespondenceAssembly
open Filter Topology

/-- The heat-trace short-time asymptotic, a DEFERRED interface EXTENDING the SDW coefficient data.
    `heatTrace t` = `Tr e^{−tP}`; `d` = dimension.  The `asymptotic` field carries the Phase-4
    heat-kernel fact in difference-quotient form: writing `N(t) := (4πt)^{d/2} · heatTrace t`
    (the normalized trace, stripping the `(4πt)^{−d/2}` prefactor),

      `(N(t) − a₀) / t → a₁`   as `t → 0⁺`,

    which encodes `N(t) = a₀ + a₁ t + o(t)`.  This field is CARRIED (the deferred analytic fact),
    never proved. -/
structure HeatTraceAsymptotics extends SeeleyDeWittData where
  /-- the spatial dimension `d`. -/
  d : ℕ
  /-- the heat trace `heatTrace t = Tr e^{−tP}`. -/
  heatTrace : ℝ → ℝ
  /-- the carried Phase-4 heat-kernel fact: the normalized-trace difference quotient converges to
      the first Seeley–DeWitt coefficient `a₁`. -/
  asymptotic :
    Filter.Tendsto
      (fun t : ℝ => ((4 * Real.pi * t) ^ ((d : ℝ) / 2) * heatTrace t - a0) / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds a1)

/-- The normalized heat trace `N(t) = (4πt)^{d/2} · heatTrace t`. -/
def normalizedTrace (H : HeatTraceAsymptotics) (t : ℝ) : ℝ :=
  (4 * Real.pi * t) ^ ((H.d : ℝ) / 2) * H.heatTrace t

/-- ★ EXTRACTION 1 — the normalized heat trace tends to `a₀` (the leading SDW coefficient recovered
    as a limit).  From `(N−a₀)/t → a₁` and `t → 0`, `N − a₀ = ((N−a₀)/t)·t → a₁·0 = 0`, so
    `N → a₀`. -/
theorem normalizedTrace_tendsto_a0 (H : HeatTraceAsymptotics) :
    Filter.Tendsto (normalizedTrace H) (nhdsWithin 0 (Set.Ioi 0)) (nhds H.a0) := by
  -- the carried difference-quotient limit, phrased through `normalizedTrace` (defeq).
  have hquot : Filter.Tendsto
      (fun t : ℝ => (normalizedTrace H t - H.a0) / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds H.a1) := H.asymptotic
  -- `t → 0` along `𝓝[>] 0`.
  have ht0 : Filter.Tendsto (fun t : ℝ => t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  -- product tends to `a₁ · 0 = 0`.
  have hprod : Filter.Tendsto
      (fun t : ℝ => (normalizedTrace H t - H.a0) / t * t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have := hquot.mul ht0
    rwa [mul_zero] at this
  -- on `𝓝[>] 0`, `t ≠ 0`, so `((N−a₀)/t)·t = N − a₀` eventually.
  have hsub : Filter.Tendsto
      (fun t : ℝ => normalizedTrace H t - H.a0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine hprod.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htne : t ≠ 0 := ne_of_gt ht
    rw [div_mul_cancel₀ _ htne]
  -- add back `a₀`.
  have hfin := hsub.add_const H.a0
  simpa using hfin

/-- ★ EXTRACTION 2 — with `a₀ = 1`: the normalized heat trace `→ 1` (the leading Seeley–DeWitt
    normalization as a genuine limit). -/
theorem normalizedTrace_tendsto_one (H : HeatTraceAsymptotics) :
    Filter.Tendsto (normalizedTrace H) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have := normalizedTrace_tendsto_a0 H
  rwa [H.a0_eq] at this

/-- ★★ EXTRACTION 3 — the SUBLEADING SLOPE equals the `a₁ = R/6 + tr E` coefficient: with `a₀ = 1`,
    `(N(t) − 1)/t → R/6 + tr E`.  The short-time expansion's first correction IS the carried
    Seeley–DeWitt coefficient. -/
theorem subleading_slope_eq_a1Laplace (H : HeatTraceAsymptotics) :
    Filter.Tendsto (fun t => (normalizedTrace H t - 1) / t) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (a1Laplace H.R H.trE)) := by
  have h := H.asymptotic
  rw [H.a0_eq, H.a1_eq] at h
  simpa only [normalizedTrace] using h

/-- Capstone: the interface's coefficients ARE the short-time expansion data (leading `→ 1`,
    slope `= R/6 + tr E`). -/
theorem heatTrace_determines_coefficients (H : HeatTraceAsymptotics) :
    Filter.Tendsto (normalizedTrace H) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)
    ∧ Filter.Tendsto (fun t => (normalizedTrace H t - 1) / t) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (a1Laplace H.R H.trE)) :=
  ⟨normalizedTrace_tendsto_one H, subleading_slope_eq_a1Laplace H⟩

end QIQTH.HeatTraceAsymptotics
