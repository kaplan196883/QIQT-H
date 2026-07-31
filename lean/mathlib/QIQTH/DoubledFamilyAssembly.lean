/-
  DoubledFamilyAssembly — J4-43: assembling the confined DOUBLED-FAMILY integral curve for the CLOSE
  bridge `expMap_common_nondeg_radius_of_doubled_supply` (`JacobiDoubledFamily.lean`).

  ## Context

  The CLOSE bridge `(J)` (compact-uniform local exp-nondegeneracy radius) is proved in
  `JacobiDoubledFamily.lean` from a CARRIED doubled-family SUPPLY over the compact `K`: the doubled
  integral-curve family `Y q v a b s τ` (integral curves of `G = doubledField g gi`), the doubled
  linearized field `Vf`, a per-`(q,v)` compact convex confinement set `S q v`, the first-jet link
  `hlink`, and the base second-jet / geometry data.  `DoubledFamilyConstruction.lean` (J4-40) landed the
  pure REUSE cores (`doubledField_prod_hasDerivAt`, `doubledField_prod_mem_prod`); `GenericJacobiExists`
  landed the Jacobi/linear-ODE existence over an arbitrary base curve
  (`geodesicJacobi_exists_on_Icc` / `..._hasDerivAt_Icc`); `BoundedGeometryConfine` landed the
  compact-uniform confined geodesic phase-flow (`geodesic_apriori_confinement_uniform`).

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion)

  * `confined_doubled_family_exists` — **the confined doubled integral-curve constructor.**  Over a
    compact `K`, ONE radius `ρ > 0` and ONE constant `C₀ ≥ 0` such that for every `q ∈ K`, every
    velocity `v` with `‖v‖ ≤ ρ`, and every Jacobi seed `b`, there is a genuine integral curve
    `Y : ℝ → (Point n × Point n) × (Point n × Point n)` of `doubledField g gi` with the doubled IC
    `Y 0 = ((q, v), (0, b))`, solving `Y' τ = doubledField g gi (Y τ)` on the interior `Ioo 0 1`, whose
    geodesic factor `(Y τ).1` stays `C₀‖v‖`-confined to the equilibrium `(q, 0)` on `[0,1]`.

    This is DERIVED by welding three existing engines: the confined geodesic phase-flow `P` from
    `geodesic_apriori_confinement_uniform` (the base factor + confinement, uniform over `K`), the
    Jacobi field `J` along `P` with seed `(0, b)` from `geodesicJacobi_exists_on_Icc`, and the pure
    product-rule repackaging `doubledField_prod_hasDerivAt` identifying the pair `τ ↦ (P τ, J τ)` as a
    `doubledField` integral curve.  So it constructs, over `K`, the genuine confined doubled integral
    curve that the bridge's `(S1)` supply exhibits — the "carried construction residual" named in
    `JacobiDoubledFamily.lean` — for a fixed seed, with the geodesic-factor confinement uniform over `K`.

  ## HONEST FIREWALL (binding) — why this does NOT yet close `(J)` self-contained

  `confined_doubled_family_exists` is the HEART of the bridge's `(S1)` doubled integral-curve supply,
  but it does NOT feed the full bridge, which additionally CARRIES:

  1. The `s`-perturbed re-parametrization `Y q v a b s` (base velocity `v + s·a`) with the exact IC
     `hIC`/`hV0` and the doubled linearized field `Vf` (A2) — a further linODE along the base doubled
     curve.  Buildable from the same engines by re-instantiating at velocity `v + s·a`; carried here.
  2. The compact-convex confinement set `S q v` with `hScompact`/`hSconvex`/`hmem` holding for ALL
     seeds `a, b` — the QUANTITATIVE step.  The Jacobi factor `J` scales linearly in the seed, so its
     confinement into a FIXED compact `S q v` uniformly over unbounded `a, b` needs a Grönwall spread
     bound (product-ball confinement of the linearized factor), NOT available from the black-box
     confinement export (which bounds only the geodesic factor).  This is the genuine quantitative
     residual and is CARRIED, not smuggled.
  3. `hlink : (Y q v a b s 1).2.1 = fderiv ℝ (expMap g gi hC q) (v + s·a) b` (A3) — the FIRST-jet
     endpoint identification of the Jacobi position field with the exp-map derivative.  The pointwise
     ingredient exists (`flowVelocity_endpoint_position_hasFDerivAt_exists`, `VelocitySecondJetId`), but
     welding it to the `expMap`-as-flow-endpoint definitional bridge (identifying `Y`'s Jacobi factor
     with `V`) is a separate assembly; CARRIED.
  4. The base-geodesic second-variation field `Zf`/`Src` and its ODE data (`hZf`, `h0d`, `hKbd`, `hZ`,
     `h0cap`, `hKbcap`, `hAd`, `hXb`, `hSd`) — the second-variation engine plus the uniform / Lipschitz-
     in-`q` operator-norm bounds over `K` (`BoundedGeometry`); CARRIED.

  So `(J)` is NOT closed self-contained here.  This file constructs the confined doubled integral curve
  (the (S1) heart, for a fixed seed) and firewalls (1)–(4) honestly.  It does NOT smuggle `hid`/`hlink`/
  `Zf`, does NOT build the covariant `D²/dτ²`, NOT Raychaudhuri (L3), NOT `a₁ = R/6`, and the conclusion
  (a uniform common exp-nondeg radius) is NOT among any hypotheses.
-/
import QIQTH.JacobiDoubledFamily
import QIQTH.GenericJacobiExists
import QIQTH.DoubledFamilyConstruction
import QIQTH.BoundedGeometryConfine
import QIQTH.VelocitySecondJetId
import QIQTH.UniformFlowBridge
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Topology

set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 6

variable {n : ℕ}

/-- **The confined doubled integral-curve constructor (the `(S1)` heart, per seed).**

    Over a compact `K` of base points there is ONE radius `ρ > 0` and ONE constant `C₀ ≥ 0` such that
    for every `q ∈ K`, every velocity `v` with `‖v‖ ≤ ρ`, and every Jacobi seed `b`, the doubled system
    has a genuine integral curve `Y : ℝ → (Point n × Point n) × (Point n × Point n)`:
      * `Y 0 = ((q, v), (0, b))` — the base geodesic IC `(q, v)` paired with the Jacobi seed `(0, b)`;
      * `∀ τ ∈ Ioo 0 1, HasDerivAt Y (doubledField g gi (Y τ)) τ` — a genuine `doubledField` integral
        curve on the interior (two-sided derivatives), the exact shape of the bridge's `hYode`;
      * `∀ τ ∈ Icc 0 1, ‖(Y τ).1 - (q, 0)‖ ≤ C₀‖v‖` — the geodesic factor stays `C₀‖v‖`-confined to the
        equilibrium `(q, 0)`, uniformly over `q ∈ K`.

    DERIVED by welding `geodesic_apriori_confinement_uniform` (the confined geodesic phase-flow `P`, the
    base factor + confinement, uniform over `K`), `geodesicJacobi_exists_on_Icc` (the Jacobi field `J`
    along `P` with seed `(0, b)`), and the product-rule repackaging `doubledField_prod_hasDerivAt`
    (`τ ↦ (P τ, J τ)` is a `doubledField` integral curve).  This is the `(S1)` doubled integral-curve
    heart of the CLOSE bridge, for a fixed seed; the `s`-perturbation, the seed-uniform compact
    confinement, the first-jet link and the second-variation data remain CARRIED (see file firewall). -/
theorem confined_doubled_family_exists (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ > (0 : ℝ), ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ ≤ ρ → ∀ b : Point n,
      ∃ Y : ℝ → (Point n × Point n) × (Point n × Point n),
        Y 0 = ((q, v), ((0 : Point n), b)) ∧
        (∀ τ ∈ Set.Ioo (0 : ℝ) 1,
          HasDerivAt Y (doubledField g gi (Y τ)) τ) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          ‖(Y τ).1 - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖v‖) := by
  obtain ⟨ρ, hρ0, C₀, hC0, hconf⟩ := geodesic_apriori_confinement_uniform g gi hC hK
  refine ⟨ρ, hρ0, C₀, hC0, ?_⟩
  intro q hq v hv b
  obtain ⟨P, hP0, hPderiv, hPconf⟩ := hconf q hq v hv
  -- The base geodesic phase-flow is continuous on `[0,1] ⊆ (-2,2)` (from its two-sided derivatives).
  have hPcont : ContinuousOn P (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    have htoo : t ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ((hPderiv t htoo).continuousAt).continuousWithinAt
  -- The Jacobi field along `P` with seed `(0, b)`.
  obtain ⟨J, hJ0, hJderiv⟩ :=
    geodesicJacobi_exists_on_Icc g gi hC P hPcont ((0 : Point n), b)
  refine ⟨fun τ => (P τ, J τ), ?_, ?_, ?_⟩
  · -- Doubled IC.
    show (P 0, J 0) = ((q, v), ((0 : Point n), b))
    rw [hP0, hJ0]
  · -- Doubled ODE on the interior via the product rule.
    intro τ hτ
    have htIcc : τ ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hτ
    have htoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hPd : HasDerivAt P (geodesicField g gi (P τ)) τ := hPderiv τ htoo
    have hJd : HasDerivAt J (fderiv ℝ (geodesicField g gi) (P τ) (J τ)) τ :=
      (hJderiv τ htIcc).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)
    exact doubledField_prod_hasDerivAt g gi hPd hJd
  · -- Confinement of the geodesic factor.
    intro τ hτ
    simpa using hPconf τ hτ

end QIQTH.ExpMap

