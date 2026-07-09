# QG PLAN — moving geometry from HYPOTHESIS to CONCLUSION

**Date:** 2026-07-09. **Basis:** live Lean-type audit (not docstrings) + GPT-5.5-pro critical-path consult.
**One-line thesis:** the whole framework today has the metric `g` as a *hypothesis* (left of the
turnstile); genuine QG needs a theorem where **geometry is the conclusion**, constructed from a finite
quantum/entanglement substrate. This plan is the minimal Lean-shaped path to that.

---

## 0. Where we actually are (Lean ground truth, verified 2026-07-09)

- Strongest GR theorem `WedgeKMSToGR.qiqt_gr_freefield_complete`: takes `g, gi : Point 4 → Fin 4 →
  Fin 4 → ℝ` as **universally-quantified hypotheses** (smooth, symmetric, invertible, Lorentzian);
  concludes `∃ Λ, a·T_μν[φ,g] = G_μν[g] + Λ g_μν` — Einstein's eq as a thermodynamic equation of state
  **for the given g**. `G_μν` is the genuine Christoffel→Riemann→Ricci tensor; curved `g` allowed
  (explicit pp-wave). Axiom-free. ⟹ **Jacobson induced gravity on an assumed manifold**; `g` never derived.
- `HolographicCapacityBound` is a Lean **`class`** — `log|H_R| ≤ A/4ℓ_P²` is a *typeclass hypothesis*.
- Emergent-geometry results (`weightedCutDist`, `embedDist`, `graphDist`) are genuine metrics but built
  from **supplied** probes `χ : I → X → ℝ` / a supplied graph on abstract `X`. `minCut_area_not_metric`
  proves min-cut violates the triangle inequality (it is area, not distance). **No theorem constructs a
  metric from a quantum state.**
- `RecordMincut.mincut_bounds_distinguishable_records`: Schmidt rank across a cut ≤ min-cut bond
  capacity (finite, axiom-free) + concrete MPS instance. "min-cut = GEOMETRIC area" is NOT a theorem.
- Finite + free-field modular theory (finite Tomita–Takesaki, one-particle BW, boost=rapidity-translation
  unitary, symmetric Fock, second quantization) EXISTS axiom-free. Continuum Type III₁ / unbounded GNS /
  crossed-product→trace does NOT (Mathlib lacks unbounded self-adjoint + continuum modular theory).
- Unconditional finite max-flow = min-cut theorem exists (`QG/MaxFlowMinCut`).

## 0.1 What's missing for QG (dependency order)

1. **Geometry-as-output** — a theorem mapping (finite quantum state) → (metric), with the graph/probes
   *derived from the state*, not supplied. **The core gap; everything else supports it.**
2. **Capacity ↔ geometric area as a theorem, not a typeclass** — replace `HolographicCapacityBound`.
3. **A finite substrate with a refinement/continuum knob** (Tier-2 §2.1).
4. **Emergent Lorentz invariance with quantified error** (the recurring killer for finite programs).
5. **Constraints / diffeomorphism / dynamical geometry** (GR is constrained dynamics).
6. **Linearized Einstein FROM the state** — first law where `δg` is *derived* from `δstate`.
7. **Continuum Type III₁ / crossed-product → FQ** — needs unbounded-operator Mathlib infra.

---

## 1. The first genuinely-QG theorem (highest leverage) — geometry as OUTPUT

**Route (GPT-5.5-pro):** NOT `d(A,B) := f(I(A:B))` directly (mutual information has no triangle
inequality). Instead: **state → MI/cut-rank adjacency graph → graph shortest-path metric.** The metric
is then a genuine metric (Mathlib `SimpleGraph.dist`), and the *content* theorem is that an explicitly
constructed finite state DECODES to the intended graph.

**Anti-circularity (critical):** the Hilbert substrate must NOT be indexed by the graph's edges. Use a
fixed "complete pair register" substrate depending only on `V` and `q`; the graph appears only in the
*state vector*, not in the decoder type. Use Rényi-0 / cut-rank MI first (no matrix logs).

**Target theorem (Lean-shaped):**
```
completePairBell_outputs_rankMI_graphGeometry
  (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G connected) {q} (hq : 2 ≤ q) :
  let ψ := completePairBellState G q
  rankMIAdj ψ = G                                    -- the state DECODES to G (edges from rank-MI)
  ∧ (∀ A, cutRank ψ A = q ^ crossingEdgeCard G A)    -- cut rank = bond count (area law, by construction)
  ∧ IsMetric (decodedDist ψ)                          -- graph shortest-path metric is a genuine metric
  ∧ (∀ u v, decodedDist ψ u v = (G.dist u v : ℝ))     -- and equals the intended graph distance
```
where `rankMIAdj ψ` has `Adj u v ↔ cutRank ψ {u}·cutRank ψ {v} > cutRank ψ {u,v}` (strict rank
submultiplicativity — positive Rényi-0 MI, no logs). Public demo corollary: `∃ ψ, decodedDist ψ` is a
metric equal to the line/interval distance (`pathGraph`).

This closes the "supplied `χ`" gap: **a metric that is the OUTPUT of an explicit entangled state.**

---

## 2. Phased plan (each phase: Lean deliverable + honest tractability tag)

Tags: **(b)** tractable now · **(c)** research-grade / needs new Mathlib infra · **(sim)** simulation, not Lean.

| Ph | Deliverable | Lean target | Tag |
|----|-------------|-------------|-----|
| 1 | **Geometry-as-output toy** | `rankMIAdj (completePairBellState G q) = G` ⟹ `decodedDist` is a metric = `G.dist` | **(b)** |
| 2 | **Capacity/area = theorem** (not typeclass) | `cutRank ψ A = q^(crossing edges)`; `Real.log (cutRank ψ A) = stateArea0 ψ A` (area from decoded links); routed-Bell fixed-partition entropy = min-cut (via max-flow=min-cut) | **(b)** for Bell/fixed-partition; **(c)** for full RT code |
| 3 | **Refinement / continuum knob** | `chainState N q`; `scaledDecodedDist` refines the unit interval (chain→[0,1]); lattice→torus | **(b)** 1D; **(c)** higher-dim Riemannian / Gromov–Hausdorff |
| 4 | **Finite capacity + Lorentz-violation scaling** | `latticeDirac_lorentzViolation_bound : |disp² − (m²+k²)| ≤ C·a²·k⁴` (finite Hilbert dim, staggered/free fermion) | **(b)** free; **(sim)** interacting |
| 5 | **Differentiable weighted geometry from `δstate`** | `weightedDecodedDist` metric with MI-derived edge weights; finite first law `d/dε S(ρ+εδρ)|₀ = −Re tr(δρ·log ρ)` | **(c)**; diagonal/commuting case **(b)** |
| 6 | **Linearized Einstein FROM the state** | `finite_firstLaw_implies_linearizedRegge`: `δg` DECODED from `δstate`, `Regge(δg) = T[δstate]`; and PROVE the first law `hFL` from an explicit finite state (not assume it) | **(c)** — the first genuine QG wall |
| 7 | **Continuum / Type III bridge** | `decodedMetric_continuum_Einstein`: `g = lim decode(ψ_N)` satisfying EFE | **(c)** — blocked by Mathlib (unbounded self-adjoint, continuum modular) |

### Phase-1 supporting lemmas
`bellPair_cutRank_cross = q`, `bellPair_cutRank_sameSide = 1`, `tensorProduct_cutRank_mul`
(⟹ `cutRank ψ A = q^(#edges crossing A)`), then singleton rank-MI detects exactly the edges.
**Fallback if tensor bookkeeping is painful:** prove the same for a *classical* shared-edge random
variable (classical MI) first, then upgrade to Bell/stabilizer entanglement.

### Phase-2 area-from-state (replaces the typeclass)
`linkArea0 ψ u v := ½·rankMI0 ψ u v`, `stateArea0 ψ A := ∑ boundary links`, target
`Real.log (cutRank ψ A) = stateArea0 ψ A` — for this explicit state the area law is a **theorem**, not
`HolographicCapacityBound`. Min-cut saturation for a FIXED partition is tractable (route Bell pairs
along an integral max-flow); one state saturating RT for ALL regions is research-grade.

---

## 3. Honest verdict + the named walls

**Reachable in ~months (Lean, genuine):** Phases 1–3 (+4 free-field). A theorem where a **finite
entangled state outputs a spatial graph metric**, the area law holds **as a theorem** for that state,
and the metric **refines** a continuum interval/torus — with quantified Lorentz-violation scaling for
free matter. This is a real, non-circular improvement over supplied-`χ` and supplied-`g`: geometry
becomes an **output**. It is a finite *spatial* graph metric, **not GR**.

**The first genuine wall (Phase 5→6):**
- *Lean blocker:* differentiability of finite matrix-log entropy `d/dε S(ρ+εδρ)` for non-commuting `ρ`
  (commuting/diagonal case is tractable now).
- *Physics blocker:* producing the entanglement-equilibrium / linearized-first-law condition **from an
  explicit finite state + Hamiltonian**, rather than adding it as a hypothesis.

**The continuum wall (Phase 7):** unbounded self-adjoint operators + spectral/functional calculus, GNS
for continuum QFT, von Neumann algebras beyond finite/bounded, Type III modular theory, crossed
products/traces — all absent from Mathlib. Finite modular theory suffices for Phases 1–6 toys; the
continuum Jacobson/BW/Type-III does not.

**Bottom line:** yes, there is a route to a Lean theorem with **geometry as output** within months (a
meaningful toy), and it is the honest first QG step. It does **not** reach GR; the irreducible core
(non-assumed linearized Einstein from an explicit state; the continuum limit) is blocked on the two
named walls above. Every phase ships an axiom-free green increment; nothing is faked; the walls are
named, not hidden.
