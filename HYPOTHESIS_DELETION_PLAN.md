# HYPOTHESIS DELETION — the joins campaign (J1–J4)

**Status:** ✅ COMPLETE (2026-07-02, J1–J4 all landed). **GPT-5.5-pro-VERIFIED** (J1 RECOMMEND; J2/J3/J4 REDIRECTED to the honest forms
below — the redirected shapes are BINDING). **Goal:** delete/weaken carried hypotheses of the landed campaigns by
connecting held theorems: make the eigen-core trace laws unconditional in the finite corner (J1), replace the
Iyer–Wald hypothesis by a derivable kernel-probe theorem + bridge refactor (J2), reduce CHM to an abstract
conformal-transport theorem with named analytic inputs (J3), and land the all-order Deser statement in its honest
formal-Bianchi form (J4).

## Binding corrections (from the verdict — never violate)
- **J2:** the physical FGHMVR identity is NOT derivable from held pieces — land the **kernel-moment
  normalization** (`CHMSymbolProbe_eq_areaVar`) and REFACTOR the bridge to consume the probe; keeping arbitrary
  physical `δK, δS` equal to it by assumption is `hIW` in disguise (forbidden). Fix the `2π` convention
  (chmWeight is unit-edge-slope); the plane-wave phase `e^{ik·x}` under the kernel gives a Fourier multiplier —
  work at the pure algebraic symbol level or normalize by it.
- **J3:** the positive-mass BW theorem (`m > 0`) must NOT be instantiated at `m = 0`. The honest increment is the
  ABSTRACT `CHMTransportData` theorem (modular flow transports under vacuum-preserving unitary conjugacy); the
  carried analytic inputs are: standardness/RS, massless wedge BW, vacuum-invariant conformal covariance, and the
  wedge→ball geometric conjugacy — named structure fields, never axioms. The genuine massless discharge (1+1
  chiral current — beware the scalar zero-mode — or 3+1 conformal scalar) is a follow-on campaign.
- **J4:** NO "DeserTower" whose fields posit conservation at every order (relabeling — forbidden). The honest
  all-order content is **formal-Bianchi consistency propagation**: `FormalDeserSystem` (L, div, order-n source S
  with S_depends_lt + the formalBianchi_step field) and the theorem `next_source_conserved`; extension needs a
  solver/right inverse (`extend_of_solver`). Nonlinear products shift momenta (`n•k` harmonics) — symbol-level
  order-n equations must use the correct total momentum. Order 2 stays the honest concrete Deser theorem until
  the nonlinear Einstein coefficients are formalized.
- **J1 conventions (verified):** `σ_t(E_ij) = e^{it·κ_ij}E_ij` with `κ_ij = log p_i − log p_j` (modular flow
  `ρ^{it}·ρ^{−it}`, `ρ = diag p`); frequency vanishing is AUTOMATIC from the matrix-unit index loop (no
  nondegeneracy needed); `ω(E_ij·B) = e^{κ_ij}·ω(B·E_ij)` from `ρE_ij = e^{κ_ij}E_ij ρ`.

## Increments (verified order)
- [x] **J1 — the finite corner discharges the eigen-core matter inputs.** ✅ DONE (`QIQTH/FiniteCornerEigen.lean`;
  the eigen law landed as `sigmaDiag_single` on `QIQTH.FiniteModularTheory.sigmaDiag`; capstones
  `finiteCorner_tau_trace`/`finiteCorner_tau_pos` — hkms/hfreq/hpos DELETED for the concrete model). `rhoDiag p`, `matState p = tr(ρ·)`,
  matrix units `E i j` (`Matrix.stdBasisMatrix`), `kappa p i j = log p_i − log p_j`. Theorems: `modAut_E`
  (the eigen law), `matState_E_mul_E` (the matrix-unit trace formula `if j=k ∧ i=l then p_i else 0`),
  **`finiteCorner_kms_E`** (the KMS-eigen law — PROVEN), **`finiteCorner_freq_E`** (frequency conservation —
  PROVEN via the index loop), **`finiteCorner_pos`** (`= ∑ p_i‖A_ki‖²` — PROVEN). Then the concrete
  `finiteCornerEigenTerm` family: `eigen_tau_trace` and `eigen_tau_star_mul_nonneg` hold with **NO matter
  hypotheses** — the constructed trace's laws unconditional in a concrete model. (General PosDef ρ via unitary
  eigenbasis transport = follow-on.)
- [x] **J2 — the CHM symbol probe + bridge refactor.** ✅ DONE (`QIQTH/CHMSymbolProbe.lean`; hIW SHRUNK to hDeficit). `chmRadialMass3 R := ∫₀^R 4πr²·chmWeight R r` with
  **`chmRadialMass3_eq`** (`= 4πR⁴/15`, one-variable calculus); the normalized probe `CHMSymbolProbe3` and
  **`CHMSymbolProbe3_einstein_eq_areaVar`** — the kernel-weighted symbol pairing EQUALS the ray-probe pairing
  `areaVar (raySurf v) (einsteinSymbol k h)`. Then the REFACTOR: a bridge-assembly variant
  (`bridge_conditional_probe`) whose deficit input is the derivable probe (the carried content shrinks to the
  identification of the PHYSICAL first-law deficit with the probe — stated once, honestly, as the residual).
- [x] **J3 — the abstract CHM transport theorem.** ✅ DONE (`QIQTH/CHMTransport.lean`; hCHM SHRUNK to hBW + hmodVac + geometry). `CHMTransportData` (wedge, conformal element, vacuum-preserving
  unitary, algebra conjugacy, wedge standardness, wedge BW, geometric conjugacy — named carried fields);
  **`hCHM_of_conformal_transport`** — the ball modular flow is the conformal image of the wedge boost (Tomita
  modular data under vacuum-preserving unitary equivalence, at the one-particle/standard-subspace level we hold);
  corollary: `BallModularFamily.hCHM` is REDUCED from a bare identification to the named transport inputs.
- [x] **J4 — the formal Deser system.** ✅ DONE (`QIQTH/FormalDeser.lean`; per-order conservation tower SHRUNK to one coefficient identity; linear Bianchi DELETED). `FormalDeserSystem` (additive `Field/Source/Constraint`, `L`, `div`,
  order-n source `S` with `S_depends_lt`, the `formalBianchi_step` field — the coefficient-Bianchi content,
  carried until nonlinear coefficients are formalized); `DeserTowerUpTo`; **`next_source_conserved`** (the
  propagation theorem); **`extend_of_solver`** (tower extension given a solver). Instantiate `L`/`div` with the
  HELD linearized symbols (`einsteinSymbol`, `divT`/`kContract`, `bianchi_einsteinSymbol` proving the N=1 step).
  Label: the all-order statement is consistency PROPAGATION; order 2 remains the concrete Deser theorem.

## Discipline (every increment)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green; `#print axioms` std-3; budget 0; AxiomAudit
pins; wire `QIQTH.lean`; ONE commit + `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`; push schannel;
update this checklist + `LEAN_RESULTS_INVENTORY.md`. Honest scope: hypothesis DELETION means the named carried
input becomes a theorem or shrinks to a smaller named input — say which, every time; NEVER claim QG solved.
Consults: `mcp__OpenAI__ask` gpt-5.5-pro.

## Progress log
- **2026-07-02** — plan created from the GPT-5.5-pro joins consult (J1 RECOMMEND with verified conventions;
  J2 → the kernel-probe normalization + refactor; J3 → the abstract transport with named inputs; J4 → the
  formal-Bianchi propagation system). NEXT → J1.
- **2026-07-02** — **J1 LANDED** (`FiniteCornerEigen.lean`, axiom-free std-3, budget 0): the finite corner
  discharges ALL THREE eigen-core matter inputs — `finiteCorner_kms_E` (the KMS-eigen law), `finiteCorner_freq_E`
  (frequency conservation, automatic from the matrix-unit index loop), `finiteCorner_pos` (positivity), plus the
  eigen law `sigmaDiag_single`. Capstones `finiteCorner_tau_trace` + `finiteCorner_tau_pos`: the W3b trace laws
  hold on the `finiteCornerTerm` family with NO matter hypotheses. HYPOTHESES DELETED (for the concrete model):
  hkms, hfreq, hpos. Carried still: the vN closure; general PosDef rho = follow-on. NEXT → J2.
- **2026-07-02** — **J2 LANDED** (`CHMSymbolProbe.lean`, axiom-free std-3, budget 0): `chmRadialMass3_eq`
  (the CHM kernel's radial mass = 4 pi R^4/15, one-variable calculus), `CHMSymbolProbe3_eq` +
  `CHMSymbolProbe3_einstein_eq_areaVar` (the mass-normalized kernel pairing = the ray area probe, at the pure
  algebraic symbol level per the binding correction), and the REFACTOR `bridge_conditional_probe`: the carried
  Iyer–Wald input FACTORS as (deficit = kernel probe) . (kernel probe = areaVar); the second factor is now a
  THEOREM; the residual carried input is hDeficit (the FGHMVR physics, stated once). HYPOTHESIS SHRUNK:
  hIW → hDeficit. NEXT → J3.
- **2026-07-02** — **J3 LANDED** (`CHMTransport.lean`, axiom-free std-3, budget 0): `CHMTransportData` (the
  named carried analytic inputs — ONE massless wedge-BW datum hBW, never the m>0 theorem at m=0; per-ball
  conformal unitaries with geometric conjugacy hflow; the carried modular transport hmodVac in its SMALLEST
  pointwise-on-vacuum form). `hCHM_of_conformal_transport`: the CHM identification at EVERY ball is a THEOREM
  of these inputs; `toBallModularFamily`: C2b's carried per-ball hCHM field is DERIVED;
  `transport_ballHeatFlux_spec`: the forced Clausius datum end-to-end. HYPOTHESIS SHRUNK: hCHM (per-ball
  physics identification) → hBW (one wedge datum) + hmodVac (Tomita functoriality) + geometry. Follow-ons:
  derive hmodVac from the RvD tower (projection transport + Borel-FC covariance); the genuine massless wedge
  BW (1+1 chiral / 3+1 conformal scalar). NEXT → J4.
- **2026-07-02** — **J4 LANDED** (`FormalDeser.lean`, axiom-free std-3, budget 0): `FormalDeserSystem`
  (order-indexed L n/div n — harmonics at n•k per the binding bookkeeping; PROVEN linear Bianchi; S_depends_lt;
  ONE carried coefficient field formalBianchi_step, an identity in the history, NOT a conservation posit).
  `next_source_conserved` (conservation DERIVED at each order), `extend_of_solver` (the bootstrap formally
  unobstructed), `einsteinDeserSystem` (L n = einsteinSymbol(n•k), div n = kContract(n•k), bianchi DISCHARGED
  by bianchi_einsteinSymbol at every harmonic), `einstein_next_source_conserved` (end-to-end). HYPOTHESIS
  SHRUNK: the per-order conservation tower → the single coefficient identity; the linear Bianchi input DELETED.
  Order 2 stays the concrete Deser theorem; the nonlinear Einstein coefficients = the cited frontier.
- **2026-07-02** — **CAMPAIGN COMPLETE (J1–J4, 4/4).** Ledger: J1 hkms+hfreq+hpos DELETED (theorems of the
  finite corner); J2 hIW SHRUNK to hDeficit (kernel probe = area probe now a theorem); J3 hCHM SHRUNK to
  hBW (one wedge datum) + hmodVac (functoriality) + geometry; J4 the conservation tower SHRUNK to one
  coefficient identity + linear Bianchi DELETED. Named follow-ons: general PosDef rho; hmodVac from the RvD
  tower; the genuine massless wedge BW; the nonlinear Einstein coefficients; the vN closure. NOT QG; no wall
  crossed. Loop deleted.
