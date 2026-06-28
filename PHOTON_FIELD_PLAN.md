# PHOTON_FIELD_PLAN — the free Maxwell (photon) field in QIQT-H

**Status:** active plan (opened 2026-06-28). **Scope:** the **free** Maxwell / electromagnetic field
(the photon) — the second instance of "matter beyond scalars," after the free Dirac electron
(`ELECTRON_FIELD_PLAN.md`). **Out of scope (cited, not formalized):** interacting QED, charged sectors,
soft photons / infraparticles, dressed charged fields, Gupta–Bleuler/BRST indefinite metric, the full
continuum Gauss-law boundary algebra / Kabat contact determinant.

**GPT-5.5-pro-vetted (2026-06-28).**

---

## 0. The crux, stated first (do not bury it)

**The photon is BOSONIC** (CCR/Weyl, *symmetric* Fock `Γ_s` = the **same functor as the scalar**), so —
unlike the electron (which needed the CAR/exterior algebra) — it **reuses the existing bosonic Weyl/CCR
substrate AND the existing bosonic second-quantized modular flow** (`Fock/SecondQuant`,
`Fock/SecondQuantModularFlow`, `Fock/BoostKMS`). There is **no Klein twist, no graded sign**: the wedge
modular flow is the ordinary geometric boost (Bisognano–Wichmann), and the Unruh occupation is
**Bose–Einstein** `n_ω = 1/(e^{2πω}−1)` (the `−1`, vs the electron's `+1`).

> **The genuine crux is GAUGE / constraint locality** — NOT a modified modular flow. Three sharp points
> (GPT-5.5-pro):
>
> 1. **Build on the POSITIVE physical Hilbert space, never the indefinite metric first.** Use the
>    gauge-invariant field strength `F = dA` (or the transverse / helicity-±1 one-particle space
>    `h_γ ≃ h_{+1} ⊕ h_{−1}`), NOT the 4-component `A_μ` (whose naive Fock has a negative-norm temporal
>    mode). The CCR/Weyl algebra lives on the **reduced** symplectic space of Maxwell test data
>    (gauge/null directions quotiented out).
> 2. **Records/capacity attach to the GAUGE-INVARIANT observable algebra** (`F_μν`, `T_μν`,
>    energy/helicity, Wilson loops) — the photon analogue of the electron's "records = even bilinears."
> 3. **Regional information is generally a CENTERED flux-sector algebra, not a simple tensor factor.**
>    For a *regulated/cut* regional algebra, `𝒜_R ≃ ⊕_q 𝓑(𝓗_{R,q})` with `q` = boundary-flux sectors
>    (electric-center `E_⊥|_{∂R}`), and the entanglement entropy splits into a **bulk piece + a Shannon
>    piece over the flux superselection** — the EDGE-MODE / Kabat contact-term structure. (Honest: this
>    "nontrivial center" is the *regulated/cut* statement; in continuum AQFT nice contractible
>    regions/wedges can be *factors* — the sharper continuum statement is **non-factorization across
>    cuts + topological flux sectors / Haag-duality failure**, not "every local algebra has a center.")

**The big quantitative difference from the electron:** **bosonic capacity is INFINITE without a cutoff** —
`Γ_s(h)` is infinite-dimensional even for finite-dim `h` (vs CAR's finite `dim(⋀h)=2ⁿ`). So the photon
finite-capacity bound **requires a photon-number / energy / thermal cutoff**: with a number cutoff `N`,
`dim Γ_s^{≤N}(h) = C(dim h + N, N)` and `S ≤ log C(dim h + N, N)`.

---

## 1. What carries over from the scalar/electron, what's new (the work list)

| Ingredient | Status for the photon | Cat. |
|---|---|---|
| Statistics / Fock | **bosonic CCR/symmetric Fock `Γ_s`** — REUSE scalar `Fock/SecondQuant` | reuse |
| One-particle space | **transverse / helicity ±1** `h_γ = h_{+1} ⊕ h_{−1}` (massless spin-1, only 2 pol.) | new (a) |
| Capacity bound | `S ≤ log dim Γ_s^{≤N}(h) = log C(dim h+N, N)` — needs a **number cutoff `N`** | new (a) |
| Unruh occupation | **Bose–Einstein** `n_ω = 1/(e^{2πω}−1)` (the `−1`); `S_ω=(n+1)log(n+1)−n log n` | new (a) |
| Modular flow `Δ^it` | the geometric boost; **REUSE bosonic `secondQuantModFlow`** (`Δ^it_γ = Γ_s(Δ^it_1)`) | reuse |
| Records | **gauge-invariant observables** `F_μν`, `T_μν`, energy/helicity (NOT `A_μ`) | new (b) |
| Regional algebra | **centered flux-sector** `⊕_q 𝓑(𝓗_{R,q})` (cut); continuum = non-factorization/topological | new (b)/(c) |
| Entanglement entropy | `S = H(flux p_q) + Σ_q p_q S_bulk` — the edge-mode / contact-term split | new (b) |
| Gauss-law constraint | `∇·E = 0`; the constraint algebra → the boundary-flux center | new (c) |
| Gauge fixing | Gupta–Bleuler/BRST indefinite metric — **DEFER** (use `F`/transverse instead) | frontier |
| 1/G / area | photon contributes to `1/G` (species) + the Kabat contact term (sign-subtle) | cited |

`1/4` / value-of-G note: the photon is one more species in the Sakharov `1/G` sum; the contact term has
the famous Kabat sign — do NOT encode it as a naive positive finite number. Never claim the value of `G`.

---

## 2. Phases (Lean-concrete, ship-green-increments). New modules under `QIQTH/Fock/Photon/`.

Each phase is an axiom-free green checkpoint (`#print axioms` = standard 3; budget 0; wire into
`QIQTH.lean` + `AxiomAudit.lean`). Ordered most-tractable-first; reuse the bosonic substrate aggressively.

**P1 — Bosonic photon Fock (REUSE).** `PhotonFock h_γ := Γ_s h_γ` (the existing symmetric Fock), with
`h_γ` the physical/transverse helicity-±1 one-particle space. *(reuse)*

**P2 — Truncated bosonic dimension (the analytic core; START HERE).**
`dim Γ_s^{≤N}(h) = C(dim h + N, N)` (the number-cutoff Fock dimension). *(new, (a) — the cleanest first
analytic theorem)*

**P3 — The photon finite-capacity bound.** `S(ρ) ≤ log C(dim h_γ + N, N) = log dim Γ_s^{≤N}(h_γ)` — the
bosonic mirror of the CAR `S_vN ≤ log dim(⋀h_R)`, **with the number cutoff `N`**. Plus the corollary
`sup S = ∞` without a cutoff (the bosonic capacity is unbounded — the structural difference from CAR).
*(new, (a))*

**P4 — Bose–Einstein Unruh occupation.** `boseEinstein β ω = 1/(e^{βω}−1)`, the KMS+CCR balance
`n = e^{−βω}(1+n)`, uniqueness, and `n > 0` for `βω > 0`; `S_ω=(n+1)log(n+1)−n log n`; two helicities =
degeneracy, not new statistics. (The CCR `+` analog of the electron's FD/CAR `−`; partly already in
`Fock/Dirac/FermiDirac.lean`'s `boseEinstein` stub — extend it.) *(new, (a))*

**P5 — Photon modular flow (REUSE).** `Δ^it_γ = Γ_s(Δ^it_1) = secondQuantModFlow` — the existing bosonic
second-quantized modular flow IS the photon's (it's bosonic). State the one-particle action, group law,
automorphism, KMS — all by reuse. *(reuse)*

**P6 — Gauge-invariant records.** the gauge-invariant observable predicate/subalgebra (`F`, `T_μν`,
energy/helicity); records = gauge-invariant. *(new, (b))*

**P7 — Modular flow preserves the gauge-invariant records.** the boost/modular automorphism commutes
with the gauge action (up to a transformed gauge parameter), so it preserves the gauge-invariant
fixed-point algebra — the photon analogue of the electron's `fermiSecondQuantModFlow_isEven`. *(new, (b))*

**P8 — The centered (edge-mode) entropy decomposition.** `S(⊕_q p_q ρ_q) = H(p_q) + Σ_q p_q S(ρ_q)` for
a centered flux-sector algebra — the edge-mode / contact-term home, the photon analogue of the electron's
graded capacity `S(ρ_R)=H(p_q)+Σ p_q S(ρ_q)` (label = **boundary flux**, not fermion parity).  Note the
`−log p_q` central piece contributes to entropy/first-law but cancels from the *inner* modular flow.
*(new, (b) — reuse `Fock/Dirac/GradedCapacity.lean`'s chain rule, relabelled)*

**P9 — Abstract boundary-flux sectors.** model the electric-center flux labels `q`, the capacity
contribution `H(p_q)`, and the fixed-sector bulk entropy — the Gauss-law edge-mode structure abstractly.
*(new, (b)/(c))*

**P10 — Deferred frontier (cited).** Gupta–Bleuler/BRST indefinite metric; the full Maxwell field-strength
CCR from test 2-forms + the Maxwell Pauli–Jordan commutator; the Hodge/transversality quotient; Haag
duality / topological flux sectors; the continuum Gauss-law boundary algebra + Kabat contact determinant;
interacting QED. *(frontier — after the positive-metric/centered-capacity tier is stable)*

## 3. Reuse map (what the scalar/electron substrate already gives)
- **Bosonic Fock + modular flow:** `Fock/SecondQuant`, `Fock/SecondQuantModularFlow` (`secondQuantModFlow`,
  group law, isometry, vacuum), `Fock/BoostKMS`, `Fock/Weyl*` (CCR), `StandardSubspaceModularFlow`
  (`modUnitary`). The photon modular tier is mostly **reuse** (it's bosonic).
- **Modular/KMS scaffolding:** `FiniteModularTheory` (`modAut`, `stateOf`, `kms_condition`, `sigmaDiag`),
  `Spectral/SpectralTheorem` (`modFlow`).
- **Entropy/capacity:** `Fock/Dirac/QuasiFreeEntropy` (binary/relative entropy — bosonic mode entropy is
  the `+1` analog), `Fock/Dirac/GradedCapacity` (the chain rule `S=H(p)+Σp_q S_q` → P8 edge modes).
- **PhysLean:** `Physlib.QFT.PerturbationTheory` `FieldStatistic.bosonic`, the bosonic `CrAnFieldOp` /
  `WickAlgebra` (the CCR operator layer, if needed).

## 4. Honest scale
The bosonic/modular/Unruh tier is **mostly reuse** of the existing scalar+electron machinery (the photon
is bosonic — the modular flow is the *same* `secondQuantModFlow`, the only change is the helicity-±1
one-particle space and the Bose `−1` sign). The genuinely **new** work is the **gauge/edge-mode** tier
(gauge-invariant records, the centered flux-sector capacity decomposition) — tractable abstractly. The
**frontier** is the indefinite-metric/Gauss-law continuum construction + the Kabat contact term +
interacting QED — deferred and cited. No `sorry`; never claim the value of `G`; the photon contact-term
sign is subtle (Kabat) — don't encode it naively; free Maxwell only.

## 5. First theorem + progress log
**Single sharpest first theorem (P2→P3):** `dim Γ_s^{≤N}(h) = C(dim h + N, N)` ⟹ the photon capacity
bound `S(ρ) ≤ log C(dim h_γ + N, N)`, **with the number cutoff `N`** (and the `sup S = ∞`-without-cutoff
corollary — the bosonic capacity is unbounded, the structural difference from the CAR electron).

- 2026-06-28 — plan opened (GPT-5.5-pro-vetted). Crux = bosonic reuse (CCR + `secondQuantModFlow`) +
  gauge/edge-center (records = gauge-invariant; regional = centered flux-sector; capacity needs a
  CUTOFF). Bose–Einstein `−1` (vs electron `+1`). Next: **P2** (`PhotonFock.lean` — truncated bosonic
  Fock dimension `C(dim h+N, N)`), then **P3** (the cutoff capacity bound).
- 2026-06-28 — **P2 DONE** (`QIQTH/Fock/Photon/PhotonFock.lean`, axiom-free standard-3, budget 0, 2942
  jobs green). `truncFockDim d N := Σ_{k=0}^N multichoose(d,k) = dim Γ_s^{≤N}(h)`; `truncFockDim_succ`
  (cutoff recurrence); **`truncFockDim_eq_choose : truncFockDim d N = C(d+N, N)`** (induction + Pascal
  `Nat.choose_succ_succ`) — the closed-form truncated bosonic Fock dimension, FINITE only by the number
  cutoff `N`; plus `truncFockDim_mono`/`truncFockDim_strictMono` (dim ↑ in `N` for `d≥1` — the
  finite-`N` shadow of the photon's unbounded capacity, the "sup S=∞ without a cutoff" corollary). Wired
  into `QIQTH.lean` + `AxiomAudit.lean`. Next: **P3** (the capacity bound `S ≤ log C(dim h_γ+N, N)` —
  reuse `shannon_le_log_card` with `card = truncFockDim d N`), then **P4** (extend the existing
  `boseEinstein` stub: KMS balance done, add `n>0`, the Unruh `S_ω=(n+1)log(n+1)−n log n`).
- 2026-06-28 — **P3 DONE** (`QIQTH/Fock/Photon/PhotonCapacity.lean`, axiom-free standard-3, budget 0,
  3195 jobs green). **`photon_capacity_bound : S_vN(ρ) ≤ log C(dim h_γ+N, N)`** for any density `ρ` on the
  number-cutoff bosonic Fock `Γ_s^{≤N}(h_γ)` — the bosonic mirror of the electron CAR `S_vN ≤ log dim(⋀h_R)`,
  via the cutoff-free `vonNeumannEntropy_le_log_card` (`FQBoundMicro`) on `Fin (truncFockDim d N)` + P2's
  `truncFockDim_eq_choose`. `photon_capacity_unbounded` (`d≥1`): the truncated dim exceeds any `B` for
  large `N` ⟹ `log dim → ∞` — the "sup S=∞ without a cutoff" contrast with the cutoff-free electron.
  Wired into `QIQTH.lean` + `AxiomAudit.lean`. Next: **P4** (extend the `boseEinstein` stub: `n>0`, the
  Unruh `S_ω=(n+1)log(n+1)−n log n`), then **P1/P5** reuse wiring (`PhotonFock=Γ_s h_γ`, `Δ^it_γ=Γ_s(Δ^it_1)`).
- 2026-06-28 — **P4 DONE** (`QIQTH/Fock/Photon/PhotonUnruh.lean`, axiom-free standard-3, budget 0, 1926
  jobs green). The Bose–Einstein photon Unruh occupation `n_ω=1/(e^{βω}−1)` (the `−1`/CCR analog of the
  electron FD cluster): **`boseEinstein_pos`** (`0<n` for `βω>0`), **`boseEinstein_unique`** (any `n`
  solving the CCR KMS balance `n=e^{−βω}(1+n)` is the BE occupation — bosonic mirror of `fermiDirac_unique`),
  **`boseEinstein_gt_fermiDirac`** (`n_BE>n_FD` — more occupation, NO Pauli ceiling; the occupation-level
  reason the photon needs a number cutoff, P2/P3), **`rindlerOccupationBose`** (`=boseEinstein 2π ω`) +
  `_balance` + `_pos` (the Unruh occupation at the BW temperature `β=2π`; requires `βω≠0`, the photon
  zero-mode = gauge/IR frontier P10). Wired into `QIQTH.lean`+`AxiomAudit.lean`. Next: **P1/P5** reuse
  wiring (`PhotonFock=Γ_s h_γ`; `Δ^it_γ=Γ_s(Δ^it_1)=secondQuantModFlow`), then **P6** (gauge-invariant records).
- 2026-06-28 — **P1/P5 DONE** (`QIQTH/Fock/Photon/PhotonModularFlow.lean`, axiom-free standard-3, budget 0,
  3528 jobs green). Certifies the **reuse**: the photon's continuum field-level modular flow
  `Δ_γ^{it}=Γ_s(Δ^{it})` IS the existing bosonic `secondQuantModFlow` (vs the electron's fermionic
  `Γ₋=ExteriorAlgebra.map`) — nothing new built; named in the photon namespace on the transverse
  helicity-±1 one-particle space. **`photonModFlow`** + `_expVec` (`Γ_s(Δ^it)e(f)=e(Δ^it f)`), `_vacuum`,
  `_zero` (=id), **`_add`** (the one-parameter group law), `_isometric`; **`photonModFlowH`** (Hilbert
  completion) + `_isometry` + `_vacuum`. So `Δ_γ^{it}` is a one-parameter isometric automorphism group
  fixing the vacuum, reused wholesale. Wired into `QIQTH.lean`+`AxiomAudit.lean`. Next: **P6** (the
  gauge-invariant observable predicate/subalgebra — records = `F_μν`/`T_μν`), then **P7** (the modular
  flow preserves the gauge-invariant records — the photon analogue of `fermiSecondQuantModFlow_isEven`).
- 2026-06-28 — **P6+P7 DONE** (`QIQTH/Fock/Photon/PhotonGaugeRecords.lean`, axiom-free standard-3, budget
  0, 1062 jobs green). The first **genuinely new** (non-reuse) photon structure — the gauge-invariant
  observable algebra (records), the photon analogue of the electron's even subalgebra. **P6**:
  `IsGaugeInvariant a := ∀ gauge transf gaugeAct Λ, gaugeAct Λ a = a` (the gauge-fixed points = records
  `F_μν`/`T_μν`/energy, NOT raw `A_μ`); **`gaugeInvariantSubalgebra`** (the records form a `Subalgebra` —
  closed under `+`,`*`,scalars); **`isGaugeInvariant_of_trivial`** (on the positive physical transverse
  space the gauge action is trivial ⟹ every physical observable IS a record — why one builds on `F=dA`,
  not indefinite `A_μ`). **P7**: **`isGaugeInvariant_map_of_comm`** — any algebra map commuting with the
  gauge action (e.g. `photonModFlow`, gauge-blind on the physical space) preserves records — the photon
  analogue of `fermiSecondQuantModFlow_isEven` (modular dynamics keeps records as records). Wired into
  `QIQTH.lean`+`AxiomAudit.lean`. Next: **P8** (the centered edge-mode entropy decomposition
  `S=H(p_q)+Σ p_q S_q` over boundary-flux sectors — reuse `GradedCapacity` relabelled), then **P9**.
- 2026-06-29 — **P8 DONE** (`QIQTH/Fock/Photon/PhotonEdgeModes.lean`, axiom-free standard-3, budget 0,
  3056 jobs green). The centered (edge-mode) entropy decomposition: the photon's regional algebra is a
  centered flux-sector algebra `⊕_q 𝓑(𝓗_{R,q})` (Gauss-law ⟹ boundary-flux center), so
  `S(ρ_R)=H(p_q)+Σ_q p_q S(ρ_{R,q})` — the edge-mode/Kabat contact-term structure, the SAME decomposition
  as the electron's graded capacity with label = boundary flux (not parity). **`photon_edge_entropy_decomp`**
  (= `gradedShannon_chain_rule` relabelled); **`photon_edge_term_nonneg`** (the boundary-flux Shannon term
  `H(p_q)≥0` — at finite cutoff the edge modes add positively, vanishing iff the flux is definite = a
  factor); **`photon_edge_capacity_le`** (`S≤log Σ_q dim 𝓗_{R,q}`, = `gradedShannon_le_log_total`). HONEST:
  the continuum Kabat contact-term SIGN is a renormalization subtlety beyond this finite-cutoff positivity;
  the Gauss-law boundary algebra + heat-kernel determinant are deferred P10. Wired into
  `QIQTH.lean`+`AxiomAudit.lean`. Next: **P9** (abstract boundary-flux sectors — model the electric-center
  flux labels `q`, the capacity contribution `H(p_q)`, the fixed-sector bulk entropy).
- 2026-06-29 — **P9 DONE** (`QIQTH/Fock/Photon/PhotonFluxSectors.lean`, axiom-free standard-3, budget 0,
  3057 jobs green). The abstract boundary-flux sector structure (the edge-mode center): the Gauss-law
  constraint gives the regional algebra a CENTER generated by the boundary electric flux `E_⊥|_{∂R}`, with
  spectrum the flux sectors `Q`. **`fluxEntropy p = Σ_q negMulLog(p_q) = H(p_q)`** — the entropy of the
  central flux distribution (the edge-mode term of P8). **`photon_flux_entropy_nonneg`** (`H(p_q)≥0`);
  **`photon_flux_entropy_le_log_card`** (`H(p_q) ≤ log|Q|` — the edge-mode/center capacity is bounded by the
  boundary flux-sector COUNT, via `shannon_le_log_card`); **`photon_centered_entropy_eq`** (P8's split with
  the flux term named). The flux observables are CENTRAL records (P6). Wired into `QIQTH.lean`+`AxiomAudit.lean`.
  **★ This completes the photon's P2–P9 tier** — capacity (P2/P3), Bose–Einstein Unruh (P4), modular-flow
  reuse (P1/P5), gauge-invariant records (P6/P7), centered edge-mode entropy (P8), boundary-flux sectors (P9).
  Remaining = the cited continuum frontier **P10** (Gupta–Bleuler/BRST indefinite metric; Maxwell `F=dA` CCR
  from test 2-forms + Pauli–Jordan; Gauss-law boundary algebra; Kabat contact determinant; interacting QED).
