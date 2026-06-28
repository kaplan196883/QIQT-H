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
- 2026-06-29 — **P4 completion: the photon Unruh thermal entropy** (`PhotonUnruh.lean`, axiom-free
  standard-3, budget 0, 1926 jobs green). **`boseEntropy n := (1+n)log(1+n) − n log n`** (the thermal
  harmonic-oscillator entropy); **`photon_mode_entropy`** (`βω>0`): `boseEntropy(1/(e^{βω}−1)) =
  −log(1−e^{−βω}) + βω·n = log Z + β⟨E⟩` — the bosonic mirror of `electron_mode_entropy`. **UNBOUNDED**: as
  `βω→0⁺`, `n→∞` and `S→∞` (the entropy-level reason the photon needs a number cutoff, P2/P3) — the sharp
  contrast with the electron's Pauli ceiling `S≤log 2` (`electron_mode_entropy_le_log2`). Wired into
  `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **P4 completion: the photon entanglement first law `δS=δ⟨K⟩`** (`PhotonUnruh.lean`,
  axiom-free standard-3, budget 0, 2180 jobs green). **`boseEinstein_logit`** (`log((1+n)/n)=βω` at the BE
  occupation — the CCR analog of `fermiDirac_logit`); **`hasDerivAt_boseEntropy`** (`d/dn S_BE =
  log((1+n)/n)`, via `S_BE = negMulLog n − negMulLog(1+n)`); **`photon_firstLaw`**: `HasDerivAt boseEntropy
  (βω) (boseEinstein β ω)` — at the Unruh occupation the bosonic mode entropy's derivative IS the modular
  energy `βω` (`=2πω` at the BW temperature), the bosonic mirror of `electron_firstLaw`. Completes the
  photon thermodynamic chain (occupation → mode entropy → first law `δS=δ⟨K⟩` that drives the area law).
  (Added `import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`.) Wired into `AxiomAudit.lean`;
  standard-3; budget 0.
- 2026-06-29 — **P6/P10 bridge: the field strength `F=dA` is gauge-invariant + the Bianchi identity, via
  `d²=0`** (`QIQTH/Fock/Photon/PhotonFieldStrength.lean`, axiom-free standard-3, budget 0, 799 jobs green).
  The concrete reason the photon's records are the gauge-invariant `F_μν` (P6): modelling `d_gauge:Λ→ₗA`
  (`Λ↦dΛ`, pure gauge) and `d_F:A→ₗF` (`F=dA`) with the cochain condition `d_F∘d_gauge=0`. **`fieldStrength_
  gauge_invariant`**: `d_F(A + d_gauge Λ) = d_F A` — `F=dA` is unchanged by `A↦A+dΛ` (the pure-gauge shift
  lands in `ker d_F`), so records are `F`, NOT `A`. **`bianchi_identity`**: `d_next(F)=0` for `F=dA` — the
  homogeneous Maxwell eqs `dF=0`. Both the gauge-invariance of `F` and its closedness are the two faces of
  the single condition `d²=0`. Wired into `QIQTH.lean`+`AxiomAudit.lean`; standard-3; budget 0. (The full
  continuum Maxwell `F`-net CCR from de Rham test 2-forms remains the deferred P10 frontier.)
- 2026-06-29 — **P6 (sharpest form): the field strength descends to the gauge quotient** (added to
  `PhotonFieldStrength.lean`, axiom-free standard-3, budget 0, 1177 jobs green). **`fieldStrength_descends_
  to_quotient`**: since `range d_gauge ⊆ ker d_F` (`d²=0`), `F=dA` factors as `F̄ ∘ mkQ` through the quotient
  `A ⧸ range d_gauge` (`Submodule.liftQ`) — so the photon's physical observable is a function of the
  **gauge-equivalence class** `[A]`, not the gauge representative `A`. The "records live on the physical
  (gauge-quotient) configuration space" thesis (§0/P6) in its sharpest form. (Added
  `import Mathlib.LinearAlgebra.Quotient.Basic`.) Wired into `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **P6/P9 bridge: the cohomological closed/exact structure** (`PhotonFieldStrength.lean`,
  axiom-free standard-3, budget 0, 1177 jobs green). **`fieldStrength_eq_iff_sub_mem_ker`**: `d_F a = d_F a'
  ↔ a−a' ∈ ker d_F` (the `F`-fibers are closed-element cosets). **`pureGauge_le_ker`**: `range d_gauge ≤
  ker d_F` — the `d²=0` cochain condition as a submodule inclusion (**exact ⊆ closed**; a gauge shift never
  changes `F`). The quotient `ker d_F ⧸ range d_gauge` is the first cohomology = the **topological /
  boundary-flux sectors** (closed-but-not-exact) — the algebraic home of the photon's edge-mode center
  (P9 `PhotonFluxSectors`): nontrivial cohomology = nontrivial boundary flux; trivial for a contractible
  region (a factor, no center — the §0 honest caveat). Wired into `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **P6/P9: trivial cohomology ⟹ `F` determines `A` up to gauge** (`PhotonFieldStrength.lean`,
  axiom-free standard-3, budget 0, 1177 jobs green). **`fieldStrength_eq_iff_gauge_of_trivial_cohomology`**:
  when `ker d_F = range d_gauge` (every closed is exact — a **contractible** region, no flux sectors, the
  regional algebra a *factor*), `d_F a = d_F a' ↔ a−a' ∈ range d_gauge`: the field-strength record `F=dA`
  is a **complete** invariant of the physical (gauge) configuration. The honest §0/P9 caveat made precise —
  the boundary-flux center exists *only* when the cohomology (closed-mod-exact) is nontrivial. Wired into
  `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **P1: the transverse helicity-±1 one-particle space (2 physical polarizations)**
  (`QIQTH/Fock/Photon/PhotonHelicity.lean`, axiom-free standard-3, budget 0, 2943 jobs green). The photon is
  massless spin-1 with exactly 2 helicities ±1; model `h_γ = h_{+1}⊕h_{−1}`.
  **`photon_helicity_finrank`**: `dim h_γ = dim h_+ + dim h_−`. **`photon_two_polarizations`**: `dim(ℂ×ℂ)=2`
  — exactly **2 transverse polarizations per momentum** (vs the 4 components of `A_μ`, the extra 2 being the
  unphysical gauge/longitudinal modes excluded by working on the positive physical space).
  **`photon_capacity_helicity`**: `dim Γ_s^{≤N}(h_γ) = C(dim h_+ + dim h_− + N, N)` — the cutoff bosonic
  capacity (P2/P3) counts the 2 polarizations. Wired into `QIQTH.lean`+`AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **P1/P3: the 2-polarization capacity, explicit** (`PhotonHelicity.lean`, axiom-free
  standard-3, budget 0, 2943 jobs green). **`photon_capacity_two_helicity`**: for `d` modes per helicity the
  photon capacity is `C(2d+N, N)` (the two transverse polarizations doubling the mode count, parity-symmetric
  `d_{+1}=d_{−1}=d`). **`photon_capacity_helicity_ge`**: `truncFockDim d N ≤ truncFockDim (2d) N` — the second
  polarization enlarges the capacity (the photon carries more information than a single-component scalar-like
  field of the same per-helicity mode count). Wired into `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **P4: the Bose occupation decreases with mode energy** (`PhotonUnruh.lean`, axiom-free
  standard-3, budget 0, 2180 jobs green). **`boseEinstein_le_of_le`**: for `0<βω₁≤βω₂`, `n(βω₂) ≤ n(βω₁)` —
  higher-energy photon modes are thermally less occupied (`1/(e^{βω}−1)` antitone in `βω`). The expected
  monotone falloff of the thermal/Unruh photon spectrum with energy. Wired into `AxiomAudit.lean`;
  standard-3; budget 0.
- 2026-06-29 — **P4: the bosonic enhancement factor `1 + n = e^{βω}·n`** (`boseEinstein_one_add`, in
  `PhotonUnruh.lean`, axiom-free standard-3, budget 0, 2180 jobs green). The `(n+1)` of bosonic emission
  (spontaneous `1` + stimulated `n`) equals `e^{βω}` times the occupation — the multiplicative CCR/KMS
  balance, and the source of the Bose–Einstein distribution. The **exact bosonic mirror of the fermionic
  depletion** `1 − n = e^{βω}·n` (`fermiDirac_one_sub`): the `+n` (stimulated) vs `−n` (Pauli) is the
  spin–statistics signature, now stated symmetrically on both sides. Wired into `AxiomAudit.lean`;
  standard-3; budget 0.
- 2026-06-29 — **P4: the bosonic Gibbs form `n = e^{−βω}/(1−e^{−βω})`** (`boseEinstein_gibbs_form`, in
  `PhotonUnruh.lean`, axiom-free standard-3, budget 0, 2180 jobs green). The Bose occupation is the **mean
  of the geometric (Bose) distribution** `p_k=(1−x)x^k` over number states `k=0,1,2,…`, Boltzmann factor
  `x=e^{−βω}`, single-mode partition function `Z=1/(1−x)`, `n=x·Z`. The bosonic `1−x` denominator vs the
  fermionic `1+x` (`n=x/(1+x)`) is the geometric-vs-two-level spin–statistics signature — the bosonic
  partition picture mirroring the electron's (fermionic 2-state). Wired into `AxiomAudit.lean`; standard-3;
  budget 0.
- 2026-06-29 — **P4: the Unruh photon occupation in Gibbs form** (`rindlerOccupationBose_gibbs_form`, in
  `PhotonUnruh.lean`, axiom-free standard-3, budget 0, 2180 jobs green). At `β=2π`,
  `n_ω = e^{−2πω}/(1−e^{−2πω})`: the Rindler/Unruh photon occupation at the Bisognano–Wichmann temperature
  is the mean of the geometric (Bose) distribution with Boltzmann factor `e^{−2πω}` — the `β=2π`
  specialization of `boseEinstein_gibbs_form`. Wired into `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **P4: the bosonic partition function is `n+1`** (`boseEinstein_add_one_mul`, in
  `PhotonUnruh.lean`, axiom-free standard-3, budget 0, 2180 jobs green). `(n+1)(1−e^{−βω}) = 1`, i.e.
  `n+1 = 1/(1−e^{−βω}) = Z_bose = ∑_k e^{−βωk}` (the geometric-series sum over number states): the `(n+1)`
  enhancement factor IS the single-mode bosonic partition function. Contrast `Z_fermi = 1+e^{−βω}` (two-level):
  geometric `1/(1−x)` vs two-level `1+x` is the spin–statistics signature at the partition level. Wired into
  `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **P4: the bosonic thermal entropy is non-negative `S_BE(n) ≥ 0`** (`boseEntropy_nonneg`, in
  `PhotonUnruh.lean`, axiom-free standard-3, budget 0, 2180 jobs green). The photon mode entropy
  `(1+n)log(1+n) − n log n = log(1+n) + n·log((1+n)/n)` is a sum of two non-negative terms (`log(1+n) ≥ 0`
  since `1+n ≥ 1`; `n·log((1+n)/n) ≥ 0` since `(1+n)/n ≥ 1`) — the thermal/Unruh photon entropy is a genuine
  (non-negative) entropy. Wired into `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **P1: the photon helicity operator (spin-1, helicity ±1)** (`PhotonHelicity.lean`, axiom-free
  standard-3, budget 0, 2943 jobs green). **`helicityOp`** = `(+1 on h_{+1}, −1 on h_{−1})`, the spin
  projection along the momentum; **`helicityOp_sq`**: `Λ² = 1` (eigenvalues `±1`) — the photon is massless
  spin-1 with exactly two helicities `±1` (never the longitudinal `0` of a *massive* vector). Pins the
  spin-1/2-polarization structure at the operator level. Wired into `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **P1: the two polarizations resolve the identity `P_{+1} + P_{−1} = 1`** (`PhotonHelicity.lean`,
  axiom-free standard-3, budget 0, 2943 jobs green). **`helicityProjPlus`/`helicityProjMinus`** (the `Λ=±1`
  eigen-projections onto `h_{+1}`/`h_{−1}`); **`helicityProj_complete`**: `P_{+1} + P_{−1} = 1` — the two
  transverse helicity projections sum to the identity (the photon's **two physical polarizations form a
  complete set**, no third longitudinal mode); **`helicityProjPlus_idem`**: `P_{+1}²=P_{+1}` (a genuine
  projection). Wired into `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **P1: the spectral decomposition of the helicity** (`PhotonHelicity.lean`, axiom-free
  standard-3, budget 0, 2943 jobs green). **`helicityOp_eq_proj`**: `Λ = P_{+1} − P_{−1}`
  (`= (+1)P_{+1}+(−1)P_{−1}`), the eigen-decomposition of the photon helicity. **`helicityProj_orthogonal`**:
  `P_{+1}·P_{−1} = 0` — the `±1` sectors are orthogonal (a photon has a *definite* helicity); so with
  completeness + idempotence the `P_{±1}` form a **complete orthogonal system of projections**. Wired into
  `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **P1: the helicity eigenvalues `±1`, concrete** (`PhotonHelicity.lean`, axiom-free standard-3,
  budget 0, 2943 jobs green). **`helicityOp_plus`**: `Λ(x,0)=(x,0)` (a positive-helicity photon is a `Λ=+1`
  eigenvector); **`helicityOp_minus`**: `Λ(0,y)=(0,−y)` (a negative-helicity photon is a `Λ=−1`
  eigenvector). The two eigenvalues `±1` are the photon's two transverse helicities, exhibited on concrete
  eigenvectors. Wired into `AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **★ P10 FOOTHOLD: abstract BRST cohomology `H_Q = ker Q ⧸ im Q`** (new module
  `PhotonBRST.lean`, axiom-free standard-3, budget 0, 1162 jobs green; GPT-5.5-pro-identified). The covariant
  (Gupta–Bleuler/BRST) photon handles the gauge redundancy + unphysical modes via a nilpotent BRST charge
  `Q` (`Q²=0`); the physical states are the BRST cohomology. **`BRST.exact_le_closed`**: `im Q ⊆ ker Q`
  (every exact/BRST-trivial state is closed/BRST-invariant). **`BRST.cohomology = ker Q ⧸ im Q`** (the
  physical photon states — the 2 transverse polarizations, unphysical longitudinal/temporal/ghost modes
  quotiented out). **`BRST.cohomology_trivial_iff`** (trivial `H_Q` ⟺ every closed is exact). The
  single-nilpotent (BRST) cohomology, complementing the de Rham `F=dA` cohomology. (HONEST: the
  indefinite-metric Krein space + metric descent to a *positive* form + no-ghost theorem are the deferred
  continuum P10 frontier.) Wired into `QIQTH.lean`+`AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **P10: BRST-invariant observables descend to the physical (cohomology) states** (extended
  `PhotonBRST.lean`, axiom-free standard-3, budget 0, 1162 jobs green). A BRST-invariant observable `O`
  (`[O,Q]=0`, i.e. `O∘Q=Q∘O`) preserves both physical submodules: **`BRST.closed_mem_of_comm`** (`O` maps
  `ker Q → ker Q`: `Q(Ov)=O(Qv)=0`, a physical/BRST-closed state stays physical) and
  **`BRST.exact_mem_of_comm`** (`O` maps `im Q → im Q`: `O(Qx)=Q(Ox)`, a BRST-trivial state stays trivial).
  Together they say a BRST-invariant observable **descends to a well-defined operator on the cohomology
  `H_Q`** — the physical (gauge-invariant) photon observables act on the physical photon states (the §0/P6
  "records = gauge-invariant observables" decision realized at the cohomology level). Wired into
  `QIQTH.lean`+`AxiomAudit.lean`; standard-3; budget 0.
- 2026-06-29 — **P10: the induced operator on the cohomology — CONSTRUCTED (not asserted)** (extended
  `PhotonBRST.lean`, axiom-free standard-3, budget 0, 1162 jobs green). The previous increment proved a
  BRST-invariant `O` *preserves* `ker Q` and `im Q`; this **builds** the descended map.
  **`BRST.closedRestrict`**: `O` restricted to the closed states `ker Q` it preserves (a genuine
  `closed Q →ₗ closed Q`). **`BRST.inducedCohomologyMap`**: via `Submodule.mapQ`, the well-defined induced
  operator **`H_Q →ₗ H_Q`** on the BRST cohomology — using that `closedRestrict` maps `im Q → im Q`
  (`Q(Ov)=O(Qv)`). So a gauge-invariant photon observable genuinely **acts on the space of physical
  (cohomology) photon states** — the constructed operator, completing the "descends to a well-defined
  operator on `H_Q`" claim of the prior increment. Wired into `QIQTH.lean`+`AxiomAudit.lean`; standard-3;
  budget 0. **★ This exhausts the tractable P10 algebraic footholds** (BRST cohomology + observable descent
  + induced cohomology operator); the remaining P10 is the genuinely-blocked continuum frontier
  (Gupta–Bleuler/BRST indefinite-metric Krein space + positive-form descent + no-ghost theorem; Maxwell
  `F`-net CCR from test 2-forms; Gauss-law boundary algebra + Kabat contact determinant; interacting QED).
