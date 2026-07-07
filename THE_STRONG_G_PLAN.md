# THE STRONG-G PLAN — derive the entropy AREA LAW (the load-bearing assumption behind `1/G = N·Λ_s²`)

**Status:** SCOPED (GPT-5.5-pro consult, high, 2026-07-07; survey-grounded). **Track:** QG / induced-G. **Commits LOCAL ONLY (no push).**

## Binding verdict (GPT-5.5-pro)
The QIQT-H G-derivation is already the exact axiom-free Sakharov/Dvali relation `1/G = N·Λ_s²` (G as OUTPUT;
`inducedG_delivers`), with the genuinely-derived core = the dimensionless `G/a₀²=1/N`, the circularity-clean `1/4`
ratio (`sakharov_ratio`), and the FORCED regulator power form (`regulator_forced_power`, κ=2 an output). The remaining
free/cited inputs are: `Λ_s` (the one unavoidable dimensionful scale — a genuine postulate, cannot be made from a count),
the species `c_i` (cited Seeley–DeWitt data), `κ=1/6` (curved-heat-kernel wall = the checkpointed `ContDiff³ exp_p`
frontier), and — the SINGLE biggest strengthening available — the **entropy AREA-LAW scaling `S ∝ A`**, currently CARRIED.
"`1/G = N Λ²` is an AREA law ONLY because `S ∝ A`." The whole holographic-capacity claim `Q_R = A/4ℓ_P²` rests on it.

**The strongest TRACTABLE increment = `BoundaryGaussianAreaLaw`**: a finite, axiom-free theorem proving `S ∝ A` for an
explicit boundary-local Gaussian capacity model, + a volume-law guard. This turns "ASSUME `S∝A`" into "PROVE `S∝A` for an
explicit boundary-local Gaussian model; ASSUME the physical holographic vacuum is described by / flows to that model" —
a real, bounded strengthening that sharply isolates the one remaining physical postulate.

**NOT the target (GPT-5.5-pro, honest):** full Srednicki (free scalar in a ball, radial discretization, Williamson
spectrum, asymptotic `S ∼ c·A/a²`) is a longer research program, NOT a few-week Lean increment — Mathlib lacks Williamson
normal form / symplectic eigenvalues / Autonne–Takagi / Bloch–Messiah / Gaussian-state covariance entropy (weeks–months to
build), and "nearest-neighbour coupling ⟹ only boundary modes entangle" is FALSE without gap/correlation-decay hypotheses
(Lieb–Robinson / Hastings — also not bounded). Do the boundary-channel theorem, NOT full Srednicki.

## Current G-spine (survey, all [AF] std-3, budget 0) — what we build ON
`InducedNewtonConstant.lean` (`inducedG`, `inducedG_delivers`, `inducedG_ratio_is_pure_number`,
`capacity_exponent_in_primitives`, `inducedInvG`, `effSpeciesN`), `SakharovRatio.lean` (`sakharov_ratio`,
`geometric_quarter`), `SpeciesCrossCheck.lean` (`species_sakharov_ratio`, `speciesEntropy_eq_capacity`),
`Rigidity/RegulatorRigidity.lean` (`regulator_forced_power`, `dyadic_covariance_insufficient` vacuity guard),
`GaussianStateEntropy.lean` (per-mode Srednicki entropy, single-mode symplectic invariance — the n=1 SEED of the area law).

## The plan (6 sequenced axiom-free green checkpoints; new file `QIQTH/BoundaryGaussianAreaLaw.lean`)

- [ ] **SG1 — bosonic normal-mode entropy** (~2–5 days). Define
  `bosonModeEntropy (ν) := ((ν+1)/2)·log((ν+1)/2) − ((ν−1)/2)·log((ν−1)/2)`. Prove: for `0<q<1`, the geometric thermal
  law `p n = (1−q)·q^n` has `−∑' n, p n·log(p n) = −log(1−q) − (q/(1−q))·log q`, and with `ν=(1+q)/(1−q)`,
  `geomEntropy q = bosonModeEntropy ν`. Mathlib: `Real.log`, geometric `tsum` (`tsum_geometric_of_lt_one`), `Summable`,
  `ring_nf`/`field_simp`/`positivity`/`nlinarith`. Likely small gap: `∑' n, n·q^n = q/(1−q)²` (prove from finite geometric
  sums / `tsum` derivative if absent). Fallback: define `bosonModeEntropy` + postpone the `tsum` identity.
- [x] **SG2/SG3/SG5 — DONE 2026-07-07** (`QIQTH/BoundaryGaussianAreaLaw.lean`, commit eec26a2; [AF] std-3, budget 0):
  `card_cubeBoundary` (=6L²), `latticeArea`, `sum_odd_eq_sq`; **`boundary_entropy_area_law`** = the axiom-free `S∝A`
  (`boundaryEntropy = (A/a₀²)·gaussStateEntropy ν₀`, reusing the Srednicki per-mode entropy); `boundary_entropy_factorizes`;
  and the VOLUME-LAW GUARD **`bulk_entropy_volume_law`** (`= L³·gaussStateEntropy`, contrast 6L² ⟹ boundary-locality is
  load-bearing). **The carried assumption `S∝A` is now a THEOREM for this explicit boundary-local model.**
- [x] **SG6 — DONE 2026-07-07** (same file, commit pending; [AF] std-3): **`boundary_entropy_eq_area_over_4G`** — the
  conditional Bekenstein–Hawking bridge `S = A/(4·G)` for the induced `G = 1/(N_eff Λ_s²)` (`QIQTH.InducedG.inducedG`),
  GIVEN `a₀=1/Λ_s` and the calibration `gaussStateEntropy ν₀ = N_eff/4` (an explicit HYPOTHESIS `hcal` — the
  boundary-channel↔species matching, the remaining postulate, NOT derived). Connects the area law to the actual G layer.
- [ ] **SG2 — (superseded by the DONE entry above) boundary plaquette combinatorics** — `CubeBoundary L := Fin 6 × Fin L × Fin L`;
  `Fintype.card = 6·L²` (`Fintype.card_prod`, `Fintype.card_fin`); lattice area `A := (card boundary : ℝ)·a₀²`. Bonus
  angular-degeneracy identity `∑ l in range (L+1), (2l+1) = (L+1)²`. Mathlib: `Fintype.card_prod`, `Finset.sum_range`,
  `omega`/`ring_nf`.
- [ ] **SG3 — the boundary-channel AREA-LAW theorem (the CORE)** (~1–3 days).
  `boundaryEntropy := ∑ b:Boundary, ∑ i:Species, (mult i : ℝ)·bosonModeEntropy (ν i)`. Prove
  `boundary_entropy_factorizes : boundaryEntropy = (card Boundary : ℝ)·∑ i, (mult i)·bosonModeEntropy (ν i)` (ν
  boundary-independent), hence with `A = card Boundary·a₀²`,
  `boundary_entropy_area_law : boundaryEntropy = (A/a₀²)·∑ i, (mult i)·bosonModeEntropy (ν i)` — **the axiom-free `S∝A`**.
- [ ] **SG4 — (optional) explicit two-mode Gaussian block** (~2–7 days). The two-mode squeezed covariance
  `V(r) = [[c,0,s,0],[0,c,0,−s],[s,0,c,0],[0,−s,0,c]]`, `c=cosh 2r`, `s=sinh 2r`; reduced one-mode cov `= c·I₂`, one-mode
  symplectic eigenvalue `symplEig1 V := √(det V) = cosh 2r` (`twoMode_reduced_symplEig`). Makes "Gaussian" concrete WITHOUT
  full Williamson. Mathlib: `Matrix.det`, `Real.cosh`/`sinh`, `cosh²−sinh²=1`. Skippable if it bogs down.
- [ ] **SG5 — volume-law GUARD (vacuity check, mirrors the regulator guard)** (~0.5–2 days). `bulkEntropy := (card bulk :
  ℝ)·s_mode`, cubic bulk `card = L³`, `bulk_product_entropy_volume_law : bulkEntropy = (L^3 : ℝ)·s_mode`. Proves finite
  Gaussian modes do NOT auto-give area law ⟹ the boundary-locality hypothesis is genuinely LOAD-BEARING.
- [ ] **SG6 — connect to the induced-G layer (conditional bridge)** (~1–2 days). Prove the calibrated conditional:
  `(1/G = N_eff·Λ_s²) → (a₀ = 1/Λ_s) → (∑ i, n_i·bosonModeEntropy(ν i) = N_eff/4) → S = A/(4·G)`, i.e. `S/A = (1/4)·(1/G)`.
  Does NOT derive the calibration `∑ n_i s(ν_i) = N_eff/4` (the boundary-channel↔species matching — the remaining
  postulate); `sakharov_ratio` already explains why once one shared coefficient controls both sides the `1/4` is forced.

## Verbatim HAVE / HAVE-NOT (after the increment)
- **HAVE:** "Machine-checked, axiom-free: boundary-local Gaussian normal modes ⟹ entropy ∝ (# boundary plaquettes) ∝ AREA;
  and bulk-local independent channels ⟹ entropy ∝ VOLUME (the guard). Plus the conditional bridge: boundary channel
  coefficient = induced species coefficient / 4 ⟹ `S = A/(4G)`, using the existing `1/G = N_eff Λ_s²`."
- **HAVE NOT (binding):** "This does NOT prove Srednicki's free-scalar vacuum area law, NOT the numerical Srednicki
  coefficient, NOT that nearest-neighbour coupling implies area law, NOT that the actual QIQT-H microscopic vacuum realizes
  the boundary-channel model, NOT `Λ_s`, NOT the cutoff value/universality, NOT the full species `c_i`, NOT κ=1/6, and NOT a
  numerical value of G. The strengthening is precise: previously 'ASSUME `S∝A`', now 'PROVE `S∝A` for an explicit
  boundary-local Gaussian model; ASSUME the physical vacuum flows to it.'"

## Mathlib gaps to AVOID (do NOT require for this increment)
Full Williamson decomposition, Autonne–Takagi/Bloch–Messiah, Fock space, trace-class density operators, von Neumann
entropy as `−Tr ρ log ρ`, spherical harmonics, radial lattice spectral asymptotics, Lieb–Robinson/Hastings, `ContDiff³
exp_p`. Live in: finite types, finite sums, real logs, geometric `tsum`, elementary matrices (SG4 only).

## Discipline (every increment)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.BoundaryGaussianAreaLaw` GREEN; every new theorem `#print axioms` = only
`propext, Classical.choice, Quot.sound`; `bash scripts/axiom_budget_check.sh` budget 0; wire into `QIQTH.lean`; AxiomAudit
pins; ONE commit per SG-step (LOCAL ONLY, no push) with the `Co-Authored-By: Claude Opus 4.8 (1M context)
<noreply@anthropic.com>` trailer; update this plan + `LEAN_RESULTS_INVENTORY.md`; check sibling jobs FIRST (git log/status,
ps for lake — website-SEO sibling job may be active); explicit git paths only (never `-A`). NO `sorry`; carried inputs
(ν_i, mult, the calibration) as HYPOTHESES/struct fields, NEVER axioms; NEVER a vacuous discharge (SG5 is the guard);
NEVER claim numerical-G, Srednicki proved, or `S∝A` for the actual vacuum — honest HAVE/HAVE-NOT.

## Progress log
- **2026-07-07 (scoped):** GPT-5.5-pro consult (high) + faithful survey of the G-spine. Ranked the free inputs by
  value×tractability: BoundaryGaussianAreaLaw (top), scalar `c_i` from carried a₁ (high), κ=1/6 (medium, blocked),
  full Srednicki (highest value, low bounded tractability), Weyl/vector `c_i` (low), `Λ_s` (postulate). Chose the
  boundary-channel area law as the strongest bounded strengthening.
