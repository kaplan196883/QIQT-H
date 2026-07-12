# The flat-space record-code/gravity correspondence (the conjecture)

**Lean mirror:** `lean/mathlib/QIQTH/Conjectures.lean` (`QIQTH.Conjectures` — a named `Prop`
package: NO proof field for the continuum claim, NO axiom, NO typeclass instance). Stated
2026-07-03 at the close of THE DYNAMICS campaign (DY1–DY7).

## The statement (mirrored verbatim from the Lean docstring)

> In the continuum limit, the capacity-bounded record code with diagonal dynamics equals free
> QFT + linearized gravity on the emergent geometry: for every region, the microscopic continuum
> record entropy equals the one-loop conical (heat-kernel) entropy, equals area/4G_ind, with
> G_ind the Sakharov-induced Newton constant of the SAME field content.

Formally (`FlatSpaceRecordGravityCorrespondence`): for every region R,
`microContinuumEntropy R = oneLoopConicalEntropy R = area R / (4·G_ind)`, with
`G_ind = sakharovInducedNewtonConstant` — ONE microscopic system computing both the states and G
(the independent cross-check the finite level cannot supply; the difference between a
correspondence and a theory, per the AdS/CFT comparison).

## The finite evidence (PROVEN, `finiteEvidence_holds`, axiom-free std-3)

1. Records are stationary under the code dynamics (`alpha_recordProj`).
2. The ladders rotate at their mode frequencies (`alpha_modeLowering`).
3. The Gibbs state satisfies the finite KMS condition, with its modular flow provably the rescaled
   physical flow (`gibbs_kms_condition`, `sigmaDiag_gibbs_eq_alpha_rescale`).
4. The region Gibbs entropy is the mode-entropy sum (`entropy_gibbs_region`).
5. The saturated conditional Sakharov cross-check, calibration-free
   (`S_micro_zero_eq_inducedQuarterG`).

## The honest boundary (the DY7 checkpoint sentences, verbatim)

HAVE: "a finite, axiom-free diagonal code dynamics, explicit Gibbs/KMS states, product-mode
reductions, and a saturated conditional induced-gravity cross-check whose proof does not use the
trace/wEnt area calibration."

HAVE NOT: "a finite proof of a continuum one-loop heat-kernel area law or an equality between
finite thermal entropy at arbitrary β and an induced geometric area; that remains the named
continuum frontier/conjecture."

⚠ NOT quantum gravity solved; no wall crossed. The conjecture is stated, not assumed.

## THE FIRST CONTINUUM RUNG — LANDED (2026-07-12, `7393d3af`, `ContinuumEntropy.lean`)
The conjecture's first two terms (micro record entropy = one-loop continuum entropy) now touch at
their simplest genuine contact point, axiom-free: the finite record-region entropy (DY5 mode sums,
whose per-mode D → ∞ limit is the DS3 Planck kernel — `tendsto_thermalEntropy_sInf`, a genuine
tendsto to THIS kernel) converges along refining mode families to the EXACT continuum value
`∫₀^∞ s_∞(βω) dω = π²/(3β)` (`record_entropy_continuum_limit`), the standard c = 1 massless-boson
thermal entropy (density π/(3β) per unit length with the Δω = π/L spacing). The Bose integral
`∫₀^∞ s_∞ = π²/3` is derived from scratch (geometric + log series, Tonelli, Basel — no
dilogarithms), and the Riemann-sum convergence theorem was also proved from scratch — both absent
from Mathlib. HONEST: the positive-temperature limit ONLY — no conical/heat-kernel leg, no induced
G, no β → 0 saturation, the D → ∞/mode-density limit interchange not addressed, 1D massless; the
next named rung (per the design consult) = the heat-kernel representation of the same 1D
thermodynamics, then the conical/induced-gravity leg.

## THE SECOND CONTINUUM RUNG — LANDED (2026-07-12, `04c22cb2`, `HeatKernelThermal.lean`)
The conjecture's "one-loop continuum entropy" leg is no longer prose: the winding-subtracted
one-loop heat-kernel sum on the thermal cylinder S¹_β × ℝ (the image sum over windings of the
DERIVED flat kernel (4πt)^{−1/2}) evaluates EXACTLY to π/(6β) (`heat_logZ_density`), agrees with
the canonical Bose free energy (`windings_eq_canonical` — one object, two descriptions), and its
thermodynamic entropy π/(3β) IS the DOS-weighted D3a record entropy
(`record_entropy_has_heat_kernel_form`). The guard `naive_winding_diverges` machine-checks that
the Euclidean-time trace factor is load-bearing. HONEST: the SMOOTH cylinder only — the CONE
(Sommerfeld, conical coefficients, UV control, renormalized G) is the cited next rung; the m = 0
vacuum winding removed by construction; no induced-G, no β → 0 saturation, no limit interchange.

## THE THIRD CONTINUUM RUNG — LANDED (2026-07-12, `a1d3a65e`, `ConicalHeatKernel.lean`)
The conical leg of the conjecture's one-loop entropy is now machine-checked at the integer-cone
level, via the ℤ_n orbifold image method (no Sommerfeld): the non-area heat-trace excess of the
cone C_{2π/n} = ℝ²/ℤ_n is EXACTLY (1/12)(n − 1/n), t-INDEPENDENT (`zmodConeExcess_eq_standard`),
and its replica interpolation `coneCoeff` has derivative 1/6 at the smooth point
(`hasDerivAt_coneCoeff_one` — the c/6 entanglement coefficient, c = 1). The arithmetic core, the
cosecant sum Σ csc²(πk/n) = (n²−1)/3, is a Mathlib-first. HONEST: integer cones only; the n → 1
analytic continuation, the general-angle Sommerfeld kernel, the one-loop determinant + UV
regularization, and the A/4G coupling all CITED — the last is the D3d rung (design recorded, the
Susskind–Uglum counterterm identity).

## THE FOURTH RUNG (A/4G COUPLING) — LANDED (2026-07-12, `0aa98ee3`, `ConicalSakharov.lean`)
The conical coefficient now couples to Newton's constant: the exact algebraic Susskind–Uglum
content is machine-checked — the divergent one-loop entanglement entropy S_ent = (A/4)·δ(1/G)
equals the area times the induced-1/G counterterm (`ent_eq_area_quarter_dInvG`), so entanglement
entropy IS the counterterm renormalizing 1/G (`bare_entropy_renormalizes`), and the induced-only
reading gives 4·G_ind·S_ent = A cutoff-INDEPENDENTLY (`induced_product`, holds at every finite
cutoff, ε → 0 never taken). The D=4 specialization reproduces the held Sakharov ratio
1/48π = (1/4)(1/12π) (`sakharov_ratio_join`, formal re-export); D=2 gives the c/6 log. Both joins
(D3c's 1/6, the held Sakharov ratio) are FORMAL imports. HONEST: a REGULATED counterterm identity
with the cutoff carried explicit — CITED: the Gaussian determinant, the replica identity, the
n → 1 continuation, a₁ = R/6, the SAME-regulator physical assumption. The conjecture's
'micro entropy = A/4G_ind' now has its exact one-loop-counterterm SKELETON machine-checked;
the full `FlatSpaceRecordGravityCorrespondence` Prop (with those cited physical inputs discharged)
remains open.

## THE FIFTH / FINAL RUNG (SATURATION BRIDGE) — LANDED (2026-07-12, `22bbd7b2`, `SaturationBridge.lean`)
The β→0 corner and the non-commuting-limit diagram are machine-checked: the core bridge
`tendsto_sInf_add_log` proves s_∞(x) = −log x + 1 + o(1) (the continuum per-mode entropy's exact
log-divergence), `sInf_logCutoff_bridge` matches it to the finite saturated log D (D_eff·x → C ⟹
offset 1 − log C), and the three-regime theorem + `saturation_diagram_noncommuting` guard prove the
(D→∞, β→0) limits DON'T commute — the finite A/4G saturation (log D) and the continuum thermal
entropy (−log x + 1) are the two order-of-limits corners of one double sequence, quantitatively
linked. HONEST: a matching of DIVERGENCES; the cutoff identification D_eff ~ 1/x is a modeling
choice, not derived.

## THE D3 LADDER — COMPLETE (2026-07-12). THE CONJECTURE'S SKELETON IS MACHINE-CHECKED TERM BY TERM.
- D3a `7393d3af` — micro record entropy = the exact continuum thermal entropy π²/(3β) (Bose
  integral + Riemann-sum theorem, both Mathlib-firsts).
- D3b `04c22cb2` — the one-loop leg's heat-kernel (winding proper-time) form, = the canonical Bose
  free energy (one object, two descriptions).
- D3c `a1d3a65e` — the exact conical excess (1/12)(n−1/n), t-independent, + the c/6 replica
  coefficient (cosecant sum a Mathlib-first).
- D3d `0aa98ee3` — the Susskind–Uglum counterterm S_ent = (A/4)δ(1/G): entanglement entropy
  renormalizes 1/G; 4·G_ind·S_ent = A cutoff-independent; the D=4 join to the held Sakharov ratio.
- D3e/f `22bbd7b2` — the saturation bridge + the non-commuting-limit diagram.
**WHAT REMAINS for the full `FlatSpaceRecordGravityCorrespondence` Prop:** discharging the CITED
physical inputs — the Gaussian one-loop determinant log Z = ½∫(dt/t)Tr K, the replica analytic
continuation n → 1, the curved-space heat-kernel coefficient a₁ = R/6, the SAME-regulator physical
assumption, and the cutoff/temperature-frequency identification D_eff ~ 1/x. Each is a standard-QFT
input; none is a QIQT-H-specific gap. The skeleton is proved; the Prop awaits those inputs.
