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
