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
