# Bell-Theorem Stance — No Superdeterminism

**Commitment:** QIQT-H **preserves Statistical Independence**. Hidden variables (if posited at all) are not correlated with experimenters' measurement settings. The framework rejects superdeterminism as an explanatory mechanism.

## Position in one paragraph

QIQT-H is a **no-hidden-variable, no-superdeterminism, objective-single-outcome** framework. Within a coherence patch, dynamics are exactly unitary quantum mechanics (axiom A4); Bell inequalities are violated within the patch by ordinary quantum nonlocality, inherited from QM without modification. At capacity saturation, the informational projection `P_Q` selects a single outcome consistent with the in-patch nonlocal correlations. The patch boundary — not any superdeterministic conspiracy — is what reconciles unitary evolution with single-outcome experience.

## What this commits the paper to

| Claim | Status in QIQT-H |
|---|---|
| Locality (no-signaling) | Holds (inherited from QM). |
| Bell-CHSH violations occur in entangled systems | Yes — within each coherence patch, QIQT-H = QM. |
| Hidden variables that determine outcomes | **None.** `Q_R` is a structural bound on coherent information capacity, not a hidden state variable. |
| Statistical Independence of hidden variables and settings | **Preserved.** No correlation between any `Q_R`-related quantities and experimenter choices. |
| Measurement settings can be freely chosen | Yes — assumed (`free choice`). |
| Bell's theorem applies | Yes — and QIQT-H accepts its standard conclusion: local realism is false. |
| Objective single outcomes occur | Yes — via `P_Q` at patch boundary. |

## Why this is different from each rival

### Versus Palmer (RaQM / IST)
Palmer evades Bell by violating Statistical Independence (formally superdeterministic). The mechanism is the "Impossible Triangle Corollary" to Niven's Theorem: certain joint counterfactual measurement bases are mathematically excluded by rationality constraints, so the bases needed to *state* Bell's inequality with full generality don't exist.

QIQT-H rejects this route. Statistical Independence holds. Bell's theorem applies in its standard form. QIQT-H accepts that local realism is false and moves on; the question shifts from "how does QIQT-H evade Bell?" to "how does QIQT-H produce a single outcome compatible with QM's already-Bell-violating predictions?" Answer: `P_Q`.

### Versus CSL / GRW / Diósi-Penrose
Same Bell stance (Statistical Independence preserved, single outcomes), but different mechanism. CSL/GRW add stochastic noise *inside* the patch — modifying Schrödinger dynamics — to produce gradual collapse. QIQT-H leaves Schrödinger dynamics intact within the patch (axiom A4); the single outcome is produced *at* the patch boundary via informational saturation, not by continuous noise.

This is a real difference. CSL has constrained empirical signatures (rotational decoherence of LISA-Pathfinder-style test masses, X-ray emission); QIQT-H has *no in-patch decoherence above environmental*, because there's no stochastic noise term. The QIQT-H signature is different: it appears as coherence cutoffs for systems whose effective Hilbert dimension approaches the local `Q_R`.

### Versus Many-Worlds
MWI denies single outcomes occur; all branches are real. QIQT-H asserts a single outcome occurs (`P_Q` produces one). They are *contradictory* on the central metaphysical question. Bell stance differs too: in MWI there is no Bell-violation to explain because no probabilities are fundamental.

### Versus 't Hooft CA
'tHooft is superdeterministic. QIQT-H is not. Architecturally distinct.

### Versus QBism / Relational QM
QBism / RQM make collapse epistemic. QIQT-H makes it objective and physical. Bell stance similar in form (no hidden variables, Statistical Independence preserved) but interpretation differs.

## A new prediction this stance permits

Because QIQT-H does **not** add stochastic noise to Schrödinger evolution, it must produce *less* in-patch decoherence than CSL for the same external conditions. This is a comparative prediction: any experiment that tightens CSL bounds *does not directly constrain QIQT-H*. QIQT-H is only constrained where the effective dimension of the experimental system approaches its local `Q_R`.

This is also a vulnerability: if a future experiment forces stochastic-noise behavior at a level CSL predicts but QIQT-H rejects, QIQT-H is in trouble. Worth flagging.

## What the paper must explicitly state

1. **"QIQT-H preserves Statistical Independence and free choice."** Single sentence in the introduction, single sentence in the comparison section. Reviewers reading quickly for the Bell-stance need to find it without searching.
2. **"Bell-CHSH violations within a coherence patch are inherited from QM; QIQT-H does not modify them."** Removes the ambiguity that some readers will assume from "objective collapse"-flavored theories.
3. **"P_Q does not act at spacelike separation; it acts at the boundary of a coherence patch determined by the local Q_R."** This forestalls "doesn't this require nonlocal collapse?" objections.

## Subtleties for the comparison section

- The "patch" needs a clean technical definition. Candidate: a region `R` whose joint quantum state has `d_eff ≤ 2^{Q_R}` and is dynamically isolated (no entanglement growth across `∂R` faster than `Q_R` permits).
- For entangled pairs separated across two patches, the joint state straddles both. The `P_Q` projection on one patch may select an outcome that constrains the other patch's later outcome via the joint state. This is *not* spooky action — it is the same correlation structure that ordinary QM uses.
- Patches are not fixed regions of spacetime; they are dynamically defined by the system's interactions and the local `Q_R`. A measurement event creates a patch boundary.

## Acknowledged weaknesses

- **The patch concept needs more formal development.** Currently informal.
- **What happens for two patches that try to merge?** I.e., when two previously isolated systems come into contact. The joint patch has its own `Q_R`; if the sum of pre-merger entropies exceeds it, what happens? Plausible answer: forced `P_Q` projection of the joint state. Needs explicit treatment.
- **Free choice is assumed, not derived.** Standard for all non-superdeterministic interpretations.
