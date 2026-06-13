# 54 — QIQT-H as a constraint-set on holographic dynamics (2026-06-14)

QIQT-H is kinematic, not a dynamics — but it can be read as a set of **consistency conditions** any
holographic quantum-gravity dynamics must satisfy to realize a single-world, no-collapse, Born-correct
universe. This is arguably the most honest *positive* framing of the program: not "here is the dynamics" but
"here is the specification a candidate dynamics must meet." Several items are machine-checked, which is
unusual for boundary-conditions-on-QG. (Authority order used throughout: Lean > papers > pro; pro is a checked
input.)

## The constraints

**Distinctive (where QIQT-H actually says something a generic QG doesn't):**

- **C1 — Area-law records as fundamental.** Per causal diamond, the number of distinguishable records scales
  as `e^{A/4ℓ_P²}` (area, not volume). Excludes volume-scaling local-cutoff theories (naive lattices/causal
  sets); forces holographic/nonlocal DOF (AdS/CFT, matrix-model class). The holographic principle is
  consensus, but QIQT-H commits to it as the organizing fundamental.
- **C2 — The single-record constraint (MDC).** The dynamics must yield one macroscopic record per region
  while (a) staying exactly unitary, (b) empirically equivalent to QM, (c) NOT relying on capacity-counting
  alone (machine-checked: `RankCountNoGo` — finite capacity does not forbid superpositions). This is the tight,
  distinctive one — and the joint-satisfiability analysis below shows it is far more constraining (and more
  demoting of capacity) than it first appears.

**Automatic (real conditions, but standard holographic QG already meets them — not new content):**

- **C3 — Born = the conserved quadratic.** The dynamics must be ordinary unitary QM at the probability level:
  the `L²` inner product as probability, no `ℓ^p`/`w^α` deviation (`RotationBorn`, meta no-go).
- **C4 — Microcausality + no-signaling.** A Haag–Kastler causal net (or holographic dual reproducing one),
  no-signaling marginals (`weyl_microcausality`, Pauli–Jordan, no-signaling theorems).
- **C5 — Finite generalized entropy / Type II.** In the observer-dressed semiclassical limit, a Type II
  algebra with finite `S_gen = A/4G + S_out` (CLPW) — i.e. black-hole thermodynamics + the GSL.
- **C6 — Covariant, foliation-free, contextual-but-no-signaling actuality.** A Poincaré-equivariant
  typicality measure with no preferred slice (OP3b), and λ contextual (not pointwise-local — Bell guardrail:
  CHSH≤2 vs Tsirelson 2√2, machine-checked). Rules out preferred-frame collapse models.

Honest meta-point: C3–C6 are the inevitable shadow of empirical equivalence — the constraints an
interpretation generates are automatically met by the theory it is equivalent to. The genuinely
QIQT-H-specific constraints are C1 and C2.

## Stress-test of C2: are {MDC + exact unitarity + empirical equivalence + not-from-capacity} jointly
## satisfiable? (consult, checked vs our no-gos + standard QM)

**Verdict: only in the weak reading — and capacity is demoted.** Two readings of the MDC:

- **Ontic/dynamical MDC** (a region physically *cannot* be in a 2-macroscopic-record superposition): **contradictory** with exact unitarity + empirical equivalence. Exact measurement linearity *forces*
  `U(α|0⟩+β|1⟩)|A₀⟩ = α|0⟩|A₀ᵣₑc⟩ + β|1⟩|A₁ᵣₑc⟩` — a global superposition of macroscopic records. Forbidding it
  requires either collapse (breaks unitarity), modified dynamics (detectable — a collapse model, largely
  excluded), or exact record-superselection (an extra postulate, not from capacity, and it changes QM's
  in-principle interference predictions). Decoherence only gives an improper mixture, not one actual record.
  And capacity-counting can't supply it (our `RankCountNoGo`). So the *strong* MDC is not viable.
- **Selection/λ MDC** (all branches present in unitary Φ; λ marks one as actual — single-world-Everett /
  Kent-style modal): **logically consistent** with all four, PROVIDED λ is Born-equivariant
  (`Pr = ‖P_r Φ‖²` — our Born=quadratic) and Bell-nonlocal/contextual (our guardrail). But then **λ, not
  `Q_max`, does the single-record work.**

**Consequence (load-bearing honesty correction):** the slogan **"finite `Q_max` removes the need for the
collapse postulate by forbidding multi-record states" is FALSE as stated.** The honest statement is: *"the
global state stays unitary and branched; an actuality/selection rule λ gives one experienced record
(Everett-like); finite capacity only bounds the number/information-content of distinguishable records."*
There is **no third reading** in which finite capacity *alone* forbids superpositions while preserving exact
unitarity and full empirical equivalence.

## What finite capacity genuinely contributes — vs what it cannot

**Can (real roles):** bound the number of distinguishable records `N ≤ e^{Q_max}`; a finite entropy bound
`S_R ≤ Q_max`; finite memory for bounded observers; a finite-trace record algebra (Type III → Type I/II,
removing the entanglement-entropy pathology); covariant/holographic accounting of boundary records; a bound
on decoherence redundancy (how many fragments encode a record); a regulator for infinite branch-labels / UV
entanglement entropy.

**Cannot:** forbid `α|R₁⟩+β|R₂⟩`; turn an improper decohered mixture into one actual outcome; derive Born by
record/capacity-counting; select a branch; make hidden-variable selection Bell-local; produce irreversible
collapse in a finite closed unitary system; remove the need for either many-worlds semantics or a λ/actuality
rule.

## Net

Read as a constraint-set, QIQT-H is a precise (partly machine-checked) specification of what a single-world,
no-collapse, holographic quantum gravity must satisfy — genuine "boundary conditions on QG." But the
stress-test sharpens the central honesty point beyond "H2 is unproven": **even granting the machinery, finite
capacity cannot be what enforces single-world; λ (an Everett-like selection rule) is. Capacity is demoted to
bounding the record structure.** Same through-line as `51`/`52`/`53`: finiteness of *information* (kinematic)
does not deliver *dynamics* (here, the dynamical enforcement of single-outcome). Propagation TODO: the
headline-thesis wording ("finite Q_max removes collapse") in the foundations paper / memory / site should be
brought into line with the selection-MDC reading.
