# D4 — Fork A distinctiveness audit: what is QIQT-H's irreducible claim?

**Date:** 2026-06-30. **Plan:** `FINITE_MATTER_OR_ENTROPY_PLAN.md` D4. **Setting:** D1 found QIQT-H is committed
to **Fork A** (a finite *renormalized-entropy* bound over covariant Type III₁ matter); D2 proved Fork B (finite
*matter*) untenable for exact Lorentz; D3 proved Fork A's capacity is genuinely an *entropy* bound, not a state
count. **Question (the red-team's deflation test):** on Fork A, is QIQT-H merely *"covariant QFT + the holographic
entropy bound + a selection rule"*, or is there an irreducible distinctive claim?

## What QIQT-H reduces to on Fork A

Stripped to Fork A, the framework is: **standard covariant (Type III₁) QFT** + **a holographic renormalized-
*entropy* bound** `S_ren(ρ_R) ≤ A(∂R)/4ℓ_P²` + **decoherence** + a **single-world record-selection ontology
(Φ, λ)** with a **derived Born rule**. Two of these are *not* distinctive, and we must say so plainly:

- **Covariant QFT** — borrowed wholesale (the matter is unmodified, that is the whole point of Fork A).
- **The holographic entropy bound** — on Fork A this *is* essentially the covariant entropy / Bousso bound
  (`area_floor_vonNeumann`: `S_vN(ρ_R) ≤ A/4ℓ_P²`, conditional on `HolographicCapacityBound`). It is a known
  holographic principle stated in the Type II setting, **not** a new postulate unique to QIQT-H. The "finite
  *quantized information* / finite *capacity*" branding, which connotes a finite Hilbert space or discrete
  substrate, **overclaims** here: D3 shows it is a finite *entropy*, not a finite *count*; the radical-sounding
  "finite" must be reworded.

## The genuinely irreducible content (all Fork-A-safe, machine-checked where applicable)

What survives as distinctive is an **interpretation with real machine-checked content**, not a new dynamics or
substrate:

1. **Born from typicality — a *derived* Born rule.** The Zurek amplitude→count bridge `‖ψ_k‖²/‖ψ‖² =
   count/|I|` holds by orthonormality (`BornEquiprobable.born_from_equiprobability`), so the equiprobable measure
   over an equal-amplitude orthonormal fine-graining has outcome marginal *exactly* `|c_k|²`. This reduces Born
   to a **single named premise** (P5, the canonicity of that measure: envariance + refinement-additivity) — most
   interpretations *assume* Born; QIQT-H *derives* it from a typicality measure, machine-checked. **Entropy/measure
   level — fully Fork-A-safe** (no finite matter).
2. **The (Φ, λ) "one wave function, one world" ontology.** Exact global unitarity, no collapse, no Bohmian
   particles, no branching multiverse; a **non-dynamical selector λ** = the run's microscopic initial conditions
   indexing which decohered record is lived; Born as the **across-run typicality** of λ. Distinct from collapse,
   Bohm, and bare Everett. The single-outcome mechanism is **λ + decoherence, NOT capacity** (the "Macroscopic
   Definiteness" reading was retired) — so the ontology never depended on finite matter either.
3. **The algebraic reframing of the measurement problem.** Per-run vs formal wave function; regional physical
   content as the state on the Type II regional algebra; algebra-state equivalence as basis-independent regional
   indistinguishability. This is the paper's stated contribution, and it is intrinsically a Type II *entropy*-side
   construction — Fork-A-native.
4. **The area law / 1/4 ratio (`SakharovRatio`), and the conditional free-field Einstein equation.** Genuine,
   machine-checked, *entropy-level* results (the 1/4 ratio is derived; the value of `G` is not). Fork-A-safe.
   Honest caveat: these follow from the entropy bound + induced gravity; they are QIQT-H's *own* derivation but
   not unique consequences of a finite *substrate*.

## Verdict

**On Fork A, QIQT-H's irreducible distinctive claim is an *interpretation*, not a finite substrate:** a
single-world (Φ, λ) ontology with a **machine-checked Born-from-typicality derivation** and an **algebraic
regional-content reframing** of the measurement problem, layered on standard covariant QFT + the holographic
*entropy* bound + decoherence. This is a **legitimate, non-vacuous contribution** — deriving Born from a single
typicality premise and the "observer is the wave function" ontology are real and unusual — but it must be branded
honestly:

> **"Finite capacity" / "finite quantized information" should be restated as "finite holographic *entropy* over
> covariant matter."** QIQT-H is a **typicality-based single-world interpretation with a holographic entropy
> bound**, NOT a finite-matter / discrete-Hilbert-space theory. The radical "finite information substrate" reading
> is dropped (Fork B, dead — D2); the "QI" finiteness is the entropy bound (D3).

What this is **not**, and must not be sold as: a finite matter Hilbert space; a new UV-complete dynamics; a
discrete substrate; or a mechanism whereby finiteness *forces* single outcomes (that is λ + decoherence). The
genuine open problems are unchanged and are *interpretational/measure-theoretic*, not substrate-theoretic: **λ's
dynamical, Lorentz-covariant law** and the **canonicity of the P5 typicality measure**.

**Hand-off to D5:** the resolution + adversarial re-check + a punch-list to align the papers/site/memory with
"finite *entropy*, not finite *matter*." Never claim QG or the value of `G`; the `1/4` ratio is derived
(`SakharovRatio.lean`).
