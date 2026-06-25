# Stage B — the QIQT-H finiteness regulator and the circularity audit

**Stage B of `SAKHAROV_KG_PLAN.md`.** Stage A derived `S_ent = A/(4 G_ind)` for the free scalar, with the `1/4`
the geometric ratio `(conical 4π)/(EH 16π)`. Stage B does two things: (i) replaces the generic UV cutoff `ε` by
**QIQT-H's finiteness regulator**, and (ii) performs the **circularity audit** — the load-bearing check that the
`1/4` is *derived*, not *smuggled in* via the regulator (which matters because P4 *literally contains* the number
`1/4`, as `η = 1/4ℓ_P²`).

## 1. The finiteness regulator

QIQT-H's distinctive content is **finiteness**: a bounded region `R` holds only finitely many distinguishable
records (`P4`), which — taken to its microscopic conclusion — deforms the field theory to a **minimal-length /
bounded-phase-space** structure with a built-in UV cutoff at the Planck scale (the framework's own
"finite lattice with a hard edge"). Concretely this *is* a physical regulator: it replaces the proper-time
cutoff `ε` by a Planck-scale cutoff,
```
   ε  →  ℓ_P  (or, equivalently, the finite-record / minimal-length scale).
```
Substituting into the Stage-A result:
```
   1/G_ind = 1/(12π ε²)  →  1/(12π ℓ_P²) ,    i.e.  G_ind ~ ℓ_P²    (the induced Newton constant IS Planckian),
   S_ent   = A/(4 G_ind)  →  A/(4 ℓ_P²)·(12π/12π) = A/(4 G_ind) ~ A/(4 ℓ_P²)     — matching P4.
```
So the finiteness regulator turns the *divergent* `ε^{-2}` into a *finite* Planck-scale number, and the
entanglement entropy becomes the holographic `A/4ℓ_P²` — exactly P4's form.

## 2. The `1/4` is regulator-independent

Crucially, **the `1/4` does not change** under the regulator substitution. It cannot: the `1/4` is the geometric
ratio `(conical-deficit 4π)/(EH 16π)`, which involves *no* cutoff and *no* matter coefficient. Every regulator
(generic `ε`, minimal-length lattice, finite-record count) gives the *same* `1/4`; what the regulator fixes is
only the *value* of `G_ind` (the Planck scale), via the heat-kernel coefficient. This is the same universality
that makes the Bekenstein–Hawking `1/4` species-independent: **regulator and matter set `G`; geometry sets the
`1/4`.**

## 3. The circularity audit (the load-bearing part)

**The danger.** P4 states `η·A = log|R|` with `η = 1/4ℓ_P²` — so P4 *already contains the number `1/4`*. If the
Sakharov derivation secretly *used* that `1/4` (e.g. via the regulator), then "deriving `1/4`" would be empty —
a circle. The audit proves it does not.

**What the derivation actually uses (trace the inputs):**

| input | supplies | contains `1/4`? |
|---|---|---|
| the matter heat kernel (`a₁ = R/6`) | the *coefficient* of the induced `1/G_ind` (and of `S_ent`) | **no** — it's `1/6`, fixes `G`, cancels in the ratio |
| the conical-deficit geometry (`∫R ⊃ 4π(1−n)A`) | the `4π` and the *emergence* of the area `A` | **no** — pure geometry of a cone |
| the Einstein–Hilbert normalization (`1/16πG`) | the `16π` | **no** — the action normalization |
| the finiteness regulator (`ε → ℓ_P`) | a *finite* UV scale | **no** — only the *value* of `G_ind`/`ℓ_P` |
| **the `1/4` (output)** | `= 4π/16π` | derived, from geometry alone |

**No input carries the `1/4`.** It is the *output*, equal to the geometric ratio `4π/16π`. In particular:

- **The area law is not assumed — it emerges.** `S ∝ A` is *not* an input; it comes out because the conical
  curvature is a *delta-function on the surface* `Σ`, whose integral is the *area* `A`. The "`∝ A`" is a theorem
  of the cone geometry, not a postulate.
- **P4's `1/4` is not used.** The derivation never reads `η = 1/4ℓ_P²`. It reads the matter content + the
  geometry + a finite cutoff, and *outputs* `S = A/4G_ind`. The result is then *compared* to P4 and found to
  **match** — so P4's coefficient is **derived, then seen to agree**, not assumed.
- **What P4 *does* supply is only finiteness.** P4 (or the minimal-length deformation) provides that a UV cutoff
  *exists* (the records are finite) — the *qualitative* content. It does *not* supply the *coefficient*. The
  finiteness makes `G_ind` finite; the geometry makes the ratio `1/4`.

**Conclusion of the audit:** the `1/4` is **non-circularly derived** — it is the geometric `4π/16π`, independent
of the regulator and of P4's stated value. P4's `η = 1/4ℓ_P²` is thereby *recovered as a consequence* of
(matter induces `G`) + (conical/EH geometry), not used as an input.

## 4. The honest residual — what *is* still an input (the species problem)

The audit clears the `1/4` *ratio*. It does **not** derive the *value* of `G_ind` (hence of `ℓ_P`). That value
depends on:
- **the matter content** — *which* fields exist (the free scalar fixes `1/G_ind` for one field; the physical `G`
  needs all species), and
- **the cutoff scale** — the actual value of the minimal length.

This is the **species problem**, and it is the genuine residual input. So the precise honest statement is:

> The `1/4` is forced by geometry + the mechanism (non-circular, regulator-independent). The *value* of `G`
> (the Planck scale) is set by QIQT-H's concrete matter content + cutoff — an input, not derived here.

And the subtlety flagged in the campaign (GPT-5.5-pro): **Type II algebraic finiteness alone is *not* this
regulator** — it gives finite *renormalized* entropy after the fact, not the microscopic spectrum that fixes
`G_ind`. So fully cashing out "QIQT-H's finiteness regulator" requires committing to the concrete finite
record/matter spectrum (Stage C's lattice is the first finite model of it). Until then, Stage B establishes the
*mechanism and the `1/4`*, with the *value* of `G` as the labelled residual.

## 5. Net

- **Derived (non-circular):** the `1/4` of `S = A/4ℓ_P²` is the geometric ratio `(conical 4π)/(EH 16π)`; the area
  law emerges from the cone; P4's coefficient is recovered, not assumed.
- **Residual input:** the *value* of `G_ind` / `ℓ_P` (the species problem + the concrete cutoff) — and the
  commitment to a concrete finite microscopic spectrum (Stage C).
- **Honest scope (unchanged):** free minimal scalar; universality across species needs contact terms; mechanism,
  not the micro-theory.

The upshot for P4: after Stage B, the `1/4` is *no longer the mystery* — it is geometry. The mystery has moved,
cleanly, to **the value of `G` / the matter spectrum** — i.e. to "what is the microscopic content," which is the
ordinary (if hard) business of physics, not a special gravitational postulate.
