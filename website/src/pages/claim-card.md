---
layout: ../layouts/Deep.astro
title: The claim card
eyebrow: Verify it yourself
description: The actual machine-extracted certificate the verification capsule prints — the verdict, the exact formal theorem, the complete trusted base, and the full ledger of physical assumptions. Proof, not a promise.
---

This is a real, unedited snapshot of what [`bash verify/verify.sh`](/verify) prints — the
`verify/out/claim_card.md` file, generated on the author's machine at commit `1bddba2`,
Lean `leanprover/lean4:v4.30.0`. Run the capsule yourself and you get your own copy, from
your own kernel. Nothing below is prose I wrote by hand — it is machine-extracted from the
Lean source.

<div class="note" style="border-left:4px solid var(--st-verified)">

## ✅ Overall verdict: PASS

**Every capstone is kernel-accepted and axiom-free; no forbidden axioms; the hypothesis
ledger below is the complete assumption surface.**

*What this card is:* a machine-extracted certificate that, **in the build on this machine**,
the Lean kernel accepted each statement below depending only on the standard axioms,
together with the complete list of hypotheses it still assumes. It certifies a *conditional
mathematical entailment*, **not** a physical truth.

</div>

## Capstone: `qiqt_gr_freefield_complete`

<small>`QIQTH.WedgeKMSToGR.qiqt_gr_freefield_complete`</small>

✅ **Kernel-accepted, axiom-free** — the complete transitive trust base is exactly the three
standard Lean/Mathlib axioms.

**Claim (informal).** For the explicit free Klein–Gordon field, the Einstein field equations
follow from the QIQT-H entropy/heat law with all geometric and field-regularity inputs
discharged, leaving only the labelled physical hypotheses below.

**Formal statement** (machine-rendered from the Lean source):

$$ \exists\, \Lambda,\ \forall (x : M^{4})\,(\mu\,\nu : \mathrm{Fin}\,4),\quad a \cdot T(x)\,\mu\,\nu \;=\; G_{\mu\nu}(x) + \Lambda \cdot g_{\mu\nu}(x) $$

**Complete transitive trusted base:** `Classical.choice`, `Quot.sound`, `propext`. *That is
the entire list.*

## The hypothesis ledger — every remaining assumption

The statement is conditional on **exactly** these binders. Nothing is hidden: every
assumption the kernel relied on appears here. These are the **load-bearing physical inputs —
the honest residue** (they are *assumed*, not derived):

- **`hKG`** — the matter field obeys the Klein–Gordon equation of motion:
  $\ \forall x,\ (\Box\varphi)(x) = m^{2}\,\varphi(x)$
- **`hcap`** — FQ reference identification: the regional holographic capacity is
  $Q_R = A/4\ell_P^2$, i.e. $\ \eta \cdot A(x,v,0) = \log(\#\,\iota)$
- **`hS`** — the realization derivative of the entropy functional $S$ (on null directions)
- **`hK`** — the realization derivative of the heat/modular functional $K = S + D_{\mathrm{KL}}$,
  equal to $\ (2\pi/\hbar)\,T(x)(v,v)$
- **`hA`** — the geometric area-variation hypothesis (the derivative of the area $A$)
- **`hbound`** — the dynamical FQ capacity bound (the P4 finite-information ceiling on the region's
  entropy): $\ S(p\,x\,v\,t) \le \eta \cdot A(x,v,t)$ for $t$ near $0$

Plus, tallied but not load-bearing: **15 data objects**, **1 typeclass instance**, and **21
routine regularity/setup binders** — all listed in full in your own generated card.

## Scope — what this does and does not establish

This certifies a **conditional mathematical entailment** (*if* the listed hypotheses, *then*
the equations), kernel-checked and axiom-free. It does **not** assert that general relativity
is physically true of our universe, nor that these Lean definitions *faithfully model*
QIQT-H / GR — an **adequacy** judgment left to you, the reader, via the rendered statement.

---

**That is the whole point.** What is *proven* (the entailment) and what is *assumed* (the six
physical inputs) are separated, in public, by a machine. Don't take my word for any of it —
[run the capsule](/verify) and read your own card. [How the capsule works →](https://github.com/kaplan196883/QIQT-H/blob/main/verify/README.md)
