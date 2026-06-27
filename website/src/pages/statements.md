---
layout: ../layouts/Deep.astro
title: Machine-rendered statements
eyebrow: Auto-generated from Lean
description: The QIQT-H headline theorems, machine-translated from the Lean 4 / Mathlib source to readable math — one page per target track, each statement with the author's explanation, conclusion first, load-bearing hypotheses shown.
---

The three **headline targets** of the development, each on its own page. Every result is
**machine-translated from the Lean&nbsp;4 / Mathlib source** by the project tool
(`lean_track latex`), which walks the *delaborated syntax tree* of each declaration. The content is
**verbatim**; only the presentation is editorial — leading universal quantifiers and type
ascriptions are factored out (free variables are implicitly universally quantified: $x$ ranges over
spacetime points, indices $\mu,\nu$ over $\{0,1,2,3\}$, $v$ over tangent vectors), each statement
leads with the **author's explanation**, the **conclusion** follows in display math, the
**load-bearing hypotheses are shown**, and routine conditions are summarized by count. To explore
the full dependency network behind these results, see the [**theorem browser**](/browser).


### [GR field equations](/statements/gr)

*Target 3 — QIQT-H gives the Einstein field equations* &nbsp;<small>(15 statements)</small>

### [Born rule](/statements/born)

*Target 1 — the Born rule: reductions and a no-go* &nbsp;<small>(13 statements)</small>

### [Lorentz covariance](/statements/lorentz)

*Target 2 — Lorentz covariance of the selection* &nbsp;<small>(11 statements)</small>
