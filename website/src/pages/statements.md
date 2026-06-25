---
layout: ../layouts/Deep.astro
title: Machine-rendered statements
eyebrow: Auto-generated from Lean
description: The QIQT-H theorem statements, machine-translated from the Lean 4 / Mathlib source to readable math — notation only, content verbatim, rendered from the delaborated syntax tree.
---

Every statement below is **machine-translated from the Lean&nbsp;4 / Mathlib source** by the
project tool (`lean_track latex`): it walks the *delaborated syntax tree* of each declaration and
maps notation to readable math. The structure (quantifiers, hypotheses, conclusion) and content are
**verbatim** — only the notation is changed (project operators via a per-track glossary; anything
unmapped is left as upright text). Names like `hKG` are the Lean hypothesis labels. Regenerate with
`python scripts/lean-track.py latex -c tracks/<id>.toml`.


## GR field equations

*Target 3 — QIQT-H → the Einstein field equations*

### `qiqt_gr_freefield_complete`

**QIQTH.WedgeKMSToGR.qiqt_gr_freefield_complete** — *capstone*  
Given $\iota,\ g,\ \mathrm{gi},\ \varphi,\ m,\ \eta,\ \hbar,\ a,\ P,\ \mathrm{Pinv},\ A,\ \mathrm{sd},\ p,\ W,\ \mathrm{mw}$,

assume

- `(inst._@.QIQTH.QiqtGrComplete.4163739781._hygCtx._hyg.6)` &nbsp; $\mathrm{Nonempty}\,\iota$
- `(hsymm)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), g_{{a}{b}}({y}) = g_{{b}{a}}({y})$
- `(hsymm_gi)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})$
- `(hinv)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}$
- `(hCg)` &nbsp; $\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}$
- `(hCgi)` &nbsp; $\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}$
- `(hbar0)` &nbsp; $\hbar \ne 0$
- `(hbar_pos)` &nbsp; $0 < \hbar$
- `(heta)` &nbsp; $\eta \ne 0$
- `(ha)` &nbsp; $a = 2 \cdot \pi / (\hbar \cdot \eta)$
- `(hφ)` &nbsp; $({\varphi})\in C^{\infty}$
- `(hKG)` &nbsp; $\forall (x : M^{{4}}), (\Box {\varphi})({x}) = {m}^{2} \cdot \varphi\,x$
- `(hPP)` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}$
- `(hPP')` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}$
- `(hcong)` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \eta_{{k}{l}} \cdot P_{{l}{j}}({x})$
- `(hpp_nn)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (t : \mathbb{R}) (r : \iota), 0 \le p\,x\,v\,t\,r$
- `(hpp1)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (t : \mathbb{R}), \sum_{r} p\,x\,v\,t\,r = 1$
- `(hpp0)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), p\,x\,v\,0 = \lambda x \mapsto {((\#\,\iota))}^{-1}$
- `(hcap)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \eta \cdot A({x},{v},{0}) = \log\,(\#\,\iota)$
- `(hWx)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to W\,x\,v\,x = v$
- `(hWC)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\mu : \mathrm{Fin}\,4), ({\lambda y \mapsto W\,x\,v\,y\,\mu})\in C^{\infty}$
- `(hWgeo)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (y : M^{{4}}) (\mu : \mathrm{Fin}\,4), \sum_{\nu} W\,x\,v\,y\,\nu \cdot (\nabla {W\,x\,v})_{{\nu}}{}^{{\mu}}({y}) = 0$
- `(hWequil)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \sum_{\mu} \sum_{\nu} (\nabla {W\,x\,v})_{{\mu}}{}^{{\nu}}({x}) \cdot (\nabla {W\,x\,v})_{{\nu}}{}^{{\mu}}({x}) = 0$
- `(hS)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({\lambda t \mapsto S({p\,x\,v\,t})})'({0})={\dot{S}({x},{v})}$
- `(hK)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({\lambda t \mapsto S({p\,x\,v\,t}) + D_{\mathrm{KL}}({p\,x\,v\,t}\,\|\,{p\,x\,v\,0})})'({0})={2 \cdot \pi / \hbar \cdot ({T({x})})({v},{v})}$
- `(hA)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({A\,x\,v})'({0})={-\sum_{\nu} W\,x\,v\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \theta({y})})({x})}$
- `(hbound)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \text{for }t\text{ near }0,\; S({p\,x\,v\,t}) \le \eta \cdot A({x},{v},{t})$
- `(hmw)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), 0 < \mathrm{mw}\,x\,v$

then

$$ \exists \Lambda, \forall (x : M^{{4}}) (\mu \nu : \mathrm{Fin}\,4), a \cdot T({x})\,\mu\,\nu = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

### `qiqt_gr_ppwave_showcase`

**QIQTH.WedgeKMSToGR.qiqt_gr_ppwave_showcase** — *spine*  
Given $\iota,\ H,\ \varphi,\ m,\ \eta,\ \hbar,\ a,\ c,\ \mathrm{sd},\ p,\ W,\ \mathrm{mw}$,

assume

- `(inst._@.QIQTH.QiqtGrShowcase.1910216171._hygCtx._hyg.6)` &nbsp; $\mathrm{Nonempty}\,\iota$
- `(hCH)` &nbsp; $({H})\in C^{\infty}$
- `(hbar0)` &nbsp; $\hbar \ne 0$
- `(hbar_pos)` &nbsp; $0 < \hbar$
- `(heta)` &nbsp; $\eta \ne 0$
- `(ha)` &nbsp; $a = 2 \cdot \pi / (\hbar \cdot \eta)$
- `(hφ)` &nbsp; $({\varphi})\in C^{\infty}$
- `(hKG)` &nbsp; $\forall (x : M^{{4}}), (\Box {\varphi})({x}) = {m}^{2} \cdot \varphi\,x$
- `(hcap)` &nbsp; $\eta \cdot c = \log\,(\#\,\iota)$
- `(hpp_nn)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (t : \mathbb{R}) (r : \iota), 0 \le p\,x\,v\,t\,r$
- `(hpp1)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (t : \mathbb{R}), \sum_{r} p\,x\,v\,t\,r = 1$
- `(hpp0)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), p\,x\,v\,0 = \lambda x \mapsto {((\#\,\iota))}^{-1}$
- `(hWx)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g^{\mathrm{pp}}\,H\,x})({v},{v}) = 0 \to W\,x\,v\,x = v$
- `(hWC)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\mu : \mathrm{Fin}\,4), ({\lambda y \mapsto W\,x\,v\,y\,\mu})\in C^{\infty}$
- `(hcov)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (p q : \mathrm{Fin}\,4) (y : M^{{4}}), (\nabla {W\,x\,v})_{{p}}{}^{{q}}({y}) = 0$
- `(hS)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g^{\mathrm{pp}}\,H\,x})({v},{v}) = 0 \to ({\lambda t \mapsto S({p\,x\,v\,t})})'({0})={\dot{S}({x},{v})}$
- `(hK)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g^{\mathrm{pp}}\,H\,x})({v},{v}) = 0 \to ({\lambda t \mapsto S({p\,x\,v\,t}) + D_{\mathrm{KL}}({p\,x\,v\,t}\,\|\,{p\,x\,v\,0})})'({0})={2 \cdot \pi / \hbar \cdot ({T({x})})({v},{v})}$
- `(hmw)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), 0 < \mathrm{mw}\,x\,v$

then

$$ \exists \Lambda, \forall (x : M^{{4}}) (\mu \nu : \mathrm{Fin}\,4), a \cdot T({x})\,\mu\,\nu = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g^{\mathrm{pp}}\,H\,x\,\mu\,\nu $$

### `qiqt_gr_freefield_gaussian`

**QIQTH.WedgeKMSToGR.qiqt_gr_freefield_gaussian** — *spine*  
Given $g,\ \mathrm{gi},\ \varphi,\ m,\ \eta,\ \hbar,\ a,\ P,\ \mathrm{Pinv},\ \mathrm{Sf},\ \mathrm{KE},\ A,\ \mathrm{sd},\ \mathrm{ad},\ \mathrm{mw},\ W$,

assume

- `(hsymm)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), g_{{a}{b}}({y}) = g_{{b}{a}}({y})$
- `(hsymm_gi)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})$
- `(hinv)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}$
- `(hCg)` &nbsp; $\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}$
- `(hCgi)` &nbsp; $\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}$
- `(hbar0)` &nbsp; $\hbar \ne 0$
- `(hbar_pos)` &nbsp; $0 < \hbar$
- `(heta)` &nbsp; $\eta \ne 0$
- `(ha)` &nbsp; $a = 2 \cdot \pi / (\hbar \cdot \eta)$
- `(hφ)` &nbsp; $({\varphi})\in C^{\infty}$
- `(hKG)` &nbsp; $\forall (x : M^{{4}}), (\Box {\varphi})({x}) = {m}^{2} \cdot \varphi\,x$
- `(hPP)` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}$
- `(hPP')` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}$
- `(hcong)` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \eta_{{k}{l}} \cdot P_{{l}{j}}({x})$
- `(hS)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({\mathrm{Sf}\,x\,v})'({0})={\dot{S}({x},{v})}$
- `(hK)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({\mathrm{KE}\,x\,v})'({0})={2 \cdot \pi / \hbar \cdot ({T({x})})({v},{v})}$
- `(hA)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({A\,x\,v})'({0})={\dot{A}({x},{v})}$
- `(hbound)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `(hsat)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `(hDnn)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `(hD0)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `(hmw)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), 0 < \mathrm{mw}\,x\,v$
- `(hWx)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to W\,x\,v\,x = v$
- `(hWC)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\mu : \mathrm{Fin}\,4), ({\lambda y \mapsto W\,x\,v\,y\,\mu})\in C^{\infty}$
- `(hWgeo)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (y : M^{{4}}) (\mu : \mathrm{Fin}\,4), \sum_{\nu} W\,x\,v\,y\,\nu \cdot (\nabla {W\,x\,v})_{{\nu}}{}^{{\mu}}({y}) = 0$
- `(hWequil)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \sum_{\mu} \sum_{\nu} (\nabla {W\,x\,v})_{{\mu}}{}^{{\nu}}({x}) \cdot (\nabla {W\,x\,v})_{{\nu}}{}^{{\mu}}({x}) = 0$
- `(hWarea)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \dot{A}({x},{v}) = -\sum_{\nu} W\,x\,v\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \theta({y})})({x})$

then

$$ \exists \Lambda, \forall (x : M^{{4}}) (\mu \nu : \mathrm{Fin}\,4), a \cdot T({x})\,\mu\,\nu = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

### `qiqt_gr_freefield_thermo`

**QIQTH.WedgeKMSToGR.qiqt_gr_freefield_thermo** — *spine*  
Given $\iota,\ g,\ \mathrm{gi},\ \varphi,\ m,\ \eta,\ \hbar,\ a,\ P,\ \mathrm{Pinv},\ A,\ \mathrm{sd},\ p,\ W,\ \mathrm{mw},\ \mathrm{ff},\ \mathrm{ff}^{\prime},\ \mathrm{Bd}$,

assume

- `(inst._@.QIQTH.QiqtGrThermo.1369663628._hygCtx._hyg.6)` &nbsp; $\mathrm{Nonempty}\,\iota$
- `(hsymm)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), g_{{a}{b}}({y}) = g_{{b}{a}}({y})$
- `(hsymm_gi)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})$
- `(hinv)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}$
- `(hCg)` &nbsp; $\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}$
- `(hCgi)` &nbsp; $\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}$
- `(hbar0)` &nbsp; $\hbar \ne 0$
- `(heta)` &nbsp; $\eta \ne 0$
- `(ha)` &nbsp; $a = 2 \cdot \pi / (\hbar \cdot \eta)$
- `(hφ)` &nbsp; $({\varphi})\in C^{\infty}$
- `(hKG)` &nbsp; $\forall (x : M^{{4}}), (\Box {\varphi})({x}) = {m}^{2} \cdot \varphi\,x$
- `(hPP)` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}$
- `(hPP')` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}$
- `(hcong)` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \eta_{{k}{l}} \cdot P_{{l}{j}}({x})$
- `(hpp_nn)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (t : \mathbb{R}) (r : \iota), 0 \le p\,x\,v\,t\,r$
- `(hpp1)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (t : \mathbb{R}), \sum_{r} p\,x\,v\,t\,r = 1$
- `(hpp0)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), p\,x\,v\,0 = \lambda x \mapsto {((\#\,\iota))}^{-1}$
- `(hcap)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \eta \cdot A({x},{v},{0}) = \log\,(\#\,\iota)$
- `(hWx)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to W\,x\,v\,x = v$
- `(hWC)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\mu : \mathrm{Fin}\,4), ({\lambda y \mapsto W\,x\,v\,y\,\mu})\in C^{\infty}$
- `(hWgeo)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (y : M^{{4}}) (\mu : \mathrm{Fin}\,4), \sum_{\nu} W\,x\,v\,y\,\nu \cdot (\nabla {W\,x\,v})_{{\nu}}{}^{{\mu}}({y}) = 0$
- `(hWequil)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \sum_{\mu} \sum_{\nu} (\nabla {W\,x\,v})_{{\mu}}{}^{{\nu}}({x}) \cdot (\nabla {W\,x\,v})_{{\nu}}{}^{{\mu}}({x}) = 0$
- `(hS)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({\lambda t \mapsto S({p\,x\,v\,t})})'({0})={\dot{S}({x},{v})}$
- `(hK)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({\lambda t \mapsto S({p\,x\,v\,t}) + D_{\mathrm{KL}}({p\,x\,v\,t}\,\|\,{p\,x\,v\,0})})'({0})={2 \cdot \pi / \hbar \cdot ({T({x})})({v},{v})}$
- `(hA)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({A\,x\,v})'({0})={-\sum_{\nu} W\,x\,v\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \theta({y})})({x})}$
- `(hbound)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \text{for }t\text{ near }0,\; S({p\,x\,v\,t}) \le \eta \cdot A({x},{v},{t})$
- `(hmw)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), 0 < \mathrm{mw}\,x\,v$
- `(hf2)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{MemLp}\,(\mathrm{ff}\,x\,v)\,2\,\mathrm{volume}$
- `(hf_int)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{Integrable}\,(\mathrm{ff}\,x\,v)\,\mathrm{volume}$
- `(hfd)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), ({\mathrm{ff}\,x\,v})'({\theta})={\mathrm{ff}^{\prime}\,x\,v\,\theta}$
- `(hf'_meas)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{AEStronglyMeasurable}\,(\mathrm{ff}^{\prime}\,x\,v)\,\mathrm{volume}$
- `(hB)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), \|\mathrm{ff}^{\prime}\,x\,v\,\theta\| \le \mathrm{Bd}\,x\,v$
- `(hTkk)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to 2 \cdot \pi / \hbar \cdot {(\sum_{b} v\,b \cdot \partial_{{b}}({\varphi})({x}))}^{2} = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{ff}\,x\,v\,\theta) \cdot \mathrm{ff}^{\prime}\,x\,v\,\theta)).\mathrm{im}$

then

$$ \exists \Lambda, \forall (x : M^{{4}}) (\mu \nu : \mathrm{Fin}\,4), a \cdot T({x})\,\mu\,\nu = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

### `qiqt_gr_freefield_geom`

**QIQTH.WedgeKMSToGR.qiqt_gr_freefield_geom** — *spine*  
Given $g,\ \mathrm{gi},\ \varphi,\ m,\ \eta,\ \hbar,\ a,\ P,\ \mathrm{Pinv},\ \mathrm{Sf},\ \mathrm{KE},\ A,\ \mathrm{sd},\ W,\ \mathrm{mw},\ \mathrm{ff},\ \mathrm{ff}^{\prime},\ \mathrm{Bd}$,

assume

- `(hsymm)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), g_{{a}{b}}({y}) = g_{{b}{a}}({y})$
- `(hsymm_gi)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})$
- `(hinv)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}$
- `(hCg)` &nbsp; $\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}$
- `(hCgi)` &nbsp; $\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}$
- `(hbar0)` &nbsp; $\hbar \ne 0$
- `(heta)` &nbsp; $\eta \ne 0$
- `(ha)` &nbsp; $a = 2 \cdot \pi / (\hbar \cdot \eta)$
- `(hφ)` &nbsp; $({\varphi})\in C^{\infty}$
- `(hKG)` &nbsp; $\forall (x : M^{{4}}), (\Box {\varphi})({x}) = {m}^{2} \cdot \varphi\,x$
- `(hPP)` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}$
- `(hPP')` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}$
- `(hcong)` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \eta_{{k}{l}} \cdot P_{{l}{j}}({x})$
- `(hWx)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to W\,x\,v\,x = v$
- `(hWC)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\mu : \mathrm{Fin}\,4), ({\lambda y \mapsto W\,x\,v\,y\,\mu})\in C^{\infty}$
- `(hWgeo)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (y : M^{{4}}) (\mu : \mathrm{Fin}\,4), \sum_{\nu} W\,x\,v\,y\,\nu \cdot (\nabla {W\,x\,v})_{{\nu}}{}^{{\mu}}({y}) = 0$
- `(hWequil)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \sum_{\mu} \sum_{\nu} (\nabla {W\,x\,v})_{{\mu}}{}^{{\nu}}({x}) \cdot (\nabla {W\,x\,v})_{{\nu}}{}^{{\mu}}({x}) = 0$
- `(hS)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({\mathrm{Sf}\,x\,v})'({0})={\dot{S}({x},{v})}$
- `(hK)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({\mathrm{KE}\,x\,v})'({0})={2 \cdot \pi / \hbar \cdot ({T({x})})({v},{v})}$
- `(hA)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({A\,x\,v})'({0})={-\sum_{\nu} W\,x\,v\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \theta({y})})({x})}$
- `(hbound)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `(hsat)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `(hDnn)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `(hD0)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `(hmw)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), 0 < \mathrm{mw}\,x\,v$
- `(hf2)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{MemLp}\,(\mathrm{ff}\,x\,v)\,2\,\mathrm{volume}$
- `(hf_int)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{Integrable}\,(\mathrm{ff}\,x\,v)\,\mathrm{volume}$
- `(hfd)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), ({\mathrm{ff}\,x\,v})'({\theta})={\mathrm{ff}^{\prime}\,x\,v\,\theta}$
- `(hf'_meas)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{AEStronglyMeasurable}\,(\mathrm{ff}^{\prime}\,x\,v)\,\mathrm{volume}$
- `(hB)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), \|\mathrm{ff}^{\prime}\,x\,v\,\theta\| \le \mathrm{Bd}\,x\,v$
- `(hTkk)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to 2 \cdot \pi / \hbar \cdot {(\sum_{b} v\,b \cdot \partial_{{b}}({\varphi})({x}))}^{2} = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{ff}\,x\,v\,\theta) \cdot \mathrm{ff}^{\prime}\,x\,v\,\theta)).\mathrm{im}$

then

$$ \exists \Lambda, \forall (x : M^{{4}}) (\mu \nu : \mathrm{Fin}\,4), a \cdot T({x})\,\mu\,\nu = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

### `qiqt_gr_freefield_nullEnergy`

**QIQTH.WedgeKMSToGR.qiqt_gr_freefield_nullEnergy** — *spine*  
Given $g,\ \mathrm{gi},\ \varphi,\ m,\ \eta,\ \hbar,\ a,\ P,\ \mathrm{Pinv},\ \mathrm{Sf},\ \mathrm{KE},\ A,\ \mathrm{sd},\ \mathrm{ad},\ \mathrm{mw},\ \mathrm{ff},\ \mathrm{ff}^{\prime},\ \mathrm{Bd},\ W$,

assume

- `(hsymm)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), g_{{a}{b}}({y}) = g_{{b}{a}}({y})$
- `(hsymm_gi)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})$
- `(hinv)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}$
- `(hCg)` &nbsp; $\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}$
- `(hCgi)` &nbsp; $\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}$
- `(hbar0)` &nbsp; $\hbar \ne 0$
- `(heta)` &nbsp; $\eta \ne 0$
- `(ha)` &nbsp; $a = 2 \cdot \pi / (\hbar \cdot \eta)$
- `(hφ)` &nbsp; $({\varphi})\in C^{\infty}$
- `(hKG)` &nbsp; $\forall (x : M^{{4}}), (\Box {\varphi})({x}) = {m}^{2} \cdot \varphi\,x$
- `(hPP)` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}$
- `(hPP')` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}$
- `(hcong)` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \eta_{{k}{l}} \cdot P_{{l}{j}}({x})$
- `(hS)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({\mathrm{Sf}\,x\,v})'({0})={\dot{S}({x},{v})}$
- `(hK)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({\mathrm{KE}\,x\,v})'({0})={2 \cdot \pi / \hbar \cdot ({T({x})})({v},{v})}$
- `(hA)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({A\,x\,v})'({0})={\dot{A}({x},{v})}$
- `(hbound)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `(hsat)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `(hDnn)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `(hD0)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `(hmw)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), 0 < \mathrm{mw}\,x\,v$
- `(hf2)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{MemLp}\,(\mathrm{ff}\,x\,v)\,2\,\mathrm{volume}$
- `(hf_int)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{Integrable}\,(\mathrm{ff}\,x\,v)\,\mathrm{volume}$
- `(hfd)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), ({\mathrm{ff}\,x\,v})'({\theta})={\mathrm{ff}^{\prime}\,x\,v\,\theta}$
- `(hf'_meas)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{AEStronglyMeasurable}\,(\mathrm{ff}^{\prime}\,x\,v)\,\mathrm{volume}$
- `(hB)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), \|\mathrm{ff}^{\prime}\,x\,v\,\theta\| \le \mathrm{Bd}\,x\,v$
- `(hTkk)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to 2 \cdot \pi / \hbar \cdot {(\sum_{b} v\,b \cdot \partial_{{b}}({\varphi})({x}))}^{2} = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{ff}\,x\,v\,\theta) \cdot \mathrm{ff}^{\prime}\,x\,v\,\theta)).\mathrm{im}$
- `(hWx)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to W\,x\,v\,x = v$
- `(hWC)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\mu : \mathrm{Fin}\,4), ({\lambda y \mapsto W\,x\,v\,y\,\mu})\in C^{\infty}$
- `(hWgeo)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (y : M^{{4}}) (\mu : \mathrm{Fin}\,4), \sum_{\nu} W\,x\,v\,y\,\nu \cdot (\nabla {W\,x\,v})_{{\nu}}{}^{{\mu}}({y}) = 0$
- `(hWequil)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \sum_{\mu} \sum_{\nu} (\nabla {W\,x\,v})_{{\mu}}{}^{{\nu}}({x}) \cdot (\nabla {W\,x\,v})_{{\nu}}{}^{{\mu}}({x}) = 0$
- `(hWarea)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \dot{A}({x},{v}) = -\sum_{\nu} W\,x\,v\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \theta({y})})({x})$

then

$$ \exists \Lambda, \forall (x : M^{{4}}) (\mu \nu : \mathrm{Fin}\,4), a \cdot T({x})\,\mu\,\nu = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

### `qiqt_gr_freefield_localized'`

**QIQTH.WedgeKMSToGR.qiqt_gr_freefield_localized'** — *spine*  
Given $g,\ \mathrm{gi},\ \varphi,\ m,\ \eta,\ \hbar,\ a,\ P,\ \mathrm{Pinv},\ \mathrm{Sf},\ \mathrm{KE},\ A,\ \mathrm{sd},\ \mathrm{ad},\ \mathrm{mw},\ \mathrm{ff},\ \mathrm{ff}^{\prime},\ \mathrm{Bd},\ W$,

assume

- `(hsymm)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), g_{{a}{b}}({y}) = g_{{b}{a}}({y})$
- `(hsymm_gi)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})$
- `(hinv)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}$
- `(hCg)` &nbsp; $\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}$
- `(hCgi)` &nbsp; $\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}$
- `(hbar0)` &nbsp; $\hbar \ne 0$
- `(heta)` &nbsp; $\eta \ne 0$
- `(ha)` &nbsp; $a = 2 \cdot \pi / (\hbar \cdot \eta)$
- `(hφ)` &nbsp; $({\varphi})\in C^{\infty}$
- `(hKG)` &nbsp; $\forall (x : M^{{4}}), (\Box {\varphi})({x}) = {m}^{2} \cdot \varphi\,x$
- `(hPP)` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}$
- `(hPP')` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}$
- `(hcong)` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \eta_{{k}{l}} \cdot P_{{l}{j}}({x})$
- `(hS)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({\mathrm{Sf}\,x\,v})'({0})={\dot{S}({x},{v})}$
- `(hK)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({\mathrm{KE}\,x\,v})'({0})={2 \cdot \pi / \hbar \cdot ({T({x})})({v},{v})}$
- `(hA)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({A\,x\,v})'({0})={\dot{A}({x},{v})}$
- `(hbound)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `(hsat)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `(hDnn)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `(hD0)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `(hmw)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), 0 < \mathrm{mw}\,x\,v$
- `(hf2)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{MemLp}\,(\mathrm{ff}\,x\,v)\,2\,\mathrm{volume}$
- `(hf_int)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{Integrable}\,(\mathrm{ff}\,x\,v)\,\mathrm{volume}$
- `(hfd)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), ({\mathrm{ff}\,x\,v})'({\theta})={\mathrm{ff}^{\prime}\,x\,v\,\theta}$
- `(hf'_meas)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{AEStronglyMeasurable}\,(\mathrm{ff}^{\prime}\,x\,v)\,\mathrm{volume}$
- `(hB)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), \|\mathrm{ff}^{\prime}\,x\,v\,\theta\| \le \mathrm{Bd}\,x\,v$
- `(hTkk)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to 2 \cdot \pi / \hbar \cdot ({T({x})})({v},{v}) = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{ff}\,x\,v\,\theta) \cdot \mathrm{ff}^{\prime}\,x\,v\,\theta)).\mathrm{im}$
- `(hWx)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to W\,x\,v\,x = v$
- `(hWC)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\mu : \mathrm{Fin}\,4), ({\lambda y \mapsto W\,x\,v\,y\,\mu})\in C^{\infty}$
- `(hWgeo)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (y : M^{{4}}) (\mu : \mathrm{Fin}\,4), \sum_{\nu} W\,x\,v\,y\,\nu \cdot (\nabla {W\,x\,v})_{{\nu}}{}^{{\mu}}({y}) = 0$
- `(hWequil)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \sum_{\mu} \sum_{\nu} (\nabla {W\,x\,v})_{{\mu}}{}^{{\nu}}({x}) \cdot (\nabla {W\,x\,v})_{{\nu}}{}^{{\mu}}({x}) = 0$
- `(hWarea)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \dot{A}({x},{v}) = -\sum_{\nu} W\,x\,v\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \theta({y})})({x})$

then

$$ \exists \Lambda, \forall (x : M^{{4}}) (\mu \nu : \mathrm{Fin}\,4), a \cdot T({x})\,\mu\,\nu = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

### `qiqt_gr_freefield_localized`

**QIQTH.WedgeKMSToGR.qiqt_gr_freefield_localized** — *spine*  
Given $g,\ \mathrm{gi},\ \varphi,\ m,\ \eta,\ \hbar,\ a,\ P,\ \mathrm{Pinv},\ \mathrm{Sf},\ \mathrm{KE},\ A,\ \mathrm{sd},\ \mathrm{ad},\ \mathrm{mw},\ \mathrm{ff},\ \mathrm{ff}^{\prime},\ \mathrm{Bd}$,

assume

- `(hsymm)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), g_{{a}{b}}({y}) = g_{{b}{a}}({y})$
- `(hsymm_gi)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})$
- `(hinv)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}$
- `(hCg)` &nbsp; $\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}$
- `(hCgi)` &nbsp; $\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}$
- `(hbar0)` &nbsp; $\hbar \ne 0$
- `(heta)` &nbsp; $\eta \ne 0$
- `(ha)` &nbsp; $a = 2 \cdot \pi / (\hbar \cdot \eta)$
- `(hφ)` &nbsp; $({\varphi})\in C^{\infty}$
- `(hKG)` &nbsp; $\forall (x : M^{{4}}), (\Box {\varphi})({x}) = {m}^{2} \cdot \varphi\,x$
- `(hPP)` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}$
- `(hPP')` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}$
- `(hcong)` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \eta_{{k}{l}} \cdot P_{{l}{j}}({x})$
- `(hS)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({\mathrm{Sf}\,x\,v})'({0})={\dot{S}({x},{v})}$
- `(hK)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({\mathrm{KE}\,x\,v})'({0})={2 \cdot \pi / \hbar \cdot ({T({x})})({v},{v})}$
- `(hA)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({A\,x\,v})'({0})={\dot{A}({x},{v})}$
- `(hbound)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `(hsat)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `(hDnn)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `(hD0)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `(hmw)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), 0 < \mathrm{mw}\,x\,v$
- `(hf2)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{MemLp}\,(\mathrm{ff}\,x\,v)\,2\,\mathrm{volume}$
- `(hf_int)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{Integrable}\,(\mathrm{ff}\,x\,v)\,\mathrm{volume}$
- `(hfd)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), ({\mathrm{ff}\,x\,v})'({\theta})={\mathrm{ff}^{\prime}\,x\,v\,\theta}$
- `(hf'_meas)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{AEStronglyMeasurable}\,(\mathrm{ff}^{\prime}\,x\,v)\,\mathrm{volume}$
- `(hB)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), \|\mathrm{ff}^{\prime}\,x\,v\,\theta\| \le \mathrm{Bd}\,x\,v$
- `(hTkk)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to 2 \cdot \pi / \hbar \cdot ({T({x})})({v},{v}) = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{ff}\,x\,v\,\theta) \cdot \mathrm{ff}^{\prime}\,x\,v\,\theta)).\mathrm{im}$
- `(hFocus)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \dot{A}({x},{v}) = ({\lambda i j \mapsto R_{{i}{j}}({x})})({v},{v})$

then

$$ \exists \Lambda, \forall (x : M^{{4}}) (\mu \nu : \mathrm{Fin}\,4), a \cdot T({x})\,\mu\,\nu = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

### `qiqt_gr_freefield`

**QIQTH.WedgeKMSToGR.qiqt_gr_freefield** — *spine*  
Given $g,\ \mathrm{gi},\ \varphi,\ m,\ \eta,\ \hbar,\ a,\ P,\ \mathrm{Pinv},\ \mathrm{Sf},\ \mathrm{KE},\ A,\ \mathrm{sd},\ \mathrm{kd},\ \mathrm{ad},\ \mathrm{mw},\ \mathrm{ff},\ \mathrm{ff}^{\prime},\ \mathrm{Bd}$,

assume

- `(hsymm)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), g_{{a}{b}}({y}) = g_{{b}{a}}({y})$
- `(hsymm_gi)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})$
- `(hinv)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}$
- `(hCg)` &nbsp; $\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}$
- `(hCgi)` &nbsp; $\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}$
- `(hbar0)` &nbsp; $\hbar \ne 0$
- `(heta)` &nbsp; $\eta \ne 0$
- `(ha)` &nbsp; $a = 2 \cdot \pi / (\hbar \cdot \eta)$
- `(hφ)` &nbsp; $({\varphi})\in C^{\infty}$
- `(hKG)` &nbsp; $\forall (x : M^{{4}}), (\Box {\varphi})({x}) = {m}^{2} \cdot \varphi\,x$
- `(hPP)` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}$
- `(hPP')` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}$
- `(hcong)` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \eta_{{k}{l}} \cdot P_{{l}{j}}({x})$
- `(hS)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({\mathrm{Sf}\,x\,v})'({0})={\dot{S}({x},{v})}$
- `(hK)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({\mathrm{KE}\,x\,v})'({0})={\dot{K}({x},{v})}$
- `(hA)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({A\,x\,v})'({0})={\dot{A}({x},{v})}$
- `(hbound)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `(hsat)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `(hDnn)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `(hD0)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `(hmw)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), 0 < \mathrm{mw}\,x\,v$
- `(hf2)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{MemLp}\,(\mathrm{ff}\,x\,v)\,2\,\mathrm{volume}$
- `(hf_int)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{Integrable}\,(\mathrm{ff}\,x\,v)\,\mathrm{volume}$
- `(hfd)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), ({\mathrm{ff}\,x\,v})'({\theta})={\mathrm{ff}^{\prime}\,x\,v\,\theta}$
- `(hf'_meas)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{AEStronglyMeasurable}\,(\mathrm{ff}^{\prime}\,x\,v)\,\mathrm{volume}$
- `(hB)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), \|\mathrm{ff}^{\prime}\,x\,v\,\theta\| \le \mathrm{Bd}\,x\,v$
- `(hTkk)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to 2 \cdot \pi / \hbar \cdot ({T({x})})({v},{v}) = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{ff}\,x\,v\,\theta) \cdot \mathrm{ff}^{\prime}\,x\,v\,\theta)).\mathrm{im}$
- `(hbridge)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({\lambda t \mapsto \mathrm{inner}\,\mathbb{C}\,(\mathrm{toLp}\,(\mathrm{ff}\,x\,v)\,\cdots )\,((\mathrm{modUnitary}\,(\mathrm{niceWedgeStandardSubspace}\,(\mathrm{mw}\,x\,v)\,\cdots \,\cdots )\,t)\,(\mathrm{toLp}\,(\mathrm{ff}\,x\,v)\,\cdots ))})'({0})={i \cdot (\dot{K}({x},{v}))}$
- `(hFocus)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \dot{A}({x},{v}) = ({\lambda i j \mapsto R_{{i}{j}}({x})})({v},{v})$

then

$$ \exists \Lambda, \forall (x : M^{{4}}) (\mu \nu : \mathrm{Fin}\,4), a \cdot T({x})\,\mu\,\nu = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

### `qiqt_gr_explicit_kg`

**QIQTH.WedgeKMSToGR.qiqt_gr_explicit_kg** — *spine*  
Given $g,\ \mathrm{gi},\ \varphi,\ m,\ \eta,\ \hbar,\ a,\ P,\ \mathrm{Pinv},\ \mathrm{Sf},\ \mathrm{KE},\ A,\ \mathrm{sd},\ \mathrm{kd},\ \mathrm{ad}$,

assume

- `(hsymm)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), g_{{a}{b}}({y}) = g_{{b}{a}}({y})$
- `(hsymm_gi)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})$
- `(hinv)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}$
- `(hCg)` &nbsp; $\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}$
- `(hCgi)` &nbsp; $\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}$
- `(hbar0)` &nbsp; $\hbar \ne 0$
- `(heta)` &nbsp; $\eta \ne 0$
- `(ha)` &nbsp; $a = 2 \cdot \pi / (\hbar \cdot \eta)$
- `(hφ)` &nbsp; $({\varphi})\in C^{\infty}$
- `(hKG)` &nbsp; $\forall (x : M^{{4}}), (\Box {\varphi})({x}) = {m}^{2} \cdot \varphi\,x$
- `(hPP)` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}$
- `(hPP')` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}$
- `(hcong)` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \eta_{{k}{l}} \cdot P_{{l}{j}}({x})$
- `(hS)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({\mathrm{Sf}\,x\,v})'({0})={\dot{S}({x},{v})}$
- `(hK)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({\mathrm{KE}\,x\,v})'({0})={\dot{K}({x},{v})}$
- `(hA)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({A\,x\,v})'({0})={\dot{A}({x},{v})}$
- `(hbound)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `(hsat)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `(hDnn)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `(hD0)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `(hKMS)` &nbsp; $\mathrm{WedgeKMSFlux\_complete}\,g\,(\mathrm{kgStress}\,m\,\varphi\,g\,\mathrm{gi})\,\mathrm{kd}\,\hbar$
- `(hFocus)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \dot{A}({x},{v}) = ({\lambda i j \mapsto R_{{i}{j}}({x})})({v},{v})$

then

$$ \exists \Lambda, \forall (x : M^{{4}}) (\mu \nu : \mathrm{Fin}\,4), a \cdot T({x})\,\mu\,\nu = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

### `qiqt_gr_from_flux_complete`

**QIQTH.WedgeKMSToGR.qiqt_gr_from_flux_complete** — *spine*  
Given $g,\ \mathrm{gi},\ T,\ \eta,\ \hbar,\ a,\ P,\ \mathrm{Pinv},\ \mathrm{Sf},\ \mathrm{KE},\ A,\ \mathrm{sd},\ \mathrm{kd},\ \mathrm{ad}$,

assume

- `(hsymm)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), g_{{a}{b}}({y}) = g_{{b}{a}}({y})$
- `(hsymm_gi)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})$
- `(hinv)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}$
- `(hCg)` &nbsp; $\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}$
- `(hCgi)` &nbsp; $\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}$
- `(hbar0)` &nbsp; $\hbar \ne 0$
- `(heta)` &nbsp; $\eta \ne 0$
- `(ha)` &nbsp; $a = 2 \cdot \pi / (\hbar \cdot \eta)$
- `(hT_symm)` &nbsp; $\forall (x : M^{{4}}) (a^{\prime} b : \mathrm{Fin}\,4), T_{{a^{\prime}}{b}}({x}) = T_{{b}{a^{\prime}}}({x})$
- `(hPP)` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}$
- `(hPP')` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}$
- `(hcong)` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \eta_{{k}{l}} \cdot P_{{l}{j}}({x})$
- `(hS)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({\mathrm{Sf}\,x\,v})'({0})={\dot{S}({x},{v})}$
- `(hK)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({\mathrm{KE}\,x\,v})'({0})={\dot{K}({x},{v})}$
- `(hA)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({A\,x\,v})'({0})={\dot{A}({x},{v})}$
- `(hbound)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `(hsat)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `(hDnn)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `(hD0)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `(hflux)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \dot{K}({x},{v}) = 2 \cdot \pi / \hbar \cdot ({T\,x})({v},{v})$
- `(hFocus)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \dot{A}({x},{v}) = ({\lambda i j \mapsto R_{{i}{j}}({x})})({v},{v})$
- `(hreg)` &nbsp; $\forall (f : M^{{4}} \to \mathbb{R}), (\forall (y : M^{{4}}) (a^{\prime} b : \mathrm{Fin}\,4), a \cdot T_{{a^{\prime}}{b}}({y}) = R_{{a^{\prime}}{b}}({y}) + f\,y \cdot g_{{a^{\prime}}{b}}({y})) \to (\forall (x : M^{{4}}) (\rho : \mathrm{Fin}\,4), \mathrm{PdiffAt}\,f\,\rho\,x) \wedge \mathrm{Differentiable}\,\mathbb{R}\,\lambda y \mapsto f\,y + 1/2 \cdot R({y})$
- `(conserv)` &nbsp; $\forall (x : M^{{4}}) (\nu : \mathrm{Fin}\,4), (\nabla\!\cdot {\lambda y a^{\prime} b \mapsto a \cdot T_{{a^{\prime}}{b}}({y})})_{{\nu}}({x}) = 0$

then

$$ \exists \Lambda, \forall (x : M^{{4}}) (\mu \nu : \mathrm{Fin}\,4), a \cdot T_{{\mu}{\nu}}({x}) = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

### `qiqt_bekenstein_gives_gr`

**QIQTH.QiqtToGR.qiqt_bekenstein_gives_gr** — *spine*  
Given $g,\ \mathrm{gi},\ T,\ \eta,\ \hbar,\ a,\ P,\ \mathrm{Pinv},\ S,\ \mathrm{KE},\ A,\ \mathrm{sd},\ \mathrm{kd},\ \mathrm{ad}$,

assume

- `(hsymm)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), g_{{a}{b}}({y}) = g_{{b}{a}}({y})$
- `(hsymm_gi)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})$
- `(hinv)` &nbsp; $\forall (y : M^{{4}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}$
- `(hCg)` &nbsp; $\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}$
- `(hCgi)` &nbsp; $\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}$
- `(hbar0)` &nbsp; $\hbar \ne 0$
- `(heta)` &nbsp; $\eta \ne 0$
- `(ha)` &nbsp; $a = 2 \cdot \pi / (\hbar \cdot \eta)$
- `(hT_symm)` &nbsp; $\forall (x : M^{{4}}) (a^{\prime} b : \mathrm{Fin}\,4), T_{{a^{\prime}}{b}}({x}) = T_{{b}{a^{\prime}}}({x})$
- `(hPP)` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}$
- `(hPP')` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}$
- `(hcong)` &nbsp; $\forall (x : M^{{4}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \eta_{{k}{l}} \cdot P_{{l}{j}}({x})$
- `(hS)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({S\,x\,v})'({0})={\dot{S}({x},{v})}$
- `(hK)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({\mathrm{KE}\,x\,v})'({0})={\dot{K}({x},{v})}$
- `(hA)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to ({A\,x\,v})'({0})={\dot{A}({x},{v})}$
- `(hbound)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \text{for }t\text{ near }0,\; S({x},{v},{t}) \le \eta \cdot A({x},{v},{t})$
- `(hsat)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to S({x},{v},{0}) = \eta \cdot A({x},{v},{0})$
- `(hDnn)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - S({x},{v},{t})$
- `(hD0)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \mathrm{KE}({x},{v},{0}) - S({x},{v},{0}) = 0$
- `(hFlux)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \dot{K}({x},{v}) = 2 \cdot \pi / \hbar \cdot ({T\,x})({v},{v})$
- `(hFocus)` &nbsp; $\forall (x : M^{{4}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), ({g\,x})({v},{v}) = 0 \to \dot{A}({x},{v}) = ({\lambda i j \mapsto R_{{i}{j}}({x})})({v},{v})$
- `(hreg)` &nbsp; $\forall (f : M^{{4}} \to \mathbb{R}), (\forall (y : M^{{4}}) (a^{\prime} b : \mathrm{Fin}\,4), a \cdot T_{{a^{\prime}}{b}}({y}) = R_{{a^{\prime}}{b}}({y}) + f\,y \cdot g_{{a^{\prime}}{b}}({y})) \to (\forall (x : M^{{4}}) (\rho : \mathrm{Fin}\,4), \mathrm{PdiffAt}\,f\,\rho\,x) \wedge \mathrm{Differentiable}\,\mathbb{R}\,\lambda y \mapsto f\,y + 1/2 \cdot R({y})$
- `(conserv)` &nbsp; $\forall (x : M^{{4}}) (\nu : \mathrm{Fin}\,4), (\nabla\!\cdot {\lambda y a^{\prime} b \mapsto a \cdot T_{{a^{\prime}}{b}}({y})})_{{\nu}}({x}) = 0$

then

$$ \exists \Lambda, \forall (x : M^{{4}}) (\mu \nu : \mathrm{Fin}\,4), a \cdot T_{{\mu}{\nu}}({x}) = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

### `oneParticleBW_niceWedge_unconditional`

**QIQTH.Fock.CyclicWitness.oneParticleBW_niceWedge_unconditional** — *spine*  
Given $m,\ V,\ t$,

assume

- `(hm)` &nbsp; $0 < m$
- `(hVboost)` &nbsp; $\forall (t : \mathbb{R}) (x : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (V\,t)\,x = (\mathrm{boostUnitary}\,(2 \cdot \pi \cdot t))\,x$

then

$$ \mathrm{modUnitary}\,(\mathrm{niceWedgeStandardSubspace}\,m\,\cdots \,\cdots )\,t = V\,t $$

### `freeField_oneParticle_hFlux`

**QIQTH.Fock.freeField_oneParticle_hFlux** — *spine*  
Given $m,\ f,\ f^{\prime},\ B,\ \hbar,\ T_{kk}$,

assume

- `(hm)` &nbsp; $0 < m$
- `(hf2)` &nbsp; $\mathrm{MemLp}\,f\,2\,\mathrm{volume}$
- `(hf_int)` &nbsp; $\mathrm{Integrable}\,f\,\mathrm{volume}$
- `(hfd)` &nbsp; $\forall (x : \mathbb{R}), ({f})'({x})={f^{\prime}\,x}$
- `(hf'_meas)` &nbsp; $\mathrm{AEStronglyMeasurable}\,f^{\prime}\,\mathrm{volume}$
- `(hB)` &nbsp; $\forall (x : \mathbb{R}), \|f^{\prime}\,x\| \le B$
- `(hTkk)` &nbsp; $2 \cdot \pi / \hbar \cdot T_{kk} = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\theta) \cdot f^{\prime}\,\theta)).\mathrm{im}$

then

$$ ({\lambda t \mapsto \mathrm{inner}\,\mathbb{C}\,(\mathrm{toLp}\,f\,\mathrm{hf2})\,((\mathrm{modUnitary}\,(\mathrm{niceWedgeStandardSubspace}\,m\,\cdots \,\cdots )\,t)\,(\mathrm{toLp}\,f\,\mathrm{hf2}))})'({0})={i \cdot (2 \cdot \pi / \hbar \cdot T_{kk})} $$

### `freeField_component_hFlux`

**QIQTH.Fock.freeField_component_hFlux** — *spine*  
Given $m,\ f,\ f^{\prime},\ B,\ \hbar,\ \mathrm{kd},\ T_{kk}$,

assume

- `(hm)` &nbsp; $0 < m$
- `(hf2)` &nbsp; $\mathrm{MemLp}\,f\,2\,\mathrm{volume}$
- `(hf_int)` &nbsp; $\mathrm{Integrable}\,f\,\mathrm{volume}$
- `(hfd)` &nbsp; $\forall (x : \mathbb{R}), ({f})'({x})={f^{\prime}\,x}$
- `(hf'_meas)` &nbsp; $\mathrm{AEStronglyMeasurable}\,f^{\prime}\,\mathrm{volume}$
- `(hB)` &nbsp; $\forall (x : \mathbb{R}), \|f^{\prime}\,x\| \le B$
- `(hTkk)` &nbsp; $2 \cdot \pi / \hbar \cdot T_{kk} = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\theta) \cdot f^{\prime}\,\theta)).\mathrm{im}$
- `(hbridge)` &nbsp; $({\lambda t \mapsto \mathrm{inner}\,\mathbb{C}\,(\mathrm{toLp}\,f\,\mathrm{hf2})\,((\mathrm{modUnitary}\,(\mathrm{niceWedgeStandardSubspace}\,m\,\cdots \,\cdots )\,t)\,(\mathrm{toLp}\,f\,\mathrm{hf2}))})'({0})={i \cdot \mathrm{kd}}$

then

$$ \mathrm{kd} = 2 \cdot \pi / \hbar \cdot T_{kk} $$


## Born rule

*Target 1 — the Born rule, reductions and no-go*

### `finite_noCollapseBorn_fromNoncontextuality`

**QIQTH.BornJoinGleason.finite_noCollapseBorn_fromNoncontextuality** — *capstone*  
Given $m,\ n,\ d,\ E,\ M,\ P,\ k,\ \varepsilon$,

assume

- `(hP)` &nbsp; $\forall (a : \mathrm{Fin}\,m), \mathrm{IsEffect}\,(P\,a)$
- `(hcal)` &nbsp; $\forall (a : \mathrm{Fin}\,m), M.\mu\,(P\,a) = E.p\,a$
- `(hε)` &nbsp; $0 < \varepsilon$
- `(hn)` &nbsp; $0 < n$

then

$$ \exists \rho, \rho.\mathrm{PosSemidef} \wedge \rho.\mathrm{trace} = 1 \wedge (\forall (\omega : E.\Omega), \exists !h, \forall (t : \mathrm{Fin}\,n), \exists r\in (E.V\,\omega\,t).\mathrm{config}.\mathrm{active}, (E.V\,\omega\,t).\mathrm{ctx}.\mathrm{valueOf}\,r = h\,t) \wedge (\forall (a : \mathrm{Fin}\,m), E.p\,a = (\rho \cdot P\,a).\mathrm{trace}.\mathrm{re}) \wedge (\forall (h : \mathrm{Fin}\,n \to \mathrm{Fin}\,m), E.P.\mathrm{massSet}\,\{\omega|E.\mathrm{actualHist}\,\omega = h\} = w\,E.p\,h) \wedge E.P.\mathrm{massSet}\,\{\omega|{(n \cdot \varepsilon)}^{2} \le {(\mathrm{count}\,k\,(E.\mathrm{actualHist}\,\omega) - n \cdot E.p\,k)}^{2}\} \le E.p\,k \cdot (1 - E.p\,k) / (n \cdot {\varepsilon}^{2}) $$

### `finite_effect_gleason`

**QIQTH.EffectGleason.EffectMeasure.finite_effect_gleason** — *spine*  
Given $d,\ m$,
then

$$ \exists \rho, \rho.\mathrm{PosSemidef} \wedge \rho.\mathrm{trace} = 1 \wedge \forall (E : \mathrm{Mat}\,(\mathrm{Fin}\,d)\,(\mathrm{Fin}\,d)\,\mathbb{C}), \mathrm{IsEffect}\,E \to (m.\mu\,E) = (\rho \cdot E).\mathrm{trace} $$

### `positive_ray_certain_forces_born`

**QIQTH.GleasonSelector.positive_ray_certain_forces_born** — *spine*  
Given $n,\ \psi,\ w,\ E$,

assume

- `(hψ)` &nbsp; ${{\psi}}^{*} \cdot _{v} \psi = 1$
- `(hadd)` &nbsp; $\forall (A B : \mathrm{Mat}\,n\,n\,\mathbb{C}), w\,(A + B) = w\,A + w\,B$
- `(hhom)` &nbsp; $\forall (c : \mathbb{C}) (A : \mathrm{Mat}\,n\,n\,\mathbb{C}), w\,(c \cdot A) = c \cdot w\,A$
- `(hpsd)` &nbsp; $\forall (A : \mathrm{Mat}\,n\,n\,\mathbb{C}), \mathrm{NonnegC}\,(w\,(A.\mathrm{conjTranspose} \cdot A))$
- `(hray)` &nbsp; $w\,(\mathrm{vecMulVec}\,\psi\,({{\psi}}^{*})) = 1$
- `(hone)` &nbsp; $w\,1 = 1$

then

$$ w\,E = \mathrm{born}\,\psi\,E $$

### `continuous_additive_fMeasure_eq_born`

**QIQTH.RefinementBorn.continuous_additive_fMeasure_eq_born** — *spine*  
Given $n,\ f,\ w,\ k$,

assume

- `(hf)` &nbsp; $\mathrm{Continuous}\,f$
- `(h1)` &nbsp; $f\,1 \ne 0$
- `(hsum)` &nbsp; $\sum_{j} w\,j = 1$

then

$$ \mathrm{fMeasure}\,(f)\,w\,k = w\,k $$

### `decoherent_partition_additive`

**QIQTH.RecordGleason.decoherent_partition_additive** — *spine*  
Given $n,\ \psi,\ \iota,\ C,\ S$,

assume

- `(hdec)` &nbsp; $\mathrm{Decoherent}\,\psi\,C$

then

$$ \mathrm{born}\,\psi\,((\sum_{a S} C\,a).\mathrm{conjTranspose} \cdot \sum_{a S} C\,a) = \sum_{a S} \mathrm{born}\,\psi\,((C\,a).\mathrm{conjTranspose} \cdot C\,a) $$

### `finite_noCollapseBornRepresentation`

**QIQTH.BornJoin.ActualEnsemble.finite_noCollapseBornRepresentation** — *spine*  
Given $m,\ n,\ E,\ k,\ \varepsilon$,

assume

- `(hε)` &nbsp; $0 < \varepsilon$
- `(hn)` &nbsp; $0 < n$

then

$$ (\forall (\omega : E.\Omega), \exists !h, \forall (t : \mathrm{Fin}\,n), \exists r\in (E.V\,\omega\,t).\mathrm{config}.\mathrm{active}, (E.V\,\omega\,t).\mathrm{ctx}.\mathrm{valueOf}\,r = h\,t) \wedge (\forall (h : \mathrm{Fin}\,n \to \mathrm{Fin}\,m), E.P.\mathrm{massSet}\,\{\omega|E.\mathrm{actualHist}\,\omega = h\} = w\,E.p\,h) \wedge E.P.\mathrm{massSet}\,\{\omega|{(n \cdot \varepsilon)}^{2} \le {(\mathrm{count}\,k\,(E.\mathrm{actualHist}\,\omega) - n \cdot E.p\,k)}^{2}\} \le E.p\,k \cdot (1 - E.p\,k) / (n \cdot {\varepsilon}^{2}) $$

### `product_born_measure_unique`

**QIQTH.BornMeasureUniqueness.product_born_measure_unique** — *spine*  
Given $n,\ d,\ m,\ \rho,\ E,\ \mu,\ S$,

assume

- `(hρ)` &nbsp; $\rho.\mathrm{PosSemidef}$
- `(hE)` &nbsp; $\forall (k : \mathrm{Fin}\,m), (E\,k).\mathrm{PosSemidef}$
- `(hμ0)` &nbsp; $\mu\,\emptyset = 0$
- `(hμins)` &nbsp; $\forall (a : \mathrm{Fin}\,n \to \mathrm{Fin}\,m) (S : \mathrm{Finset}\,(\mathrm{Fin}\,n \to \mathrm{Fin}\,m)), a\notin S \to \mu\,(\mathrm{insert}\,a\,S) = \mu\,\{a\} + \mu\,S$
- `(hpt)` &nbsp; $\forall (\omega : \mathrm{Fin}\,n \to \mathrm{Fin}\,m), \mu\,\{\omega\} = \prod_{t} \mathrm{bornProb}\,\rho\,E\,(\omega\,t)$

then

$$ \mu\,S = ((\mathrm{kronN}\,\lambda x \mapsto \rho) \cdot \mathrm{eventEffect}\,E\,S).\mathrm{trace}.\mathrm{re} $$

### `chebyshev_freq`

**QIQTH.BornTypicalityFinite.chebyshev_freq** — *spine*  
Given $m,\ N,\ p,\ k,\ \varepsilon$,

assume

- `(hp)` &nbsp; $\forall (i : \mathrm{Fin}\,m), 0 \le p\,i$
- `(hp1)` &nbsp; $\sum_{i} p\,i = 1$
- `(hε)` &nbsp; $0 < \varepsilon$
- `(hN)` &nbsp; $0 < N$

then

$$ \sum_{\omega} w\,p\,\omega \le p\,k \cdot (1 - p\,k) / (N \cdot {\varepsilon}^{2}) $$

### `qiqth_born_typicality_conditional`

**QIQTH.BornTypicality.qiqth_born_typicality_conditional** — *spine*  
Given $\Gamma,\ \mathrm{Outcome},\ \mathrm{outcome},\ c,\ M,\ k$,
then

$$ \mathrm{expectedIndicator}\,\mathrm{outcome}\,M.\mu\,k = {c\,k}^{2} $$

### `born_distribution_realizable_conditional`

**QIQTH.NoBornFromNothing.born_distribution_realizable_conditional** — *nogo*  
Given $\Gamma,\ \mathrm{Outcome},\ \mathrm{outcome},\ c$,

assume

- `(h_surj)` &nbsp; $\mathrm{Surjective}\,\mathrm{outcome}$
- `(hc_norm)` &nbsp; $\sum_{k} {c\,k}^{2} = 1$

then

$$ \exists \mu, (\forall (\gamma : \Gamma), 0 \le \mu\,\gamma) \wedge \sum_{\gamma} \mu\,\gamma = 1 \wedge \forall (k : \mathrm{Outcome}), \mathrm{outcomeMarginal}\,\mathrm{outcome}\,\mu\,k = {c\,k}^{2} $$

### `decoherence_does_not_concentrate`

**QIQTH.NoConcentration.decoherence_does_not_concentrate** — *nogo*  
Given $c$,

assume

- `(h0)` &nbsp; $c\,0 \ne 0$
- `(h1)` &nbsp; $c\,1 \ne 0$

then

$$ 0 < \mathrm{branchWeight}\,c\,0 \wedge 0 < \mathrm{branchWeight}\,c\,1 $$

### `support_preservation_does_not_imply_measure_preservation`

**QIQTH.EquivarianceGap.support_preservation_does_not_imply_measure_preservation** — *nogo*  
then

$$ \exists T \mu, \mathrm{Bijective}\,T \wedge \mathrm{SupportPreserving}\,T \wedge \neg \mathrm{MeasurePreserving}\,T\,\mu $$

### `operational_data_insufficient`

**QIQTH.OperationalNoGo.operational_data_insufficient** — *nogo*  
then

$$ \exists \mathrm{outcome} \nu_{1} \nu_{2}, (\forall (k : \mathrm{Fin}\,2), \mathrm{marginal3to2}\,\nu_{1}\,\mathrm{outcome}\,k = \mathrm{marginal3to2}\,\nu_{2}\,\mathrm{outcome}\,k) \wedge \nu_{1} \ne \nu_{2} $$


## Lorentz covariance

*Target 2 — Lorentz covariance of the selection*

### `upvm_covariant_probability`

**QIQTH.LorentzSelectionStrong.upvm_covariant_probability** — *capstone*  
Given $\mathrm{Diam},\ G,\ P,\ A,\ B,\ C,\ g,\ D$,
then

$$ (\forall (x : P.X\,D), 0 \le \mathrm{uborn}\,B.\mathrm{toUniformBornData}\,D\,x) \wedge .\mathrm{sum}\,(\mathrm{uborn}\,B.\mathrm{toUniformBornData}\,D) = 1 \wedge \forall (x : P.X\,D), \mathrm{uborn}\,B.\mathrm{toUniformBornData}\,((A.\mathrm{act}\,g)\,D)\,((A.\gamma\,g\,D)\,x) = \mathrm{uborn}\,B.\mathrm{toUniformBornData}\,D\,x $$

### `evaluation_covariance`

**QIQTH.LorentzSelection.evaluation_covariance** — *spine*  
Given $\mathrm{Diam},\ P,\ g,\ \mathrm{lam},\ D$,
then

$$ \mathrm{selector}\,(\mathrm{actSection}\,g\,\mathrm{lam})\,(g.\mathrm{act}\,D) = (g.\gamma\,D)\,(\mathrm{selector}\,\mathrm{lam}\,D) $$

### `group_evaluation_covariance`

**QIQTH.LorentzSelectionStrong.group_evaluation_covariance** — *spine*  
Given $\mathrm{Diam},\ G,\ P,\ A,\ \mathrm{lam},\ g,\ D$,
then

$$ \mathrm{selector}\,(\mathrm{actSection}\,(A.\mathrm{toPoincare}\,g)\,\mathrm{lam})\,((A.\mathrm{act}\,g)\,D) = (A.\gamma\,g\,D)\,(\mathrm{selector}\,\mathrm{lam}\,D) $$

### `freeFieldMeasure_boost_invariant`

**QIQTH.FreeFieldTypicality.freeFieldMeasure_boost_invariant** — *spine*  
Given $m,\ \nu,\ e$,

assume

- `(inst._@.QIQTH.FreeFieldTypicality.4290387588._hygCtx._hyg.15)` &nbsp; $\mathrm{IsProbabilityMeasure}\,\nu$
- `(hν)` &nbsp; $\mathrm{map}\,(\mathrm{boostMap}\,e)\,\nu = \nu$

then

$$ \mathrm{map}\,(\mathrm{diagBoost}\,e)\,(\mathrm{freeFieldMeasure}\,\nu) = \mathrm{freeFieldMeasure}\,\nu $$

### `bh_typicalityMeasure_exists`

**QIQTH.BHTypicalityMeasure.bh_typicalityMeasure_exists** — *spine*  
Given $\iota,\ \alpha,\ \kappa,\ H,\ b,\ p,\ g$,

assume

- `(inst._@.QIQTH.BHTypicalityMeasure.2998898123._hygCtx._hyg.36)` &nbsp; $\forall (i : \iota), \mathrm{MeasurableSingletonClass}\,(\alpha\,i)$
- `(inst._@.QIQTH.BHTypicalityMeasure.2998898123._hygCtx._hyg.56)` &nbsp; $\mathrm{CompleteSpace}\,H$
- `(inst._@.QIQTH.BHTypicalityMeasure.2998898123._hygCtx._hyg.79)` &nbsp; $\forall (i : \iota), \mathrm{DiscreteTopology}\,(\alpha\,i)$
- `(inst._@.QIQTH.BHTypicalityMeasure.2998898123._hygCtx._hyg.88)` &nbsp; $\forall (i : \iota), \mathrm{Finite}\,(\alpha\,i)$
- `(hb)` &nbsp; $\mathrm{Orthonormal}\,\mathbb{C}\,b$
- `(hp)` &nbsp; $\forall (i : \kappa), 0 \le p\,i$
- `(hsum)` &nbsp; $\mathrm{Summable}\,p$
- `(hp1)` &nbsp; $\sum ' (i : \kappa), p\,i = 1$

then

$$ \exists \mu, \mathrm{IsProbabilityMeasure}\,\mu \wedge (\mathrm{diagNet}\,\mathrm{hb}\,\mathrm{hp}\,\mathrm{hsum}\,\mathrm{hp1}\,g).\mathrm{toFiniteMarginals}.\mathrm{IsLimit}\,\mu $$

### `fock_typicalityMeasure_exists`

**QIQTH.Fock.fock_typicalityMeasure_exists** — *spine*  
Given $\iota,\ \alpha,\ H,\ g$,

assume

- `(inst._@.QIQTH.Fock.FockTypicality.377538603._hygCtx._hyg.36)` &nbsp; $\forall (i : \iota), \mathrm{MeasurableSingletonClass}\,(\alpha\,i)$
- `(inst._@.QIQTH.Fock.FockTypicality.377538603._hygCtx._hyg.64)` &nbsp; $\forall (i : \iota), \mathrm{DiscreteTopology}\,(\alpha\,i)$
- `(inst._@.QIQTH.Fock.FockTypicality.377538603._hygCtx._hyg.73)` &nbsp; $\forall (i : \iota), \mathrm{Finite}\,(\alpha\,i)$

then

$$ \exists \mu, \mathrm{IsProbabilityMeasure}\,\mu \wedge (\mathrm{fockVacuumNet}\,g).\mathrm{toFiniteMarginals}.\mathrm{IsLimit}\,\mu $$

### `continuum_volume_selects`

**QIQTH.ContinuumSelection.continuum_volume_selects** — *spine*  
Given $H,\ S,\ \xi,\ n,\ s,\ k$,

assume

- `(inst._@.QIQTH.ContinuumSelection.1070711794._hygCtx._hyg.12)` &nbsp; $\mathrm{CompleteSpace}\,H$

then

$$ \mathrm{volume}\,\{\mathrm{seed}|\mathrm{selects}\,(\mathrm{contWeights}\,S\,\xi\,s)\,\mathrm{seed}\,k\} = {{\mathrm{contWeights}\,S\,\xi\,s\,k}} $$

### `no_signaling`

**QIQTH.Theorem7.Setup.no_signaling** — *spine*  
Given $S,\ x,\ a,\ y$,
then

$$ S.P\,x\,a\,y = S.\mathrm{PAlice}\,x\,a $$

### `bipartite_no_signaling`

**QIQTH.NoSignalingGeneral.bipartite_no_signaling** — *spine*  
Given $d_{1},\ d_{2},\ \beta,\ \rho,\ E,\ F$,

assume

- `(hF)` &nbsp; $\sum_{b} F\,b = 1$

then

$$ \sum_{b} (\rho \cdot \mathrm{kroneckerMap}\,(\lambda x_{1} x_{2} \mapsto x_{1} \cdot x_{2})\,E\,(F\,b)).\mathrm{trace} = (\rho \cdot \mathrm{kroneckerMap}\,(\lambda x_{1} x_{2} \mapsto x_{1} \cdot x_{2})\,E\,1).\mathrm{trace} $$

### `no_covariant_selector`

**QIQTH.CovariantGluing.no_covariant_selector** — *nogo*  
Given $\mathrm{State},\ \mathrm{History},\ \mathrm{actS},\ \mathrm{actH},\ \sigma,\ \Phi$,

assume

- `(equiv)` &nbsp; $\forall (\Phi : \mathrm{State}), \sigma\,(\mathrm{actS}\,\Phi) = \mathrm{actH}\,(\sigma\,\Phi)$
- `(hΦ)` &nbsp; $\mathrm{actS}\,\Phi = \Phi$
- `(hno)` &nbsp; $\forall (h : \mathrm{History}), \mathrm{actH}\,h \ne h$

then

$$ \bot $$

### `bool_swap_no_selector`

**QIQTH.CovariantGluing.bool_swap_no_selector** — *nogo*  
Given $\sigma$,

assume

- `(equiv)` &nbsp; $\forall (u : \mathrm{Unit}), \sigma\,u = !\sigma\,u$

then

$$ \bot $$
