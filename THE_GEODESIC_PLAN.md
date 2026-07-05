# THE GEODESIC ODE — local existence/uniqueness (the foundation stone; RNC-existence gated behind it)

**Status:** SCOPED (fable consult verified against pin v4.30.0). **Track:** QG / curved-G. **Commits LOCAL ONLY.**

## Binding verdict
The clean, buildable-now brick after the RNC campaign: the **geodesic ODE** on the component space
`Point n = Fin n → ℝ` — the curve `γ` with `γ'' + Γ(γ)(γ',γ') = 0` — has **local existence + uniqueness** via
Mathlib's Picard–Lindelöf (`Analysis/ODE/PicardLindelof.lean`) + `ODE_solution_unique` (`Analysis/ODE/Gronwall.lean`),
rewriting the 2nd-order system as a 1st-order field `F(x,v)=(v, −Γ(x)(v,v))` on `Point n × Point n` (finite-dim ⟹
`CompleteSpace`). **HONEST HAVE-NOT (binding):** this is geodesic EXISTENCE only. It does **NOT** discharge the
RNC normal-coordinate gauge (that needs the exponential map's C¹-ness, hence **smooth dependence of ODE solutions
on the initial condition** — a theorem Mathlib genuinely LACKS, only Lipschitz dependence is present; a research-
grade Mathlib PR), and does **NOT** move numerical-G. Never claim RNC-existence, an exp-map, or numerical-G.

## The gate behind this brick (why RNC-existence stops here)
metric → Levi-Civita (done) → **geodesics (existence, THIS brick)** → ⟨WALL: smooth dependence of the geodesic
flow on `v` ⟩ → `exp_p` C¹ + `D exp_p(0)=id` + inverse function theorem → normal coordinates → derive the gauge.
The WALL (`ContDiff`/variational dependence on initial conditions) is absent from Mathlib; the carried
normal-coordinate gauge (`hgauge`, `RNCExpansion.lean`) is the honest geometric input to stop at.

## Increments
- [ ] **GEO1 — the geodesic field + local existence/uniqueness (std-3).** Define `geodesicField g gi : (Point n ×
  Point n) → (Point n × Point n) := fun (x,v) => (v, fun i => −∑_{j,k} christoffel g gi i j k x * v j * v k)`; prove
  `ContDiff ℝ 1 (geodesicField …)` from the carried `christoffel` smoothness (`contDiff_pi`/`_fst`/`_snd` + products);
  obtain a local solution `γ` with `γ t₀ = (x₀,v₀)`, `HasDerivAt γ (geodesicField (γ t)) t` on an interval
  (`ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`, PicardLindelof.lean); uniqueness
  via `ODE_solution_unique`. Optionally repackage the first component as the geodesic curve with
  `γ'' + Γ(γ)(γ',γ') = 0`. Risk: LOW (the only work is the `ContDiff` assembly of the field).

## Verbatim HAVE / HAVE-NOT
- **HAVE:** "The geodesic ODE of a component connection has local existence and uniqueness, via Mathlib's
  Picard–Lindelöf on the phase space `Point n × Point n` — component geodesics exist and are unique. Axiom-free std-3."
- **HAVE NOT:** "Geodesic EXISTENCE only. It does NOT build the exponential map or normal coordinates, does NOT
  discharge the carried RNC gauge (gated on smooth dependence of ODE solutions on initial conditions — absent from
  Mathlib), and does NOT move numerical-G (N, Λ_s, E/ξ remain). The carried normal-coordinate gauge stays the honest
  curved-G input."

## Failure modes
- The `ContDiff` assembly of `geodesicField` fiddly ⟹ land existence at `ContDiff ℝ 1` (enough for Picard–Lindelöf),
  don't chase `⊤`. If the exact PicardLindelof lemma's hypotheses mismatch, checkpoint with the precise goal.
- Do NOT attempt smooth-dependence-on-IC / the exp-map — that's the research-grade Mathlib gap; stop at existence.

## Discipline
`lake build QIQTH.<module>` green; `#print axioms` std-3; budget 0; AxiomAudit pins; wire QIQTH.lean; ONE commit
LOCAL ONLY (no push) with the Co-Authored-By trailer; update this plan + inventory. NO `sorry`; NEVER claim
RNC-existence, an exp-map, or numerical-G.

## Progress log
- **2026-07 (scoped):** consult (fable, high) — geodesic ODE existence buildable std-3 (Picard–Lindelöf PRESENT);
  RNC-existence gated on the ABSENT "smooth dependence on initial conditions" (Mathlib has only Lipschitz) — the
  carried normal-coordinate gauge is the honest stopping point. (Consult's "radial→hgauge std-3/4" claim corrected:
  the `∂Γ(0)` content is at THIRD order in `pd` ⟹ std-5, gated on third-order pd/Schwarz — not built.)
