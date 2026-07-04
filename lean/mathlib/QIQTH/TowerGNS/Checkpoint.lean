/-
  THE REPRESENTATION — CHECKPOINT (THE_REPRESENTATION_PLAN.md, R1–R9 complete).

  This is a MARKER MODULE: it imports the capstone and declares nothing. Its docstring is the
  binding honest-scope statement of what the tower-GNS campaign has and has not established.

  HAVE: "One Hilbert space — the completion of the semidefinite Gibbs-GNS pre-space on the
  direct sum of all finite corners — carrying compatible unital ⋆-representations of every
  corner algebra (π_{C′} ∘ cornerEmbed = π_C for all C ⊆ C′), a unit cyclic vector Ω
  implementing every corner Gibbs state as a vector state (⟪Ω, π_C(a)Ω⟫ = φ_C(a)), and the
  directed-union limit von Neumann algebra towerLimitVN = limitVN of the representation
  images, with membership characterized by SOT-approximation from the finite stages — all
  axiom-free."

  HAVE NOT: "The type of towerLimitVN is not classified — no factor, no ITPFI identification,
  no III₁ claim is made or proved (the T3 fingerprint stays arithmetic; Araki–Woods 1968 and
  Connes 1973 stay cited, never invoked); Ω is not shown separating, the modular theory of the
  limit state on the completion is not constructed, and the representations are not shown
  isometric."

  The increments:
  R1 — EmbedTrans.lean: tower transitivity — the one missing T7 lemma (cornerEmbed_trans).
  R2 — StageInner.lean: the per-stage GNS form gnsInner + pairInner_embed (stability under a common deep stage).
  R3 — PreSpace.lean: the pre-Hilbert space — TowerPre synonym, rawInner, stage collapse, semidefinite Core, completion TowerGNS.
  R4 — Germ.lean: the germ identity towerGerm (the direct-limit gluing dies in the completion) + towerCyclicVec.
  R5 — StageBound.lean: the GNS boundedness inequality — the Frobenius bound (never the C*-norm).
  R6 — LeftMul.lean: the bounded pre-operator towerLeftMul (left multiplication after embedding, norm-bounded).
  R7 — Representation.lean: towerRep — the unital ⋆-representation of every corner, compatible with the tower (towerRep_cornerEmbed).
  R8 — CyclicVector.lean: Ω implements every corner Gibbs state as a vector state and its orbit is dense (cyclicity).
  R9 — LimitVN.lean: the capstone — towerStageAlg, towerStageAlg_mono, towerLimitVN, mem_towerLimitVN_iff, towerVectorState_stage, freqTowerLimitVN.
-/
import Mathlib
import QIQTH.TowerGNS.CyclicVector
/-
  THE TRANSPORT (B1–B8) — THE CAMPAIGN CHECKPOINT (Track B of
  THE_TRANSPORT_AND_ACCOUNTING_PLAN.md; all increments landed INCLUDING the B7 strong-continuity
  stretch; axiom-free std-3, budget 0).

  HAVE: "We have the transported Gibbs modular flow as a one-parameter unitary group on the
  tower GNS space — U_t obtained by isometric extension of the per-corner flows through the
  completion, with U_0 = 1, the group law U_t U_s = U_{t+s}, adjoint U_t* = U_{−t}, invariance
  of the cyclic vector U_t Ω = Ω, the implementation theorem U_t π_C(a) U_{−t} = π_C(σ_t a) at
  every finite stage, and invariance of the limit von Neumann algebra towerLimitVN under
  conjugation by the flow — all axiom-free." (The B7 stretch SHIPPED: the group is moreover
  STRONGLY CONTINUOUS — continuous_towerFlow_apply.)

  HAVE NOT: "We do not have the modular theory of the limit: no Tomita operator, Δ, or J on the
  completion is constructed, Ω is not shown separating, no analytic (strip) KMS condition for
  the limit state is proved — only the finite-stage boundary identity is displayed — and no
  type is classified; U_t is defined by transport of the finite corner flows, not derived from
  the limit state." (With B7 shipped, strong continuity IS claimed; the Stone generator is NOT —
  the named post-campaign hook into the held Spectral/Stone tower.)
-/
import QIQTH.TowerGNS.LimitVN

namespace QIQTH.TowerGNS

end QIQTH.TowerGNS
