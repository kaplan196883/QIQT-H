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
/-
  THE GENERATOR (G1–G6) — THE CAMPAIGN CHECKPOINT (all increments landed; axiom-free std-3,
  budget 0).

  HAVE: "The transported tower flow has a genuine self-adjoint unbounded generator: towerGen :=
  stoneGen (towerFlow) is a LinearPMap with IsSelfAdjoint towerGen (K = K† in Mathlib's adjoint
  sense), axiom-free, obtained by instantiating the general Stone-generator theorem with the
  five held Track-B group facts." "The cyclic vector is a zero-mode: Ω ∈ dom(towerGen) and
  towerGen Ω = 0, because the flow fixes Ω exactly." "The generator is explicitly computed on a
  dense core: every coerced pure component ↑(of C a) lies in dom(towerGen) with
  towerGen ↑(of C a) = ↑(of C ([H_C, a])), where H_C = diagonal(log gibbsWeight) — the
  finite-stage phases κ_nm = log w_n − log w_m of the held entry formula; the domain is
  therefore dense constructively, not only via Gårding mollification." "The generator commutes
  with its own flow: U_s maps dom(towerGen) into itself and towerGen (U_s ξ) = U_s (towerGen ξ)."

  HAVE NOT: "towerGen is NOT constructed from, and NOT claimed equal to, a Tomita modular
  Hamiltonian log Δ of the limit state — no Δ, J, S, separating property, KMS-at-the-limit, or
  von Neumann type is claimed. No spectral resolution (PVM) of the unbounded towerGen is
  claimed, and no exponential-recovery identity towerFlow t = exp(it·towerGen) is claimed — the
  recovery wall is open by design and the campaign does not cross it."
-/
/-
  THE SEPARATION (S1–S8) — THE CAMPAIGN CHECKPOINT (all increments landed; axiom-free std-3,
  budget 0).

  HAVE: "Ω is CYCLIC AND SEPARATING for the tower limit von Neumann algebra:
  `dense_span_towerRep_cyclicVec` + `towerCyclicVec_separating` — the standard-form HYPOTHESIS
  PAIR of Tomita–Takesaki theory, exhibited axiom-free on the tower Hilbert space." "Right
  multiplication by a corner element is BOUNDED with the weighted Frobenius constant
  `frobNormSq((rightConj a)ᴴ) = Σ_{n,m} ‖a n m‖²·(wₘ/wₙ)` and lies in the commutant of every
  stage algebra — hence commutes with the whole limit algebra by the bicommutant, purely
  algebraically."

  HAVE NOT: "No Tomita operator S₀, no modular operator Δ, no conjugation J, no KMS condition
  at the limit, and no type classification is constructed or claimed here — separation is the
  HYPOTHESIS for that theory, not the theory." "The right action is bounded with a weighted
  Frobenius (Hilbert–Schmidt) constant, NOT the C*-norm — never claimed contractive; and no
  right ⋆-anti-representation laws are stated: exactly the operators the separation argument
  needs, nothing more."
-/
/-
  THE TOMITA OPERATOR (T0_1–T0_6) — THE CAMPAIGN CHECKPOINT (all increments landed; axiom-free
  std-3, budget 0).

  HAVE: "The Tomita operator S₀ of the tower limit state is constructed on its classical orbit
  domain {TΩ : T ∈ towerLimitVN}: it is well-defined (Ω is separating), conjugate-linear,
  involutive, and densely defined; its action on the dense core of pure components is computed
  exactly (S₀ ↑(of C a) = ↑(of C aᴴ)); the commutant-side right multiplications R_a admit the
  exact adjoint R_a† = R_{ρ aᴴ ρ⁻¹} (the finite-stage σ₋ᵢ, computed — not analytically
  continued), witnessing the pairing ⟪T*Ω, R_aΩ⟫ = ⟪R_a†Ω, TΩ⟫ on a dense family; consequently
  S₀ is closable in the graph-limit sense (TₙΩ → 0 and Tₙ*Ω → v force v = 0)."

  HAVE NOT: "The closure S̄ is not constructed as an object, and no polar decomposition, no
  modular operator Δ, no modular conjugation J, no KMS condition of the limit state, and no von
  Neumann type classification is constructed or claimed; Mathlib's LinearPMap closure and
  adjoint theories cover only ℂ-linear (identity ring-hom) partial maps, and a conjugate-linear
  closure theory is not built here."
-/
/-
  THE CONJUGATE CLOSURE (CC1–CC7) — THE CAMPAIGN CHECKPOINT (CC1–CC5 + CC7 landed; CC6 — the
  semilinear re-bundle — CUT per the plan's unconditional pre-authorization: not needed by the
  Δ contract; axiom-free std-3, budget 0).

  HAVE: "The closure S̄ of the Tomita operator is constructed as an object — towerTomitaBar, the
  Mathlib closure of the ℝ-linear restriction of towerTomita₀, with the four new abstract
  theorems this required (the ℝ-restriction view of a conjugate-linear partial map, the
  sequence-criterion closability bridge, and the transfer theorems showing
  conjugate-homogeneity and the involution survive closure): S̄ is closed, extends S₀ with the
  orbit domain as a core, fixes Ω, acts as conjugate-transpose on pure components, is
  conjugate-homogeneous, and is FULLY involutive on its domain with trivial kernel and range
  equal to domain — all axiom-free, with no real inner product and no adjoint used anywhere."

  HAVE NOT: "The modular operator Δ, the conjugation J, and the polar decomposition are not
  constructed (the documented Δ contract — Tomita's F as the conjugate-linear adjoint through
  the sesquilinear pairing, then Δ := F∘S̄ ℂ-linear — is the named next campaign); no
  σ-semilinear graph or closure theory is contributed to Mathlib here (the ℝ-reduction
  sidesteps it; the σ-graph remains Mathlib's own open TODO); no KMS condition of the limit
  state and no von Neumann type is claimed."
-/
/-
  THE MODULAR OPERATOR (M1–M7) — THE CAMPAIGN CHECKPOINT (all increments landed; axiom-free
  std-3, budget 0).

  HAVE: "The modular operator of the tower limit state is constructed and computed: Tomita's F —
  the conjugate-linear adjoint of S̄ through the sesquilinear pairing ⟪Fy, x⟫ = ⟪S̄x, y⟫, built
  on the ∃-Riesz domain with no real inner product, no dual-space machinery, and no completeness
  argument — and Δ := F∘S̄, a ℂ-linear densely defined partial operator that is SYMMETRIC
  (IsFormalAdjoint Δ Δ), POSITIVE (⟪Δx, x⟫ = ‖S̄x‖² ≥ 0), CLOSABLE (Δ ≤ Δ† with Δ† closed),
  fixes Ω, and ACTS AS THE FINITE MODULAR AUTOMORPHISM ON THE DENSE PURE-COMPONENT CORE:
  Δ↑(of C a) = ↑(of C (modAut ρ_C a)) — the modular operator of the physics, computed."

  HAVE NOT: "Full self-adjointness Δ† = Δ is not proved — it is von Neumann's S̄*S̄ theorem,
  absent from Mathlib and named as the next target; no polar decomposition, no J, no Δ^{1/2} or
  Δ^{it} (no unbounded positive square-root or spectral theory for partial operators exists in
  the pin), no KMS condition of the limit state, and no von Neumann type is constructed or
  claimed; the classical equivalence of the ∃-Riesz adjoint domain with the boundedness domain
  is not formalized (it is not needed)."
-/
import QIQTH.TowerGNS.LimitVN

namespace QIQTH.TowerGNS

end QIQTH.TowerGNS
