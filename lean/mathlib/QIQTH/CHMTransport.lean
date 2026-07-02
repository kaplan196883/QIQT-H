/-
  J3 (HYPOTHESIS_DELETION_PLAN.md) — the abstract CHM transport theorem: `hCHM` REDUCED to named inputs.

  BINDING (consult): the positive-mass Bisognano–Wichmann theorem (`oneParticleBW_niceWedge_unconditional`,
  `m > 0`) must NOT be instantiated at `m = 0` — it is not applicable to the CFT vacuum, and nothing here does
  so. The honest increment is the ABSTRACT transport theorem: the CHM identification at every ball follows from
  a WEDGE-ONLY BW datum plus conformal transport.

  `CHMTransportData` — the named carried analytic inputs (structure fields, NEVER axioms):
  • `W`, `vac`         — the wedge standard subspace and the vacuum/probe state (standardness/RS is the
                          `StandardSubspace` typing itself);
  • `boost`, `hBW`     — the geometric wedge boost and the CARRIED **massless wedge BW** datum
                          `boost t vac = modUnitary W t vac` — ONE wedge identity (not one per ball);
  • `U`                — the vacuum-based conformal element per ball, a genuine unitary (`H ≃ₗᵢ[ℂ] H`);
                          the ball state is DEFINED as `U B vac` (vacuum-preserving conformal covariance);
  • `hflow`            — the wedge→ball GEOMETRIC conjugacy: the ball flow is the conformal image of the
                          wedge boost, `flow B t = U B ∘ boost t ∘ (U B)⁻¹`;
  • `hmodVac`          — the CARRIED modular transport (Tomita functoriality at the one-particle/
                          standard-subspace level): `modUnitary (S B) t (U B vac) = U B (modUnitary W t vac)`,
                          carried in its SMALLEST form — pointwise on the vacuum only, not operator-level
                          algebra conjugacy (deriving it from the RvD tower via projection transport +
                          Borel-FC unitary covariance is the named follow-on).

  THE THEOREM: `hCHM_of_conformal_transport` — from these, the CHM identification `flow B t (state B) =
  modUnitary (S B) t (state B)` holds at EVERY ball. COROLLARY: `toBallModularFamily` — C2b's carried per-ball
  `hCHM` field is DERIVED; every ball then inherits the forced Clausius datum (`transport_ballHeatFlux_spec`).
  HYPOTHESIS SHRUNK: hCHM (a per-ball physics identification) → hBW (one wedge BW datum) + hmodVac (modular
  functoriality) + geometric conjugacy data.

  ⚠ Honest scope: hBW stays a genuine carried analytic input (the massless wedge BW — the genuine massless
  discharge via a 1+1 chiral current or 3+1 conformal scalar is a follow-on campaign); hmodVac stays carried
  mathematics; free-field/RvD one-particle setting; NOT a derivation of gravity. Axiom-free, std-3.
-/
import Mathlib
import QIQTH.BallClausius

namespace QIQTH.BallModular

open QIQTH.StandardSubspaceModular QIQTH.SpectralTheorem QIQTH.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {Ball : Type*}

/-- **The CHM transport data** — the named carried analytic inputs from which the per-ball CHM identification
    is DERIVED: the wedge (`W`, `vac`, `boost`) with its single carried BW datum `hBW`; the per-ball conformal
    unitaries `U` with the geometric conjugacy `hflow`; and the carried modular transport `hmodVac` (Tomita
    functoriality, pointwise on the vacuum — its smallest form). -/
structure CHMTransportData (Ball : Type*) (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- the wedge standard subspace -/
  W : StandardSubspace H
  /-- the vacuum / wedge probe state -/
  vac : H
  /-- the geometric wedge boost flow -/
  boost : ℝ → H → H
  /-- CARRIED (named): the massless wedge BW datum — ONE wedge identity, never the `m>0` theorem at `m=0` -/
  hBW : ∀ t, boost t vac = modUnitary W t vac
  /-- the vacuum-based conformal element mapping the wedge to each ball (a genuine unitary) -/
  U : Ball → (H ≃ₗᵢ[ℂ] H)
  /-- the ball standard subspaces (the conformal-image wedges) -/
  S : Ball → StandardSubspace H
  /-- the geometric conformal (CHM) flow of each ball -/
  flow : Ball → ℝ → H → H
  /-- the wedge→ball GEOMETRIC conjugacy: the ball flow is the conformal image of the wedge boost -/
  hflow : ∀ B t x, flow B t x = U B (boost t ((U B).symm x))
  /-- CARRIED (named): the modular transport (Tomita functoriality), pointwise on the vacuum -/
  hmodVac : ∀ B t, modUnitary (S B) t (U B vac) = U B (modUnitary W t vac)

/-- The ball probe state is the conformal image of the vacuum (vacuum-preserving conformal covariance is
    DEFINITIONAL here, not carried). -/
def CHMTransportData.state (D : CHMTransportData Ball H) (B : Ball) : H := D.U B D.vac

/-- **J3 THEOREM — the CHM identification at EVERY ball from the named transport inputs:** the ball's
    geometric conformal flow acts on the ball state as its modular flow. C2b's per-ball carried `hCHM` is
    now a consequence of ONE wedge BW datum + geometric conjugacy + modular functoriality. -/
theorem hCHM_of_conformal_transport (D : CHMTransportData Ball H) (B : Ball) (t : ℝ) :
    D.flow B t (D.state B) = modUnitary (D.S B) t (D.state B) := by
  rw [CHMTransportData.state, D.hflow B t, LinearIsometryEquiv.symm_apply_apply, D.hBW t]
  exact (D.hmodVac B t).symm

/-- If the operator-level algebra conjugacy holds (`modUnitary (S B) t ∘ U = U ∘ modUnitary W t`), the carried
    pointwise field follows — `hmodVac` is the WEAKEST form of the transport input. -/
theorem hmodVac_of_operator_conj (W : StandardSubspace H) (vac : H) (U : Ball → (H ≃ₗᵢ[ℂ] H))
    (S : Ball → StandardSubspace H)
    (hconj : ∀ B t x, modUnitary (S B) t (U B x) = U B (modUnitary W t x)) :
    ∀ B t, modUnitary (S B) t (U B vac) = U B (modUnitary W t vac) :=
  fun B t => hconj B t vac

/-- **J3 COROLLARY — C2b's `hCHM` field is DERIVED.** A `CHMTransportData` (plus the per-ball domain/spectral
    conditions of the derived modular machinery) yields a full `BallModularFamily` whose `hCHM` is the
    transport THEOREM, not a carried identification. -/
noncomputable def CHMTransportData.toBallModularFamily (D : CHMTransportData Ball H)
    (hdom : ∀ B, D.state B ∈ (PVM_of_selfAdjoint (rvdRC (D.S B))
      (rvdRC_isSelfAdjoint (D.S B))).fcDomain
      (fun ω : spectrum ℝ (rvdRC (D.S B)) => kFn ω.val))
    (hspec : ∀ B, ∀ ω : spectrum ℝ (rvdRC (D.S B)),
      (ω : spectrum ℝ (rvdRC (D.S B))).val ∈ Set.Ioo (0 : ℝ) 2) :
    BallModularFamily Ball H where
  S := D.S
  state := D.state
  flow := D.flow
  hCHM := fun B t => hCHM_of_conformal_transport D B t
  hdom := hdom
  hspec := hspec

/-- **End-to-end:** under the named transport inputs, every ball inherits the FORCED Clausius datum — the
    correlator derivative of the ball's own conformal flow is `i·(−S_B)` (the first-law data the bridge
    assembly consumes), now downstream of the transport THEOREM rather than a carried per-ball `hCHM`. -/
theorem transport_ballHeatFlux_spec (D : CHMTransportData Ball H)
    (hdom : ∀ B, D.state B ∈ (PVM_of_selfAdjoint (rvdRC (D.S B))
      (rvdRC_isSelfAdjoint (D.S B))).fcDomain
      (fun ω : spectrum ℝ (rvdRC (D.S B)) => kFn ω.val))
    (hspec : ∀ B, ∀ ω : spectrum ℝ (rvdRC (D.S B)),
      (ω : spectrum ℝ (rvdRC (D.S B))).val ∈ Set.Ioo (0 : ℝ) 2) (B : Ball) :
    HasDerivAt (fun t : ℝ => inner ℂ (D.state B) (D.flow B t (D.state B)))
      (Complex.I * ((ballHeatFlux (D.toBallModularFamily hdom hspec) B : ℝ) : ℂ)) 0 :=
  ballHeatFlux_spec (D.toBallModularFamily hdom hspec) B

end QIQTH.BallModular
