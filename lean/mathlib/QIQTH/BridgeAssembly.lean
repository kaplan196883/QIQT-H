/-
  BRIDGE ASM — the assembly: the FGHMVR skeleton instantiated with the bridge's REAL parts.

  ★ SCOPE (BRIDGE_PLAN.md, GPT-5.5-pro-verified; the FINAL increment). The G1 skeleton
    (`allBall_firstLaw_iff_residual_zero`: first law at every probe ⟺ residual = 0) was proven over abstract
    carried inputs. Here it is instantiated with the objects the bridge built:
  • **residual** := `einsteinSymbol k h` — the FULL linearized Einstein tensor of A1 (proven symmetric here,
    `einsteinSymbol_isSymm`, so it lives in the symmetric submodule where the probes separate);
  • **probes** := the ray AREA probes `areaProbe (raySurf v)` of A2 — genuinely geometric linear functionals,
    with A2's `area_probes_separate` supplying G1's `Separating` hypothesis as a THEOREM (not carried!);
  • **δK** := the ball first-law data — supplied per ball by C1/C2b (`ballHeatFlux`: the modular Clausius datum,
    FORCED at every ball given BW/CHM); its identification with the geometric area pairing of the residual is the
    carried **Iyer–Wald** input `hIW` (bridging the modular Hilbert space and the finite symbol space is exactly
    what Iyer–Wald supplies — carried, never an axiom);
  • **δS = δA/4G** — the CARRIED Clausius/area law (the one irreducible physical input), with `G` carried.

  Results (all axiom-free, std-3):
  • `bridge_firstLaw_iff_einstein` — **THE ASSEMBLED SKELETON**: given the carried Iyer–Wald identity at the ray
    probes, the entanglement first law `δS = δK` at EVERY probe ⟺ `einsteinSymbol k h = 0` — the emergent
    perturbation satisfies linearized vacuum Einstein. The separation side is now a PROVEN geometric fact.
  • `bridge_conditional` — **THE JACOBSON-SHAPE CAPSTONE**: carried area law (`δS = δA/4G`) + carried
    modular-geometric matching (`δK = δA/4G`) + carried Iyer–Wald ⟹ the emergent graviton satisfies linearized
    Einstein. The exact conditional structure of "entanglement + area law ⟹ Einstein", assembled from real parts.

  ⚠ HONEST STATUS — what this is and is not. This closes the bridge plan's LINEARIZED, CONDITIONAL assembly:
    every derived piece is a theorem (A1 anchor + Bianchi; A2 probes + separation; B1/B2 coupling + equivalence
    principle; C1/C2 forced Clausius data), and every physical input is an EXPLICIT hypothesis (Clausius/area law,
    Iyer–Wald, BW/CHM, genericity, `G`). It is NOT a derivation of gravity: removing those carried inputs —
    background independence, the nonlinear completion, the area law from counting, the value of `G` — is
    ingredient D, the open quantum-gravity problem. NEVER claim QG solved or the mechanism gap closed.
-/
import Mathlib
import QIQTH.LinearizedEinstein
import QIQTH.AreaEmergence

namespace QIQTH.BridgeASM

open QIQTH.GravDyn QIQTH.LinEinstein QIQTH.AreaMap

/-- The submodule of **symmetric** 4×4 perturbations — where the metric perturbation and the Einstein residual
    live, and where the area probes separate (A2). -/
def symmMat : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ) where
  carrier := {A | A.IsSymm}
  add_mem' := by
    intro A B hA hB
    simp only [Set.mem_setOf_eq, Matrix.IsSymm, Matrix.transpose_add] at *
    rw [hA, hB]
  zero_mem' := by simp [Matrix.IsSymm]
  smul_mem' := by
    intro c A hA
    simp only [Set.mem_setOf_eq, Matrix.IsSymm, Matrix.transpose_smul] at *
    rw [hA]

/-- **The linearized Einstein tensor of a symmetric perturbation is symmetric** — the residual lives in
    `symmMat`. -/
theorem einsteinSymbol_isSymm (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ) (hSym : e.IsSymm) :
    (einsteinSymbol k e).IsSymm := by
  unfold Matrix.IsSymm
  ext i j
  rw [Matrix.transpose_apply]
  have he : e j i = e i j := hSym.apply i j
  have hm : minkMetric j i = minkMetric i j := by
    unfold minkMetric
    rcases eq_or_ne i j with rfl | hij
    · rfl
    · rw [Matrix.diagonal_apply_ne _ hij.symm, Matrix.diagonal_apply_ne _ hij]
  simp only [einsteinSymbol, ricciSymbol, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
    smul_eq_mul]
  rw [he, hm]
  ring

/-- **The ray area probes on the symmetric sector** — A2's geometric linear functionals, restricted to `symmMat`:
    exactly the `P : Ball → E →ₗ[ℝ] ℝ` family the G1 skeleton consumes (`Ball` = the ray tangents). -/
noncomputable def rayProbe (v : Fin 4 → ℝ) : symmMat →ₗ[ℝ] ℝ :=
  (areaProbe (raySurf v)).comp symmMat.subtype

/-- **G1's separating hypothesis is a PROVEN geometric fact** on the symmetric sector: the ray area probes
    separate (A2's `area_probes_separate`) — no longer carried. -/
theorem rayProbe_separating : Separating rayProbe := by
  intro e he
  have h0 : (e : Matrix (Fin 4) (Fin 4) ℝ) = 0 :=
    area_probes_separate (e : Matrix (Fin 4) (Fin 4) ℝ) e.2 (fun v => he v)
  exact Subtype.ext h0

/-- The Einstein residual as an element of the symmetric sector. -/
noncomputable def einsteinResidual (k : Fin 4 → ℝ) (h : Matrix (Fin 4) (Fin 4) ℝ)
    (hSym : h.IsSymm) : symmMat :=
  ⟨einsteinSymbol k h, einsteinSymbol_isSymm k h hSym⟩

/-- **ASM — THE ASSEMBLED FGHMVR SKELETON.** With the carried Iyer–Wald identity `hIW` (the first-law deficit at
    each ray probe equals the probe's area pairing with the Einstein residual — the bridge between the modular
    first-law data (C1/C2b) and the geometric symbol space), the entanglement first law at EVERY probe is
    EQUIVALENT to the linearized vacuum Einstein equation for the emergent perturbation:
    `(∀ v, δS v = δK v) ⟺ einsteinSymbol k h = 0`. G1 instantiated with real parts — the probes are A2's
    geometric area functionals and the separation is PROVEN (`rayProbe_separating`), not carried. -/
theorem bridge_firstLaw_iff_einstein (k : Fin 4 → ℝ) (h : Matrix (Fin 4) (Fin 4) ℝ)
    (hSym : h.IsSymm) (δS δK : (Fin 4 → ℝ) → ℝ)
    (hIW : ∀ v : Fin 4 → ℝ, δK v - δS v = areaVar (raySurf v) (einsteinSymbol k h)) :
    (∀ v : Fin 4 → ℝ, δS v = δK v) ↔ einsteinSymbol k h = 0 := by
  have hmain := allBall_firstLaw_iff_residual_zero rayProbe rayProbe_separating
    (einsteinResidual k h hSym) δS δK (fun v => hIW v)
  rw [hmain]
  constructor
  · intro hz
    have := congrArg (Subtype.val) hz
    simpa [einsteinResidual] using this
  · intro hz
    exact Subtype.ext (by simpa [einsteinResidual] using hz)

/-- **ASM CAPSTONE — the conditional Jacobson-shape assembly.** Carried inputs, each an explicit hypothesis:
    the **Clausius/area law** `δS = δA/4G` (the one irreducible physical input), the **modular-geometric
    matching** `δK = δA/4G` (the ball first-law datum — supplied by C1/C2b's forced Clausius data — matches the
    area change; Jacobson's "heat = area"), and the **Iyer–Wald identity** `hIW`. Conclusion: the emergent
    perturbation satisfies **linearized vacuum Einstein**, `einsteinSymbol k h = 0`. The complete conditional
    structure "entanglement + area law ⟹ Einstein", assembled from the bridge's real parts. ⚠ CONDITIONAL —
    the carried inputs are the physics; removing them is ingredient D (the open QG problem). NOT a derivation
    of gravity; linearized, free, flat. -/
theorem bridge_conditional (k : Fin 4 → ℝ) (h : Matrix (Fin 4) (Fin 4) ℝ) (hSym : h.IsSymm)
    (G : ℝ) (δA δS δK : (Fin 4 → ℝ) → ℝ)
    (hClausius : ∀ v, δS v = δA v / (4 * G))
    (hGeom : ∀ v, δK v = δA v / (4 * G))
    (hIW : ∀ v : Fin 4 → ℝ, δK v - δS v = areaVar (raySurf v) (einsteinSymbol k h)) :
    einsteinSymbol k h = 0 := by
  rw [← bridge_firstLaw_iff_einstein k h hSym δS δK hIW]
  intro v
  rw [hClausius v, hGeom v]

end QIQTH.BridgeASM
