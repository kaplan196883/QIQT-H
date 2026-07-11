/-
  BULK RELAXATION — the emergent geometry is the CONSERVED CHARGE of boundary decoherence
  (duality campaign, brick D4a).

  THE STATICS→DYNAMICS RUNG.  RC1–IC1 built the boundary relaxation: the record channel
  `T_s = e^{−s}·id + (1 − e^{−s})·dephase` under which records FORM (pointer basis as input,
  exponential einselection as theorem).  RC2 proved that its equilibria are (conditionally)
  Einstein states.  THIS brick upgrades the statics to a CONSERVATION LAW along the WHOLE
  approach to equilibrium:

  • THE LEDGER — `ledger A = (n ↦ A n n)`, the boundary's classical/geometric record data —
    is INVARIANT under the relaxation at every time (`ledger_Tsem_invariant`, the named
    principle over RC1's frozen diagonal).
  • THE CONSERVATION LAW — every LEDGER-FUNCTION (any functional of the state that depends
    only on the ledger) is a CONSERVED CHARGE of the boundary relaxation
    (`ledgerFunction_conserved`).  Instances proved here: the diagonal record/Born weights
    (`bornWeight_conserved`), the trace (`trace_conserved`), the EQUILIBRIUM ENTROPY
    `S(dephase A)` (`equilibriumEntropy_conserved` — well-defined on the ledger by
    `dephase_ledger_eq`), and on the held code the K2a counting trace
    (`tauCount_conserved`).  By the held K2a/JI chain the saturated equilibrium entropy
    reads as the AREA: `S = log N_C = cutτ = A_τ(C)/4G` (`log_NC_eq_cutTau`,
    `inducedScreenAreaTau`, `entropy_saturation_eq_area`, `Stau_eq_sum_wEnt` — CITED, not
    re-proved; its calibration conditions are unchanged).  The held area functionals
    (`inducedScreenArea`, `Stau`, `inducedScreenAreaTau`) are functions of the calibrated
    WEIGHTS/LINKS, not of a density argument; the weights of the SATURATED state are its
    ledger, and the state-side realization of "the area is conserved" is exactly instance
    (c) + instance (d): the equilibrium entropy and the counting trace never move.
  • THE CONTRAST — what is NOT a ledger-function DIES: every off-diagonal coherence decays
    at the exact exponential rate 1 (`coherence_decay`), and the flow converges to
    `dephase A`, whose ledger EQUALS the initial ledger.  Packaged as
    `geometry_is_conserved_charge`: THE BOUNDARY RELAXATION FORGETS EVERYTHING EXCEPT THE
    GEOMETRY.
  • THE METRIC TRAJECTORY — through the held E2 decoder (`AreaMap.reconstruct`, the
    explicit metric-from-area-data inverse), if the boundary state's area data is ANY
    ledger-function assignment, then the induced bulk metric trajectory along the entire
    relaxation is CONSTANT (`bulk_metric_frozen`), and when the initial data is the
    ray-probe data of a symmetric perturbation `h`, the frozen metric IS `h`
    (`bulk_metric_frozen_emergent`) — the first machine-checked DYNAMICAL bulk–boundary
    statement: boundary decoherence does not move the bulk metric; the metric is the
    fixed-point content of the boundary dynamics.  CONTRAST (CITED, not re-proved): under
    the held free/coherent dynamics the classical metric OSCILLATES as the graviton wave
    (OperatorEmergence Q4, `hHatT_wave` / `coherent_hHat`) — decoherence FREEZES geometry,
    coherent dynamics WAVES it.

  ⚠ MANDATORY FIREWALL.  This is CONSERVATION, not GENERATION: no bulk equation of motion
  is derived, and there is NO backreaction (the metric does not act on the boundary).  The
  E2 decoder link is at the held expectation-level dictionary (pointwise, linearized,
  chosen basis); the area/4G reading of the conserved entropy is the held K2a/JI
  calibration chain, CITED with its conditions unchanged.  Finite corner, single code;
  the record/pointer basis is an INPUT (RC1's firewall applies verbatim).  NOT bulk
  Einstein evolution, NOT the strong holographic principle, NOT quantum gravity.
  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.RecordChannel
import QIQTH.AreaDecoder

namespace QIQTH.BulkRelaxation

open QIQTH.QuantumEntropy QIQTH.Keystone QIQTH.RecordChannel

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## D4a.1 — the ledger and the ledger-function principle -/

/-- **The record ledger**: the diagonal record data of a boundary state — the boundary's
    classical/geometric content (Born weights, counts, and through the K2a/JI calibration
    the area data all read off it). -/
def ledger (A : Matrix ι ι ℂ) : ι → ℂ := fun n => A n n

/-- The ledger of the record readout is the original ledger — reading the ledger does not
    rewrite it. -/
theorem ledger_dephase (A : Matrix ι ι ℂ) : ledger (dephase A) = ledger A :=
  funext fun n => dephase_apply_eq A n

/-- **THE LEDGER IS INVARIANT** along the entire boundary relaxation: `T_s` never moves the
    record ledger, at any time `s` (the named principle over RC1's `Tsem_apply_eq`). -/
theorem ledger_Tsem_invariant (s : ℝ) (A : Matrix ι ι ℂ) :
    ledger (Tsem s A) = ledger A :=
  funext fun n => Tsem_apply_eq s A n

/-- **A ledger-function**: a functional of the boundary state that depends ONLY on the
    record ledger — the abstract shape of every "geometric" observable (Born weights,
    trace, equilibrium entropy, area data). -/
def LedgerFunction {α : Sort*} (F : Matrix ι ι ℂ → α) : Prop :=
  ∀ A B : Matrix ι ι ℂ, ledger A = ledger B → F A = F B

/-- **THE CONSERVATION LAW — every ledger-function is a conserved charge of the boundary
    relaxation**: `F (T_s A) = F A` for every ledger-function `F`, every time `s`, and
    every state `A`.  One line over `ledger_Tsem_invariant`; the content is the instances
    below (Born weights, trace, equilibrium entropy, counting trace) and the frozen bulk
    metric of D4a.3. -/
theorem ledgerFunction_conserved {α : Sort*} (F : Matrix ι ι ℂ → α)
    (hF : LedgerFunction F) (s : ℝ) (A : Matrix ι ι ℂ) : F (Tsem s A) = F A :=
  hF _ _ (ledger_Tsem_invariant s A)

/-- Ledger-functions take the same value on the relaxation's LIMIT `dephase A` as on the
    initial state — the charge survives all the way to equilibrium. -/
theorem ledgerFunction_dephase {α : Sort*} (F : Matrix ι ι ℂ → α)
    (hF : LedgerFunction F) (A : Matrix ι ι ℂ) : F (dephase A) = F A :=
  hF _ _ (ledger_dephase A)

/-! ## D4a.2 — the conserved charges: Born weights, trace, equilibrium entropy, count -/

/-- **Instance (a) — the record/Born weight** at record `n`: the diagonal probability
    weight `Re(A n n)` of readout outcome `n`. -/
def bornWeight (n : ι) (A : Matrix ι ι ℂ) : ℝ := (A n n).re

/-- The Born weight is a ledger-function. -/
theorem bornWeight_ledgerFunction (n : ι) : LedgerFunction (bornWeight (ι := ι) n) := by
  intro A B h
  show (A n n).re = (B n n).re
  exact congrArg Complex.re (congrFun h n)

/-- **The Born weights are conserved charges**: the record statistics never move along the
    relaxation. -/
theorem bornWeight_conserved (n : ι) (s : ℝ) (A : Matrix ι ι ℂ) :
    bornWeight n (Tsem s A) = bornWeight n A :=
  ledgerFunction_conserved _ (bornWeight_ledgerFunction n) s A

/-- **Instance (b) — the trace is a ledger-function.** -/
theorem trace_ledgerFunction : LedgerFunction (fun A : Matrix ι ι ℂ => A.trace) := by
  intro A B h
  show A.trace = B.trace
  rw [Matrix.trace, Matrix.trace]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply]
  exact congrFun h n

/-- **The trace is a conserved charge** (recovering RC1's `Tsem_trace` from the ledger
    principle). -/
theorem trace_conserved (s : ℝ) (A : Matrix ι ι ℂ) : (Tsem s A).trace = A.trace :=
  ledgerFunction_conserved _ trace_ledgerFunction s A

/-- The ledger determines the record readout ENTRYWISE: states with the same ledger have
    the same dephasing — the readout is a function of the ledger alone. -/
theorem dephase_ledger_eq {A B : Matrix ι ι ℂ} (h : ledger A = ledger B) :
    dephase A = dephase B := by
  ext n m
  by_cases hnm : n = m
  · subst hnm
    rw [dephase_apply_eq, dephase_apply_eq]
    exact congrFun h n
  · rw [dephase_apply_ne _ hnm, dephase_apply_ne _ hnm]

open Classical in
/-- The entropy of a matrix when it is a density, `0` otherwise (the total-function
    packaging of the von Neumann entropy — proof-irrelevant on densities). -/
noncomputable def diagEntropy (D : Matrix ι ι ℂ) : ℝ :=
  if h : IsDensity D then vonNeumannEntropy h else 0

/-- On densities, `diagEntropy` IS the von Neumann entropy. -/
theorem diagEntropy_of_isDensity {D : Matrix ι ι ℂ} (h : IsDensity D) :
    diagEntropy D = vonNeumannEntropy h := by
  unfold diagEntropy
  exact dif_pos h

/-- **Instance (c) — the equilibrium entropy** `A ↦ S(dephase A)`: the von Neumann entropy
    of the state's record readout — the entropy the relaxation converges TO.  At capacity
    saturation this is the AREA reading of the held K2a/JI chain:
    `S = log N_C = cutτ = A_τ(C)/4G` (`saturation_fixed`, `log_NC_eq_cutTau`,
    `inducedScreenAreaTau`, `entropy_saturation_eq_area` — CITED, not re-proved). -/
noncomputable def equilibriumEntropy (A : Matrix ι ι ℂ) : ℝ := diagEntropy (dephase A)

/-- On densities, the equilibrium entropy is the genuine von Neumann entropy of the
    readout. -/
theorem equilibriumEntropy_eq {A : Matrix ι ι ℂ} (h : IsDensity A) :
    equilibriumEntropy A = vonNeumannEntropy (dephase_isDensity h) :=
  diagEntropy_of_isDensity (dephase_isDensity h)

/-- **The equilibrium entropy is a ledger-function**: `dephase A` is determined entrywise
    by the ledger (`dephase_ledger_eq`), hence so is its entropy. -/
theorem equilibriumEntropy_ledgerFunction :
    LedgerFunction (equilibriumEntropy (ι := ι)) := fun _ _ h =>
  congrArg diagEntropy (dephase_ledger_eq h)

/-- **THE EQUILIBRIUM ENTROPY IS A CONSERVED CHARGE**: the entropy of the record readout —
    the quantity that reads as `A_τ/4G` at saturation via the held K2a/JI calibration
    (CITED) — never moves along the entire relaxation.  The geometry's thermodynamic
    reading is fixed from time zero. -/
theorem equilibriumEntropy_conserved (s : ℝ) (A : Matrix ι ι ℂ) :
    equilibriumEntropy (Tsem s A) = equilibriumEntropy A :=
  ledgerFunction_conserved _ equilibriumEntropy_ledgerFunction s A

/-- The conserved equilibrium entropy never exceeds capacity (the held K0 guard
    `vonNeumannEntropy_le_log_card` on the readout). -/
theorem equilibriumEntropy_le_capacity {A : Matrix ι ι ℂ} (h : IsDensity A) :
    equilibriumEntropy A ≤ Real.log (Fintype.card ι) := by
  rw [equilibriumEntropy_eq h]
  exact vonNeumannEntropy_le_log_card _

section Diamond

variable {E : Type*} [DecidableEq E] (L : LinkDims E) (C : Finset E)

/-- **Instance (d) — the K2a counting trace is a ledger-function** on the held code: the
    unnormalized microstate-counting trace `τ` of the Keystone (whose value on the record
    projector is the count whose log is the calibrated area, `log N_C = cutτ = A_τ(C)/4G`
    — the held `log_NC_eq_cutTau` / `inducedScreenAreaTau` K2a chain, CITED).  The held
    area functionals themselves (`inducedScreenArea`, `Stau`) are functions of the
    calibrated weights/links, not of a density argument; the counting trace is the
    state-side functional that connects formally. -/
theorem tauCount_ledgerFunction : LedgerFunction (tauCount L C) := by
  intro A B h
  rw [tauCount, tauCount]
  exact trace_ledgerFunction A B h

/-- **The counting trace is a conserved charge** of the boundary relaxation on the code:
    the microstate count (the area's combinatorial substrate, K2a CITED) never moves. -/
theorem tauCount_conserved (s : ℝ) (A : DiamondAlg L C) :
    tauCount L C (Tsem s A) = tauCount L C A :=
  ledgerFunction_conserved _ (tauCount_ledgerFunction L C) s A

end Diamond

/-! ## D4a.3 — the contrast: the non-ledger data decays, the package -/

/-- **THE CONTRAST — what is not conserved decays**: every off-diagonal coherence scales
    by the exact exponential factor `e^{−s}` and tends to `0` — the non-ledger
    (non-geometric) data dies at rate 1 while every ledger charge stays fixed. -/
theorem coherence_decay (A : Matrix ι ι ℂ) {n m : ι} (h : n ≠ m) :
    (∀ s : ℝ, Tsem s A n m = ((Real.exp (-s) : ℝ) : ℂ) * A n m) ∧
      Filter.Tendsto (fun s : ℝ => Tsem s A n m) Filter.atTop (nhds 0) := by
  refine ⟨fun s => Tsem_apply_ne s A h, ?_⟩
  have h0 := tendsto_Tsem_dephase A n m
  rwa [dephase_apply_ne A h] at h0

/-- **THE PACKAGE — the emergent geometry is the conserved charge of boundary
    decoherence.**  Along the boundary relaxation of any state `A`:
    (i)   every ledger-function is CONSTANT along the flow (the conservation law);
    (ii)  the ledger itself is invariant at every time;
    (iii) every off-diagonal (non-geometric) coherence decays exactly exponentially;
    (iv)  the flow converges to the record readout `dephase A`, and the limit's ledger
          EQUALS the initial ledger.
    The boundary relaxation forgets everything EXCEPT the geometry. -/
theorem geometry_is_conserved_charge (A : Matrix ι ι ℂ) :
    (∀ (α : Type*) (F : Matrix ι ι ℂ → α),
        LedgerFunction F → ∀ s : ℝ, F (Tsem s A) = F A) ∧
      (∀ s : ℝ, ledger (Tsem s A) = ledger A) ∧
      (∀ (s : ℝ) (n m : ι), n ≠ m →
        Tsem s A n m = ((Real.exp (-s) : ℝ) : ℂ) * A n m) ∧
      (∀ n m : ι, Filter.Tendsto (fun s : ℝ => Tsem s A n m) Filter.atTop
        (nhds (dephase A n m))) ∧
      ledger (dephase A) = ledger A :=
  ⟨fun _ F hF s => ledgerFunction_conserved F hF s A,
    fun s => ledger_Tsem_invariant s A,
    fun s _ _ h => Tsem_apply_ne s A h,
    fun n m => tendsto_Tsem_dephase A n m,
    ledger_dephase A⟩

/-! ## D4a.4 — the metric trajectory: the bulk metric is FROZEN

Through the held E2 decoder `AreaMap.reconstruct` (pointwise, linearized, chosen basis —
its honest labels apply verbatim).  CONTRAST (CITED, not re-proved): under the held
free/coherent dynamics the classical metric OSCILLATES as the graviton wave
(OperatorEmergence Q4, `hHatT_wave` / `coherent_hHat`) — decoherence freezes geometry,
coherent dynamics waves it. -/

open QIQTH.AreaMap

/-- **The bulk metric trajectory** induced by a path of ray-probe area data: at each
    boundary time `s`, decode the metric from the data via the held E2 decoder. -/
noncomputable def metricPath (d : ℝ → ((Fin 4 → ℝ) → ℝ)) (s : ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  reconstruct (d s)

/-- Constant area data induces a constant bulk metric (well-definedness of the decoder
    along a path). -/
theorem metricPath_const {d : ℝ → ((Fin 4 → ℝ) → ℝ)} {d0 : (Fin 4 → ℝ) → ℝ}
    (hconst : ∀ s, d s = d0) : metricPath d = fun _ => reconstruct d0 := by
  funext s
  show reconstruct (d s) = reconstruct d0
  rw [hconst s]

/-- **THE FIRST DYNAMICAL BULK–BOUNDARY STATEMENT — the bulk metric is FROZEN under
    boundary decoherence.**  If the boundary state path is the relaxation `s ↦ T_s A` and
    its area data is ANY ledger-function assignment (`hLF` — the honest abstraction, made
    non-vacuous by the D4a.2 instances), then the induced bulk metric trajectory is
    CONSTANT: boundary decoherence does not move the bulk metric — the metric is the
    fixed-point content of the boundary dynamics.  Conservation, NOT generation: no bulk
    equation of motion, no backreaction. -/
theorem bulk_metric_frozen (areaData : Matrix ι ι ℂ → ((Fin 4 → ℝ) → ℝ))
    (hLF : LedgerFunction areaData) (A : Matrix ι ι ℂ) :
    metricPath (fun s => areaData (Tsem s A)) = fun _ => reconstruct (areaData A) := by
  funext s
  show reconstruct (areaData (Tsem s A)) = reconstruct (areaData A)
  rw [ledgerFunction_conserved areaData hLF s A]

/-- **The frozen metric is the emergent metric**: when the initial area data is the
    ray-probe data of a symmetric perturbation `h` (the held E2 dictionary
    `reconstruct_areaVar`), the entire bulk metric trajectory along the boundary
    relaxation IS `h` — the emergent geometry, unmoved by decoherence, all the way to the
    record equilibrium. -/
theorem bulk_metric_frozen_emergent (areaData : Matrix ι ι ℂ → ((Fin 4 → ℝ) → ℝ))
    (hLF : LedgerFunction areaData) (A : Matrix ι ι ℂ)
    (h : Matrix (Fin 4) (Fin 4) ℝ) (hSym : h.IsSymm)
    (hinit : areaData A = fun v => areaVar (raySurf v) h) :
    metricPath (fun s => areaData (Tsem s A)) = fun _ => h := by
  rw [bulk_metric_frozen areaData hLF A, hinit, reconstruct_areaVar h hSym]

end QIQTH.BulkRelaxation
