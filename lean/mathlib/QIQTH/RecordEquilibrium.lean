/-
  RECORD EQUILIBRIUM — the second law with rigidity and the E4 join: the boundary dynamics'
  equilibria are geometry (RC campaign, brick RC2).

  Brick RC1 (`RecordChannel.lean`) built the record-dephasing semigroup
  `T_s = e^{−s}·id + (1 − e^{−s})·dephase` on the held finite code: records FORM
  (`tendsto_Tsem_dephase`), entropy grows (`entropy_Tsem_ge`), and the relative entropy to
  every record equilibrium is a Lyapunov functional (`relEntropy_Tsem_le`).  THIS brick adds
  the missing halves and composes them with the held E4 gravity capstone:

  • THE SECOND LAW WITH RIGIDITY (the equality case of RC1's entropy production) —
    `entropy_production_zero_iff`: `S(dephase A) = S(A)` **iff** `dephase A = A` — entropy
    production under record formation vanishes EXACTLY at the records.  Route: RC1's
    cross-entropy identity gives `D(A‖dephase A) = S(dephase A) − S(A)`, and the held Klein
    FAITHFULNESS (`relEntropy_eq_zero`, the tracked equality case of Klein's inequality)
    forces `A = dephase A` at zero production.  Strict form `entropy_strict_increase`:
    off-equilibrium, `S(A) < S(dephase A)` — a genuine second law, with its rigidity.
  • THE FLOW PRESERVES (NON-)EQUILIBRIUM AT FINITE TIME — `Tsem_record_iff`: for EVERY real
    `s`, `T_s A` is a record iff `A` is (off-diagonal entries scale by `e^{−s} ≠ 0`); the
    semigroup never creates or destroys equilibrium in finite time — records are reached
    only in the `s → ∞` limit.  Strict entropy gap `entropy_Tsem_strict`: off-equilibrium,
    `S(T_s A) < S(dephase A)` for all `s ≥ 0` — the flow never exhausts the entropy budget
    in finite time.
  • THE E4 JOIN — `record_dynamics_einstein`: the held E4 capstone
    `code_equilibrium_einstein` re-exported with the per-ray references REQUIRED to be
    record equilibria (`IsRecordEquilibrium`, = `Tsem`-fixed points for every `s > 0` by
    `isRecordEquilibrium_iff_Tsem_fixed`).  "Equilibrium" is upgraded from a bare label on
    a state to a DYNAMICAL notion — a fixed point (attractor) of the RC1 boundary
    semigroup — so the composed theorem reads: **states the boundary dynamics relaxes to
    satisfy linearized vacuum Einstein** (with E4's ray-path/BW/derivative/Iyer–Wald data
    still carried, honestly).  HONESTY NOTE: `code_equilibrium_einstein`'s PROOF does not
    consume any stationarity property of the reference beyond the `RayPathFamilyRealizes`
    data, so inside `record_dynamics_einstein` the hypothesis `hEq` is a labelling upgrade,
    not load-bearing.  The GENUINE dynamical link is delivered separately:
    `record_reference_stationary` (E4's references are fixed points of `T_s` at every time)
    and `record_reference_lyapunov` (perturbations relax back: the relative entropy of ANY
    positive density to each E4 reference is non-increasing along the flow — the references
    are Lyapunov-STABLE attractors of the boundary dynamics).
  • THE PACKAGE — `boundary_dynamics_equilibria_are_geometry`: one conjunction, per
    equilibrium code: (i) the references are stationary under the record channel,
    (ii) they are Lyapunov-stable (relative-entropy contraction), and (iii) the emergent
    perturbation satisfies linearized vacuum Einstein.  The boundary dynamics' equilibria
    ARE geometry.

  ⚠ MANDATORY FIREWALL.  E4's carried inputs STAY carried: the per-ray BW identification,
  the analytic derivative data, and the Iyer–Wald identity are structure fields of
  `RayPathFamilyRealizes` (never axioms).  The record/pointer basis is an INPUT (RC1's
  firewall).  PosDef per the held conventions; finite, single code corner; linearized,
  free, flat.  NOT bulk reconstruction, NOT the strong holographic principle, NOT quantum
  gravity.  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.RecordChannel
import QIQTH.CodeEquilibrium

namespace QIQTH.RecordEquilibrium

open QIQTH.QuantumEntropy QIQTH.Keystone QIQTH.Entropy QIQTH.RecordChannel
open QIQTH.EarnGravity QIQTH.ModularEnergyBound QIQTH.BridgeASM QIQTH.AreaMap QIQTH.GravDyn
  QIQTH.LinEinstein
open scoped ComplexOrder

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The von Neumann entropy depends only on the matrix, not on the density witness
    (proof irrelevance). -/
private lemma entropy_val_congr {A B : Matrix ι ι ℂ} (hA : IsDensity A) (hB : IsDensity B)
    (h : A = B) : vonNeumannEntropy hA = vonNeumannEntropy hB := by
  subst h; rfl

/-! ## RC2.1 — the second law with rigidity

RC1 proved entropy production: `S(A) ≤ S(dephase A)` (`entropy_dephase_ge`).  Here is its
EQUALITY CASE, via the held Klein faithfulness `relEntropy_eq_zero`: production vanishes
exactly at the records. -/

/-- **THE SECOND LAW WITH RIGIDITY — the equality case of entropy production.**  For a
    positive density `A`, reading the ledger produces NO entropy iff `A` already is a
    record: `S(dephase A) = S(A) ↔ dephase A = A`.  Route: RC1's cross-entropy identity
    gives the exact production formula `D(A‖dephase A) = S(dephase A) − S(A)`, and the held
    Klein faithfulness (`relEntropy_eq_zero`, the tracked equality case of the
    doubly-stochastic/Jensen proof) forces `A = dephase A` at zero relative entropy. -/
theorem entropy_production_zero_iff {A : Matrix ι ι ℂ} (hA : A.PosDef) (hd : IsDensity A) :
    vonNeumannEntropy (dephase_isDensity hd) = vonNeumannEntropy hd ↔ dephase A = A := by
  constructor
  · intro hS
    have hDApd : (dephase A).PosDef := dephase_posDef hA
    -- the exact production formula D(A‖dephase A) = S(dephase A) − S(A)
    have hid := relEntropy_eq_crossEntropy_sub_entropy hA hDApd hd
    have hcross : crossEntropy A hDApd.1 = vonNeumannEntropy (dephase_isDensity hd) := by
      rw [← crossEntropy_dephase hDApd (dephase_dephase A) A]
      exact crossEntropy_self hDApd (dephase_isDensity hd)
    have hzero : relEntropy hA.1 hDApd.1 = 0 := by
      rw [hid, hcross, hS, sub_self]
    -- Klein faithfulness: D = 0 forces A = dephase A
    exact (relEntropy_eq_zero hA hDApd hd.trace_one (dephase_isDensity hd).trace_one
      hzero).symm
  · intro h
    exact entropy_val_congr (dephase_isDensity hd) hd h

/-- **THE SECOND LAW, strict form**: off-equilibrium, record formation STRICTLY produces
    entropy — `S(A) < S(dephase A)` whenever `A` is not a record.  RC1's `≤` plus the
    rigidity of `entropy_production_zero_iff`. -/
theorem entropy_strict_increase {A : Matrix ι ι ℂ} (hA : A.PosDef) (hd : IsDensity A)
    (h : dephase A ≠ A) :
    vonNeumannEntropy hd < vonNeumannEntropy (dephase_isDensity hd) := by
  refine lt_of_le_of_ne (entropy_dephase_ge hA hd) fun heq => h ?_
  exact (entropy_production_zero_iff hA hd).mp heq.symm

/-! ## RC2.2 — the flow preserves (non-)equilibrium at finite time -/

/-- **The flow never creates or destroys equilibrium at finite time** — for EVERY real `s`
    (not just `s > 0`): `T_s A` is a record iff `A` is.  Off-diagonal entries of `T_s A`
    are `e^{−s}·A n m` with `e^{−s} ≠ 0`, so the coherences of `T_s A` vanish exactly when
    those of `A` do — records are reached only in the `s → ∞` limit, never at finite time. -/
theorem Tsem_record_iff (s : ℝ) (A : Matrix ι ι ℂ) :
    dephase (Tsem s A) = Tsem s A ↔ dephase A = A := by
  rw [dephase_eq_self_iff, dephase_eq_self_iff]
  constructor
  · intro hrec n m hnm
    have h0 : ((Real.exp (-s) : ℝ) : ℂ) * A n m = 0 := by
      rw [← Tsem_apply_ne s A hnm]
      exact hrec n m hnm
    rcases mul_eq_zero.mp h0 with h1 | h2
    · exact absurd (Complex.ofReal_eq_zero.mp h1) (Real.exp_pos (-s)).ne'
    · exact h2
  · intro hrec n m hnm
    rw [Tsem_apply_ne s A hnm, hrec n m hnm, mul_zero]

/-- **The strict entropy gap at finite time**: off-equilibrium, the evolved state NEVER
    exhausts the entropy budget — `S(T_s A) < S(dephase A)` for every `s ≥ 0`.  Proof:
    `T_s A` is not a record (`Tsem_record_iff`), so the strict second law applies to it,
    and its readout is the original readout (`dephase_Tsem`). -/
theorem entropy_Tsem_strict {A : Matrix ι ι ℂ} (hA : A.PosDef) (hd : IsDensity A)
    {s : ℝ} (hs : 0 ≤ s) (h : dephase A ≠ A) :
    vonNeumannEntropy (Tsem_isDensity hd hs) < vonNeumannEntropy (dephase_isDensity hd) := by
  have hT : dephase (Tsem s A) ≠ Tsem s A := fun hc => h ((Tsem_record_iff s A).mp hc)
  have hlt := entropy_strict_increase (Tsem_posDef hA hs) (Tsem_isDensity hd hs) hT
  have heq : vonNeumannEntropy (dephase_isDensity (Tsem_isDensity hd hs))
      = vonNeumannEntropy (dephase_isDensity hd) :=
    entropy_val_congr _ _ (dephase_Tsem s A)
  linarith

/-! ## RC2.3 — THE E4 JOIN: the boundary dynamics' equilibria are geometry

E4 (`CodeEquilibrium.code_equilibrium_einstein`) proves: a code whose per-ray state paths
are at relative-entropy equilibrium — the `RayPathFamilyRealizes` family, with carried
BW/derivative/Iyer–Wald data — has an emergent perturbation satisfying linearized vacuum
Einstein.  Here "equilibrium" is upgraded to a DYNAMICAL notion: a fixed point of the RC1
record channel. -/

/-- **Record equilibrium** — the dynamical notion of equilibrium supplied by RC1: a state
    fixed by the record readout, equivalently (`isRecordEquilibrium_iff_Tsem_fixed`) a
    fixed point of the record-dephasing semigroup at every positive time. -/
def IsRecordEquilibrium (ρ : Matrix ι ι ℂ) : Prop :=
  QIQTH.RecordChannel.dephase ρ = ρ

/-- **The bridge**: record equilibrium = stationarity under the boundary dynamics.  For
    every `s > 0`, `ρ` is a record equilibrium iff it is a fixed point of `T_s` (RC1's
    `Tsem_fixed_iff`) — the dynamical characterization of the records. -/
theorem isRecordEquilibrium_iff_Tsem_fixed {s : ℝ} (hs : 0 < s) (ρ : Matrix ι ι ℂ) :
    IsRecordEquilibrium ρ ↔ Tsem s ρ = ρ :=
  ⟨fun h => Tsem_of_dephase_eq s h, fun h => (Tsem_fixed_iff hs ρ).mp h⟩

/-- **E4's references are stationary under the boundary dynamics**: if every per-ray
    reference `ρ_0(v)` is a record equilibrium, the record channel fixes it at EVERY time
    — the equilibrium code is an invariant configuration of the open dynamics. -/
theorem record_reference_stationary (δS δK : (Fin 4 → ℝ) → ℝ)
    (F : RayPathFamilyRealizes ι δS δK) (hEq : ∀ v, IsRecordEquilibrium (F.ρt v 0))
    (s : ℝ) (v : Fin 4 → ℝ) :
    Tsem s (F.ρt v 0) = F.ρt v 0 :=
  Tsem_of_dephase_eq s (hEq v)

/-- **E4's references are Lyapunov-STABLE attractors of the boundary dynamics** — the
    GENUINE dynamical link of the join: under `hEq`, RC1's Lyapunov theorem
    (`relEntropy_Tsem_le`) applies per ray with `σ = ρ_0(v)`: the relative entropy of ANY
    positive density to each E4 reference is non-increasing along the record channel —
    perturbations relax BACK toward the reference. -/
theorem record_reference_lyapunov (δS δK : (Fin 4 → ℝ) → ℝ)
    (F : RayPathFamilyRealizes ι δS δK) (hEq : ∀ v, IsRecordEquilibrium (F.ρt v 0))
    (v : Fin 4 → ℝ) {ρ : Matrix ι ι ℂ} (hρ : ρ.PosDef) (hρd : IsDensity ρ)
    {s : ℝ} (hs : 0 ≤ s) :
    relEntropy (Tsem_posDef hρ hs).1 (F.hpos v 0).1 ≤ relEntropy hρ.1 (F.hpos v 0).1 :=
  relEntropy_Tsem_le hs hρ hρd (F.hpos v 0) (hEq v)

/-- **THE E4 JOIN — record dynamics ⟹ linearized Einstein.**  The held E4 capstone
    `code_equilibrium_einstein` with the per-ray references REQUIRED to be record
    equilibria of the RC1 boundary semigroup (`hEq`): the composed theorem reads —
    **states the boundary dynamics relaxes to satisfy linearized vacuum Einstein.**

    "Equilibrium" is here a property of the boundary DYNAMICS, machine-checked as
    `Tsem`-fixedness (`isRecordEquilibrium_iff_Tsem_fixed`), not a bare label.
    HONESTY NOTE: E4's proof does not consume any stationarity property of the reference
    beyond the `RayPathFamilyRealizes` data, so `hEq` is a labelling upgrade inside THIS
    proof; the genuine dynamical content of the join is `record_reference_stationary` +
    `record_reference_lyapunov` (the references are stable attractors of the flow).
    ⚠ CONDITIONAL on E4's carried per-ray BW/analytic data + Iyer–Wald (structure fields,
    never axioms); linearized, free, finite/model.  NOT QG. -/
theorem record_dynamics_einstein (k : Fin 4 → ℝ) (h : Matrix (Fin 4) (Fin 4) ℝ)
    (hSym : h.IsSymm) (δS δK : (Fin 4 → ℝ) → ℝ) (F : RayPathFamilyRealizes ι δS δK)
    (hEq : ∀ v, IsRecordEquilibrium (F.ρt v 0))
    (hIW : ∀ v : Fin 4 → ℝ, δK v - δS v = areaVar (raySurf v) (einsteinSymbol k h)) :
    einsteinSymbol k h = 0 :=
  code_equilibrium_einstein k h hSym δS δK F hIW

/-- **RC2 CAPSTONE — the boundary dynamics' equilibria ARE geometry.**  For an equilibrium
    code (E4's per-ray family with every reference a record equilibrium) and any positive
    time `s`, ONE conjunction: (i) the references are FIXED POINTS of the record channel,
    (ii) they are LYAPUNOV-STABLE (the relative entropy of any positive density to each
    reference is non-increasing along the flow — perturbations relax back), and (iii) the
    emergent perturbation satisfies LINEARIZED VACUUM EINSTEIN.  Equilibria of the boundary
    dynamics, dynamically characterized and dynamically stable, are exactly where the
    geometry lives.  ⚠ Same firewall as `record_dynamics_einstein`. -/
theorem boundary_dynamics_equilibria_are_geometry (k : Fin 4 → ℝ)
    (h : Matrix (Fin 4) (Fin 4) ℝ) (hSym : h.IsSymm) (δS δK : (Fin 4 → ℝ) → ℝ)
    (F : RayPathFamilyRealizes ι δS δK) (hEq : ∀ v, IsRecordEquilibrium (F.ρt v 0))
    (hIW : ∀ v : Fin 4 → ℝ, δK v - δS v = areaVar (raySurf v) (einsteinSymbol k h))
    {s : ℝ} (hs : 0 < s) :
    (∀ v : Fin 4 → ℝ, Tsem s (F.ρt v 0) = F.ρt v 0)
      ∧ (∀ (v : Fin 4 → ℝ) (ρ : Matrix ι ι ℂ) (hρ : ρ.PosDef) (hρd : IsDensity ρ),
          relEntropy (Tsem_posDef hρ hs.le).1 (F.hpos v 0).1
            ≤ relEntropy hρ.1 (F.hpos v 0).1)
      ∧ einsteinSymbol k h = 0 :=
  ⟨fun v => Tsem_of_dephase_eq s (hEq v),
   fun v ρ hρ hρd => relEntropy_Tsem_le hs.le hρ hρd (F.hpos v 0) (hEq v),
   code_equilibrium_einstein k h hSym δS δK F hIW⟩

end QIQTH.RecordEquilibrium
