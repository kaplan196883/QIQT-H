/-
  J2 (HYPOTHESIS_DELETION_PLAN.md) — the CHM symbol probe + the bridge refactor.

  BINDING (consult): the physical FGHMVR identity is NOT derivable from the held pieces, and assuming an
  arbitrary physical `δK − δS` equals a kernel pairing would be `hIW` in disguise (forbidden). What IS derivable,
  by real one-variable calculus, is the KERNEL-MOMENT NORMALIZATION:
  • `chmRadialMass3_eq` — the radial mass of the CHM ball kernel, `∫₀^R 4πr²·β_R(r) dr = 4πR⁴/15`
    (`β_R(r) = (R²−r²)/2R`, the C2a weight);
  • `CHMSymbolProbe3` — the kernel-weighted symbol pairing at the PURE ALGEBRAIC SYMBOL level (constant radial
    density — no plane-wave phase, per the binding correction), normalized by the kernel mass;
  • `CHMSymbolProbe3_eq` / `CHMSymbolProbe3_einstein_eq_areaVar` — the normalized kernel pairing EQUALS the ray
    area probe `areaVar (raySurf v)`: the CHM kernel, once its moment is computed, reproduces exactly the probe
    the assembled bridge consumes.
  THE REFACTOR: `bridge_conditional_probe` — the bridge assembly consuming the DERIVABLE probe. The carried
  Iyer–Wald content SHRINKS: `hIW` (deficit = abstract geometric pairing) factors as
  (deficit = CHM kernel probe) ∘ (kernel probe = areaVar), and the second factor is now a THEOREM
  (`CHMSymbolProbe3_eq`); the residual carried input is `hDeficit` — the identification of the PHYSICAL
  first-law deficit with the kernel probe, stated ONCE. HYPOTHESIS SHRUNK: hIW → hDeficit.

  ⚠ Honest scope: linearized, free, flat; the physical deficit=probe identification stays carried (that is the
  FGHMVR content, not derivable here); NOT a derivation of gravity. Axiom-free, std-3.
-/
import Mathlib
import QIQTH.CHMKernel
import QIQTH.BridgeAssembly

namespace QIQTH.CHM

open MeasureTheory intervalIntegral QIQTH.LinEinstein QIQTH.AreaMap QIQTH.BridgeASM

/-- **The radial mass of the CHM ball kernel**: `∫₀^R 4πr²·β_R(r) dr` — the total kernel moment weighting a
    constant (symbol-level) density over the ball. -/
noncomputable def chmRadialMass3 (R : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..R, 4 * Real.pi * r ^ 2 * chmWeight R r

/-- **J2 normalization (one-variable calculus)**: `chmRadialMass3 R = 4πR⁴/15`. -/
theorem chmRadialMass3_eq (R : ℝ) (hR : R ≠ 0) :
    chmRadialMass3 R = 4 * Real.pi * R ^ 4 / 15 := by
  have h1 : ∀ r : ℝ, 4 * Real.pi * r ^ 2 * chmWeight R r
      = 2 * Real.pi * R * r ^ 2 - (2 * Real.pi / R) * r ^ 4 := by
    intro r
    rw [chmWeight]
    field_simp
    ring
  rw [chmRadialMass3,
    intervalIntegral.integral_congr (g := fun r : ℝ =>
      2 * Real.pi * R * r ^ 2 - (2 * Real.pi / R) * r ^ 4) (fun r _ => h1 r)]
  have hi2 : IntervalIntegrable (fun r : ℝ => 2 * Real.pi * R * r ^ 2) volume 0 R :=
    (intervalIntegrable_pow 2).const_mul _
  have hi4 : IntervalIntegrable (fun r : ℝ => (2 * Real.pi / R) * r ^ 4) volume 0 R :=
    (intervalIntegrable_pow 4).const_mul _
  rw [intervalIntegral.integral_sub hi2 hi4, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow]
  field_simp
  ring

/-- The kernel mass is strictly positive on a genuine ball. -/
theorem chmRadialMass3_pos (R : ℝ) (hR : 0 < R) : 0 < chmRadialMass3 R := by
  rw [chmRadialMass3_eq R hR.ne']
  have h4 : (0 : ℝ) < R ^ 4 := by positivity
  positivity

/-- **The CHM symbol probe**: the kernel-weighted pairing of the constant (pure algebraic symbol level, no
    plane-wave phase) ray-probe density over the ball, NORMALIZED by the kernel mass. -/
noncomputable def CHMSymbolProbe3 (R : ℝ) (v : Fin 4 → ℝ)
    (h : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..R, 4 * Real.pi * r ^ 2 * chmWeight R r * areaVar (raySurf v) h)
    / chmRadialMass3 R

/-- **J2 probe theorem**: on a genuine ball the normalized CHM kernel pairing EQUALS the ray area probe —
    `CHMSymbolProbe3 R v h = areaVar (raySurf v) h`. The kernel's moment cancels exactly. -/
theorem CHMSymbolProbe3_eq (R : ℝ) (hR : 0 < R) (v : Fin 4 → ℝ)
    (h : Matrix (Fin 4) (Fin 4) ℝ) :
    CHMSymbolProbe3 R v h = areaVar (raySurf v) h := by
  rw [CHMSymbolProbe3, intervalIntegral.integral_mul_const, ← chmRadialMass3,
    mul_div_cancel_left₀ _ (chmRadialMass3_pos R hR).ne']

/-- **J2 probe theorem, Einstein form**: the kernel-weighted pairing against the Einstein symbol is exactly the
    ray-probe pairing the assembled bridge consumes. -/
theorem CHMSymbolProbe3_einstein_eq_areaVar (R : ℝ) (hR : 0 < R) (v k : Fin 4 → ℝ)
    (h : Matrix (Fin 4) (Fin 4) ℝ) :
    CHMSymbolProbe3 R v (einsteinSymbol k h) = areaVar (raySurf v) (einsteinSymbol k h) :=
  CHMSymbolProbe3_eq R hR v _

/-- **J2 REFACTOR — the bridge assembly consuming the DERIVABLE probe.** The conditional Jacobson-shape
    assembly with the Iyer–Wald input FACTORED: the carried content shrinks from `hIW` (first-law deficit =
    abstract geometric pairing) to **`hDeficit`** — the identification of the physical first-law deficit with
    the CHM KERNEL probe, stated once; the kernel-probe = area-probe half is now a THEOREM
    (`CHMSymbolProbe3_eq`). Conclusion: linearized vacuum Einstein. HYPOTHESIS SHRUNK: hIW → hDeficit.
    ⚠ CONDITIONAL — hDeficit is the FGHMVR physics (not derivable from the held pieces, per the binding
    correction); Clausius + geometric matching stay the explicit physical inputs. NOT a derivation of gravity;
    linearized, free, flat. -/
theorem bridge_conditional_probe (R : ℝ) (hR : 0 < R) (k : Fin 4 → ℝ)
    (h : Matrix (Fin 4) (Fin 4) ℝ) (hSym : h.IsSymm) (G : ℝ)
    (δA δS δK : (Fin 4 → ℝ) → ℝ)
    (hClausius : ∀ v, δS v = δA v / (4 * G))
    (hGeom : ∀ v, δK v = δA v / (4 * G))
    (hDeficit : ∀ v : Fin 4 → ℝ, δK v - δS v = CHMSymbolProbe3 R v (einsteinSymbol k h)) :
    einsteinSymbol k h = 0 :=
  bridge_conditional k h hSym G δA δS δK hClausius hGeom
    (fun v => by rw [hDeficit v, CHMSymbolProbe3_eq R hR v _])

end QIQTH.CHM
