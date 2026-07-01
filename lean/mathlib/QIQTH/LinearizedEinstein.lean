/-
  BRIDGE A1b — structural extensions of the A1 anchor (`BridgeLinearizedGR.lean`): Bianchi, gauge-class,
  and the converse dispersion theorem.

  ★ SCOPE (BRIDGE_PLAN.md; the GPT-5.5-pro verification of the bridge plan explicitly recommended these three
    sanity/strengthening layers on top of A1). Everything is about the SAME `linRicci`/`linEinstein` symbols
    landed in A1 — no new physics objects, no duplicate definitions. Honest labels: linearized ≠ full GR;
    vacuum only; fixed Minkowski background; the symbol calculus is exact per plane-wave mode (`∂ → k` times the
    profile's `f''`, so all `= 0` statements are profile- and sign-insensitive).

  Contents (all finite algebra, axiom-free):
  • **Linearity** of the symbols in the perturbation (`linEinstein_add`) and the resulting **additive gauge
    invariance** `linEinstein k (e + k⊙ξ) = linEinstein k e` (`linEinstein_add_gauge`): `G⁽¹⁾` is a function of
    the GAUGE CLASS of the perturbation, not just "pure gauge maps to zero" (A1's `linEinstein_gauge`).
  • **The linearized Bianchi identity** `k^μ G⁽¹⁾_{μν} = 0` — IDENTICALLY, for every wavevector `k` and every
    perturbation `e` (no gauge, trace, symmetry, or on-shell condition) — `bianchi_linEinstein`. This is the
    plane-wave image of `∂^μ δG_{μν} = 0`: the structural identity that will force stress-energy conservation
    in B1 and grounds the `φ`-removal step of G7b.
  • **The converse of the anchor** (non-vacuous): a NONZERO transverse-traceless perturbation solves
    `G⁽¹⁾ = 0` **iff** `k² = 0` (`linEinstein_eq_zero_iff_massless`). On the z-directed family
    `kZ ω κ = (ω,0,0,κ)` with a nontrivial polarization content `a•e₊ + b•e×` this is the light-cone
    dispersion relation `ω² = κ²` (`einstein_iff_dispersion`): linearized Einstein FORCES the graviton to
    propagate at the speed of light, and conversely — the wave equation and the Einstein equation have the
    same solution set on the physical sector. ⚠ The trivial `k = 0` (a constant, non-propagating `h`) is
    included in `k² = 0`; "propagating at `c`" is the `k ≠ 0` reading.
  • The kDown capstone extended to the whole physical polarization plane: `graviton_combo_solves_linEinstein`
    (every `a•e₊ + b•e×`, not only the two basis polarizations).
-/
import QIQTH.BridgeLinearizedGR

namespace QIQTH.Bridge

open QIQTH.GravDyn

/-! ## Linearity of the symbols in the perturbation -/

theorem kContr_add (k : Fin 4 → ℝ) (e f : Matrix (Fin 4) (Fin 4) ℝ) (ν : Fin 4) :
    kContr k (e + f) ν = kContr k e ν + kContr k f ν := by
  simp only [kContr, Matrix.add_apply]; ring

theorem trEta_add (e f : Matrix (Fin 4) (Fin 4) ℝ) :
    trEta (e + f) = trEta e + trEta f := by
  simp only [trEta, Matrix.add_apply]; ring

theorem linRicci_add (k : Fin 4 → ℝ) (e f : Matrix (Fin 4) (Fin 4) ℝ) :
    linRicci k (e + f) = linRicci k e + linRicci k f := by
  ext μ ν
  simp only [linRicci, Matrix.of_apply, Matrix.add_apply, kContr_add, trEta_add]
  ring

theorem linRicciScalar_add (k : Fin 4 → ℝ) (e f : Matrix (Fin 4) (Fin 4) ℝ) :
    linRicciScalar k (e + f) = linRicciScalar k e + linRicciScalar k f := by
  simp only [linRicciScalar, linRicci_add, Matrix.add_apply]
  ring

/-- **`G⁽¹⁾` is linear in the perturbation** (additivity; the symbol is a linear map of `e`). -/
theorem linEinstein_add (k : Fin 4 → ℝ) (e f : Matrix (Fin 4) (Fin 4) ℝ) :
    linEinstein k (e + f) = linEinstein k e + linEinstein k f := by
  ext μ ν
  simp only [linEinstein, Matrix.of_apply, Matrix.add_apply, linRicci_add, linRicciScalar_add]
  ring

/-- **Additive gauge invariance: `G⁽¹⁾` depends only on the gauge class.** Shifting ANY perturbation by pure
    gauge (`k_μξ_ν + k_νξ_μ`, any `k`, on- or off-shell) leaves the linearized Einstein tensor unchanged —
    strengthening A1's `linEinstein_gauge` ("pure gauge ↦ 0") to the full statement of linearized
    diffeomorphism invariance. -/
theorem linEinstein_add_gauge (k ξ : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ) :
    linEinstein k (e + Matrix.of fun μ ν => k μ * ξ ν + k ν * ξ μ) = linEinstein k e := by
  rw [linEinstein_add, linEinstein_gauge, add_zero]

/-! ## The linearized Bianchi identity (identically — any `k`, any `e`) -/

/-- **The linearized Bianchi identity (plane-wave symbol form):** `k^μ G⁽¹⁾_{μν} = 0` IDENTICALLY — for every
    wavevector `k` and every perturbation `e`, with no gauge, trace, symmetry, or on-shell hypothesis. The
    momentum-space image of the contracted Bianchi identity `∂^μ δG_{μν} = 0`; the structural reason a
    consistent coupling `h_{μν}T^{μν}` forces `∂_μ T^{μν} = 0` (B1) and the engine of the `φ`-removal in G7b. -/
theorem bianchi_linEinstein (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ) (ν : Fin 4) :
    kContr k (linEinstein k e) ν = 0 := by
  fin_cases ν <;>
    simp only [kContr, linEinstein, linRicci, linRicciScalar, trEta, minkQuad, minkMetric,
      Matrix.of_apply, Matrix.diagonal_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;>
    norm_num <;> ring

/-! ## The converse of the anchor: linearized Einstein ⟺ masslessness on the TT sector -/

/-- **Linearized Einstein forces masslessness.** A NONZERO transverse-traceless perturbation solves
    `G⁽¹⁾ = 0` only if `k² = 0`. (The trivial `k = 0` is included; "propagating at `c`" is the `k ≠ 0`
    reading — see header.) -/
theorem massless_of_linEinstein_eq_zero (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ)
    (hT : ∀ ν, kContr k e ν = 0) (hTr : trEta e = 0) (he : e ≠ 0)
    (h0 : linEinstein k e = 0) : minkQuad k = 0 := by
  have h := linEinstein_tt k e hT hTr
  rw [h0] at h
  rcases smul_eq_zero.mp h.symm with hc | hE
  · linarith
  · exact absurd hE he

/-- **A1b — on the TT plane-wave sector, linearized vacuum Einstein ⟺ the massless dispersion `k² = 0`.**
    For a nonzero TT perturbation, `G⁽¹⁾ = 0` exactly when the wavevector is null: the Einstein equation and
    the G11c wave equation have the SAME solution set (the anchor upgraded from ⟸ to ⟺). -/
theorem linEinstein_eq_zero_iff_massless (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ)
    (hT : ∀ ν, kContr k e ν = 0) (hTr : trEta e = 0) (he : e ≠ 0) :
    linEinstein k e = 0 ↔ minkQuad k = 0 := by
  constructor
  · exact massless_of_linEinstein_eq_zero k e hT hTr he
  · intro h
    rw [linEinstein_tt k e hT hTr, h]
    simp

/-! ## Instantiation on the quantized graviton's polarization plane (non-vacuity witnesses) -/

/-- A nontrivial polarization combination is a nonzero matrix (from the G11a linear independence). -/
theorem pol_combo_ne_zero (a b : ℝ) (hab : ¬(a = 0 ∧ b = 0)) :
    a • polPlus + b • polCross ≠ 0 :=
  fun h => hab (graviton_polarizations_indep a b h)

/-- Every polarization combination is transverse (to the fixed `kUp`, i.e. TT for `kDown`). -/
theorem pol_combo_transverse (a b : ℝ) : Transverse (a • polPlus + b • polCross) := by
  intro ν
  fin_cases ν <;>
    simp [kUp, polPlus, polCross, Fin.sum_univ_four, Matrix.add_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

/-- Every polarization combination is traceless. -/
theorem pol_combo_traceless (a b : ℝ) : Traceless (a • polPlus + b • polCross) := by
  simp only [Traceless, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, polPlus, polCross,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **The whole physical polarization plane solves linearized vacuum Einstein at the null `kDown`** — the A1
    capstone extended from the two basis polarizations (`einstein_polPlus`/`einstein_polCross`) to every
    physical polarization content `a•e₊ + b•e×` of the quantized graviton (Q1–Q6). -/
theorem graviton_combo_solves_linEinstein (a b : ℝ) :
    linEinstein kDown (a • polPlus + b • polCross) = 0 :=
  graviton_solves_linEinstein _ (pol_combo_transverse a b) (pol_combo_traceless a b)

/-- The z-directed wavevector family `k = (ω, 0, 0, κ)` — frequency `ω`, wavenumber `κ` (down-index);
    genuinely OFF-shell for `ω² ≠ κ²`, with `kDown = kZ 1 1` the on-shell member. -/
def kZ (ω κ : ℝ) : Fin 4 → ℝ := ![ω, 0, 0, κ]

/-- `kDown` is the on-shell member `kZ 1 1` of the family. -/
theorem kDown_eq_kZ : kDown = kZ 1 1 := rfl

theorem minkQuad_kZ (ω κ : ℝ) : minkQuad (kZ ω κ) = κ ^ 2 - ω ^ 2 := by
  simp only [minkQuad, kZ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- Every polarization combination is transverse to EVERY z-directed wavevector (on- or off-shell). -/
theorem kZ_kContr_pol_combo (ω κ a b : ℝ) (ν : Fin 4) :
    kContr (kZ ω κ) (a • polPlus + b • polCross) ν = 0 := by
  fin_cases ν <;>
    simp only [kContr, kZ, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, polPlus, polCross,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;>
    ring

/-- **A1b CAPSTONE — linearized Einstein ⟺ the light-cone dispersion `ω² = κ²`.** For any nontrivial
    polarization content of the quantized graviton on the z-directed wavevector family `(ω,0,0,κ)`, the
    linearized vacuum Einstein equation holds exactly when `ω² = κ²`: the graviton propagates at the SPEED
    OF LIGHT because Einstein says so — and conversely. Non-vacuous: the polarization is a nonzero matrix
    (`pol_combo_ne_zero`) and the family is genuinely off-shell for `ω² ≠ κ²` (`minkQuad_kZ`). (`k = 0` — the
    constant perturbation — sits inside `ω² = κ²`; "propagating" is the `k ≠ 0` reading.) -/
theorem einstein_iff_dispersion (ω κ a b : ℝ) (hab : ¬(a = 0 ∧ b = 0)) :
    linEinstein (kZ ω κ) (a • polPlus + b • polCross) = 0 ↔ ω ^ 2 = κ ^ 2 := by
  rw [linEinstein_eq_zero_iff_massless _ _ (kZ_kContr_pol_combo ω κ a b)
    (trEta_of_traceless _ (pol_combo_traceless a b)) (pol_combo_ne_zero a b hab), minkQuad_kZ]
  constructor <;> intro h <;> linarith

end QIQTH.Bridge
