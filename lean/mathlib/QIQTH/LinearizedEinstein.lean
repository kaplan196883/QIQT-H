/-
  A1 of BRIDGE_PLAN.md — the linearized-GR anchor: the quantized graviton solves linearized VACUUM Einstein.

  ★ SCOPE (honest labels; GPT-5.5-pro-verified design 2026-07-02). This is the momentum-space (plane-wave-symbol)
    LINEARIZED Einstein tensor on a fixed Minkowski background, in finite 4×4 matrix algebra — the anchor that makes
    the field quantized in `GravitonQuantization.lean` provably *the graviton of general relativity*: in TT gauge
    `δG_{μν} = −½□h_{μν}` (symbol form `einsteinSymbol_tt`), so the G11c wave equation IS `δG = 0`
    (`graviton_solves_linearized_einstein`), and conversely linearized Einstein FORCES the null dispersion
    `ω² = κ²` — propagation at the speed of light (`einstein_iff_dispersion`). It is **NOT**: the nonlinear or
    second-order Einstein equation, background independence, a sourced equation (no `T_{μν}` here — that is B1),
    or a derivation of gravity (plan ingredient D, cited open research). Vacuum only; first order only.

  ★ SIGN CONVENTION (load-bearing; GPT-5.5-pro-checked). For the plane wave `h_{μν}(x) = e_{μν}·cos(k·x)`
    (`k` the DOWN-index wavevector, `k·x = k_μ x^μ`) one has `∂_μ∂_ν h_{αβ} = −k_μ k_ν h_{αβ}`, so the
    position-space linearized Ricci/Einstein tensors are the NEGATIVES of the symbols defined here:
        δR_{μν}(x) = −(ricciSymbol k e)_{μν}·cos(k·x),   δG_{μν}(x) = −(einsteinSymbol k e)_{μν}·cos(k·x).
    The PHYSICAL coefficient is `linEinsteinCoeff := −einsteinSymbol` (`δG(x) = linEinsteinCoeff·cos(k·x)`).
    All vanishing statements (`= 0`) are insensitive to this sign; it matters only for sourced equations (B1/ASM).
    The trace step `δR = η^{μν} δR_{μν}` is exact on a flat background (the missing `δg^{μν} R^{bg}_{μν}` term
    vanishes since `R^{bg} = 0`).

  Contents (all axiom-free, std 3):
  • `ricciSymbol` / `einsteinSymbol` — the linearized curvature symbols for arbitrary down-index `k`.
  • Gauge invariance: `ricciSymbol k (k⊙ξ) = 0` IDENTICALLY (any `k`, on- or off-shell), additive form
    `einsteinSymbol_add_gauge`, and the fixed-`kDown` corollary for the existing `gaugeShift`.
  • The linearized Bianchi identity `k^μ (einsteinSymbol k e)_{μν} = 0` IDENTICALLY (`bianchi_einsteinSymbol`).
  • TT reduction `einsteinSymbol_tt`: transverse+traceless ⟹ `einsteinSymbol k e = (−k²/2)•e` — "δG = −½□h in
    TT gauge" at symbol level (the symbol of `−½□` on `e·cos(k·x)` is `(k²/2)e`; see the sign convention).
  • The anchor: null `k` ⟹ TT perturbations solve linearized vacuum Einstein; instantiated on the quantized
    graviton's polarization content `a•e₊ + b•e×` at the null `kDown` (`graviton_solves_linearized_einstein`).
  • The converse (non-vacuous): for a NONZERO TT polarization, `δG = 0 ⟺ k² = 0` — on the z-directed family
    `kZ ω κ = (ω,0,0,κ)` this is the light-cone dispersion `ω² = κ²` (`einstein_iff_dispersion`). ⚠ The trivial
    solution `k = 0` (a constant, non-propagating `h`) is included in `k² = 0`; "propagating at `c`" is the
    `k ≠ 0` reading.
-/
import QIQTH.EmergentDynamics

namespace QIQTH.LinEinstein

open QIQTH.GravDyn

noncomputable section

/-! ## Index calculus for a general down-index wavevector `k` -/

/-- Raise a down-index vector with `η = diag(−1,1,1,1)`: `k^μ = η^{μν} k_ν`. -/
def raiseIdx (k : Fin 4 → ℝ) : Fin 4 → ℝ := ![-(k 0), k 1, k 2, k 3]

/-- The contraction `k^μ e_{μν}` (first index raised against `e`). -/
def kContract (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ) (ν : Fin 4) : ℝ :=
  ∑ μ, raiseIdx k μ * e μ ν

/-- The Minkowski trace `η^{μν} e_{μν} = −e₀₀ + e₁₁ + e₂₂ + e₃₃`. -/
def etaTrace (e : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := -e 0 0 + e 1 1 + e 2 2 + e 3 3

/-- The double contraction `k^μ k^ν e_{μν}`. -/
def doubleContract (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  ∑ μ, raiseIdx k μ * kContract k e μ

/-- The Minkowski pairing `k^μ ξ_μ` of two down-index vectors. -/
def kDot (k ξ : Fin 4 → ℝ) : ℝ := ∑ μ, raiseIdx k μ * ξ μ

/-- `e` is **transverse to `k`**: `k^μ e_{μν} = 0` for every `ν` (the momentum-space TT-gauge condition
    `∂^μ h_{μν} = 0` for the plane wave `h = e·cos(k·x)`). -/
def TransverseTo (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∀ ν, kContract k e ν = 0

/-- Raising the existing down-index null `kDown = (1,0,0,1)` gives the existing raised `kUp = (−1,0,0,1)`
    (consistency with `EmergentDynamics`). -/
theorem raiseIdx_kDown : raiseIdx kDown = kUp := by
  funext μ
  fin_cases μ <;>
    simp [raiseIdx, kDown, kUp, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three]

/-- The existing `Transverse` (fixed `kUp`) is exactly `TransverseTo kDown`. -/
theorem transverseTo_kDown_of_transverse {e : Matrix (Fin 4) (Fin 4) ℝ} (h : Transverse e) :
    TransverseTo kDown e := by
  intro ν
  simp only [kContract, raiseIdx_kDown]
  exact h ν

/-- The existing `Traceless` is exactly `etaTrace e = 0`. -/
theorem etaTrace_eq_zero_of_traceless {e : Matrix (Fin 4) (Fin 4) ℝ} (h : Traceless e) :
    etaTrace e = 0 := h

/-- `k^μ k_μ = minkQuad k` (the pairing of `k` with itself is the existing quadratic form). -/
theorem kDot_self (k : Fin 4 → ℝ) : kDot k k = minkQuad k := by
  simp only [kDot, raiseIdx, minkQuad, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  ring

/-! ## The linearized curvature symbols -/

/-- The **linearized Ricci symbol**: the momentum-space coefficient of the linearized Ricci tensor of the
    plane wave `h_{μν} = e_{μν}·cos(k·x)`,
        `(ricciSymbol k e)_{μν} = ½( k_μ (k·e)_ν + k_ν (k·e)_μ − k² e_{μν} − k_μ k_ν tr e )`,
    with `δR_{μν}(x) = −(ricciSymbol k e)_{μν}·cos(k·x)` (see the header sign convention). -/
def ricciSymbol (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun μ ν =>
    (1 / 2) * (k μ * kContract k e ν + k ν * kContract k e μ
      - minkQuad k * e μ ν - k μ * k ν * etaTrace e)

/-- The **linearized Einstein symbol** `δG = δR − ½ η_{μν} δR` (on a flat background `δR = η^{μν} δR_{μν}`
    exactly, since `R^{bg}_{μν} = 0`), with `δG_{μν}(x) = −(einsteinSymbol k e)_{μν}·cos(k·x)`. -/
def einsteinSymbol (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  ricciSymbol k e - (etaTrace (ricciSymbol k e) / 2) • minkMetric

/-- The **physical linearized-Einstein coefficient** `δG_{μν}(x) = (linEinsteinCoeff k e)_{μν}·cos(k·x)`
    — the sign-corrected symbol (the one a SOURCED equation `δG = 8πG δT` must use; vanishing statements
    are insensitive to the sign). -/
def linEinsteinCoeff (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  -einsteinSymbol k e

/-! ## Linearity in the perturbation -/

theorem kContract_add (k : Fin 4 → ℝ) (e f : Matrix (Fin 4) (Fin 4) ℝ) (ν : Fin 4) :
    kContract k (e + f) ν = kContract k e ν + kContract k f ν := by
  simp only [kContract, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem kContract_sub (k : Fin 4 → ℝ) (e f : Matrix (Fin 4) (Fin 4) ℝ) (ν : Fin 4) :
    kContract k (e - f) ν = kContract k e ν - kContract k f ν := by
  simp only [kContract, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem kContract_smul (k : Fin 4 → ℝ) (c : ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ) (ν : Fin 4) :
    kContract k (c • e) ν = c * kContract k e ν := by
  simp only [kContract, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun μ _ => by ring)

theorem etaTrace_add (e f : Matrix (Fin 4) (Fin 4) ℝ) :
    etaTrace (e + f) = etaTrace e + etaTrace f := by
  simp only [etaTrace, Matrix.add_apply]; ring

theorem etaTrace_smul (c : ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ) :
    etaTrace (c • e) = c * etaTrace e := by
  simp only [etaTrace, Matrix.smul_apply, smul_eq_mul]; ring

theorem ricciSymbol_add (k : Fin 4 → ℝ) (e f : Matrix (Fin 4) (Fin 4) ℝ) :
    ricciSymbol k (e + f) = ricciSymbol k e + ricciSymbol k f := by
  ext μ ν
  simp only [ricciSymbol, Matrix.of_apply, Matrix.add_apply, kContract_add, etaTrace_add]
  ring

theorem einsteinSymbol_add (k : Fin 4 → ℝ) (e f : Matrix (Fin 4) (Fin 4) ℝ) :
    einsteinSymbol k (e + f) = einsteinSymbol k e + einsteinSymbol k f := by
  ext μ ν
  simp only [einsteinSymbol, ricciSymbol_add, etaTrace_add, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

/-! ## Gauge invariance (linearized diffeomorphisms drop out — identically, any `k`) -/

/-- The pure-gauge plane-wave shift for a GENERAL down-index `k`: `δe_{μν} = k_μ ξ_ν + k_ν ξ_μ`
    (the momentum-space image of `δh_{μν} = ∂_μ ξ_ν + ∂_ν ξ_μ`). -/
def gaugeShiftK (k ξ : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun μ ν => k μ * ξ ν + k ν * ξ μ

/-- At `kDown`, the general gauge shift is the existing `gaugeShift` of `EmergentDynamics`. -/
theorem gaugeShiftK_kDown (ξ : Fin 4 → ℝ) : gaugeShiftK kDown ξ = gaugeShift ξ := rfl

theorem kContract_gaugeShiftK (k ξ : Fin 4 → ℝ) (ν : Fin 4) :
    kContract k (gaugeShiftK k ξ) ν = minkQuad k * ξ ν + k ν * kDot k ξ := by
  simp only [kContract, gaugeShiftK, Matrix.of_apply, kDot, minkQuad, raiseIdx,
    Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem etaTrace_gaugeShiftK (k ξ : Fin 4 → ℝ) :
    etaTrace (gaugeShiftK k ξ) = 2 * kDot k ξ := by
  simp only [etaTrace, gaugeShiftK, Matrix.of_apply, kDot, raiseIdx, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **Gauge invariance of the linearized Ricci symbol — identically, for ANY `k` (on- or off-shell).**
    A pure-gauge perturbation `k⊙ξ` has vanishing linearized Ricci: the plane-wave image of the fact that
    `δR_{μν}` is invariant under linearized diffeomorphisms on a flat background. -/
theorem ricciSymbol_gauge (k ξ : Fin 4 → ℝ) : ricciSymbol k (gaugeShiftK k ξ) = 0 := by
  ext μ ν
  simp only [ricciSymbol, Matrix.of_apply, kContract_gaugeShiftK, etaTrace_gaugeShiftK,
    Matrix.zero_apply]
  simp only [gaugeShiftK, Matrix.of_apply]
  ring

/-- **Gauge invariance of the linearized Einstein symbol** `einsteinSymbol k (k⊙ξ) = 0` (any `k`). -/
theorem einsteinSymbol_gauge (k ξ : Fin 4 → ℝ) : einsteinSymbol k (gaugeShiftK k ξ) = 0 := by
  rw [einsteinSymbol, ricciSymbol_gauge]
  simp [etaTrace]

/-- **Additive gauge invariance**: shifting any perturbation by pure gauge leaves `δG` unchanged —
    `einsteinSymbol k (e + k⊙ξ) = einsteinSymbol k e`. The linearized Einstein tensor is a function of the
    gauge class only. -/
theorem einsteinSymbol_add_gauge (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ) (ξ : Fin 4 → ℝ) :
    einsteinSymbol k (e + gaugeShiftK k ξ) = einsteinSymbol k e := by
  rw [einsteinSymbol_add, einsteinSymbol_gauge, add_zero]

/-- The fixed-`kDown` corollary for the existing `gaugeShift`: pure linearized diffeomorphisms solve
    linearized vacuum Einstein. -/
theorem gauge_solves_linearized_einstein (ξ : Fin 4 → ℝ) :
    einsteinSymbol kDown (gaugeShift ξ) = 0 := by
  rw [← gaugeShiftK_kDown]
  exact einsteinSymbol_gauge kDown ξ

/-! ## The linearized Bianchi identity (symbol form — identically, any `k`, any `e`) -/

/-- `k^μ η_{μν} = k_ν`: contracting the raised `k` into the metric returns the down-index `k`. -/
theorem kContract_minkMetric (k : Fin 4 → ℝ) (ν : Fin 4) :
    kContract k minkMetric ν = k ν := by
  fin_cases ν <;>
    simp [kContract, minkMetric, raiseIdx, Fin.sum_univ_four, Matrix.diagonal_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

/-- The Minkowski trace of the linearized Ricci symbol: `η^{μν}(δR)_{μν} = k^μk^νe_{μν} − k² tr e`
    (symbol form of the linearized Ricci scalar). -/
theorem etaTrace_ricciSymbol (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ) :
    etaTrace (ricciSymbol k e) = doubleContract k e - minkQuad k * etaTrace e := by
  simp only [etaTrace, ricciSymbol, Matrix.of_apply, doubleContract, kContract, minkQuad,
    raiseIdx, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- The divergence of the linearized Ricci symbol: `k^μ(δR)_{μν} = ½ k_ν (k^αk^βe_{αβ} − k² tr e)`
    (the contracted-Bianchi engine). -/
theorem kContract_ricciSymbol (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ) (ν : Fin 4) :
    kContract k (ricciSymbol k e) ν
      = k ν / 2 * (doubleContract k e - minkQuad k * etaTrace e) := by
  simp only [kContract, ricciSymbol, Matrix.of_apply, doubleContract, minkQuad, etaTrace,
    raiseIdx, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **The linearized Bianchi identity (symbol form)** `k^μ (δG)_{μν} = 0` — IDENTICALLY, for every `k` and
    every perturbation `e` (no gauge, trace, or on-shell condition). The plane-wave image of
    `∂^μ δG_{μν} = 0`; the structural identity behind stress-energy conservation (B1) and the `φ`-removal
    of G7b. -/
theorem bianchi_einsteinSymbol (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ) (ν : Fin 4) :
    kContract k (einsteinSymbol k e) ν = 0 := by
  rw [einsteinSymbol, kContract_sub, kContract_smul, kContract_minkMetric,
    kContract_ricciSymbol, etaTrace_ricciSymbol]
  ring

/-! ## A1 — the TT reduction: `δG = −½□h` in transverse-traceless gauge -/

/-- In TT gauge the linearized Ricci symbol collapses to `(−k²/2)•e`. -/
theorem ricciSymbol_tt (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ)
    (hT : TransverseTo k e) (hTr : etaTrace e = 0) :
    ricciSymbol k e = (-(minkQuad k) / 2) • e := by
  ext μ ν
  simp only [ricciSymbol, Matrix.of_apply, hT μ, hT ν, hTr, Matrix.smul_apply, smul_eq_mul]
  ring

/-- **A1 — in TT gauge, `δG_{μν} = −½□h_{μν}` (symbol form).** For a transverse-traceless perturbation the
    linearized Einstein symbol is `(−k²/2)•e`. Position-space reading (header convention): `δG_{μν}(x) =
    (k²/2)e_{μν}cos(k·x)` and `−½□h_{μν} = −½(−k²)e_{μν}cos(k·x) = (k²/2)e_{μν}cos(k·x)` — EQUAL. So on the TT
    sector the linearized vacuum Einstein equation IS the massless wave equation `□h = 0` proven in G11c
    (`graviton_null_wave`): the field quantized in `GravitonQuantization.lean` is the graviton OF GENERAL
    RELATIVITY. Linearized, vacuum, fixed background — see header scope. -/
theorem einsteinSymbol_tt (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ)
    (hT : TransverseTo k e) (hTr : etaTrace e = 0) :
    einsteinSymbol k e = (-(minkQuad k) / 2) • e := by
  rw [einsteinSymbol, ricciSymbol_tt k e hT hTr, etaTrace_smul, hTr, mul_zero, zero_div,
    zero_smul, sub_zero]

/-- The physical coefficient on the TT sector: `linEinsteinCoeff k e = (k²/2)•e` — literally the symbol of
    `−½□` acting on `h = e·cos(k·x)`. -/
theorem linEinsteinCoeff_tt (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ)
    (hT : TransverseTo k e) (hTr : etaTrace e = 0) :
    linEinsteinCoeff k e = (minkQuad k / 2) • e := by
  rw [linEinsteinCoeff, einsteinSymbol_tt k e hT hTr]
  ext μ ν
  simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-! ## The anchor and its converse: linearized Einstein ⟺ masslessness on the TT sector -/

/-- **Null `k` ⟹ TT perturbations solve linearized vacuum Einstein** (`δG = 0`). -/
theorem einsteinSymbol_null_tt (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ)
    (hT : TransverseTo k e) (hTr : etaTrace e = 0) (hnull : minkQuad k = 0) :
    einsteinSymbol k e = 0 := by
  rw [einsteinSymbol_tt k e hT hTr, hnull]
  simp

/-- **The converse: linearized Einstein forces masslessness.** A NONZERO transverse-traceless perturbation
    solves `δG = 0` only if `k² = 0`. (The trivial `k = 0` is included; "propagating at `c`" is the `k ≠ 0`
    reading — see header.) -/
theorem massless_of_einsteinSymbol_eq_zero (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ)
    (hT : TransverseTo k e) (hTr : etaTrace e = 0) (he : e ≠ 0)
    (h0 : einsteinSymbol k e = 0) : minkQuad k = 0 := by
  have h := einsteinSymbol_tt k e hT hTr
  rw [h0] at h
  rcases smul_eq_zero.mp h.symm with hc | hE
  · linarith
  · exact absurd hE he

/-- **A1 — on the TT plane-wave sector, linearized vacuum Einstein ⟺ the massless dispersion `k² = 0`.**
    For a nonzero TT polarization, `δG = 0` exactly when the wavevector is null: the Einstein equation and
    the G11c wave equation have the same solution set. -/
theorem einsteinSymbol_eq_zero_iff_massless (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ)
    (hT : TransverseTo k e) (hTr : etaTrace e = 0) (he : e ≠ 0) :
    einsteinSymbol k e = 0 ↔ minkQuad k = 0 :=
  ⟨massless_of_einsteinSymbol_eq_zero k e hT hTr he, einsteinSymbol_null_tt k e hT hTr⟩

/-! ## Instantiation on the quantized graviton's polarizations (non-vacuity witnesses) -/

/-- The `+` polarization is a nonzero matrix (non-vacuity witness). -/
theorem polPlus_ne_zero : polPlus ≠ 0 := fun h => by
  simpa [polPlus] using congrFun (congrFun h 1) 1

/-- A nontrivial polarization combination is a nonzero matrix (from the G11a linear independence). -/
theorem pol_combo_ne_zero (a b : ℝ) (hab : ¬(a = 0 ∧ b = 0)) :
    a • polPlus + b • polCross ≠ 0 :=
  fun h => hab (graviton_polarizations_indep a b h)

/-- The z-directed wavevector family `k = (ω, 0, 0, κ)` — frequency `ω`, wavenumber `κ` (down-index). -/
def kZ (ω κ : ℝ) : Fin 4 → ℝ := ![ω, 0, 0, κ]

/-- `kDown` is the on-shell member `kZ 1 1` of the family. -/
theorem kDown_eq_kZ : kDown = kZ 1 1 := rfl

theorem minkQuad_kZ (ω κ : ℝ) : minkQuad (kZ ω κ) = κ ^ 2 - ω ^ 2 := by
  simp only [minkQuad, kZ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- Every polarization combination is transverse to every z-directed wavevector (on- or off-shell). -/
theorem kZ_transverse (ω κ a b : ℝ) :
    TransverseTo (kZ ω κ) (a • polPlus + b • polCross) := by
  intro ν
  fin_cases ν <;>
    simp [kContract, raiseIdx, kZ, polPlus, polCross, Fin.sum_univ_four, Matrix.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

/-- Every polarization combination is traceless. -/
theorem pol_combo_traceless (a b : ℝ) : etaTrace (a • polPlus + b • polCross) = 0 := by
  simp only [etaTrace, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, polPlus, polCross,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **A1 CAPSTONE — the quantized graviton solves linearized vacuum Einstein.** Every polarization content
    `a•e₊ + b•e×` of the quantized free graviton (the two helicity modes of `GravitonQuantization.lean`,
    kinematics G11a) at the null wavevector `kDown` satisfies `δG_{μν} = 0`: the field we quantized IS the
    graviton of general relativity (linearized, vacuum — header scope). -/
theorem graviton_solves_linearized_einstein (a b : ℝ) :
    einsteinSymbol kDown (a • polPlus + b • polCross) = 0 := by
  rw [kDown_eq_kZ]
  exact einsteinSymbol_null_tt _ _ (kZ_transverse 1 1 a b) (pol_combo_traceless a b)
    (by rw [minkQuad_kZ]; ring)

/-- **A1 CAPSTONE — linearized Einstein ⟺ the light-cone dispersion `ω² = κ²`.** For any nontrivial
    graviton polarization on the z-directed wavevector family `(ω,0,0,κ)`, the linearized vacuum Einstein
    equation holds exactly when `ω² = κ²` — the graviton propagates at the SPEED OF LIGHT because Einstein
    says so (and conversely). Non-vacuous: the polarization is a nonzero matrix, the family is genuinely
    off-shell for `ω² ≠ κ²`. (`k = 0` — the constant perturbation — sits inside `ω² = κ²`; "propagating"
    is the `k ≠ 0` reading.) -/
theorem einstein_iff_dispersion (ω κ a b : ℝ) (hab : ¬(a = 0 ∧ b = 0)) :
    einsteinSymbol (kZ ω κ) (a • polPlus + b • polCross) = 0 ↔ ω ^ 2 = κ ^ 2 := by
  rw [einsteinSymbol_eq_zero_iff_massless _ _ (kZ_transverse ω κ a b)
    (pol_combo_traceless a b) (pol_combo_ne_zero a b hab), minkQuad_kZ]
  constructor <;> intro h <;> linarith

end

end QIQTH.LinEinstein
