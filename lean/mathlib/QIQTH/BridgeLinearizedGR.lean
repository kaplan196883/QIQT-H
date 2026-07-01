/-
  BRIDGE A1 — the full linearized Einstein tensor: the quantized graviton solves linearized vacuum Einstein.

  ★ SCOPE (BRIDGE_PLAN.md, GPT-5.5-pro-verified). Flat Minkowski background (Jacobson-style linearized bridge, NOT
    AdS/FGHMVR). We define the **full flat-background linearized Einstein tensor** — for a *general* perturbation,
    not only on-shell radiative modes — in its **plane-wave symbol** form: for `h_{μν}(x) = e_{μν}·f(k·x)` every
    derivative `∂_μ` becomes the wavevector `k_μ` (times `f''`), so the linearized Ricci tensor
        R⁽¹⁾_{μν} = ½(∂_α∂_μ h^α_ν + ∂_α∂_ν h^α_μ − □h_{μν} − ∂_μ∂_ν h)
    becomes the algebraic symbol
        linRicci k e μ ν = ½(k_μ (k·e)_ν + k_ν (k·e)_μ − k² e_{μν} − k_μ k_ν tr_η e),
    and the linearized Einstein tensor is `linEinstein = linRicci − ½ η · (η-trace of linRicci)`. This IS the full
    `G⁽¹⁾` (as a function of any symmetric symbol `e` and any wavevector `k`) — the `residual` object the assembly
    increment (ASM) feeds into the FGHMVR skeleton `G1`.

  Results (all finite algebra, axiom-free):
  • `linEinstein_gauge` — **gauge invariance**: a pure-gauge symbol `e = k⊙ξ` has `G⁽¹⁾ = 0` identically (any `k`).
  • `linEinstein_tt` — **the TT-gauge reduction lemma**: transverse (`k^α e_{αν} = 0`) + traceless (`tr_η e = 0`) ⟹
    `G⁽¹⁾ = −½ k² e` — the momentum-space form of `G⁽¹⁾_{μν} = −½ □h_{μν}` in TT gauge.
  • `graviton_solves_linEinstein` — **the corollary/anchor**: for the null `k` (`k² = 0`, `kUp_null`) every TT
    polarization satisfies `G⁽¹⁾ = 0`; instantiated at `polPlus`/`polCross` — **the field we quantized (Q1–Q6) is
    provably the graviton of general relativity** (its polarizations solve linearized vacuum Einstein).

  ⚠ Honest labels: linearized ≠ full GR; the SYMBOL calculus is exact for plane waves (each mode of the free field);
    free ≠ interacting; this anchors the graviton to GR — it does NOT derive gravity (BRIDGE_PLAN.md ingredient D).
-/
import Mathlib
import QIQTH.EmergentDynamics

namespace QIQTH.Bridge

open QIQTH.GravDyn

/-- Index raising with `η = diag(−1,1,1,1)`: `k^μ = η^{μν} k_ν` (flip the time component). -/
def raise (k : Fin 4 → ℝ) : Fin 4 → ℝ := ![-(k 0), k 1, k 2, k 3]

/-- The transversality contraction `(k·e)_ν = k^α e_{αν}`. -/
def kContr (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ) (ν : Fin 4) : ℝ :=
  -(k 0) * e 0 ν + k 1 * e 1 ν + k 2 * e 2 ν + k 3 * e 3 ν

/-- The `η`-trace `tr_η e = η^{μν} e_{μν} = −e₀₀ + e₁₁ + e₂₂ + e₃₃` (the `Traceless` expression). -/
def trEta (e : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := -(e 0 0) + e 1 1 + e 2 2 + e 3 3

/-- **The linearized Ricci tensor** (plane-wave symbol): `R⁽¹⁾_{μν} = ½(k_μ(k·e)_ν + k_ν(k·e)_μ − k²e_{μν}
    − k_μk_ν tr_η e)` — every `∂` of the position-space formula replaced by `k` on the plane-wave sector. -/
noncomputable def linRicci (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun μ ν =>
    (1 / 2) * (k μ * kContr k e ν + k ν * kContr k e μ - minkQuad k * e μ ν - k μ * k ν * trEta e)

/-- The linearized Ricci scalar `R⁽¹⁾ = η^{μν} R⁽¹⁾_{μν}`. -/
noncomputable def linRicciScalar (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  -(linRicci k e 0 0) + linRicci k e 1 1 + linRicci k e 2 2 + linRicci k e 3 3

/-- **The full linearized Einstein tensor** `G⁽¹⁾_{μν} = R⁽¹⁾_{μν} − ½ η_{μν} R⁽¹⁾` — defined for EVERY wavevector
    `k` and EVERY perturbation symbol `e` (not only on-shell/TT modes): the `residual` of the bridge assembly. -/
noncomputable def linEinstein (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun μ ν => linRicci k e μ ν - (1 / 2) * minkMetric μ ν * linRicciScalar k e

/-- **Gauge invariance of the linearized Einstein tensor.** A pure-gauge perturbation `e_{μν} = k_μξ_ν + k_νξ_μ`
    (a linearized diffeomorphism, ANY wavevector `k`, on- or off-shell) has `G⁽¹⁾ = 0` identically — the linearized
    diffeomorphism invariance of GR at the symbol level. -/
theorem linEinstein_gauge (k ξ : Fin 4 → ℝ) :
    linEinstein k (Matrix.of fun μ ν => k μ * ξ ν + k ν * ξ μ) = 0 := by
  ext μ ν
  fin_cases μ <;> fin_cases ν <;>
    simp only [linEinstein, linRicci, linRicciScalar, kContr, trEta, minkQuad, minkMetric,
      Matrix.of_apply, Matrix.diagonal_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.zero_apply] <;>
    norm_num <;> ring

/-- **The TT-gauge reduction lemma** `G⁽¹⁾_{μν} = −½ k² e_{μν}`: for a transverse (`k^αe_{αν} = 0`) and traceless
    (`tr_η e = 0`) perturbation, the full linearized Einstein tensor collapses to `−½ k² e` — the momentum-space
    statement of "`G⁽¹⁾ = −½ □h` in TT gauge". So on the TT sector, `□h = 0` IS the linearized Einstein equation. -/
theorem linEinstein_tt (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ)
    (hT : ∀ ν, kContr k e ν = 0) (hTr : trEta e = 0) :
    linEinstein k e = (-(1 / 2) * minkQuad k) • e := by
  have hR : ∀ μ ν, linRicci k e μ ν = -(1 / 2) * minkQuad k * e μ ν := by
    intro μ ν
    simp only [linRicci, Matrix.of_apply, hT, hTr]
    ring
  have hS : linRicciScalar k e = 0 := by
    have htr' : -(e 0 0) + e 1 1 + e 2 2 + e 3 3 = 0 := by simpa [trEta] using hTr
    simp only [linRicciScalar, hR]
    linear_combination (-(1 / 2) * minkQuad k) * htr'
  ext μ ν
  simp only [linEinstein, Matrix.of_apply, hR, hS, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The existing `Transverse` (built on the raised `kUp`) is exactly the `kContr`-transversality for `kDown`. -/
theorem kContr_kDown_of_transverse (e : Matrix (Fin 4) (Fin 4) ℝ) (hT : Transverse e) :
    ∀ ν, kContr kDown e ν = 0 := by
  intro ν
  have h := hT ν
  simp only [kUp, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three] at h
  simp only [kContr, kDown, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]
  linarith

/-- The existing `Traceless` is exactly `trEta e = 0`. -/
theorem trEta_of_traceless (e : Matrix (Fin 4) (Fin 4) ℝ) (hTr : Traceless e) : trEta e = 0 := by
  simpa [trEta, Traceless] using hTr

/-- The canonical wavevector is null in the `minkQuad` sense: `k² = 0` (the masslessness of `kUp_null`). -/
theorem minkQuad_kDown : minkQuad kDown = 0 := by
  simp only [minkQuad, kDown, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]
  norm_num

/-- **A1 CAPSTONE — the quantized graviton solves linearized vacuum Einstein.** Every transverse-traceless
    perturbation on the null wavevector `k` satisfies `G⁽¹⁾ = 0`: the TT reduction gives `G⁽¹⁾ = −½k²e` and
    masslessness (`k² = 0`) kills it. The field quantized in Q1–Q6 — whose polarization content is exactly this TT
    sector (`tt_decomposition`) — is provably **the graviton of general relativity**. ⚠ Linearized, vacuum, free. -/
theorem graviton_solves_linEinstein (e : Matrix (Fin 4) (Fin 4) ℝ)
    (hT : Transverse e) (hTr : Traceless e) :
    linEinstein kDown e = 0 := by
  rw [linEinstein_tt kDown e (kContr_kDown_of_transverse e hT) (trEta_of_traceless e hTr),
    minkQuad_kDown]
  simp

/-- The `+` polarization solves linearized vacuum Einstein. -/
theorem einstein_polPlus : linEinstein kDown polPlus = 0 :=
  graviton_solves_linEinstein polPlus polPlus_transverse polPlus_traceless

/-- The `×` polarization solves linearized vacuum Einstein. -/
theorem einstein_polCross : linEinstein kDown polCross = 0 :=
  graviton_solves_linEinstein polCross polCross_transverse polCross_traceless

end QIQTH.Bridge
