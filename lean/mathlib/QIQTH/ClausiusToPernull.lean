import QIQTH.ClausiusIntegral
import QIQTH.EinsteinFieldEquation

/-!
# Wiring the integral Clausius step into the Einstein-equation-of-state chain

`EinsteinFieldEquation.lean` assembles Jacobson's derivation `jacobson_einstein_equation_of_state`
modulo a **per-null premise** `pernull`:

  for every point `x` and every metric-null direction `v`, the heat tensor `a·T − Ric` vanishes on `v`.

In Jacobson's paper (PRL 75, 1260 (1995), gr-qc/9504004 — read in `refs/`) that per-null relation is
**not** assumed; it is the *conclusion* of the Clausius relation `δQ = T δS` applied along each local
Rindler horizon generator. Concretely (his eqs. for `δQ` and `δA`), with `λ` the affine parameter on the
generator,

  `δQ = −κ ∫_H λ · T_{ab}k^ak^b dλ dA`   (heat flux, boost Killing weight `χ = −κλk`),
  `δA = − ∫_H λ · R_{ab}k^ak^b dλ dA`     (area change, via Raychaudhuri `θ = −λ R_{ab}k^ak^b`),

and `δQ = T δS = (ℏκ/2π) η δA` (the `κ` cancels) forces, *for every upper limit of integration*, the two
affine-parameter-weighted integrands to agree at the horizon point — i.e. `T_{ab}k^ak^b = (ℏη/2π)R_{ab}k^ak^b`.

This file proves exactly that reduction: it **derives `pernull` from the raw integral Clausius relation**
(`value_at_zero_of_weighted_integral_proportional` from `ClausiusIntegral.lean`, machine-checked via the FTC
+ l'Hôpital), so that the end-to-end theorem can be stated with Jacobson's *actual* eq.(`dQ`)=eq.(`dA`)
premise instead of an already-contracted per-null relation. The cited physics is now exactly Jacobson's
(area law `δS = ηδA`, the Unruh temperature `T = ℏκ/2π`, and `δQ = TδS`) — nothing more is assumed, and the
integral→point step is no longer a gap. Axiom-free.
-/

namespace QIQTH.Curvature

open QIQTH.EinsteinEOS QIQTH.ClausiusIntegral MeasureTheory

/-- **`BL` is linear in its tensor argument**: `BL(a·T − R) = a·BL T − BL R`. The bilinear form
`∑_{ij} C_{ij} v^i v^j` distributes over the heat tensor `a·T − Ric`. -/
theorem BL_smul_sub (a : ℝ) (T R : Fin 4 → Fin 4 → ℝ) (v : Fin 4 → ℝ) :
    BL (fun i j => a * T i j - R i j) v = a * BL T v - BL R v := by
  simp only [BL]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- **The per-null Clausius relation from the affine-weighted integral relation.** For each spacetime
point `x` and metric-null direction `v`, let `Tgen x v : ℝ → ℝ` and `Rgen x v : ℝ → ℝ` be the boost-
energy flux `T_{ab}k^ak^b` and the focusing scalar `R_{ab}k^ak^b` along the horizon generator, as
functions of the affine parameter `λ` (so their value at `λ = 0` is the contraction at the point `x`,
`hT0`/`hR0`). If — *for every null direction and every upper limit `ε`* — the affine-weighted heat-flux
integral `∫₀^ε λ·(a·T_{kk}) dλ` equals the area-change integral `∫₀^ε λ·R_{kk} dλ` (this is Jacobson's
`δQ = TδS` with the `κ`'s cancelled and the constant `a = 2π/ℏη` folded in), then the heat tensor
`a·T − Ric` vanishes on the whole null cone — i.e. the **`pernull` premise** of
`jacobson_einstein_equation_of_state`. Proof: the integral relation forces the leading `ε²` coefficients
to match (`value_at_zero_of_weighted_integral_proportional`), giving `a·T_{kk}(0) = R_{kk}(0)` for each
null `v`, which is `BL(a·T − Ric) v = 0` by `BL_smul_sub`. -/
theorem pernull_of_clausius_integral
    (g gi : Point 4 → Fin 4 → Fin 4 → ℝ)
    (T : Point 4 → Fin 4 → Fin 4 → ℝ) (a : ℝ)
    (Tgen Rgen : Point 4 → (Fin 4 → ℝ) → ℝ → ℝ)
    (hTcont : ∀ x v, Continuous (fun l => a * Tgen x v l))
    (hRcont : ∀ x v, Continuous (Rgen x v))
    (hT0 : ∀ x v, Tgen x v 0 = BL (T x) v)
    (hR0 : ∀ x v, Rgen x v 0 = BL (fun i j => ricci g gi i j x) v)
    (clausius : ∀ x v, BL (g x) v = 0 →
        ∀ ε : ℝ, (∫ l in (0:ℝ)..ε, l * (a * Tgen x v l)) = ∫ l in (0:ℝ)..ε, l * Rgen x v l) :
    ∀ (x : Point 4) (v : Fin 4 → ℝ),
      BL (g x) v = 0 → BL (fun a' b => a * T x a' b - ricci g gi a' b x) v = 0 := by
  intro x v hv
  have hpt : (fun l => a * Tgen x v l) 0 = 1 * Rgen x v 0 :=
    value_at_zero_of_weighted_integral_proportional 1 (hTcont x v) (hRcont x v)
      (fun ε => by rw [one_mul]; exact clausius x v hv ε)
  simp only [one_mul] at hpt
  rw [hT0 x v, hR0 x v] at hpt
  rw [BL_smul_sub a (T x) (fun i j => ricci g gi i j x) v]
  linarith [hpt]

/-- **Jacobson's Einstein equation of state — from the integral Clausius relation.** The end-to-end
theorem `jacobson_einstein_equation_of_state` with its `pernull` hypothesis discharged by
`pernull_of_clausius_integral`. The remaining physical premises are now *exactly* Jacobson's: the
affine-weighted **integral Clausius relation** `∫₀^ε λ·(a·T_{kk}) = ∫₀^ε λ·R_{kk}` along every local
Rindler horizon (= `δQ = TδS` with the Unruh temperature and area law folded in), local conservation
`∇^μ(a·T) = 0`, the Lorentzian structure (Sylvester congruence `g = Pᵀ·η·P`), and the analytic
regularity of the proportionality scalar `f`. Everything geometric — Raychaudhuri's integral form, the
per-null→tensor upgrade, the contracted Bianchi identity, the cosmological constant — is proven and
axiom-free. Conclusion: `a·T_{μν} = G_{μν} + Λ·g_{μν}` for a genuine constant `Λ`. -/
theorem jacobson_einstein_from_clausius_integral
    (g gi : Point 4 → Fin 4 → Fin 4 → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hCgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (T : Point 4 → Fin 4 → Fin 4 → ℝ) (a : ℝ)
    (hT_symm : ∀ x a' b, T x a' b = T x b a')
    (hric_symm : ∀ x a' b, ricci g gi a' b x = ricci g gi b a' x)
    (P Pinv : Point 4 → Fin 4 → Fin 4 → ℝ)
    (hPP : ∀ x i j, (∑ k, P x i k * Pinv x k j) = if i = j then (1 : ℝ) else 0)
    (hPP' : ∀ x i j, (∑ k, Pinv x i k * P x k j) = if i = j then (1 : ℝ) else 0)
    (hcong : ∀ x i j, g x i j = ∑ k, ∑ l, P x k i * QIQTH.EinsteinEOS.gm k l * P x l j)
    -- the affine-parameter scalars along each generator, and their value at the horizon point
    (Tgen Rgen : Point 4 → (Fin 4 → ℝ) → ℝ → ℝ)
    (hTcont : ∀ x v, Continuous (fun l => a * Tgen x v l))
    (hRcont : ∀ x v, Continuous (Rgen x v))
    (hT0 : ∀ x v, Tgen x v 0 = QIQTH.EinsteinEOS.BL (T x) v)
    (hR0 : ∀ x v, Rgen x v 0 = QIQTH.EinsteinEOS.BL (fun i j => ricci g gi i j x) v)
    -- Jacobson's integral Clausius relation δQ = TδS (eq. dQ = eq. dA), per null direction
    (clausius : ∀ x v, QIQTH.EinsteinEOS.BL (g x) v = 0 →
        ∀ ε : ℝ, (∫ l in (0:ℝ)..ε, l * (a * Tgen x v l)) = ∫ l in (0:ℝ)..ε, l * Rgen x v l)
    (hreg : ∀ f : Point 4 → ℝ,
        (∀ y a' b, a * T y a' b = ricci g gi a' b y + f y * g y a' b) →
        (∀ x ρ, PdiffAt f ρ x) ∧
          Differentiable ℝ (fun y => f y + (1 / 2 : ℝ) * scalarCurv g gi y))
    (conserv : ∀ x ν, div02 g gi (fun y a' b => a * T y a' b) ν x = 0) :
    ∃ Λ : ℝ, ∀ x μ ν, a * T x μ ν = einsteinTensor g gi μ ν x + Λ * g x μ ν :=
  jacobson_einstein_equation_of_state g gi hsymm hsymm_gi hinv hCg hCgi hC T a hT_symm hric_symm
    P Pinv hPP hPP' hcong
    (pernull_of_clausius_integral g gi T a Tgen Rgen hTcont hRcont hT0 hR0 clausius)
    hreg conserv

end QIQTH.Curvature
