# Symbolic (sympy) cross-check of the mixed-sliver Leibniz–Gaussian normal forms

**Date:** 2026-08-17
**Scope:** independent computer-algebra confirmation of the *target statements* the
`a₁ = R/6` mixed-sliver campaign is formalizing in Lean — specifically the on-gate second
field-partial decomposition claimed by
`QIQTH.ChartJetHessianMixed.gaussComp_amp_pd_pd_mixed` (mixed, `i ≠ j`), its diagonal
counterpart `QIQTH.HeatResidualBound.gaussComp_amp_pd_pd`, the underlying pure-Gaussian
partials (`gaussComp_pd`, `gaussComp_pd_pd_mixed`), and the Gaussian moment identities
(`HeatKernelA1.gaussianMoment_diag` and the parity cancellation for `i ≠ j`).

This is a **verification / cross-check artifact**, complementary to the Lean machine
proof: sympy re-derives each identity from scratch by direct symbolic differentiation
and reports `lhs − rhs`. Every check returned **exactly `0`**.

---

## 1. The exact mathematical claim (extracted from the Lean source)

Setup (matching the `pd` / `gaussDdim` conventions in `QIQTH/Curvature.lean` and
`QIQTH/FlatHeatEquation.lean`):

- `heatKernel1D τ w ∝ exp(−w²/(4τ))` (any `τ`-only normalization constant is
  `x`-independent and factors into `G`).
- `G(x) := gaussDdim τ (V(x)) = ∏ₖ heatKernel1D τ (Vₖ(x))`, a product Gaussian composed
  with a coordinate map `V : ℝⁿ → ℝⁿ`.
- `H(x) := G(x) · A(x)`, `A` the amplitude.
- Jets of the composed map at the base point:
  `Piₖ = ∂ᵢVₖ`, `Pjₖ = ∂ⱼVₖ`, `Qₖ = ∂ᵢ∂ⱼVₖ`.
- Contractions:
  `⟨V,Pi⟩ = Σₖ Vₖ Piₖ`, `⟨V,Pj⟩ = Σₖ Vₖ Pjₖ`,
  `⟨Pi,Pj⟩ = Σₖ Piₖ Pjₖ`, `⟨V,Q⟩ = Σₖ Vₖ Qₖ`.

**Mixed claim** (`gaussComp_amp_pd_pd_mixed`, `i ≠ j`):

```
∂ᵢ∂ⱼ(G·A) = G · [ ⟨V,Pi⟩⟨V,Pj⟩/(4τ²) − (⟨Pi,Pj⟩ + ⟨V,Q⟩)/(2τ) ] · A     (Hessian term)
          + G · (−⟨V,Pj⟩/(2τ)) · ∂ᵢA                                    (gradient-i term)
          + G · (−⟨V,Pi⟩/(2τ)) · ∂ⱼA                                    (gradient-j term)
          + G · ∂ᵢ∂ⱼA                                                    (mass term)
```

The distinctive feature (vs. the diagonal case) is that the mixed second Gaussian moment
is the **product** `⟨V,Pi⟩⟨V,Pj⟩` of two first-moment factors with **no** `−1/(2τ)`
diagonal self-term, plus the cross-jet `⟨Pi,Pj⟩` and second-jet `⟨V,Q⟩` corrections.

**Diagonal claim** (`gaussComp_amp_pd_pd`, `Pi = Pj = P`, `i = j`):

```
∂ᵢ∂ᵢ(G·A) = G · [ ⟨V,P⟩²/(4τ²) − (Σₖ Pₖ² + ⟨V,Q⟩)/(2τ) ] · A
          + 2 · G · (−⟨V,P⟩/(2τ)) · ∂ᵢA
          + G · ∂ᵢ∂ᵢA
```

(the two gradient terms merge into a single `2·(…)·∂ᵢA`).

---

## 2. sympy computations run

`V₀,…,V_{n−1}` and `A` are modeled as arbitrary smooth `sympy.Function`s of the
coordinates `x₀,…,x_{n−1}`; `∂ᵢ∂ⱼ(G·A)` is computed by `sympy.diff`, the claimed RHS is
assembled from the same symbolic jets, and `sympy.simplify(lhs − rhs)` is reported.

### 2a. Full amplitude-weighted decompositions

| identity | cases `(n,i,j)` | `simplify(lhs − rhs)` |
|---|---|---|
| `gaussComp_amp_pd_pd_mixed` | (2,0,1), (3,0,1), (3,1,2), (4,0,3) | **0** (all) |
| `gaussComp_amp_pd_pd` (diag) | (2,0), (3,1), (4,2) | **0** (all) |

### 2b. Underlying pure-Gaussian partials

| identity | cases | `simplify(lhs − rhs)` |
|---|---|---|
| `gaussComp_pd`   `∂ᵢG = G·(−⟨V,Pi⟩/2τ)` | (2,0), (3,1), (4,2) | **0** |
| `gaussComp_pd_pd_mixed`   `∂ᵢ∂ⱼG` closed form | (2,0,1), (3,0,2), (4,1,3) | **0** |

### 2c. Gaussian moment identities (weight `exp(−z²/(4τ))`, `sympy.integrate` over ℝ)

```
M0 = ∫ 1        = 2√π·√τ
M1 = ∫ z        = 0                (odd integrand → 0)
M2 = ∫ z²       = 4√π·τ^{3/2}
M2/M0           = 2τ              ← gaussianMoment_diag (diagonal second moment)
∫ zᵢzⱼ (i≠j)   = M1·M0 = 0        ← parity cancellation (off-diagonal moment)
```

The diagonal normalized second moment is exactly `2τ`, and the off-diagonal moment
vanishes by separability + oddness — confirming the parity-cancellation argument the
mixed-sliver estimate leans on.

---

## 3. Conclusion

Every algebraic identity that the mixed-sliver Lean bricks assert as their *target
statement* is **independently confirmed correct** by direct symbolic differentiation and
integration in sympy: all `lhs − rhs` residuals are exactly `0`, and the moment identities
match (`2τ` on-diagonal, `0` off-diagonal).

- No discrepancy or sign error was found.
- The mixed (`i ≠ j`) Hessian coefficient really is the *product* of first-moment factors
  with the cross-jet/second-jet corrections, with no spurious diagonal `−1/(2τ)` term.
- The diagonal specialization (merging the two gradient terms into `2·(…)·∂ᵢA`) is
  consistent with the mixed form.

This reduces risk in the remaining Lean formalization: the on-gate `mTerm`-form match the
campaign is discharging targets a **mathematically sound** identity. (This artifact
certifies the *algebra* of the target statement only; it does not machine-check the Lean
proof itself — that is the job of the Lean kernel and the `#print axioms` std-3 audit
already present in `ChartJetHessianMixed.lean`.)

Scripts: `verify_mixed.py`, `verify_aux.py` (run under the session scratchpad).
