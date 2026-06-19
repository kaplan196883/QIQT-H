# Plan 55 — Machine-checking the Unruh effect (KMS / two-point-function route)

User directive: Unruh is in the books (rigorously), so formalize it — don't treat it as a wall (same
lesson as Raychaudhuri). This plan machine-checks the Unruh effect in its sharpest rigorous form: the
**KMS-thermality of the accelerated two-point function**, taking the free-field Wightman function as a
labeled definition (the field-theory input), and *proving* the thermal periodicity (geometry + complex
analysis). This shrinks Jacobson's cited "Unruh temperature" down to "the free-field two-point function
has its standard form" — exactly as Raychaudhuri shrank the front half to its physics core.

## The rigorous statement (refs: Crispino–Higuchi–Matsas, Rev. Mod. Phys. 80 (2008), arXiv:0710.5373;
## Wald, *QFT in Curved Spacetime*; Haag, *Local Quantum Physics*)

- **Free massless scalar Wightman function** (4D Minkowski, signature −+++):
  `W(x,x′) = −1/(4π²) · 1 / [ (t−t′−iε)² − |𝐱−𝐱′|² ]`.  **[INPUT — a labeled definition]**
- **Rindler worldline** (proper acceleration `a`, proper time `τ`): `x(τ) = (a⁻¹ sinh aτ, a⁻¹ cosh aτ, 0, 0)`
  (CHM eq. 36 at ξ=0). **[geometry]**
- **Pullback** along the worldline (Lorentzian interval): verified by hand,
  `(Δt)² − (Δx)² = (4/a²) sinh²(a Δτ/2)`,  so  `W(Δτ) = −a²/(16π²) · 1/sinh²(a(Δτ−iε)/2)`. **[geometry]**
- **KMS periodicity**: `sinh(a(Δτ−2πi/a)/2) = sinh(aΔτ/2 − iπ) = −sinh(aΔτ/2)`, so
  `W(Δτ − 2πi/a) = W(Δτ)` — periodic in imaginary proper time with period `2π/a`. **[complex analysis]**
  This **is** the KMS condition at inverse temperature `β = 2π/a` ⟹ **thermal at `T = a/2π` = `ℏκ/2π`
  with κ the surface gravity** (CHM eq. 60: the `e^{−2πω/a}` factor). **[the Unruh temperature]**

## Build order (`QIQTH/Unruh.lean`, axiom-free)
1. **Rindler interval identity (pure hyperbolic trig)** — the geometric heart, no QFT, no complex
   analysis: `(sinh A − sinh B)² − (cosh A − cosh B)² = 4 sinh²((A−B)/2)` (via `cosh_sub`,
   `cosh_sq_sub_sinh_sq`, `cosh_two_mul`), hence `(Δt)²−(Δx)² = (4/a²) sinh²(aΔτ/2)` on the worldline.
2. **The worldline + two-point function** as definitions (`rindlerWorldline a τ`, `wightman`).
3. **The `1/sinh²` pullback** — combine (1) and (2).
4. **KMS periodicity** (complex analysis): the complex function `z ↦ 1/sinh²(a z/2)` has period
   `2πi/a` (`Complex.sinh_add_pi_mul_I`-type / `sinh(z−iπ)=−sinh z`). State it as the KMS condition.
5. **Conclude**: a `KMS` predicate at `β` = thermality at `T=1/β`; the pulled-back correlator satisfies
   `KMS (2π/a)`, i.e. Unruh temperature `T = a/2π`.

## Honest scope
- **What gets proven:** the accelerated two-point function is KMS at β=2π/a (the Unruh temperature) —
  geometry + complex analysis, axiom-free.
- **What stays a labeled definition:** the *form* of the free-field Wightman function. *Deriving* it from
  the quantized field (Fock space + Bogoliubov, or the algebraic free-field net + modular theory) is the
  multi-year Type-III/continuum work the project's Tomita–Takesaki roadmap already targets — the KMS
  route lets us state+prove Unruh *without* it.
- **Net for the GR chain:** Jacobson's cited "Unruh temperature `T=ℏκ/2π`" becomes a machine-checked
  theorem modulo one labeled input (the two-point function form) — narrowing the cited list just as
  Raychaudhuri did for the geometry.
