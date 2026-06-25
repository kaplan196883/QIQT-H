# Deriving the Bekenstein–Hawking `1/4` from the free Klein–Gordon field (Sakharov / induced gravity)

**Stage A of `SAKHAROV_KG_PLAN.md`.** The analytic derivation behind the symbolic check
`scripts/sakharov_kg.py`. It reproduces the **Susskind–Uglum (1994) / Jacobson (1994)** result: for the free
scalar, the **entanglement entropy** `S_ent` across a surface and the **induced Newton constant** `G_ind` come
from the *same* UV divergence, and `S_ent = A/(4 G_ind)` — so the `1/4` is **forced by the matter content**, not
postulated. This reproduces known physics; the QIQT-H-native content (the finiteness regulator + the circularity
audit) is **Stage B**.

## 1. Setup — the free scalar and its heat kernel

A free, minimally-coupled scalar `φ` on a 4D (Euclidean) background has the operator `Δ = −□ + m²`. Its heat
kernel has the Seeley–DeWitt expansion
```
   Tr e^{−tΔ}  =  (4πt)^{−2} ∫ √g d⁴x  ( a₀ + a₁ t + a₂ t² + ⋯ ) ,    a₀ = 1,   a₁ = (1/6 − ξ) R.
```
Minimal coupling (`ξ = 0`) gives **`a₁ = R/6`** — the coefficient that will produce *both* the induced Newton
constant and the entanglement entropy.

## 2. The induced Newton constant (Sakharov)

Integrating out `φ` gives the one-loop effective action
```
   W  =  −½ ∫_{ε²}^{∞} (dt/t) Tr e^{−tΔ} ,
```
with `ε` a UV (proper-time) cutoff. The `R`-term (`a₁ = R/6`) contributes
```
   W ⊃ −½ (4π)^{−2} (R/6) ∫_{ε²}^{∞} dt/t²  =  −½ (4π)^{−2} (R/6) · (1/ε²) .
```
Identifying this with the **induced Einstein–Hilbert action** `−(1/16πG_ind) ∫√g R`:
```
   1/(16πG_ind) = ½ (4π)^{−2} (1/6) (1/ε²)   ⟹   1/G_ind = 1/(12π ε²) .
```
So the scalar's vacuum fluctuations *induce* Newton's constant, with the famous quadratic (Sakharov) divergence.

## 3. The entanglement entropy (conical-deficit / replica)

The entanglement entropy of a region with boundary surface `Σ` (area `A`) is computed by the **replica trick**:
put the theory on an `n`-sheeted cover branched over `Σ` (an `n`-fold cone), compute `W_n`, and
```
   S_ent = (1 − n ∂_n) W_n |_{n=1} .
```
The `n`-cone has a **conical singularity** at `Σ` of deficit angle `2π(1−n)`, whose curvature is a
delta-function on `Σ`:
```
   ∫√g R  ⊃  4π(1−n) A          (the conical curvature, concentrated on Σ).
```
Feeding this into the induced EH action `(1/16πG_ind)∫√g R` and applying the replica formula:
```
   W_n ⊃ (1/16πG_ind) · 4π(1−n) A ,
   S_ent = (1 − n ∂_n)[ (1/16πG_ind) 4π(1−n) A ]|_{n=1}  =  (4π/16π) · A/G_ind  =  A/(4 G_ind).
```
Numerically, with `1/G_ind = 1/(12π ε²)`: `S_ent = A/(48π ε²)` — the standard leading area-law divergence.

## 4. The `1/4` — and why it is universal

The ratio is **cutoff-independent** (the `ε`-divergence cancels) and **matter-independent**:
```
   S_ent / ( A · (1/G_ind) )  =  4π / 16π  =  1/4 .
```
The decisive observation: **the `1/4` is the purely *geometric* ratio**
```
   (conical-deficit curvature normalization, 4π)  /  (Einstein–Hilbert action normalization, 16π)  =  1/4 .
```
The matter (the scalar, via the heat-kernel `a₁`) enters *only* through the common factor `1/G_ind`, which
cancels in the ratio. **This is why the Bekenstein–Hawking `1/4` is universal** — the same for every field
species, every horizon, in Einstein gravity: it is a fact about how a conical deficit couples to the
Einstein–Hilbert action, not about *which* matter induces `G`. (Different species change `G_ind`; none change
the `1/4`.)

So:
```
   S_ent  =  A / (4 G_ind)        — the Bekenstein–Hawking form, DERIVED, with the 1/4 forced.
```

## 5. What this establishes — and what it does not (honest scope)

**Establishes (the mechanism):** the `1/4` of `S = A/4ℓ_P²` is *not* an independent constant — it is the
geometric `(conical 4π)/(EH 16π)` ratio, and the area law `S_ent = A/4G_ind` is *forced* once the matter induces
`G`. The matter's vacuum entanglement entropy *is* the Bekenstein–Hawking entropy. So `P4`'s coefficient is, at
the level of this mechanism, a **theorem of the field's UV structure + the geometry**, not a postulate.

**Does NOT establish (the honest limits):**
- The individual coefficients (`48π`, `12π`) are **scheme-dependent**; only the *ratio* `1/4` is robust (it is
  geometric). The check verifies the robust quantity.
- **Free, minimally-coupled scalar only.** Non-minimal coupling, gauge fields (edge modes), and fermions need
  the **contact-term** care (Kabat 1995); the *universality* of `1/4` across all species — the full
  Susskind–Uglum — is NOT delivered by this scalar computation.
- **The species problem.** This fixes `1/G_ind` for *one* field; the *physical* value of `G` (hence `ℓ_P`) needs
  the full matter content. The derivation gives the **`1/4` ratio and the mechanism**, not the value of `G`.
- **Mechanism, not micro-theory.** It shows the `1/4` *can* come from matter entanglement; it does not build the
  finite record micro-theory (the "it-from-qubit" endpoint). It is the bridge between the machine-checked
  crossed-product dressing and that frontier.

## 6. Toward QIQT-H (Stage B preview)

The generic UV cutoff `ε` is replaced by QIQT-H's **finiteness regulator** (the finite record structure /
minimal-length deformation). Because the `1/4` is the *geometric* ratio `4π/16π` — **independent of the
regulator** — it is unchanged. The load-bearing Stage-B task is the **circularity audit**: proving the area law
is *not* smuggled in via the regulator, i.e. that the `1/4` comes from the conical/EH geometry + the matter `a₁`,
not from having *assumed* `S ∝ A`. The finiteness supplies a *finite UV*; the matter+geometry supply the
*coefficient*.

## References
Sakharov 1967 (induced gravity); Bombelli–Koul–Lee–Sorkin 1986, Srednicki 1993 (entanglement area law);
Callan–Wilczek 1994, Kabat 1995 (conical / contact terms); Susskind–Uglum 1994, Jacobson 1994
(`S_BH` = matter entanglement = `A/4G_ind`); Solodukhin, *Living Rev. Rel.* 14 (2011) 8 (review).
