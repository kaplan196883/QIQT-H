# Does QIQT-H's covariant per-diamond capacity escape CPSUV? — the decisive plan

**Status:** ACTIVE PLAN (2026-06-30), grounded in a GPT-5.5-pro consult. **Question (sharp):** the QG campaign's
I4 showed a *local-frame* finite cutoff radiatively generates `Δc² = Z_s/Z_t − 1 → (4/3)·g²/16π² ≠ 0` (CPSUV).
QIQT-H imposes capacity *covariantly, per causal diamond* (`log #Atoms ≤ Q_D = A(∂D)/4ℓ_P²`,
`LorentzSelection.lean` — see [[qiqth_lorentz_two_threads]]). **Does that covariant per-diamond / modular capacity
regulator reintroduce a preferred frame in interacting matter loops (⟹ Δc² ≠ 0, CPSUV still fires), or is it
genuinely Lorentz-scalar (⟹ Δc² = 0, escaped)?**

## 0. The crux — and the honest verdict to beat

> **Covariance of the diamond *family* is NOT invariance of a single regulator (category error to conflate).** A
> fixed diamond `D` supplies a unit timelike vector `u_D` (its tips). Family-covariance only gives
> `Π_D(p, u_D) = Π_{ΛD}(Λp, Λu_D)`, which *allows* `Γ⁽²⁾(p) = A·p² + B·(u_D·p)²` — and `B` **is** the `Z_t≠Z_s`
> term. So the answer is decided entirely by the regulator's **principal (UV) symbol** `F_D(x,k)`:
> - **Lorentz-scalar** `F = f(k_E²/Λ²)` (proper-time / □ / PV) ⟹ Ward identity `Γ⁽²⁾ = F(p²)` ⟹ **Δc² = 0 (ESCAPE)**.
> - **Frame-picking** `F = f((u_D·k)², k_⊥²)` (mode / modular-energy truncation) ⟹ **Δc² ~ C·g²/16π² (FAIL)**.
>
> A literal modular-energy (`K_D`-spectral) cutoff is, at the diamond center, a 3-momentum cutoff in the diamond
> rest frame (`Λ_K = Ω/πR`) — the CPSUV-dangerous class. **Expected: a mode-truncation capacity FAILS with the
> same 4/3.** KMS/cyclicity of the modular/crossed-product trace does **not** rescue it (finite-T field theory is
> the counterexample: a KMS state has a rest frame; `Z_t ≠ Z_s`). The escape exists **only** if "finite capacity"
> is implemented as a *nonlocal/algebraic counting constraint over a covariant UV kernel*, NOT as discarding high
> modes of one diamond's modular Hamiltonian.

### Honest invariants
- Never claim QG or the value of `G`. The `1/4` *ratio* IS derived (`SakharovRatio.lean`).
- Finiteness is a BET to be TESTED. Ship green increments (Lean) / reproducible scripts (numerics); checkpoint
  frontiers honestly. The likely outcome is that the *mode-truncation* reading FAILs and the *escape* requires a
  genuinely nonlocal capacity — say so plainly.

## 1. The decisive criterion (what "solved" means)
"Solved" = a clear verdict on **which symbol class QIQT-H's actual capacity regulator is in**:
- if it is a mode/modular-energy truncation → **FAIL** (CPSUV fires even for covariant per-diamond capacity ⟹
  finite capacity cannot be a *local* Lorentzian regulator; the escape must be nonlocal/algebraic), or
- if it is (or can be) a nonlocal counting constraint over a Lorentz-scalar UV kernel → **ESCAPE candidate**, to
  be confirmed by an explicit Ward identity / local-symbol proof.

## 2. Sequenced increments (most-tractable-first)

### J1 — numerical regulator comparison *(extend `scripts/qg/cpsuv_speed_splitting.py`; ~done; days)*
Add to the existing one-loop Δc² code three regulators on the Euclidean Yukawa self-energy
`Π_D(p) = −4g² ∫ d⁴k_E/(2π)⁴ [m²−k·(k+p)] / [(k²+m²)((k+p)²+m²)] · F_D(k) F_D(k+p)`:
- **Reg A (covariant control):** `F = exp[−(k_E²+m²)/Λ²]` ⟹ `Π = Π(p²)` ⟹ **Δc² = 0** (PASS control).
- **Reg K (WKB modular / diamond-center cutoff):** `F_K(k) = Θ(Ω/πR − |k|)` ⟹ the sharp rest-frame 3-cutoff ⟹
  **Δc² → 4/3·g²/16π²** (the diamond mode-truncation = CPSUV).
- **Reg C (modular + covariant scan):** `F = exp[−(k_E²/Λ²)ⁿ]·exp[−(k_4²/Λ_K²)ⁿ]`, scan `α = Λ_K/Λ`: `α→∞` ⟹
  Δc²→0; `α=O(1)` ⟹ Δc²→C(α,n)≠0.
**PASS/FAIL:** confirms numerically that *covariant-symbol* regulators give 0 and *modular/mode-truncation* ones
give the CPSUV constant — pinning the criterion to the symbol class. Deliverable: extended script + data + note.

### J2 — the LOCAL-SYMBOL AUDIT of QIQT-H's actual capacity *(THE key conceptual increment; days–week)*
Read `QIQTH/LorentzSelection.lean` + the capacity definition (`log #Atoms ≤ Q_D`): **is `Q_D` implemented as (a)
a per-diamond MODE/modular-energy truncation, or (b) a nonlocal/algebraic state-COUNT constraint?** Write the
high-frequency Wigner symbol `F_D(x,k)` of the actual regulator.
**PASS (escape-class):** `F_D = f(k_E²/Λ²) + O((ΛR)⁻¹)` in the bulk. **FAIL (CPSUV-class):** `F_D = f((u_D·k)²,
k_⊥²)`. *This audit decides the answer* — the numerics (J1) only calibrate the criterion. Deliverable: a markdown
verdict citing the exact code.

### J3 — the Ward dichotomy as a Lean theorem *(machine-check the interface; tractable)*
Formalize the symbol→Δc² dichotomy as an axiom-free algebraic theorem (the analog of `Phase5Master`): a 2-point
1PI `Γ⁽²⁾` that is **isotropic** (`Γ = F(p²)`, i.e. a fixed-Lorentz Ward identity holds) has `Z_t = Z_s` (Δc²=0);
a `Γ = A·p² + B·(u·p)²` has `Δc² = B/(A)` (≠0 iff B≠0). Reduces "does QIQT-H escape" to "is its regulator
fixed-Lorentz-invariant (B=0)." Deliverable: `QIQTH/QG/WardSpeedSplitting.lean`, std-3, budget 0.

### J4 — modular + covariant auxiliary scan, quantified *(numerics; days)*
Full Reg-C scan: `Δc²(α, n)` curve; locate the threshold where the modular cutoff stops mattering. Tells us, IF
QIQT-H's capacity is "modular cutoff above a covariant UV kernel," what scaling `α = Λ_K/Λ` it must satisfy to be
safe. Deliverable: data + note.

### J5 — exact wedge/Rindler modular-mode check *(frontier; weeks–months — checkpoint)*
Boost modular energy = angular momentum `n` in Euclidean polar coords; angular-mode-truncated kernel
`G_N = ∑_{|n|≤N} ∫ dq q ∫ d²k_⊥ J_{|n|}(qρ)J_{|n|}(qρ') e^{in(θ−θ')} … / (q²+k_⊥²+m²)`. Test whether the
angular/modular cutoff alone isotropizes the kinetic tensor (likely NOT — leaves UV divergence / anisotropy).
Checkpoint with the honest finding.

### J6 — covariant finite-capacity candidate *(the real construction; months–years — checkpoint)*
The genuine escape: a Lorentz-scalar UV kernel (proper-time `G_Λ(k) = ∫_{Λ⁻²}^∞ ds e^{−s(k_E²+m²)}` or Källén–
Lehmann `∫ dμ² ρ_Λ(μ²) G^cov_{μ²}`) with the area capacity imposed as a **nonlocal/algebraic** state-count
constraint (the CLPW/crossed-product trace `τ_D`, not a mode cutoff), such that one-loop Δc²=0 by Ward identity
WHILE `τ_D(P_Q^D) ≤ e^{A/4ℓ_P²}`. The crossed-product machinery we have ([[CROSSED_PRODUCT scope]]) is the
candidate home. Checkpoint: this is QIQT-H's real construction problem.

## 3. Likely outcome + what we can actually settle now
**Most likely:** J1 confirms the symbol criterion; J2 finds QIQT-H's per-diamond capacity, *as currently coded*,
is an information/counting bound (`log #Atoms ≤ Q_D`) — NOT yet a concrete matter-loop regulator — so the honest
status is: the kill applies to the *mode-truncation reading*, and the *escape* requires J6 (covariant kernel +
algebraic capacity), which is the open construction. The loop CAN settle J1–J4 (the criterion, the audit, the
Ward theorem, the scan) and decisively checkpoint J5–J6. That is "solved" in the achievable sense: a definite
verdict on whether QIQT-H's capacity is CPSUV-safe *as a regulator*, and exactly what a safe one must be.

## 4. Verification (per increment)
Lean: `cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green; `#print axioms` = std-3;
`bash scripts/axiom_budget_check.sh` budget 0; wire into `QIQTH.lean` + `AxiomAudit.lean`. Numerics: reproducible
`scripts/qg/` script + data + honest note. One commit per increment with the
`Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>` trailer; push via schannel; update §5.

## 5. Progress log
- **2026-06-30** — plan created (GPT-5.5-pro consult).
- **2026-06-30 — J1 ✅ DONE** (`scripts/qg/covariant_capacity_regulators.py` + `J1_regulator_symbol_result.md`):
  the regulator symbol test via the LV-sourcing anisotropy `A_F = ⟨k₄²−k_x²⟩_F` (=0 ⟺ Lorentz-scalar ⟺ Δc²=0).
  **Reg A (covariant) → A_F=0.000** (PASS); **Reg K (modular/diamond cutoff Θ(Λ_K−s)) → A_F≈0.33, un-suppressed
  in Λ_K** (FAIL — the I4 4/3 CPSUV class); **Reg C (modular+covariant) → A_F→0 only as α=Λ_K/Λ→∞** (modular
  factor must be parametrically inactive). Numerically confirms the crux: **covariance of the per-diamond FAMILY
  does NOT buy Δc²=0 — only a Lorentz-SCALAR symbol does.** A mode/modular-truncation capacity FAILs.
- **2026-06-30 — J2 ✅ DONE (the decisive audit)** (`scripts/qg/J2_capacity_symbol_audit.md`): read QIQT-H's
  actual capacity — `RecordedHistoryNet.card_le : Fintype.card (P.X D) ≤ N D ≈ exp(Q_D)`, a **cardinality bound on
  the decoherent record-sector fibre** per causal diamond (`LorentzSelection.lean`). **Verdict: class (b) — an
  algebraic STATE-COUNT, NOT a mode/modular-energy truncation** (there is no field momentum or modular spectrum in
  the structure; `P.X D` is an abstract finite record-atom type with the decoherence measure `ω`). Two-sided
  consequence: **(+)** it has no frame-picking matter-field UV symbol ⟹ the I4/CPSUV kill **does NOT apply** (not
  FAIL); **(−)** but it is **silent on the matter-field UV regulator** ⟹ not an escape either. **Status: "not
  FAIL, not yet ESCAPE."** A full escape requires pairing the algebraic count with a Lorentz-scalar matter kernel
  = J6. This is exactly the plan's anticipated outcome, now grounded in the code.
- **2026-06-30 — J3 ✅ DONE** (`QIQTH/QG/WardSpeedSplitting.lean`): the Ward dichotomy as axiom-free Lean.
  `speedSplitting Zt Zs = Zs/Zt − 1`; `speedSplitting_eq_zero_iff` (Δc²=0 ⟺ Zt=Zs, the Lorentz-scalar Ward
  identity); `speedSplitting_aniso` (the form `Γ⁽²⁾=A·p²+B·(u·p)²` gives Zt=A+B, Zs=A, Δc²=−B/(A+B)); **★
  `speedSplitting_aniso_eq_zero_iff` — Δc²=0 ⟺ B=0** (the escape reduces to the single scalar condition: the
  matter-loop regulator carries no preferred-`u` term); `speedSplitting_aniso_ne_zero_of_B_ne_zero`. Standard-3,
  full `QIQTH` green, budget 0; wired in. Ties the threads: B is sourced by the regulator anisotropy `A_F` (J1);
  QIQT-H's capacity is silent on B (J2) ⟹ B is set by the separately-supplied matter UV kernel (J6).
- **2026-06-30 — J4 ✅ DONE** (`scripts/qg/covariant_capacity_scan.py` + `J4_scan_result.md`): full 2D scan of
  `|A_F|(α, n)` (∝ Δc²) for Reg C. `|A_F|` falls with α; threshold `α*(n)` (where `|A_F|<3.3e-3`) = **8.0, 2.83,
  1.41, 1.41** for `n=1,2,4,8`. In **all** cases `α* ≳ 1`: the modular scale `Λ_K` must EXCEED the covariant UV
  scale `Λ` ⟹ a modular/diamond cutoff is Lorentz-safe **only when it does no UV work below `Λ`** (i.e. it is NOT
  the matter regulator). **No regime exists where a modular cutoff is both the active matter UV regulator AND
  Lorentz-safe.** Quantitatively closes the numerical side: escape needs `B=0` (J3) = a Lorentz-scalar matter
  kernel (J6), not a modular cut.
- **NEXT → J5** (Rindler/wedge modular-mode check — frontier checkpoint), J6 (covariant proper-time/PV UV kernel +
  capacity as a nonlocal crossed-product-trace constraint — the real construction, checkpoint).
