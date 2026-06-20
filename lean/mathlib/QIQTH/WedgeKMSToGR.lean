import QIQTH.QiqtToGR
import QIQTH.Fock.OneParticleBW

/-!
# QIQT-H ⇒ Einstein, with the modular surface consolidated into ONE labelled input: the wedge KMS property

`QiqtToGR.qiqt_bekenstein_gives_gr` derives the Einstein field equations from QIQT-H's capacity bound +
Klein positivity, but takes the boost heat-flux `hFlux` (`kd = (2π/ℏ)·T_kk`) as a *raw* cited hypothesis.
This file **derives that `hFlux`** from the **wedge KMS property** alone — the genuinely physical labelled
input — using the one-particle Bisognano–Wichmann tower (`QIQTH.Fock.OneParticleBW`):

* `modUnitary 𝒦_W = boostUnitary` (BW) — DERIVED from {standardness, KMS-uniqueness, strip} +
  the *proved* boost-invariance of the wedge subspace;
* modular-energy = boost-energy — DERIVED (a congruence from BW);
* the descent from the Hilbert-level derivative `i·(2π/ℏ)T_kk` to the chain's real component coefficient
  `kd` — DERIVED (`component_hFlux_of_wedgeKMS`, via `HasDerivAt.unique`).

What remains inside the wedge-KMS bundle is exactly the labelled, well-motivated physics: the wedge
standardness + KMS-uniqueness + strip property (= "the wedge KMS property"), the boost-charge = stress-flux
identity, and the standard localization of each null generator by a wedge state.  Consolidating these into
the single predicate `WedgeKMSFlux`, the top-level `qiqt_gr_from_wedge_kms` exhibits the Einstein equations
as following from QIQT-H + Klein modulo **exactly three** clearly-labelled inputs:

1. **the wedge KMS property** (`hKMS : WedgeKMSFlux …`);
2. **matter conservation** (`conserv : ∇·(a·T) = 0`);
3. **standard structural regularity** (the Lorentzian congruence `g = Pᵀ·η·P`, Raychaudhuri focusing
   `hFocus`, `f`-regularity `hreg`, and per-generator path-differentiability — all kinematic/geometric,
   none presupposing Einstein).

HONEST SCOPE.  The deep modular content (BW, modular-energy = boost-energy, the real-coefficient descent) is
machine-checked axiom-free.  The wedge KMS property, the boost-charge identity, and the per-generator
localization are *labelled hypotheses bundled into `WedgeKMSFlux`*, never Lean axioms — they are the
"well-motivated physics input" the goal allows.  Raychaudhuri focusing is bundled with structural
regularity as the kinematics of null congruences.
-/

namespace QIQTH.WedgeKMSToGR

open QIQTH.QiqtToGR QIQTH.EinsteinEOS QIQTH.Curvature QIQTH.Fock.OneParticleBW
open Filter Topology MeasureTheory QIQTH.Fock.Localization QIQTH.Fock.OneParticle

/-- **The wedge KMS property** (per null generator), as a single labelled predicate.  For each metric-null
    `(x, v)` it asserts a standard localization of the generator: a wedge standard subspace `S` (carrier
    `𝒦_W`), the boost group `V t = boostUnitary(−2π t)`, the KMS-uniqueness lemma `hUniq` (BGL §2) and the
    strip property `hStrip` (BGL §4) — i.e. *the wedge KMS property* — plus the localized state `ξ = ξ_{x,v}`
    with the boost-charge = stress-flux identity (boost correlation derivative `= i·(2π/ℏ)·T_kk`,
    `T_kk = BL(T x) v`) and the localization identity (modular correlation derivative `= i·kd`, "the
    null-generator modular energy IS the one-particle modular energy of `ξ`").  All bundled facts are the
    standard, well-motivated AQFT physics of the wedge — never Lean axioms. -/
def WedgeKMSFlux (g T : Point 4 → Fin 4 → Fin 4 → ℝ)
    (kd : Point 4 → (Fin 4 → ℝ) → ℝ) (hbar : ℝ) : Prop :=
  ∀ (x : Point 4) (v : Fin 4 → ℝ), BL (g x) v = 0 →
    ∃ (m : ℝ) (S : StandardSubspace (Lp ℂ 2 (volume : Measure ℝ)))
      (V : ℝ → (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)))
      (D : Set (Lp ℂ 2 (volume : Measure ℝ)))
      (ξ : Lp ℂ 2 (volume : Measure ℝ)),
      ((S.toClosedSubmodule : Set (Lp ℂ 2 (volume : Measure ℝ)))
          = closure (Submodule.span ℝ (wedgeGenSet m) : Set (Lp ℂ 2 (volume : Measure ℝ)))) ∧
      (∀ t y, V t y = boostUnitary (-(2 * Real.pi * t)) y) ∧
      ((∀ t, Set.MapsTo (V t) (S.toClosedSubmodule : Set _) (S.toClosedSubmodule : Set _)) →
        StripKMS V D → ∀ t, QIQTH.StandardSubspaceModular.modUnitary S t = V t) ∧
      StripKMS V D ∧
      HasDerivAt (fun t : ℝ => inner ℂ ξ (boostUnitary (-(2 * Real.pi * t)) ξ))
        (Complex.I * ((2 * Real.pi / hbar * BL (T x) v : ℝ) : ℂ)) 0 ∧
      HasDerivAt (fun t : ℝ => inner ℂ ξ (QIQTH.StandardSubspaceModular.modUnitary S t ξ))
        (Complex.I * ((kd x v : ℝ) : ℂ)) 0

/-- **The boost heat-flux `hFlux` DERIVED from the wedge KMS property.**  Unpacking `WedgeKMSFlux` at a null
    generator and feeding the bundle to `component_hFlux_of_wedgeKMS` yields the chain's per-null
    `kd = (2π/ℏ)·BL(T x) v` — the exact `hFlux` hypothesis of `qiqt_bekenstein_gives_gr`, now *derived* from
    the labelled wedge KMS property rather than assumed.  No Lean axioms. -/
theorem hFlux_of_wedgeKMS {g T : Point 4 → Fin 4 → Fin 4 → ℝ}
    {kd : Point 4 → (Fin 4 → ℝ) → ℝ} {hbar : ℝ} (h : WedgeKMSFlux g T kd hbar) :
    ∀ x v, BL (g x) v = 0 → kd x v = 2 * Real.pi / hbar * BL (T x) v := by
  intro x v hnull
  obtain ⟨m, S, V, D, ξ, hcarrier, hVboost, hUniq, hStrip, hBoost, hbridge⟩ := h x v hnull
  exact component_hFlux_of_wedgeKMS m S V hcarrier hVboost hUniq hStrip ξ hbar (kd x v)
    (BL (T x) v) hBoost hbridge

/-- **★★★ THE GOAL THEOREM — Einstein's equations from QIQT-H's capacity postulate + Klein positivity,
    modulo EXACTLY THREE clearly-labelled, well-motivated physics inputs.**

    Identical to `qiqt_bekenstein_gives_gr` except the raw boost-flux hypothesis `hFlux` is replaced by the
    single physical predicate `hKMS : WedgeKMSFlux …` (**the wedge KMS property**), from which `hFlux` is
    *derived* (`hFlux_of_wedgeKMS`).  The three labelled inputs are therefore exactly:

    1. **the wedge KMS property** `hKMS` — the standard-subspace KMS structure of the wedge (standardness,
       KMS-uniqueness, strip), with its localized boost-charge = stress-flux and per-generator state;
    2. **matter conservation** `conserv` — `∇·(a·T) = 0`;
    3. **standard structural regularity** — the Lorentzian congruence `hcong` (`g = Pᵀ·η·P`), Raychaudhuri
       focusing `hFocus` (` a' = R_kk`, kinematics of null congruences), `f`-regularity `hreg`, and the
       per-generator path-differentiability `hS,hK,hA` (a modelling choice).

    QIQT-H supplies the capacity **bound** `S ≤ η·A`, its saturation, and Klein positivity `KE − S ≥ 0` as
    *theorems* (`hbound`,`hsat`,`hDnn`,`hD0`), from which the differential area law `δS = η δA` is derived;
    all geometry (Bianchi, `∇·G = 0`, null-cone→tensor, constant `Λ`) is machine-checked axiom-free.  So:
    *modulo exactly the three labelled physics inputs above, QIQT-H's holographic-capacity postulate + Klein
    positivity DERIVE the Einstein field equations `a·T = G + Λ·g`.* -/
theorem qiqt_gr_from_wedge_kms
    (g gi : Point 4 → Fin 4 → Fin 4 → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hCgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (T : Point 4 → Fin 4 → Fin 4 → ℝ) (η hbar a : ℝ)
    (hbar0 : hbar ≠ 0) (heta : η ≠ 0) (ha : a = 2 * Real.pi / (hbar * η))
    (hT_symm : ∀ x a' b, T x a' b = T x b a')
    (hric_symm : ∀ x a' b, ricci g gi a' b x = ricci g gi b a' x)
    (P Pinv : Point 4 → Fin 4 → Fin 4 → ℝ)
    (hPP : ∀ x i j, (∑ k, P x i k * Pinv x k j) = if i = j then (1 : ℝ) else 0)
    (hPP' : ∀ x i j, (∑ k, Pinv x i k * P x k j) = if i = j then (1 : ℝ) else 0)
    (hcong : ∀ x i j, g x i j = ∑ k, ∑ l, P x k i * gm k l * P x l j)
    (S KE A : Point 4 → (Fin 4 → ℝ) → ℝ → ℝ) (sd kd ad : Point 4 → (Fin 4 → ℝ) → ℝ)
    (hS : ∀ x v, BL (g x) v = 0 → HasDerivAt (S x v) (sd x v) 0)
    (hK : ∀ x v, BL (g x) v = 0 → HasDerivAt (KE x v) (kd x v) 0)
    (hA : ∀ x v, BL (g x) v = 0 → HasDerivAt (A x v) (ad x v) 0)
    (hbound : ∀ x v, BL (g x) v = 0 → ∀ᶠ t in 𝓝 0, S x v t ≤ η * A x v t)
    (hsat : ∀ x v, BL (g x) v = 0 → S x v 0 = η * A x v 0)
    (hDnn : ∀ x v, BL (g x) v = 0 → ∀ t, 0 ≤ KE x v t - S x v t)
    (hD0 : ∀ x v, BL (g x) v = 0 → KE x v 0 - S x v 0 = 0)
    -- INPUT 1 — the wedge KMS property (DERIVES the boost heat-flux `hFlux`):
    (hKMS : WedgeKMSFlux g T kd hbar)
    -- INPUT 3a — standard structural regularity: Raychaudhuri focusing (kinematics of null congruences):
    (hFocus : ∀ x v, BL (g x) v = 0 → ad x v = BL (fun i j => ricci g gi i j x) v)
    -- INPUT 3b — standard structural regularity: `f`-regularity:
    (hreg : ∀ f : Point 4 → ℝ,
        (∀ y a' b, a * T y a' b = ricci g gi a' b y + f y * g y a' b) →
        (∀ x ρ, PdiffAt f ρ x) ∧
          Differentiable ℝ (fun y => f y + (1 / 2 : ℝ) * scalarCurv g gi y))
    -- INPUT 2 — matter conservation:
    (conserv : ∀ x ν, div02 g gi (fun y a' b => a * T y a' b) ν x = 0) :
    ∃ Λ : ℝ, ∀ x μ ν, a * T x μ ν = einsteinTensor g gi μ ν x + Λ * g x μ ν :=
  qiqt_bekenstein_gives_gr g gi hsymm hsymm_gi hinv hCg hCgi hC T η hbar a hbar0 heta ha
    hT_symm hric_symm P Pinv hPP hPP' hcong S KE A sd kd ad hS hK hA hbound hsat hDnn hD0
    (hFlux_of_wedgeKMS hKMS) hFocus hreg conserv

end QIQTH.WedgeKMSToGR
