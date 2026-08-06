/-
  RicciSourceCoeff — J4-318: the Ricci-source physics coefficient `htr` of the wide `a₁` capstone
  `ProviderSideExports.wide_a1_R6_interface_discharged_v2`, attacked as R3 of the endgame map.
  ONE brick of the `a₁ = R/6` heat-kernel campaign.  ⚠ NOT `a₁ = R/6`; proves NOTHING new about `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  `a₁ = R/6` remains CONDITIONAL after this brick.  This file does NOT discharge
  the physics coefficient `htr` from first principles: it isolates the ONE genuine Riemannian input the
  coefficient rests on (the normal-coordinate metric 2-jet) as an explicit, SATISFIABLE hypothesis, and
  proves — as small honest lemmas — the entire remaining derivation-chain (trace + Ricci-contraction
  algebra) that turns that input into the capstone's exact `htr` binder.  No hypothesis is vacuous
  (`:= True`), unsatisfiable, or equal to its conclusion.  R2 analytic walls are untouched.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ═══ Q0 — THE RECON of the `htr` carry ═══
  ══════════════════════════════════════════════════════════════════════════════════════════════════
  The capstone's binder (ProviderSideExports.lean:177), copied VERBATIM from the compiled statement:

     `(htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)`

  MATHEMATICAL CONTENT.  `pd (fun y => pd (fun w => g w a a) d y) c 0` is the mixed second coordinate
  partial `∂_c ∂_d g_{aa}` evaluated at the origin `0`.  Summed over the diagonal `a` this is
  `∑_a ∂_c ∂_d g_{aa}(0) = ∂_c ∂_d (tr g)(0)`.  In the RNC gauge the capstone already carries
  (`hg0 : g 0 = I`, `hdg0 : ∂g(0) = 0`, `hΓ : Γ(0) = 0`), this diagonal-trace of the metric 2-jet is
  exactly `∂_c ∂_d (log det g)(0)`, and `htr` asserts it equals `-(2/3) Ric_{cd}`.  `Ric` in the
  capstone is an ABSTRACT `Fin n → Fin n → ℝ` supplied by the caller — geometrically it is the metric's
  own Ricci `ricci g gi c d 0`.

  WHERE THE `-(2/3)` COMES FROM.  The Riemann-normal-coordinate (geodesic normal) 2-jet of the metric is
     `∂_c ∂_d g_{ab}(0) = -(1/3) (R_{acbd} + R_{adbc})`         (†)
  with `R` the fully-lowered Riemann tensor (this is the standard NC expansion
  `g_{ab}(x) = δ_{ab} - (1/3) R_{acbd} x^c x^d + O(x^3)`).  Tracing (†) at `a = b` and summing:
     `∑_a ∂_c ∂_d g_{aa}(0) = -(1/3) ∑_a (R_{acad} + R_{adac}) = -(1/3)(Ric_{cd} + Ric_{cd}) = -(2/3) Ric_{cd}`,
  using `∑_a R_{acad} = Ric_{cd}` and the pair-symmetry `R_{adac} = R_{acad}`.  THE `-(2/3)` IS THE
  TRACE OF THE `-(1/3)` NC 2-jet — a pure algebra step over (†).

  BANKED INVENTORY that bears on `htr` (exact names).
    • `QIQTH.Curvature`: `pd`, `christoffel`, `riemann`, `ricci` (component-level, coordinate chart);
        `pd_comm` (Schwarz), `pd_mul`/`pd_sum`/`pd_add`/`pd_sub` (the `∂` algebra), `PdiffAt_pd`,
        `christoffel_symm`, `riemann_antisymm`, `christoffel_lower`, `metric_compat`.
        ⇒ `ricci g gi σ ν x = ∑ μ, riemann g gi μ σ μ ν x` (the definitional diagonal contraction).
    • `QIQTH.VanVleckRicciUnconditional.vanVleck_ricci_unconditional` — the *directional* van-Vleck /
        Raychaudhuri radial ODE `deriv²[log det g̃(s•v)] = -2 Ric(u,u) - 2 tr((Y'Y⁻¹)²) + 2n/s²`; this is
        the `Ric(v,v)`-contracted 2-jet along a ray (commit 3e36639c lineage).  DIRECTIONAL, not the
        TRACED coefficient `htr` needs.
    • `QIQTH.VanVleckLogDetSplit.logdet_gtilde_ray_secondDeriv` — the ray second-derivative of
        `log det g̃`.  Again directional.
    • `QIQTH.OuterCarryRecon` — census classifying `htr` as the ★ physics (iv) carry; discharged the four
        NORMALIZATION carries `hg0/hgi/hΓ/hgnd` but left `htr` (physics, not normalization) CARRIED.

  THE HONEST GAP (what is banked vs what `htr` needs).
    • BANKED: the *directional* `Ric(v,v)` 2-jet (van-Vleck radial ODE) at the exp-pullback metric `g̃`,
        contracted with one ray direction `v`; the full `∂`-calculus of `QIQTH.Curvature`.
    • NOT BANKED: the *full* NC metric 2-jet (†) `∂_c ∂_d g_{ab}(0) = -(1/3)(R_{acbd}+R_{adbc})` as an
        equality of coordinate second partials of the SUPPLIED metric `g` (all four indices free), plus
        the fully-lowered Riemann pair-symmetry `R_{adac} = R_{acad}` (NO `riemann`-pair-symmetry lemma
        exists in the bank — grep confirms).  Deriving (†) from `Point`-level machinery is the geodesic-
        normal-coordinate construction (Jacobi-field expansion of `expPullbackMetric`), a large task the
        van-Vleck bank does only DIRECTIONALLY.
    ⇒ (†) is the genuine WALL for R3.  This file supplies it as the SATISFIABLE hypothesis `hjet` (a true
      theorem of Riemannian geometry) and proves the ENTIRE rest of the chain to `htr` (Q1–Q2 below).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ═══ Q1 — the derivation-chain algebra (all provable NOW; each std-3, no `sorry`, no new axioms) ═══
  ══════════════════════════════════════════════════════════════════════════════════════════════════
    • `ric_of_lowered`     — `∑_a Rlow a c a d = Ric c d` unfolds the Ricci-contraction hypothesis.
    • `jet_trace_sum`      — the trace `∑_a ∂_c∂_d g_{aa}(0) = -(1/3) ∑_a (Rlow a c a d + Rlow a d a c)`,
                             obtained by summing the NC 2-jet (†) over the diagonal `a = b`.
    • `lowered_diag_swap`  — `∑_a Rlow a d a c = ∑_a Rlow a c a d` from the pair-symmetry `hpair`.
    • `ricci_diag_contract`— `ricci g gi c d 0 = ∑ μ, riemann g gi μ c μ d 0` (the def, packaged).

  ═══ Q2 — `htr` as a THEOREM from the named residue (†) + the definitional/symmetry facts ═══
    • `htr_of_geometry`    — the capstone's `htr` binder VERBATIM, derived from `hjet` (= (†), the WALL),
                             `hRic` (Ricci-contraction definition), `hpair` (Riemann pair-symmetry).  All
                             three hypotheses are SATISFIABLE (e.g. the flat metric with `Rlow = 0`, or
                             any genuine Riemannian `g` in normal coordinates).  This CLOSES the algebra
                             gap; the ONLY residue is (†) itself.

  R3 STATUS AFTER THIS BRICK: `htr` reduced from "carried opaque coefficient" to "the trace of the ONE
  named Riemannian input (†), with the trace/contraction algebra fully discharged".  (†) stays CARRIED as
  the honest geometric wall.  R0/R1/R2 UNCHANGED.  a₁ = R/6 stays CONDITIONAL.  ⚠ NOT `a₁ = R/6`.

  No `sorry` (this header prose excepted), no new axioms, no `:= True`, no vacuous/unsatisfiable hypotheses.
-/
import Mathlib
import QIQTH.Curvature

open QIQTH.Curvature
open scoped BigOperators

namespace QIQTH.RicciSourceCoeff

variable {n : ℕ}

/-! ###############################################################################
    ### Q1 — the derivation-chain algebra (pure Finset algebra over the NC 2-jet).
    ############################################################################### -/

/-- **Q1 (1) — `ric_of_lowered`.**  Unfolds the Ricci-contraction hypothesis: the abstract Ricci `Ric`
    is the diagonal double-contraction `∑_a Rlow a c a d` of the fully-lowered Riemann `Rlow`.  A pure
    packaging lemma (the *definition* of Ricci from Riemann).  NOT `a₁ = R/6`. -/
theorem ric_of_lowered (Rlow : Fin n → Fin n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (hRic : ∀ c d, Ric c d = ∑ a, Rlow a c a d) (c d : Fin n) :
    (∑ a, Rlow a c a d) = Ric c d := (hRic c d).symm

/-- **Q1 (2) — `lowered_diag_swap`.**  The diagonal double-contraction is invariant under swapping the
    two free lower indices, by the fully-lowered Riemann pair-symmetry `R_{adac} = R_{acad}`
    (`hpair a d a c`).  `∑_a Rlow a d a c = ∑_a Rlow a c a d`.  NOT `a₁ = R/6`. -/
theorem lowered_diag_swap (Rlow : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hpair : ∀ a b c d, Rlow a b c d = Rlow c d a b) (c d : Fin n) :
    (∑ a, Rlow a d a c) = ∑ a, Rlow a c a d :=
  Finset.sum_congr rfl fun a _ => hpair a d a c

/-- **Q1 (3) — `jet_trace_sum`.**  Summing the normal-coordinate metric 2-jet
    `∂_c ∂_d g_{ab}(0) = -(1/3)(R_{acbd} + R_{adbc})` over the diagonal `a = b` gives the diagonal trace
    of the metric 2-jet as `-(1/3) ∑_a (Rlow a c a d + Rlow a d a c)`.  Pure summation of the hypothesis
    `hjet` at `b := a`.  NOT `a₁ = R/6`. -/
theorem jet_trace_sum (g : Point n → Fin n → Fin n → ℝ)
    (Rlow : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hjet : ∀ a b c d, pd (fun y => pd (fun w => g w a b) d y) c 0
              = -(1 / 3) * (Rlow a c b d + Rlow a d b c))
    (c d : Fin n) :
    (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0)
      = -(1 / 3) * ∑ a, (Rlow a c a d + Rlow a d a c) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => hjet a a c d

/-- **Q1 (4) — `ricci_diag_contract`.**  Packages the *definition* of the metric's Ricci as its diagonal
    Riemann contraction `ricci g gi c d 0 = ∑ μ, riemann g gi μ c μ d 0`.  This is the object the abstract
    `Ric` of the capstone geometrically instantiates to.  NOT `a₁ = R/6`. -/
theorem ricci_diag_contract (g gi : Point n → Fin n → Fin n → ℝ) (c d : Fin n) :
    ricci g gi c d 0 = ∑ μ, riemann g gi μ c μ d 0 := rfl

/-! ###############################################################################
    ### Q2 — `htr` as a theorem from the named residue (†) + definitional/symmetry facts.
    ############################################################################### -/

/-- **Q2 — `htr_of_geometry` (the capstone's `htr` binder, VERBATIM, DERIVED).**  From
      • `hjet` — the NORMAL-COORDINATE metric 2-jet `∂_c∂_d g_{ab}(0) = -(1/3)(Rlow a c b d + Rlow a d b c)`
                 (the ONE genuine Riemannian input = the wall (†); SATISFIABLE, e.g. flat `g`, `Rlow = 0`),
      • `hRic` — `Ric` is the fully-lowered Ricci contraction `Ric c d = ∑_a Rlow a c a d`,
      • `hpair`— the fully-lowered Riemann pair-symmetry `Rlow a b c d = Rlow c d a b`,
    we DERIVE the capstone's carried input
      `∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2/3) Ric c d`.
    Strategy: `jet_trace_sum` (trace the 2-jet) → split the diagonal sum → `lowered_diag_swap` +
    `ric_of_lowered` (both halves = `Ric`) → `-(1/3)(Ric + Ric) = -(2/3) Ric`.  CLOSES the trace/
    contraction algebra of `htr`; the sole residue is the wall `hjet`.  ⚠ NOT `a₁ = R/6`. -/
theorem htr_of_geometry (g : Point n → Fin n → Fin n → ℝ)
    (Rlow : Fin n → Fin n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (hRic : ∀ c d, Ric c d = ∑ a, Rlow a c a d)
    (hpair : ∀ a b c d, Rlow a b c d = Rlow c d a b)
    (hjet : ∀ a b c d, pd (fun y => pd (fun w => g w a b) d y) c 0
              = -(1 / 3) * (Rlow a c b d + Rlow a d b c))
    (c d : Fin n) :
    (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d := by
  rw [jet_trace_sum g Rlow hjet c d, Finset.sum_add_distrib,
      lowered_diag_swap Rlow hpair c d, ric_of_lowered Rlow Ric hRic c d]
  ring

/-- **Satisfiability witness for `htr_of_geometry`'s hypotheses.**  The flat metric `g ≡ I` with
    `Rlow = 0` and `Ric = 0` satisfies `hRic`, `hpair`, `hjet` simultaneously and NON-vacuously (the
    `hjet` LHS is a genuine second partial that happens to vanish), so the hypothesis bundle of
    `htr_of_geometry` is SATISFIABLE — no `:= True`, no unsatisfiable carry.  NOT `a₁ = R/6`. -/
theorem htr_hypotheses_satisfiable :
    ∃ (g : Point n → Fin n → Fin n → ℝ) (Rlow : Fin n → Fin n → Fin n → Fin n → ℝ)
      (Ric : Fin n → Fin n → ℝ),
      (∀ c d, Ric c d = ∑ a, Rlow a c a d)
      ∧ (∀ a b c d, Rlow a b c d = Rlow c d a b)
      ∧ (∀ a b c d, pd (fun y => pd (fun w => g w a b) d y) c 0
            = -(1 / 3) * (Rlow a c b d + Rlow a d b c)) := by
  refine ⟨fun _ i j => if i = j then (1 : ℝ) else 0, fun _ _ _ _ => 0, fun _ _ => 0,
    fun _ _ => by simp, fun _ _ _ _ => rfl, fun a b c d => ?_⟩
  -- inner `∂_d` of a constant field is `0`; then `∂_c 0 = 0`; RHS `= -(1/3)·0 = 0`.
  have hinner : (fun y : Point n => pd (fun w => (if a = b then (1 : ℝ) else 0)) d y)
      = (fun _ : Point n => (0 : ℝ)) := by
    funext y; simp [pd]
  rw [hinner]
  simp [pd]

/-! ###############################################################################
    ### Q1' — the REAL-curvature bridge: `∂Γ` and linearized Riemann at normal gauge.
    ###
    ### These connect the ABSTRACT `Rlow` of `htr_of_geometry` to the metric's actual
    ### `riemann g gi … 0`, proved from `QIQTH.Curvature` (NOT abstract).  They show the
    ### GENERAL (Γ(0)=0 / ∂g(0)=0 / g(0)=I gauge) linear part of Riemann is the metric 2-jet
    ### combination; the residual gap to `htr` is the NC-SPECIFIC symmetry of that 2-jet (†).
    ############################################################################### -/

/-- **Q1' (1) — `pd_christoffel_at_zero`.**  At the origin in the RNC first-order gauge
    (`hgi0 : gi 0 = I`, `hdg0 : ∂g(0) = 0`, `g/gi ∈ C^∞`), the derivative of the Christoffel symbol
    reduces to the raw metric 2-jet:
      `∂_μ Γ^ρ_{νσ}(0) = ½ (∂_μ∂_ν g_{ρσ} + ∂_μ∂_σ g_{ρν} − ∂_μ∂_ρ g_{νσ})(0)`.
    The `(∂gi)·(∂g)` product terms die because `∂g(0) = 0`; `gi(0) = I` collapses the `α`-sum on `α = ρ`.
    Derived from the `pd`-algebra of `QIQTH.Curvature` (`pd_const_mul`/`pd_sum`/`pd_mul`).  NOT `a₁ = R/6`. -/
theorem pd_christoffel_at_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (ρ ν σ μ : Fin n) :
    pd (fun y => christoffel g gi ρ ν σ y) μ (0 : Point n)
      = (1 / 2) * (pd (fun y => pd (fun w => g w ρ σ) ν y) μ 0
                 + pd (fun y => pd (fun w => g w ρ ν) σ y) μ 0
                 - pd (fun y => pd (fun w => g w ν σ) ρ y) μ 0) := by
  -- the α-indexed bracket `B_α(y) = ∂_ν g_{ασ} + ∂_σ g_{αν} − ∂_α g_{νσ}` and its PdiffAt.
  have hBrPd : ∀ α : Fin n, PdiffAt (fun y => pd (fun w => g w α σ) ν y
        + pd (fun w => g w α ν) σ y - pd (fun w => g w ν σ) α y) μ (0 : Point n) := fun α =>
    ((PdiffAt_pd _ (hg α σ) ν μ 0).add (PdiffAt_pd _ (hg α ν) σ μ 0)).sub
      (PdiffAt_pd _ (hg ν σ) α μ 0)
  -- each summand `gi_{ρα} · B_α` is PdiffAt.
  have hTermPd : ∀ α : Fin n, PdiffAt (fun y => gi y ρ α * (pd (fun w => g w α σ) ν y
        + pd (fun w => g w α ν) σ y - pd (fun w => g w ν σ) α y)) μ (0 : Point n) := fun α =>
    (PdiffAt_of_contDiff _ (hgiC ρ α) μ 0).mul (hBrPd α)
  simp only [christoffel]
  rw [pd_const_mul _ _ μ 0 (PdiffAt_sum _ _ μ 0 (fun α _ => hTermPd α)),
      pd_sum _ _ μ 0 (fun α _ => hTermPd α)]
  congr 1
  -- evaluate each `∂_μ(gi_{ρα}·B_α)(0)` by Leibniz: the `(∂gi)·B(0)` term dies, `gi(0)=δ` collapses.
  have hEach : ∀ α : Fin n,
      pd (fun y => gi y ρ α * (pd (fun w => g w α σ) ν y
        + pd (fun w => g w α ν) σ y - pd (fun w => g w ν σ) α y)) μ 0
      = (if ρ = α then (1 : ℝ) else 0) * (pd (fun y => pd (fun w => g w α σ) ν y
        + pd (fun w => g w α ν) σ y - pd (fun w => g w ν σ) α y) μ 0) := by
    intro α
    rw [pd_mul _ _ μ 0 (PdiffAt_of_contDiff _ (hgiC ρ α) μ 0) (hBrPd α)]
    -- `B_α(0) = 0` (all first partials of `g` vanish at `0`).
    have hB0 : (pd (fun w => g w α σ) ν (0 : Point n)
        + pd (fun w => g w α ν) σ 0 - pd (fun w => g w ν σ) α 0) = 0 := by
      rw [hdg0 α σ ν, hdg0 α ν σ, hdg0 ν σ α]; ring
    rw [hB0, mul_zero, zero_add, hgi0 ρ α]
  rw [Finset.sum_congr rfl (fun α _ => hEach α)]
  -- collapse the `α`-sum on `α = ρ`.
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  -- distribute the outer `∂_μ` over the bracket's `+`/`−`.
  rw [pd_sub _ _ μ 0 ((PdiffAt_pd _ (hg ρ σ) ν μ 0).add (PdiffAt_pd _ (hg ρ ν) σ μ 0))
      (PdiffAt_pd _ (hg ν σ) ρ μ 0),
    pd_add _ _ μ 0 (PdiffAt_pd _ (hg ρ σ) ν μ 0) (PdiffAt_pd _ (hg ρ ν) σ μ 0)]

/-- **Q1' (2) — `riemann_at_zero`.**  The *linear part* of the metric Riemann tensor at the origin, in
    the RNC first-order gauge, is the metric 2-jet combination
      `R^ρ_{σμν}(0) = ½(∂_μ∂_σ g_{ρν} − ∂_μ∂_ρ g_{νσ} − ∂_ν∂_σ g_{ρμ} + ∂_ν∂_ρ g_{μσ})(0)`.
    Proof: the `ΓΓ` quadratic part vanishes (`Γ(0) = 0`, derived inline from `hdg0`); the two `∂Γ` terms
    are `pd_christoffel_at_zero`; Schwarz (`pd_comm`) cancels the shared `∂_μ∂_ν g_{ρσ}` term.  This is
    the ACTUAL `riemann g gi` — the honest bridge from the abstract `Rlow` of `htr_of_geometry` to the
    metric's curvature.  (Full lowered-Riemann agreement additionally uses `g(0) = I`; the NC-SPECIFIC
    2-jet symmetry (†) — the residual wall — is NOT provided by this general-gauge lemma.)  NOT `a₁ = R/6`. -/
theorem riemann_at_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (ρ σ μ ν : Fin n) :
    riemann g gi ρ σ μ ν (0 : Point n)
      = (1 / 2) * (pd (fun y => pd (fun w => g w ρ ν) σ y) μ 0
                 - pd (fun y => pd (fun w => g w ν σ) ρ y) μ 0
                 - pd (fun y => pd (fun w => g w ρ μ) σ y) ν 0
                 + pd (fun y => pd (fun w => g w μ σ) ρ y) ν 0) := by
  -- `Γ(0) = 0` from `hdg0` (every bracketed `∂g` in the Γ formula vanishes at `0`).
  have hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0 := by
    intro k i j
    simp only [christoffel]
    rw [show (∑ α, gi (0 : Point n) k α *
        (pd (fun y => g y α j) i 0 + pd (fun y => g y α i) j 0 - pd (fun y => g y i j) α 0)) = 0 from
      Finset.sum_eq_zero (fun α _ => by rw [hdg0 α j i, hdg0 α i j, hdg0 i j α]; ring), mul_zero]
  simp only [riemann]
  rw [show (∑ l, (christoffel g gi ρ μ l 0 * christoffel g gi l ν σ 0
             - christoffel g gi ρ ν l 0 * christoffel g gi l μ σ 0)) = 0 from
      Finset.sum_eq_zero (fun l _ => by rw [hΓ0 ρ μ l, hΓ0 ρ ν l]; ring),
    add_zero,
    pd_christoffel_at_zero g gi hg hgiC hgi0 hdg0 ρ ν σ μ,
    pd_christoffel_at_zero g gi hg hgiC hgi0 hdg0 ρ μ σ ν]
  -- Schwarz: the shared `∂_μ∂_ν g_{ρσ}` term cancels.
  have hsch : pd (fun y => pd (fun w => g w ρ σ) ν y) μ (0 : Point n)
            = pd (fun y => pd (fun w => g w ρ σ) μ y) ν 0 :=
    pd_comm (fun w => g w ρ σ) μ ν 0 (hg ρ σ)
  linarith [hsch]

end QIQTH.RicciSourceCoeff

/-! ## Axiom checks — every new theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.RicciSourceCoeff
#print axioms ric_of_lowered
#print axioms lowered_diag_swap
#print axioms jet_trace_sum
#print axioms ricci_diag_contract
#print axioms htr_of_geometry
#print axioms htr_hypotheses_satisfiable
#print axioms pd_christoffel_at_zero
#print axioms riemann_at_zero
end AxiomChecks
