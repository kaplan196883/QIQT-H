/-
  GatedWitnessEmeas — J4-110: the `hEmeas` measurability wall for the `N = 1` gated van-Vleck
  witness residual `E = heatOp g gi H_G`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  VERDICT (route census, see the module-end note for the full write-up).

  J4-109 reduced the concrete `hInt` for the `N = 1` witness to the SINGLE base joint strong
  measurability `hEmeas` of `E = heatOp g gi (gatedKernel K S H_G)`.  This file attacks `hEmeas`.

  Route (b) — building `hEmeas` from the ground up — WALLS at the joint `q`-regularity of the
  `Classical.choose` geodesic flow `uniformFlowExp` (E1).  Two independent obstructions:

    (W1) [E1, the load-bearing wall]  `uniformFlowExp g gi hC hK q w` is `Classical.choose` of a
      per-`(q,w)` ODE-existence statement; NO joint structure across `(q,w)` is exposed
      (`BasepointSmoothDep.geodesicBasepoint_endpoint_position_hasDerivAt` explicitly states the
      concrete flow's base-point dependence "runs through opaque `Classical.choose` witnesses and is
      not exposed").  A joint-`q` measurability/continuity of this flow is, per an external ODE-
      measurability consult, a MULTI-WEEK Lean endeavour (closed integral-solution relation +
      Lusin–Souslin, or parameterized Picard convergence + `ODE_solution_unique`).

    (W2) [structural — the killer even if E1 were done]  `heatOp = ∂_τ − laplaceBeltrami`, and
      `laplaceBeltrami` contains a NESTED `pd` (second coordinate derivative).  Mathlib's
      `measurable_deriv_with_param` produces measurability of a parameterized derivative ONLY from
      JOINT CONTINUITY of the family (`Continuous f.uncurry`) — there is no "joint measurable
      derivative from a merely measurable family".  So the OUTER `pd` needs the FIRST `pd` field to
      be jointly CONTINUOUS in `(τ,p,q)`, i.e. `G` jointly `C¹` in `(τ,p,q)`, i.e. the flow's joint
      `C¹` `q`-dependence — again E1.  Measurability of the flow alone (even if obtained) does NOT
      propagate through the two nested parameterized derivatives.

  So `hEmeas` is carried as the honest firewall (satisfiable: the flat case is explicit).  What this
  file DOES land, genuinely and reusably (no `sorry`, no new axioms), is the DECOMPOSITION of
  `hEmeas` into cleaner, flow-agnostic pieces:

    • E3a  `stronglyMeasurable_pd_field_of_jointContinuous` — the FIRST-order `pd` field is jointly
      strongly measurable from JOINT CONTINUITY of the kernel (`measurable_deriv_with_param` through
      a coordinate `update` reparameterization).  [discharges the first-`pd` measurability]
    • E3b  `stronglyMeasurable_timeDeriv_field_of_jointContinuous` — the `∂_τ` field is jointly
      strongly measurable from joint continuity.  [discharges the `∂_τ` measurability]
    • E3c  `stronglyMeasurable_pd2_field_of_jointC1` — the SECOND-order `pd` field is jointly
      strongly measurable from JOINT CONTINUITY of the first-`pd` field (the residual W2 input).
    • E3d  `heatOp_stronglyMeasurable_of_deriv_fields` — MEASURABLE ALGEBRA: `heatOp g gi G` is
      jointly strongly measurable from the strong measurability of the `∂_τ`, first-`pd`, and
      second-`pd` fields, plus the (continuous) `gi` / `christoffel` coefficients.  This is the exact
      `hEmeas`-shaped conclusion, with the wall isolated to the three derivative-field inputs.

  NET after J4-110: `hEmeas` for the `N = 1` witness reduces to `{joint continuity of H_G, joint
  continuity of its first `pd` field}` — a clean geometric (ODE-smooth-dependence) input, strictly
  more honest than the monolithic `hEmeas`, with the residue pinpointed at the flow's joint
  `q`-regularity (E1 / W1).  No `sorry`, no new axioms, no vacuous hypotheses.
-/
import Mathlib
import QIQTH.GatedWitnessMeas

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation QIQTH.LeviSeries
open QIQTH.HeatDuhamel QIQTH.GaussianWidthTolerant QIQTH.ResidueBound QIQTH.PullbackMetric
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.TrueHeatKernel
open QIQTH.ParametrixFunction
open scoped BigOperators ContDiff Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### E3a. The first-order `pd` field is jointly SM from joint continuity of the kernel. -/

/-- **E3a — the first-order `pd` field, jointly strongly measurable from joint continuity.**  If the
    space-time kernel `G` is JOINTLY CONTINUOUS in `(τ,p,q)`, then for each coordinate `k` the
    first-order partial-derivative field `(τ,p,q) ↦ ∂ₖ (G τ · q) (p)` is jointly strongly measurable.
    Proof: `measurable_deriv_with_param` for the family `(a,t) ↦ G a.1 (update a.2.1 k t) a.2.2`
    (whose uncurry is continuous via `Continuous.update`), composed with the measurable evaluation
    `w ↦ (w, w.2.1 k)`. -/
theorem stronglyMeasurable_pd_field_of_jointContinuous
    (G : ℝ → Point n → Point n → ℝ) (k : Fin n)
    (hCont : Continuous (fun w : ℝ × Point n × Point n => G w.1 w.2.1 w.2.2)) :
    StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      pd (fun x => G w.1 x w.2.2) k w.2.1) := by
  classical
  set F : (ℝ × Point n × Point n) → ℝ → ℝ :=
    fun a t => G a.1 (Function.update a.2.1 k t) a.2.2 with hF
  have hFcont : Continuous (Function.uncurry F) := by
    have hrw : (Function.uncurry F) =
        (fun w : ℝ × Point n × Point n => G w.1 w.2.1 w.2.2) ∘
          (fun z : (ℝ × Point n × Point n) × ℝ =>
            (z.1.1, Function.update z.1.2.1 k z.2, z.1.2.2)) := by
      funext z; rfl
    rw [hrw]
    refine hCont.comp ?_
    refine (continuous_fst.comp continuous_fst).prodMk (Continuous.prodMk ?_ ?_)
    · exact Continuous.update (continuous_fst.comp (continuous_snd.comp continuous_fst)) k
        continuous_snd
    · exact continuous_snd.comp (continuous_snd.comp continuous_fst)
  have hderiv : Measurable (fun a : (ℝ × Point n × Point n) × ℝ => deriv (F a.1) a.2) :=
    measurable_deriv_with_param hFcont
  have hmap : Measurable (fun w : ℝ × Point n × Point n => (w, w.2.1 k)) :=
    measurable_id.prodMk ((measurable_pi_apply k).comp (measurable_fst.comp measurable_snd))
  have hcomp : Measurable (fun w : ℝ × Point n × Point n => deriv (F w) (w.2.1 k)) :=
    hderiv.comp hmap
  exact hcomp.stronglyMeasurable

/-! ### E3b. The `∂_τ` field is jointly SM from joint continuity of the kernel. -/

/-- **E3b — the `∂_τ` field, jointly strongly measurable from joint continuity.**  If `G` is jointly
    continuous in `(τ,p,q)`, the time-derivative field `(τ,p,q) ↦ ∂_τ (G · p q) (τ)` is jointly
    strongly measurable.  `measurable_deriv_with_param` for the family `(a,u) ↦ G u a.1 a.2` (uncurry
    continuous), composed with `w ↦ (w.2, w.1)` (= `Prod.swap`). -/
theorem stronglyMeasurable_timeDeriv_field_of_jointContinuous
    (G : ℝ → Point n → Point n → ℝ)
    (hCont : Continuous (fun w : ℝ × Point n × Point n => G w.1 w.2.1 w.2.2)) :
    StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      deriv (fun u => G u w.2.1 w.2.2) w.1) := by
  classical
  set F : (Point n × Point n) → ℝ → ℝ := fun a u => G u a.1 a.2 with hF
  have hFcont : Continuous (Function.uncurry F) := by
    have hrw : (Function.uncurry F) =
        (fun w : ℝ × Point n × Point n => G w.1 w.2.1 w.2.2) ∘
          (fun z : (Point n × Point n) × ℝ => (z.2, z.1.1, z.1.2)) := by
      funext z; rfl
    rw [hrw]
    refine hCont.comp ?_
    exact continuous_snd.prodMk ((continuous_fst.comp continuous_fst).prodMk
      (continuous_snd.comp continuous_fst))
  have hderiv : Measurable (fun a : (Point n × Point n) × ℝ => deriv (F a.1) a.2) :=
    measurable_deriv_with_param hFcont
  have hmap : Measurable (fun w : ℝ × Point n × Point n => (w.2, w.1)) :=
    measurable_snd.prodMk measurable_fst
  exact (hderiv.comp hmap).stronglyMeasurable

/-! ### E3c. The second-order `pd` field is jointly SM from joint continuity of the first-`pd` field. -/

/-- **E3c — the SECOND-order `pd` field, jointly strongly measurable from JOINT CONTINUITY of the
    first-`pd` field** (the residual W2 input).  A direct specialization of `E3a` to the
    first-`pd` kernel `(τ,y,q) ↦ ∂_j (G τ · q) (y)`; the joint continuity of THAT kernel is `hP1cont`
    — which requires `G` jointly `C¹`, i.e. the flow's joint `q`-regularity (E1). -/
theorem stronglyMeasurable_pd2_field_of_jointContinuous
    (G : ℝ → Point n → Point n → ℝ) (i j : Fin n)
    (hP1cont : Continuous (fun w : ℝ × Point n × Point n =>
      pd (fun x => G w.1 x w.2.2) j w.2.1)) :
    StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      pd (fun y => pd (fun x => G w.1 x w.2.2) j y) i w.2.1) :=
  stronglyMeasurable_pd_field_of_jointContinuous
    (fun τ y q => pd (fun x => G τ x q) j y) i hP1cont

/-! ### E3d. `heatOp` measurable algebra — `hEmeas` from the three derivative fields. -/

/-- **E3d — `heatOp` joint strong measurability from the derivative-field measurabilities.**  Pure
    measurable algebra: `heatOp g gi G = ∂_τ G − ∑ᵢⱼ gⁱʲ (∂ᵢ∂ⱼ G − ∑ₖ Γᵏᵢⱼ ∂ₖ G)` is jointly
    strongly measurable given the strong measurability of the `∂_τ`, first-`pd` (`hP1`) and
    second-`pd` (`hP2`) fields, plus the measurability of the coefficient fields `gⁱʲ` (`hgi`) and
    `Γᵏᵢⱼ` (`hchr`).  This is exactly the `hEmeas`-shaped conclusion, with the wall isolated to the
    three derivative-field inputs. -/
theorem heatOp_stronglyMeasurable_of_deriv_fields
    (g gi : Point n → Fin n → Fin n → ℝ) (G : ℝ → Point n → Point n → ℝ)
    (hDτ : StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      deriv (fun u => G u w.2.1 w.2.2) w.1))
    (hP1 : ∀ k : Fin n, StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      pd (fun x => G w.1 x w.2.2) k w.2.1))
    (hP2 : ∀ i j : Fin n, StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      pd (fun y => pd (fun x => G w.1 x w.2.2) j y) i w.2.1))
    (hgi : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)) :
    StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      heatOp g gi G w.1 w.2.1 w.2.2) := by
  have hp : Measurable (fun w : ℝ × Point n × Point n => w.2.1) :=
    measurable_fst.comp measurable_snd
  have hmeasfun : Measurable (fun w : ℝ × Point n × Point n =>
      heatOp g gi G w.1 w.2.1 w.2.2) := by
    simp only [heatOp, laplaceBeltrami]
    refine (hDτ.measurable).sub ?_
    refine Finset.measurable_sum _ (fun i _ => ?_)
    refine Finset.measurable_sum _ (fun j _ => ?_)
    refine ((hgi i j).comp hp).mul ?_
    refine ((hP2 i j).measurable).sub ?_
    refine Finset.measurable_sum _ (fun k _ => ?_)
    exact ((hchr k i j).comp hp).mul ((hP1 k).measurable)
  exact hmeasfun.stronglyMeasurable

/-! ### E3e. The clean reduction — `hEmeas` from joint continuity of the kernel and its first `pd`. -/

/-- **E3e — `heatOp` joint strong measurability from JOINT CONTINUITY of the kernel and its first
    `pd` fields.**  Combines `E3a`/`E3b`/`E3c`/`E3d`.  This is the flow-agnostic reduction: the only
    remaining inputs are the JOINT CONTINUITY of `G` and of each first-`pd` field of `G`, plus the
    coefficient measurabilities.  For the gated van-Vleck witness these continuity inputs are the
    clean ODE-smooth-dependence statement whose residue is the flow's joint `q`-regularity (E1/W1). -/
theorem heatOp_stronglyMeasurable_of_jointContinuous
    (g gi : Point n → Fin n → Fin n → ℝ) (G : ℝ → Point n → Point n → ℝ)
    (hCont : Continuous (fun w : ℝ × Point n × Point n => G w.1 w.2.1 w.2.2))
    (hP1cont : ∀ j : Fin n, Continuous (fun w : ℝ × Point n × Point n =>
      pd (fun x => G w.1 x w.2.2) j w.2.1))
    (hgi : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)) :
    StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      heatOp g gi G w.1 w.2.1 w.2.2) :=
  heatOp_stronglyMeasurable_of_deriv_fields g gi G
    (stronglyMeasurable_timeDeriv_field_of_jointContinuous G hCont)
    (fun k => stronglyMeasurable_pd_field_of_jointContinuous G k hCont)
    (fun i j => stronglyMeasurable_pd2_field_of_jointContinuous G i j (hP1cont j))
    hgi hchr

/-! ### E4. The decomposed concrete `hInt` — `hEmeas` replaced by kernel continuity. -/

/-- **★★ J4-110 — THE CONCRETE `hInt` FOR THE `N = 1` GATED VAN-VLECK WITNESS, CONDITIONAL ON KERNEL
    CONTINUITY (decomposed `hEmeas`).**  Identical to `gatedWitnessN1_hInt_of_hEmeas` (J4-109) except
    the opaque `hEmeas` implication-hypothesis is replaced by the strictly more granular, flow-agnostic
    inputs supplied to `heatOp_stronglyMeasurable_of_jointContinuous` (E3e):

      • `hKcont`   — JOINT CONTINUITY of the gated kernel `H_G` in `(τ,p,q)`;
      • `hKp1`     — JOINT CONTINUITY of each first-order `pd` field of `H_G`;
      • `hgiM`,`hchrM` — measurability of the inverse-metric / Christoffel coefficient fields
        (genuine, satisfiable — continuous for the concrete `g`).

    Route: `gatedWitnessN1_hInt_of_hEmeas` supplies `a,b,C,S`, the bound, and the `hEmeas → hInt`
    implication; E3e discharges its `hEmeas` from `hKcont`/`hKp1`/`hgiM`/`hchrM`.  This pinpoints the
    residual measurability input as the JOINT CONTINUITY of the gated van-Vleck kernel and its first
    derivative — whose only irreducible residue is the flow's joint `q`-regularity (E1/W1, a
    multi-week ODE-measurability endeavour; see the module note). -/
theorem gatedWitnessN1_hInt_of_kernelContinuity (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hn : 1 ≤ n)
    (hgiM : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchrM : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)) :
    ∃ a b C : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ ∃ S : Point n → Set (Point n),
      (∀ (t : ℝ), ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
            (transportCoeff (transportOp (vanVleck g) g gi)) a b
            (uniformInverseChart g gi hC hK))) τ p q|
          ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
      ∧ ∀ (Cmodel : ℝ),
          Continuous (fun w : ℝ × Point n × Point n =>
            gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) a b
              (uniformInverseChart g gi hC hK)) w.1 w.2.1 w.2.2) →
          (∀ j : Fin n, Continuous (fun w : ℝ × Point n × Point n =>
            pd (fun x => gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) a b
              (uniformInverseChart g gi hC hK)) w.1 x w.2.2) j w.2.1)) →
          IterConvIntegrableW (heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1
            (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) a b
            (uniformInverseChart g gi hC hK)))) (2 : ℝ) (0 : ℝ) Cmodel := by
  obtain ⟨a, b, C, ha, hab, hC0, S, hbound, hcond⟩ :=
    gatedWitnessN1_hInt_of_hEmeas g gi hg hC hK hgnd hgsymm hinvF hframeK hw hdg0 hg0 hn
  refine ⟨a, b, C, ha, hab, hC0, S, hbound, ?_⟩
  intro Cmodel hKcont hKp1
  exact hcond Cmodel
    (heatOp_stronglyMeasurable_of_jointContinuous g gi _ hKcont hKp1 hgiM hchrM)

end QIQTH.HeatResidualBound
