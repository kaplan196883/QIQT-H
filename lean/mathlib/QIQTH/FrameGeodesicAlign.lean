/-
  # Frame-transport curve lives along the exp geodesic (step b3d)

  The geodesic PROJECTION `s ↦ ((Γc s).1, (Γc s).2.1)` of a whole-frame transport curve `Γc`
  started at `(p, v, E₀)` coincides with the exponential geodesic `expTube g gi hC p v` on the
  transport interval `Ioo a b ⊆ Ioo (-2, 2)`.

  Mechanism (pure geodesic uniqueness).  The first two components of `geodesicFrameTransportField`
  are exactly `geodesicField` applied to the `(x, ξ)` block, so the projection of the frame ODE is
  an integral curve of `geodesicField`.  `expTube` is the confined geodesic integral curve through
  `(p, v)` (`expTube_spec`).  Both start at `(p, v)`, so by Grönwall uniqueness of geodesics
  (`geodesic_local_unique`) they agree.  The Lipschitz confinement set is produced INTERNALLY:
  on every compact subinterval `[a', b'] ⊂ (a, b)` both curves are continuous, hence their images
  are bounded and sit in a common closed ball on which `geodesicField` is Lipschitz
  (`ContDiffOn.exists_lipschitzOnWith`, closed ball compact convex).  Uniqueness on the surrounding
  open `(a', b')` then pins the two curves together at every interior point, covering all of `(a, b)`.

  HONEST CAPTION (binding): this is the geodesic-alignment floor only — it establishes that the
  parallel frame is carried ALONG the exp geodesic.  It does NOT package the orthonormal-frame data
  (`hpar`/`he`/`hortho`/`hcomplete`), does NOT discharge the van-Vleck frame jets, and does NOT
  establish `a₁ = R/6`.  Step b3d toward packaging the frame data along `expTube`.
-/
import Mathlib
import QIQTH.FrameTransportField
import QIQTH.Geodesic
import QIQTH.ExpMap

namespace QIQTH.Geodesic

open QIQTH.Curvature

set_option maxHeartbeats 1200000

variable {n : ℕ}

/-- **The geodesic projection of a frame-transport curve equals `expTube` on the transport interval.**
    Given a whole-frame transport curve `Γc` starting (in its `(x, ξ)` block) at `(p, v)` and solving
    the frame ODE on `Ioo a b ⊆ Ioo (-2, 2)` (with `0` interior), its geodesic projection
    `s ↦ ((Γc s).1, (Γc s).2.1)` coincides with the exponential geodesic `expTube g gi hC p v` on
    `Ioo a b`.  Proof by geodesic uniqueness (`geodesic_local_unique`); the Lipschitz confinement
    set is built internally on compact subintervals (no confinement hypothesis is carried).

    HONEST: parallel frame lives ALONG the exp geodesic — NOT the frame packaging, NOT `a₁ = R/6`. -/
theorem frameTransport_geodesic_eq_expTube (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ ≤ QIQTH.ExpMap.expRho g gi hC p)
    (Γc : ℝ → Point n × Point n × (Fin n → Point n)) {a b : ℝ}
    (hab : Set.Ioo a b ⊆ Set.Ioo (-2 : ℝ) 2) (h0 : (0 : ℝ) ∈ Set.Ioo a b)
    (hΓc0 : ((Γc 0).1, (Γc 0).2.1) = (p, v))
    (hΓcd : ∀ t ∈ Set.Ioo a b, HasDerivAt Γc (geodesicFrameTransportField g gi (Γc t)) t) :
    Set.EqOn (fun s => ((Γc s).1, (Γc s).2.1)) (QIQTH.ExpMap.expTube g gi hC p v)
      (Set.Ioo a b) := by
  obtain ⟨hY0, hYd, -⟩ := QIQTH.ExpMap.expTube_spec g gi hC p v hv
  -- The geodesic projection of the frame curve is an integral curve of `geodesicField`:
  -- the first two components of `geodesicFrameTransportField` ARE `geodesicField (x, ξ)`.
  have hγ₁d : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun s => ((Γc s).1, (Γc s).2.1))
        (geodesicField g gi ((Γc t).1, (Γc t).2.1)) t := by
    intro t ht
    have hd := hΓcd t ht
    have h1 : HasDerivAt (fun s => (Γc s).1)
        ((geodesicFrameTransportField g gi (Γc t)).1) t :=
      (ContinuousLinearMap.fst ℝ (Point n)
        (Point n × (Fin n → Point n))).hasFDerivAt.comp_hasDerivAt t hd
    have h2 : HasDerivAt (fun s => (Γc s).2.1)
        ((geodesicFrameTransportField g gi (Γc t)).2.1) t :=
      ((ContinuousLinearMap.fst ℝ (Point n) (Fin n → Point n)).comp
        (ContinuousLinearMap.snd ℝ (Point n)
          (Point n × (Fin n → Point n)))).hasFDerivAt.comp_hasDerivAt t hd
    exact h1.prodMk h2
  -- The two integral curves agree at `0`.
  have heq0 : ((Γc 0).1, (Γc 0).2.1) = QIQTH.ExpMap.expTube g gi hC p v 0 := hΓc0.trans hY0.symm
  -- Pointwise, via geodesic uniqueness on a compact subinterval `[a', b'] ⊂ (a, b)`.
  intro t ht
  obtain ⟨ha0, hb0⟩ := h0
  obtain ⟨hat, hbt⟩ := ht
  have hmin : a < min 0 t := lt_min ha0 hat
  have hmax : max 0 t < b := max_lt hb0 hbt
  set a' : ℝ := (a + min 0 t) / 2 with ha'
  set b' : ℝ := (max 0 t + b) / 2 with hb'
  have haa' : a < a' := by rw [ha']; linarith
  have ha'min : a' < min 0 t := by rw [ha']; linarith
  have hmaxb' : max 0 t < b' := by rw [hb']; linarith
  have hb'b : b' < b := by rw [hb']; linarith
  have ha'0 : a' < 0 := lt_of_lt_of_le ha'min (min_le_left 0 t)
  have ha't : a' < t := lt_of_lt_of_le ha'min (min_le_right 0 t)
  have h0b' : 0 < b' := lt_of_le_of_lt (le_max_left 0 t) hmaxb'
  have htb' : t < b' := lt_of_le_of_lt (le_max_right 0 t) hmaxb'
  have hIccsub : Set.Icc a' b' ⊆ Set.Ioo a b := Set.Icc_subset_Ioo haa' hb'b
  have hIoosub : Set.Ioo a' b' ⊆ Set.Ioo a b :=
    Set.Ioo_subset_Ioo (le_of_lt haa') (le_of_lt hb'b)
  -- Continuity of both curves on the compact subinterval.
  have hcont₁ : ContinuousOn (fun s => ((Γc s).1, (Γc s).2.1)) (Set.Icc a' b') :=
    fun s hs => ((hγ₁d s (hIccsub hs)).continuousAt).continuousWithinAt
  have hcont₂ : ContinuousOn (QIQTH.ExpMap.expTube g gi hC p v) (Set.Icc a' b') :=
    fun s hs => ((hYd s (hab (hIccsub hs))).continuousAt).continuousWithinAt
  -- Both images are bounded, hence sit in a common closed ball.
  have hb1 : Bornology.IsBounded ((fun s => ((Γc s).1, (Γc s).2.1)) '' Set.Icc a' b') :=
    (isCompact_Icc.image_of_continuousOn hcont₁).isBounded
  have hb2 : Bornology.IsBounded (QIQTH.ExpMap.expTube g gi hC p v '' Set.Icc a' b') :=
    (isCompact_Icc.image_of_continuousOn hcont₂).isBounded
  obtain ⟨R, hR⟩ := (hb1.union hb2).subset_closedBall (0 : Point n × Point n)
  -- `geodesicField` is Lipschitz on the closed ball (compact convex).
  obtain ⟨K, hK⟩ :=
    ((contDiff_geodesicField g gi hC).contDiffOn
      (s := Metric.closedBall (0 : Point n × Point n) R)).exists_lipschitzOnWith
      (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  -- Both curves stay in the ball on the open subinterval.
  have hmem₁ : ∀ s ∈ Set.Ioo a' b',
      ((Γc s).1, (Γc s).2.1) ∈ Metric.closedBall (0 : Point n × Point n) R :=
    fun s hs => hR (Set.mem_union_left _ ⟨s, Set.Ioo_subset_Icc_self hs, rfl⟩)
  have hmem₂ : ∀ s ∈ Set.Ioo a' b',
      QIQTH.ExpMap.expTube g gi hC p v s ∈ Metric.closedBall (0 : Point n × Point n) R :=
    fun s hs => hR (Set.mem_union_right _ ⟨s, Set.Ioo_subset_Icc_self hs, rfl⟩)
  -- Geodesic uniqueness on `(a', b')` (contains both `0` and `t`).
  have h0' : (0 : ℝ) ∈ Set.Ioo a' b' := ⟨ha'0, h0b'⟩
  have heqon : Set.EqOn (fun s => ((Γc s).1, (Γc s).2.1))
      (QIQTH.ExpMap.expTube g gi hC p v) (Set.Ioo a' b') :=
    geodesic_local_unique g gi h0' hK
      (fun s hs => ⟨hγ₁d s (hIoosub hs), hmem₁ s hs⟩)
      (fun s hs => ⟨hYd s (hab (hIoosub hs)), hmem₂ s hs⟩)
      heq0
  exact heqon ⟨ha't, htb'⟩

end QIQTH.Geodesic
