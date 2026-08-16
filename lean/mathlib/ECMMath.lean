/-  ECMMath.lean — the MATH tier of the Bitcoin Energy Cost Model (energycostmodel.com).

    L3 (core Lean, omega) proves the INTEGER model: the mining-cost floor and its monotonicity over ℤ.
    This MATH tier uses MATHLIB to prove the REAL-VALUED and ANALYTIC facts that omega cannot reach —
    the continuous cost function, and (the payoff) the LOGISTIC FORECAST that L3 had to leave at the
    untrusted boundary. The data/fit stay untrusted; the forecast FUNCTION's shape is now kernel-proven.

    Verified with Mathlib (leanprover/lean4 v4.30.0). Runs SIDE-BY-SIDE with the L3 core (ecm_cost_proof.lean). -/
import Mathlib

namespace ECMMath
open Real

/- ── Continuous cost: daily electricity spend / daily issuance (the ℝ analogue of the ℤ floor) ── -/
noncomputable def cost (dailyCost delta : ℝ) : ℝ := dailyCost / delta

theorem cost_nonneg (c d : ℝ) (hc : 0 ≤ c) (hd : 0 < d) : 0 ≤ cost c d := by
  unfold cost; positivity
/-- Higher electricity spend ⇒ higher floor (monotone, over ℝ). -/
theorem cost_mono_energy (c1 c2 d : ℝ) (hd : 0 < d) (h : c1 ≤ c2) : cost c1 d ≤ cost c2 d := by
  unfold cost; gcongr
/-- More issuance ⇒ lower cost per coin (antitone in the denominator, over ℝ). -/
theorem cost_anti_issuance (c d1 d2 : ℝ) (hc : 0 ≤ c) (hd1 : 0 < d1) (h : d1 ≤ d2) :
    cost c d2 ≤ cost c d1 := by
  unfold cost; gcongr

/- ── Logistic forecast shape:  offset + L / (1 + exp(-k(t - x0)))  — the model's power/fee growth curve.
      L3 could not touch exp; the MATH tier proves it is BOUNDED in [offset, offset+L] and MONOTONE. ── -/
noncomputable def logistic (t L k x0 offset : ℝ) : ℝ := offset + L / (1 + Real.exp (-(k * (t - x0))))

/-- The forecast never dips below its offset (floor of the S-curve). -/
theorem logistic_lb (t L k x0 offset : ℝ) (hL : 0 ≤ L) : offset ≤ logistic t L k x0 offset := by
  unfold logistic
  have : 0 ≤ L / (1 + Real.exp (-(k * (t - x0)))) := by positivity
  linarith
/-- The forecast never exceeds its saturation offset+L (ceiling of the S-curve). -/
theorem logistic_ub (t L k x0 offset : ℝ) (hL : 0 ≤ L) : logistic t L k x0 offset ≤ offset + L := by
  unfold logistic
  have hpos : (0:ℝ) < 1 + Real.exp (-(k * (t - x0))) := by positivity
  have h1 : (1:ℝ) ≤ 1 + Real.exp (-(k * (t - x0))) := by
    have := Real.exp_nonneg (-(k * (t - x0))); linarith
  have : L / (1 + Real.exp (-(k * (t - x0)))) ≤ L := by
    calc L / (1 + Real.exp (-(k * (t - x0)))) ≤ L / 1 := by gcongr
      _ = L := by ring
  linarith
/-- The forecast is monotone non-decreasing in time (a growth S-curve, k ≥ 0). -/
theorem logistic_mono (L k x0 offset t1 t2 : ℝ) (hL : 0 ≤ L) (hk : 0 ≤ k) (h : t1 ≤ t2) :
    logistic t1 L k x0 offset ≤ logistic t2 L k x0 offset := by
  unfold logistic
  have hexp : Real.exp (-(k * (t2 - x0))) ≤ Real.exp (-(k * (t1 - x0))) := by
    apply Real.exp_le_exp.mpr; nlinarith
  have hpos : (0:ℝ) < 1 + Real.exp (-(k * (t2 - x0))) := by positivity
  gcongr

/- ── Stock-to-Flow (companion model): S2F = e^{-1.84} · ratio^{3.36},  ratio = stock/flow.
      A positive constant times an rpow with a positive exponent ⇒ MONOTONE in the ratio (needs Real.rpow). ── -/
noncomputable def s2f (ratio : ℝ) : ℝ := Real.exp (-1.84) * ratio ^ (3.36 : ℝ)

/-- S2F is non-negative. -/
theorem s2f_nonneg (r : ℝ) (hr : 0 ≤ r) : 0 ≤ s2f r := by
  unfold s2f; positivity
/-- S2F is MONOTONE in the stock-to-flow ratio (rpow monotonicity, exponent 3.36 > 0). -/
theorem s2f_mono (r1 r2 : ℝ) (h1 : 0 ≤ r1) (h : r1 ≤ r2) : s2f r1 ≤ s2f r2 := by
  unfold s2f; gcongr

/- ── Global-floor STRUCTURE (Phase 1): the sector ordering and the envelope containment.
      These make the dashboard's "kernel-proven" global-floor claims actual theorems, not assertions. ── -/

/-- Sector ordering: industrial ≤ commercial ≤ self-mining. The floor is `cost (K·rate) delta` with
    K = power·hours/100 ≥ 0, so IND ≤ COM ≤ RES ⇒ the three floors are ordered (monotone in the rate). -/
theorem sector_order (K delta rIND rCOM rRES : ℝ) (hK : 0 ≤ K) (hd : 0 < delta)
    (h1 : rIND ≤ rCOM) (h2 : rCOM ≤ rRES) :
    cost (K * rIND) delta ≤ cost (K * rCOM) delta ∧
    cost (K * rCOM) delta ≤ cost (K * rRES) delta :=
  ⟨cost_mono_energy _ _ _ hd (mul_le_mul_of_nonneg_left h1 hK),
   cost_mono_energy _ _ _ hd (mul_le_mul_of_nonneg_left h2 hK)⟩

/-- Envelope containment: a hashrate-weighted average of the regional rates lies within [lo, hi]
    whenever every regional rate does (a convex combination). This is why the "today's-mix" weighted
    line provably never escapes the cheapest→priciest band. -/
theorem envelope_contains {ι : Type*} (s : Finset ι) (w f : ι → ℝ) (lo hi : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hlo : ∀ i ∈ s, lo ≤ f i) (hhi : ∀ i ∈ s, f i ≤ hi) :
    lo ≤ ∑ i ∈ s, w i * f i ∧ ∑ i ∈ s, w i * f i ≤ hi := by
  refine ⟨?_, ?_⟩
  · calc lo = ∑ i ∈ s, w i * lo := by rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ i ∈ s, w i * f i :=
          Finset.sum_le_sum fun i hi' => mul_le_mul_of_nonneg_left (hlo i hi') (hw i hi')
  · calc ∑ i ∈ s, w i * f i ≤ ∑ i ∈ s, w i * hi :=
          Finset.sum_le_sum fun i hi' => mul_le_mul_of_nonneg_left (hhi i hi') (hw i hi')
      _ = hi := by rw [← Finset.sum_mul, hsum, one_mul]

/-- Band containment carried through the (non-negative) cost scaling: cost_lo ≤ cost_weighted ≤ cost_hi. -/
theorem weighted_floor_in_band {ι : Type*} (s : Finset ι) (w f : ι → ℝ) (lo hi scale : ℝ)
    (hscale : 0 ≤ scale) (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hlo : ∀ i ∈ s, lo ≤ f i) (hhi : ∀ i ∈ s, f i ≤ hi) :
    scale * lo ≤ scale * (∑ i ∈ s, w i * f i) ∧ scale * (∑ i ∈ s, w i * f i) ≤ scale * hi := by
  obtain ⟨hL, hH⟩ := envelope_contains s w f lo hi hw hsum hlo hhi
  exact ⟨mul_le_mul_of_nonneg_left hL hscale, mul_le_mul_of_nonneg_left hH hscale⟩

/- ── C5 EMIT: generate the global-floor ARITHMETIC (Python) from proven ℝ defs, so refresh_full runs
      GENERATED code rather than hand-written. Scalar ops are rendered by ER.toPy from expressions proven
      faithful to the defs; the min/max/weighted reductions are exactly the operations envelope_contains
      bounds. Mirrors ecm_cost_proof.lean's E.toJS → generated_ecm.js, but over ℝ and to Python. ── -/
noncomputable def sectorFloor (base rate com : ℝ) : ℝ := base * rate / com   -- cost_x = cost_com·rate_x/com
noncomputable def fxCents (rate fx : ℝ) : ℝ := rate / fx * 100               -- local/kWh → USD cents
noncomputable def scaleFloor (scale c : ℝ) : ℝ := scale * c                  -- $ floor = (power·h/delta)·cents

inductive GV | base | rate | com | fx | scale | c
inductive ER | var : GV → ER | lit : Int → ER | mul : ER → ER → ER | add : ER → ER → ER | div : ER → ER → ER
noncomputable def ER.eval (g : GV → ℝ) : ER → ℝ
  | .var v   => g v
  | .lit n   => (n : ℝ)
  | .mul a b => a.eval g * b.eval g
  | .add a b => a.eval g + b.eval g
  | .div a b => a.eval g / b.eval g
def sectorER : ER := .div (.mul (.var .base) (.var .rate)) (.var .com)
def fxER : ER := .mul (.div (.var .rate) (.var .fx)) (.lit 100)
def scaleER : ER := .mul (.var .scale) (.var .c)

theorem sectorER_faithful (b r cm : ℝ) :
    sectorER.eval (fun v => match v with | .base => b | .rate => r | .com => cm | _ => 0) = sectorFloor b r cm := by
  simp [sectorER, ER.eval, sectorFloor]
theorem fxER_faithful (r fx : ℝ) :
    fxER.eval (fun v => match v with | .rate => r | .fx => fx | _ => 0) = fxCents r fx := by
  simp [fxER, ER.eval, fxCents]
theorem scaleER_faithful (s cc : ℝ) :
    scaleER.eval (fun v => match v with | .scale => s | .c => cc | _ => 0) = scaleFloor s cc := by
  simp [scaleER, ER.eval, scaleFloor]

def GV.toPy : GV → String
  | .base => "base" | .rate => "rate" | .com => "com" | .fx => "fx" | .scale => "scale" | .c => "c"
def ER.toPy : ER → String
  | .var v   => v.toPy
  | .lit n   => toString n
  | .mul a b => "(" ++ a.toPy ++ " * " ++ b.toPy ++ ")"
  | .add a b => "(" ++ a.toPy ++ " + " ++ b.toPy ++ ")"
  | .div a b => "(" ++ a.toPy ++ " / " ++ b.toPy ++ ")"

def pyGlobal : String :=
  "# ---- GENERATED BY ECMMath.lean (ER.toPy of the PROVEN global-floor ops) — DO NOT hand-edit ----\n" ++
  "def _fxCents(rate, fx): return " ++ fxER.toPy ++ "\n" ++
  "def _sectorFloor(base, rate, com): return " ++ sectorER.toPy ++ "\n" ++
  "def _scaleFloor(scale, c): return " ++ scaleER.toPy ++ "\n" ++
  "def _envLo(mat): return mat.min(axis=1)   # min over regions (envelope_contains: weighted >= min)\n" ++
  "def _envHi(mat): return mat.max(axis=1)   # max over regions (envelope_contains: weighted <= max)\n" ++
  "def _weighted(mat, w): return mat @ w     # sum_i w_i*rate_i (envelope_contains: stays in [lo,hi])\n"

end ECMMath

#eval "ECM MATH tier (Mathlib): real cost monotone/antitone + logistic BOUNDED [offset,offset+L] & MONOTONE — KERNEL-CHECKED"
#print axioms ECMMath.cost_anti_issuance
#print axioms ECMMath.logistic_ub
#print axioms ECMMath.logistic_mono
#print axioms ECMMath.s2f_mono
#print axioms ECMMath.sector_order
#print axioms ECMMath.envelope_contains
#print axioms ECMMath.weighted_floor_in_band
#print axioms ECMMath.sectorER_faithful
#print axioms ECMMath.fxER_faithful
#print axioms ECMMath.scaleER_faithful
#eval IO.FS.writeFile "generated_global.py" ECMMath.pyGlobal

def cert : String :=
  "{\"model\":\"energycostmodel — Bitcoin mining cost floor\",\"tier\":\"MATH\"," ++
  "\"prover\":\"Lean 4 + Mathlib (v4.30.0)\"," ++
  "\"proven\":[\"cost_nonneg\",\"cost_mono_energy\",\"cost_anti_issuance\"," ++
  "\"logistic_lb\",\"logistic_ub\",\"logistic_mono\",\"s2f_nonneg\",\"s2f_mono\"," ++
  "\"sector_order\",\"envelope_contains\",\"weighted_floor_in_band\"," ++
  "\"sectorER_faithful\",\"fxER_faithful\",\"scaleER_faithful\"]," ++
  "\"emits\":\"generated_global.py (_fxCents/_sectorFloor/_scaleFloor via ER.toPy of the proven defs; " ++
  "_envLo/_envHi/_weighted = the min/max/weighted reductions envelope_contains bounds) — refresh_full runs it\"," ++
  "\"note\":\"real-valued + analytic facts beyond core-Lean omega. Global-floor STRUCTURE proven " ++
  "(sector_order, envelope_contains, weighted_floor_in_band) AND the global-floor ARITHMETIC is now GENERATED " ++
  "from the proven defs (ER.toPy, *_faithful) — refresh_full runs generated code, not hand-written. " ++
  "Data/fit remain the untrusted tier\"}"
#eval IO.FS.writeFile "ecm_math_cert.json" cert
