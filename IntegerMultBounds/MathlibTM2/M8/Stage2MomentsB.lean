module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Moments
public import IntegerMultBounds.MathlibTM2.M8.Stage2HistogramB
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The moment gaps of the design-B stage-2 supplier

The certificate of `Stage2Moments` with the saving as a parameter `a`: for checked rows
(`rowOkAt a`), `(r/m)^(1-a) ≤ (r/m) cubic (a L_r)` (`rpow_le_at`), so the `(1-a)`-moment is at most
the rational sum `tauBoundAt a` (`moment_le_at`).

The design-B histogram (`histogramB`, from the actual signed geometry in `scripts/pr97/stage2framebank.py` and `stage2cert.py`)
has the same linear moment `q₁` and the same rank mass as the plain one, and its `τ*`-moment at
`τ* = 1 - 12402/10⁸` stays below `q_τ = 1 - 1/10⁸`. Its whole-projector saving is
`a* ≈ 1.24086·10⁻⁴`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Moments

open Global.Branching97 (width roleCount)

/-- A row is checked at saving `a` when its rank lies in `1..m`, its series exceeds `m/r` and
`a L_r ≤ 1`. -/
def rowOkAt (a : ℚ) (row : Row) : Bool :=
  0 < row.1 && row.1 ≤ width && decide ((width : ℚ) / row.1 < expSeries (logBound row) row.2.2.2) &&
    decide (a * logBound row ≤ 1)

/-- The rational bound of the `(1-a)`-moment. -/
def tauBoundAt (a : ℚ) : List Row → ℚ
  | [] => 0
  | row :: rows =>
    (row.2.1 : ℚ) / roleCount * ((row.1 : ℚ) / width) * cubic (a * logBound row) + tauBoundAt a rows

theorem log_lt_at {a : ℚ} {row : Row} (h : rowOkAt a row = true) :
    Real.log ((width : ℝ) / row.1) < (logBound row : ℝ) := by
  simp only [rowOkAt, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hr, -⟩, hs⟩, -⟩ := h
  have hr' : (0 : ℝ) < row.1 := by exact_mod_cast hr
  apply (Real.log_lt_iff_lt_exp (div_pos (by norm_num [width]) hr')).mpr
  have hs' : (((width : ℚ) / row.1 : ℚ) : ℝ) < (expSeries (logBound row) row.2.2.2 : ℝ) := by
    exact_mod_cast hs
  push_cast at hs'
  rw [expSeries_cast] at hs'
  exact hs'.trans_le (Real.sum_le_exp_of_nonneg (logBound_nonneg row) _)

theorem rpow_le_at {a : ℚ} (ha : 0 < a) {row : Row} (h : rowOkAt a row = true) :
    ((row.1 : ℝ) / width) ^ (1 - (a : ℝ)) ≤
      (row.1 : ℝ) / width * (cubic (a * logBound row) : ℝ) := by
  have hlog := log_lt_at h
  simp only [rowOkAt, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hr, hm⟩, -⟩, h1⟩ := h
  have hr' : (0 : ℝ) < row.1 := by exact_mod_cast hr
  have hm' : (row.1 : ℝ) ≤ width := by exact_mod_cast hm
  have hw : (0 : ℝ) < width := by norm_num [width]
  have hp : 0 < (row.1 : ℝ) / width := div_pos hr' hw
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  set x := (a : ℝ) * Real.log ((width : ℝ) / row.1) with hx
  have hlog0 : 0 ≤ Real.log ((width : ℝ) / row.1) :=
    Real.log_nonneg ((one_le_div hr').mpr hm')
  have hx0 : 0 ≤ x := mul_nonneg ha'.le hlog0
  have hxL : x ≤ (a : ℝ) * (logBound row : ℝ) := mul_le_mul_of_nonneg_left hlog.le ha'.le
  have h1' : (a : ℝ) * (logBound row : ℝ) ≤ 1 := by exact_mod_cast h1
  have hpow : ((row.1 : ℝ) / width) ^ (1 - (a : ℝ)) = (row.1 : ℝ) / width * Real.exp x := by
    rw [Real.rpow_def_of_pos hp, hx, Real.log_div hw.ne' hr'.ne', Real.log_div hr'.ne' hw.ne',
      ← Real.exp_log hp, Real.log_div hr'.ne' hw.ne', ← Real.exp_add]
    ring_nf
  have hexp : Real.exp x ≤ (cubic (a * logBound row) : ℝ) := by
    have hy0 : (0 : ℝ) ≤ (a : ℝ) * (logBound row : ℝ) := hx0.trans hxL
    calc Real.exp x ≤ 1 + x + x ^ 2 / 2 + 2 / 9 * x ^ 3 :=
          Global.Branching97.exp_le_cubic hx0 (hxL.trans h1')
      _ ≤ _ := by rw [cubic]; push_cast; gcongr
  rw [hpow]
  exact mul_le_mul_of_nonneg_left hexp hp.le

/-- The `(1-a)`-moment of checked rows is at most their rational bound. -/
theorem moment_le_at {a : ℚ} (ha : 0 < a) : ∀ {rows : List Row}, rows.all (rowOkAt a) = true →
    moment (1 - a) rows ≤ tauBoundAt a rows
  | [], _ => by simp [moment, tauBoundAt]
  | row :: rows, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [moment, tauBoundAt]
    push_cast
    have hw : (0 : ℝ) ≤ (row.2.1 : ℝ) / roleCount := by positivity
    have := mul_le_mul_of_nonneg_left (rpow_le_at ha h.1) hw
    have := moment_le_at ha h.2
    nlinarith

/-- The design-B saving `a = 1 - τ*`. -/
def savingB : ℚ := 12402 / 10 ^ 8

/-- The design-B `τ*`-moment gap. -/
def qτB : ℚ := 1 - 1 / 10 ^ 8

theorem histogramB_ok : histogramB.all (rowOkAt savingB) = true := by decide +kernel

theorem tauBoundB_lt : tauBoundAt savingB histogramB < qτB := by decide +kernel

theorem linMomentB_eq : linMoment histogramB = q₁ := by decide +kernel

/-- The design-B histogram carries the stage-1 rank sum. -/
theorem rank_massB :
    (histogramB.map fun row => row.1 * row.2.1).sum = Global.Branching97.rankBound := by
  decide +kernel

/-- Every design-B rank is below `m`. -/
theorem histogramB_lt : ∀ row ∈ histogramB, row.1 < width := by decide +kernel

/-- **The `τ*`-moment gap** of the design-B histogram. -/
theorem tau_momentB : moment (1 - savingB) histogramB < qτB := by
  have h := moment_le_at (by norm_num [savingB]) histogramB_ok
  have h' : (tauBoundAt savingB histogramB : ℝ) < qτB := by exact_mod_cast tauBoundB_lt
  linarith

/-- **The linear moment gap** of the design-B histogram. -/
theorem linear_momentB : moment 1 histogramB = q₁ := by
  rw [moment_one, linMomentB_eq]

theorem qτB_lt_one : qτB < 1 := by norm_num [qτB]

theorem qτB_nonneg : 0 ≤ qτB := by norm_num [qτB]

end IntegerMultBounds.MathlibTM2.M8.Stage2Moments
