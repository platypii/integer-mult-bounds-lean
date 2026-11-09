module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Scalar bookkeeping for the fitting complex-core ledger. Numerical precision
enters only through p ≤ P, so the same argument applies before density conversion. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

theorem cyclicComplexTimeEnvelope_le (E C F p P s V replicas cw cW W : ℝ)
    (hE : 0 ≤ E) (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hp : 1 ≤ p) (hP : p ≤ P) (hs : 0 ≤ s) (hV : s ≤ V)
    (hr : 0 ≤ replicas) (hcw : 0 ≤ cw) (hcW : 0 ≤ cW)
    (hW : 0 ≤ W) (hWbound : W ≤ cW*p) :
    4200*replicas*s*(cw*p+1)+2800*(replicas+1)*s*(cw*p+1)+
      800*((30*cw+50)*(replicas+1)*p+replicas*C*P)*V+
      680*(E+F)*replicas*V*P+7600*(replicas+1)*s*(cw*p+W+1) ≤
    (14600*(cw+cW+1)+800*(30*cw+50)+800*C+680*(E+F))*(replicas+1)*V*P := by
  let D := cw+cW+1
  have hV0 : 0 ≤ V := hs.trans hV
  have hP0 : 0 ≤ P := by linarith
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hwidth : cw*p+W+1 ≤ D*P := by
    have hh := mul_nonneg (add_nonneg hcw hcW) (sub_nonneg.mpr hP)
    dsimp only [D]
    nlinarith only [hh,hWbound,hp,hP]
  have hwidth' : cw*p+1 ≤ D*P := by linarith only [hwidth,hW]
  have hnative : s*(cw*p+1) ≤ V*(D*P) :=
    mul_le_mul hV hwidth' (by positivity) hV0
  have hnative' : s*(cw*p+W+1) ≤ V*(D*P) :=
    mul_le_mul hV hwidth (by positivity) hV0
  have htraffic₁ := mul_le_mul_of_nonneg_left hnative
    (by positivity : (0 : ℝ) ≤ 4200*replicas+2800*(replicas+1))
  have htraffic₂ := mul_le_mul_of_nonneg_left hnative'
    (by positivity : (0 : ℝ) ≤ 7600*(replicas+1))
  have htrafficPos : 0 ≤ D*V*P := by positivity
  have hlinear := mul_le_mul_of_nonneg_left hP
    (by positivity : (0 : ℝ) ≤ 800*(30*cw+50)*(replicas+1)*V)
  have hbatchPos : 0 ≤ C*V*P := by positivity
  have hsolvePos : 0 ≤ (E+F)*V*P := by positivity
  dsimp only [D] at htraffic₁ htraffic₂ htrafficPos
  nlinarith only [htraffic₁,htraffic₂,htrafficPos,hlinear,hbatchPos,hsolvePos]

end IntegerMultBounds.MathlibTM2.Cost
