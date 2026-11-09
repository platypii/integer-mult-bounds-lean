module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Fixed retirement overhead and linear input traffic preserve the numerical
fast-time exponent. Geometry supplies s ≤ volume and p ≤ working power. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

theorem cyclicOriginTime_fast_envelope (steps numerical b E A T N s p volume power : ℝ)
    (hb : 0 ≤ b) (hE : 0 ≤ E) (hN : 0 ≤ N)
    (hs : 0 ≤ s) (hp : 0 ≤ p) (hvolume : s ≤ volume) (hpower : p ≤ power)
    (hsteps : steps ≤ b*numerical+(3*b+1)*T+E*N*(7*s)*p)
    (hnumerical : numerical ≤ 5*T+A*(2*N+1)*volume*power) :
    steps ≤ (8*b+1)*T+(b*A+7*E)*(2*N+1)*volume*power := by
  have hv : 0 ≤ volume := hs.trans hvolume
  have hpow : 0 ≤ power := hp.trans hpower
  have hlocal := mul_le_mul hvolume hpower hp hv
  have htraffic := mul_le_mul_of_nonneg_left hlocal (by positivity : 0 ≤ 7*E*N)
  have hnum := mul_le_mul_of_nonneg_left hnumerical hb
  have hpad : 0 ≤ 7*E*(N+1)*volume*power := by positivity
  nlinarith only [hsteps,htraffic,hnum,hpad]

end IntegerMultBounds.MathlibTM2.Cost
