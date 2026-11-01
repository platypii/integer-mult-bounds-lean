module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellComputedRecoveryAuxiliarySchedule

/-! Compare complete grouped traffic with one polynomial setup allowance and
linear replica work; the numerical exponent is handled only after summation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

theorem computedCoreTraffic_le (cV cW p s t V count volume : ℕ)
    (hp : 1 ≤ p) (hst : s ≤ t) (hV : V ≤ cV*p)
    (hcount : count ≤ 2*t) (hvolume : volume ≤ 9*cW*s*p) :
    52*volume+count*(19*V+14*s+8754) ≤ (468*cW+38*cV+17536)*t^2*p ∧
      381*volume+34624*count ≤ (3429*cW+69248)*t*p := by
  have hvol : volume ≤ 9*cW*t*p := hvolume.trans (by gcongr)
  have hcontrol := Nat.mul_le_mul hcount
    (show 19*V+14*s+8754 ≤ 19*(cV*p)+14*t+8754 by omega)
  have htp : t ≤ t*p := by simpa using Nat.mul_le_mul_left t hp
  have htt : t ≤ t^2 := Nat.le_self_pow (by decide) t
  have htpp : t*p ≤ t^2*p := Nat.mul_le_mul_right p htt
  have httP : t^2 ≤ t^2*p := by simpa using Nat.mul_le_mul_left (t^2) hp
  have htP : t ≤ t^2*p := htt.trans httP
  have hscaled := Nat.mul_le_mul_left (468*cW+38*cV) htpp
  constructor
  · nlinarith only [hvol,hcontrol,hscaled,httP,htP]
  · nlinarith only [hvol,hcount,htp]

end IntegerMultBounds.MathlibTM2.Cost
