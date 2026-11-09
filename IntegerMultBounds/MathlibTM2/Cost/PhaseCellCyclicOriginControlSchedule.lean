module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReadSupplierEndpoints
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellDistinctCoreSetup

/-! Origin reading, ordinary numerical controls and changing-seed retirement
are shared linear work, counted at every callback before setup absorption. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

def cyclicOriginControlCost (V W a n radius core : ℕ) : ℕ :=
  readSupplierEndpointsCost V a n+(4*(W+radius+core)+13)+(2*(a+(a+n))+5)

theorem selectedCyclicOriginControlScheduleTime_le (cV cW scale : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ {ι : Type} (h : Sizes.Big m) (i : Fin (Sizes.d m))
      (jobs : List ι) (V W : ℕ) (a n radius core : ι → ℕ),
      jobs.length ≤ 2*Sizes.t m i → V ≤ cV*Sizes.p m → W ≤ cW*Sizes.p m →
      (∀ j ∈ jobs, a j ≤ Sizes.s m i ∧ n j ≤ Sizes.s m i ∧ radius j+core j ≤ Sizes.s m i) →
      scale*(jobs.map (fun j => cyclicOriginControlCost V W (a j) (n j) (radius j) (core j))).sum ≤ Sizes.T m := by
  filter_upwards [selectedDistinctCoreSetup_volume_le (19*cV+4*cW+70) 1 1 scale] with m hsetup
  intro ι h i jobs V W a n radius core hcount hV hW hgeometry
  apply hsetup i jobs (fun j => cyclicOriginControlCost V W (a j) (n j) (radius j) (core j)) hcount
  intro j hj
  obtain ⟨ha,hn,hcore⟩ := hgeometry j hj
  have ht : 1 ≤ Sizes.t m i := by have := h.good.lt i; omega
  have hp : 1 ≤ Sizes.p m := by have := h.thirteen_le_p; omega
  have htP := Nat.le_mul_of_pos_right (Sizes.t m i) hp
  have hpT := Nat.le_mul_of_pos_left (Sizes.p m) ht
  have hunit : 1 ≤ Sizes.t m i*Sizes.p m := Nat.mul_pos ht hp
  have hVaxis := hV.trans (Nat.mul_le_mul_left cV hpT)
  have hWaxis := hW.trans (Nat.mul_le_mul_left cW hpT)
  have haAxis := ha.trans ((h.good.lt i).le.trans htP)
  have hnAxis := hn.trans ((h.good.lt i).le.trans htP)
  have hcoreAxis := hcore.trans ((h.good.lt i).le.trans htP)
  simp only [pow_one]
  unfold cyclicOriginControlCost readSupplierEndpointsCost
  nlinarith only [hVaxis,hWaxis,haAxis,hnAxis,hcoreAxis,hunit]

end IntegerMultBounds.MathlibTM2.Cost
