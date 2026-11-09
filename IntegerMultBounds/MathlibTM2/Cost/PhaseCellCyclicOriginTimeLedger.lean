module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicOriginControlSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicCallerRetirementTime

/-! Sum the actual origin callback time ledger before applying any asymptotic
bounds. Retirement multiplies run time by a fixed program constant only. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  CyclicComplexCallerLayout
variable {Q A : ℕ} {U : Type}

theorem cyclicOriginTime_le_components (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (V W a n radius core N input factor numerical : ℕ) :
    readSupplierEndpointsCost V a n+
      retiredTimeCost (A := A) (U := U) hR hQ
        (input+(factor+((4*(W+radius+core)+13)+numerical))) (N*n*W)+(2*(a+(a+n))+5) ≤
    (8*executionPush (A := A) (U := U) hR hQ+1)*
      (input+factor+numerical+cyclicOriginControlCost V W a n radius core)+8*N*W*n+4*909+5 := by
  let c := 8*executionPush (A := A) (U := U) hR hQ+1
  have hc : 1 ≤ c := by dsimp only [c]; omega
  have hread := Nat.le_mul_of_pos_left (readSupplierEndpointsCost V a n) hc
  have hseed := Nat.le_mul_of_pos_left (2*(a+(a+n))+5) hc
  unfold retiredTimeCost cyclicOriginControlCost
  change readSupplierEndpointsCost V a n+
    (c*(input+(factor+((4*(W+radius+core)+13)+numerical)))+8*(N*n*W)+4*909+5)+
    (2*(a+(a+n))+5) ≤ c*(input+factor+numerical+
      (readSupplierEndpointsCost V a n+(4*(W+radius+core)+13)+(2*(a+(a+n))+5)))+8*N*W*n+4*909+5
  change _ ≤ c*_ at hread hseed
  nlinarith only [hread,hseed]

/-- Actual callback costs share one fixed multiplier on the numerical bill;
all other terms remain explicit at their execution frequencies. -/
theorem cyclicOriginScheduleTime_le_components {ι : Type} (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (jobs : List ι) (V W N : ℕ) (a n radius core input factor numerical steps : ι → ℕ)
    (hsteps : ∀ j ∈ jobs, steps j ≤ readSupplierEndpointsCost V (a j) (n j)+
      retiredTimeCost (A := A) (U := U) hR hQ
        (input j+(factor j+((4*(W+radius j+core j)+13)+numerical j))) (N*n j*W)+
        (2*(a j+(a j+n j))+5)) :
    (jobs.map steps).sum ≤ (8*executionPush (A := A) (U := U) hR hQ+1)*
      ((jobs.map input).sum+(jobs.map factor).sum+(jobs.map numerical).sum+
        (jobs.map (fun j => cyclicOriginControlCost V W (a j) (n j) (radius j) (core j))).sum)+
      8*N*W*(jobs.map n).sum+(4*909+5)*jobs.length := by
  induction jobs with
  | nil => simp
  | cons j jobs ih =>
    have hs := ih (by intro k hk; exact hsteps k (by simp [hk]))
    have hj := (hsteps j (by simp)).trans
      (cyclicOriginTime_le_components (A := A) (U := U) hR hQ V W (a j) (n j) (radius j) (core j) N
        (input j) (factor j) (numerical j))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [hs,hj]

end IntegerMultBounds.MathlibTM2.Cost
