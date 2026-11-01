module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedCoreScan
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreJobQueues

/-! Separate actual movement/control work from normalized numerical recovery,
then sum the complete executed bills before any selected-axis absorption. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {T Q A s : ℕ} [NeZero s] {U : Type}

noncomputable def computedCoreMovementTime (V : ℕ) (r : PackedNormalizedJob A s) : ℕ :=
  readSupplierEndpointsCost V r.a (r.b-r.a)+(6*(ComputedRecoveryPlan.routedPayload r).length+6)+
    restoreReplicaOrderCost r.Fs.length (coreLength s r.coreWidth r.k) r.W+(2*(r.a+r.b)+5)

theorem computedCoreTime_eq (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (V : ℕ) (r : PackedNormalizedJob A s) :
    plan.coreTimeCost b V r = plan.normalizedTimeCost b r+computedCoreMovementTime V r := by
  unfold ComputedRecoveryPlan.coreTimeCost computedCoreMovementTime
  omega

/-- Endpoint work is paid explicitly; it is not hidden in a per-job T reserve. -/
theorem computedCoreMovementTime_le (V : ℕ) (r : PackedNormalizedJob A s) (N H W L : ℕ)
    (hN : r.Fs.length = N) (hH : r.b-r.a = H) (hW : r.W = W)
    (hL : coreLength s r.coreWidth r.k = L) (hWpos : 1 ≤ W) :
    computedCoreMovementTime V r ≤ 19*V+14*s+33+6*(N*H*W)+35*((N+1)*(L*W+1)) := by
  have hread : readSupplierEndpointsCost V r.a (r.b-r.a)+(2*(r.a+r.b)+5) ≤ 19*V+14*s+27 := by
    have ha := r.bounds.hab
    have hb := r.bounds.hbs
    unfold readSupplierEndpointsCost
    omega
  have hlength : (ComputedRecoveryPlan.routedPayload r).length = N*H*W := by
    change r.inputPayload.length = N*H*W
    rw [PackedNormalizedJob.inputPayload_length,hN,hH,hW]
  have hreverse := restoreReplicaOrderCost_linear N L W hWpos
  unfold computedCoreMovementTime
  rw [hlength,hN,hL,hW]
  omega

/-- Sum the entire actual core bill, keeping normalized recovery visible and
charging local movement once per record. No shared allowance is duplicated. -/
theorem computedCoreScheduleTime_le (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (V N H W L : ℕ) (records : List (PackedNormalizedJob A s)) (hWpos : 1 ≤ W)
    (hprofile : ∀ r ∈ records, r.Fs.length = N ∧ r.b-r.a = H ∧ r.W = W ∧
      coreLength s r.coreWidth r.k = L) :
    (records.map (plan.coreTimeCost b V)).sum ≤ (records.map (plan.normalizedTimeCost b)).sum+
      records.length*(19*V+14*s+33+6*(N*H*W)+35*((N+1)*(L*W+1))) := by
  induction records with
  | nil => simp
  | cons r records ih =>
    obtain ⟨hN,hH,hW,hL⟩ := hprofile r (by simp)
    have hr := computedCoreMovementTime_le V r N H W L hN hH hW hL hWpos
    have ht := ih (by intro x hx; exact hprofile x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,computedCoreTime_eq,Nat.add_mul,Nat.one_mul]
    simp only [Nat.add_mul,Nat.one_mul] at hr ht
    omega

end IntegerMultBounds.MathlibTM2.Cost
