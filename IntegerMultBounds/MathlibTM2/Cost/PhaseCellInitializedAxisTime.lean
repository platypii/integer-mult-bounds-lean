module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellInitializedAxisWorkspace
import Mathlib.Tactic.Linarith

/-! Collect the complete axis time ledger into traffic, shared volume and the
single numerical batch term. No phase's execution is repeated. -/
@[expose] public section
set_option autoImplicit false
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem generatedDyadicStageCoeff_nonneg (T t₀ D : ℕ) : 0 ≤ generatedDyadicStageCoeff T t₀ D := by
  have := IntegerMultBounds.MathlibTM2.Node.swapConst_pos
  unfold generatedDyadicStageCoeff
  positivity

private theorem timeLedger_le (init gather publication header crop b stage N traffic total narrow route numerical B D : ℝ)
    (hq : narrow ≤ traffic) (hT : 1 ≤ total) (hB : 0 ≤ B) (hD : 0 ≤ D) (hnum : 0 ≤ numerical) :
    init*traffic+(((gather*traffic+432*stage*traffic*route+(8*b+5)*total+B*(2*N+1)*numerical)+
      (2*total+publication*traffic+6+108*stage*traffic*route))+
      (2624001*total+N*D*numerical+726*narrow+455+((header+3*crop)*traffic+1))+(21*traffic+12)) ≤
    (init+gather+publication+header+3*crop+747)*traffic+540*stage*traffic*route+
      (8*b+2624482)*total+(2*B+D)*(N+1)*numerical := by
  have hsolve := mul_nonneg (add_nonneg hB hD) hnum
  have hconst := mul_le_mul_of_nonneg_left hT (show (0 : ℝ) ≤ 474 by norm_num)
  have hq' := mul_le_mul_of_nonneg_left hq (show (0 : ℝ) ≤ 726 by norm_num)
  nlinarith only [hsolve,hconst,hq']

def initializedAxisTimeTrafficFactor (cV cG cW cVPub cDB : ℕ) :=
  coreExposureTrafficFactor cG cW+10175+100*cV+100*cVPub+
    boundaryHeaderTrafficFactor cDB+3*boundaryPublicationTrafficFactor cDB

theorem initializedAxisTime_le (cV cG cW cVPub cDB b N s p W total : ℕ)
    (B D stage route numerical : ℝ) (hPW : p ≤ W) (hT : 1 ≤ total)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hnum : 0 ≤ numerical) :
    (560+100*cV : ℕ)*(N*(s*W) : ℕ)+
      ((((coreExposureTrafficFactor cG cW+6013 : ℕ)*(N*s*W : ℕ)+
        432*(stage : ℝ)*(N*s*W : ℕ)*route+(8*(b : ℝ)+5)*(total : ℕ)+B*(2*(N : ℝ)+1)*numerical)+
        (2*(total : ℝ)+(2855+100*cVPub : ℕ)*(N*s*W : ℕ)+6+108*(stage : ℝ)*(N*s*W : ℕ)*route))+
        (2624001*(total : ℝ)+(N : ℝ)*D*numerical+726*(N*s*p : ℕ)+455+
          (boundaryHeaderTrafficFactor cDB*(N*(s*W))+(3*(boundaryPublicationTrafficFactor cDB*(N*(s*W)))+1) : ℕ))+
        (21*(N*(s*W))+12 : ℕ)) ≤
    (initializedAxisTimeTrafficFactor cV cG cW cVPub cDB : ℝ)*(N*(s*W) : ℕ)+
      540*(stage : ℝ)*(N*(s*W) : ℕ)*route+(8*(b : ℝ)+2624482)*(total : ℕ)+
      (2*B+D)*((N : ℝ)+1)*numerical := by
  have hq : ((N*s*p : ℕ) : ℝ) ≤ (N*(s*W) : ℕ) := by
    exact_mod_cast (show N*s*p ≤ N*(s*W) by
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (N*s) hPW)
  have htotal : (1 : ℝ) ≤ (total : ℝ) := by exact_mod_cast hT
  have h := timeLedger_le (560+100*cV) (coreExposureTrafficFactor cG cW+6013)
    (2855+100*cVPub) (boundaryHeaderTrafficFactor cDB) (boundaryPublicationTrafficFactor cDB)
    b stage N (N*(s*W)) total (N*s*p) route numerical B D (by simpa only [Nat.cast_mul] using hq) htotal hB hD hnum
  unfold initializedAxisTimeTrafficFactor
  convert h using 1 <;> push_cast <;> ring

/-- The raw ledger matches the executed phase composition before collection. -/
noncomputable def initializedAxisTimeLedger (cG cW cVPub cDB b N s p W total : ℕ)
    (B D stage axisLength ratio power dimension routeFactor : ℝ) : ℝ :=
  ((((coreExposureTrafficFactor cG cW+6013 : ℕ)*(N*s*W : ℕ)+
    432*stage*(N*s*W : ℕ)*dimension*routeFactor+(8*(b : ℝ)+5)*(total : ℝ)+
    B*(2*(N : ℝ)+1)*(axisLength*ratio)*power)+
    (2*(total : ℝ)+(2855+100*cVPub : ℕ)*(N*s*W : ℕ)+6+
      108*stage*(N*s*W : ℕ)*dimension*routeFactor))+
    (2624001*(total : ℝ)+(N : ℝ)*D*axisLength*ratio*power+726*(N*s*p : ℕ)+455+
      (boundaryHeaderTrafficFactor cDB*(N*(s*W))+(3*(boundaryPublicationTrafficFactor cDB*(N*(s*W)))+1) : ℕ)))+
    (21*(N*(s*W))+12 : ℕ)

theorem initializedAxisTime_steps_le (cV cG cW cVPub cDB b N s p W total steps : ℕ)
    (B D stage axisLength ratio power dimension routeFactor : ℝ)
    (hPW : p ≤ W) (hT : 1 ≤ total) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hstage : 0 ≤ stage) (haxis : 0 ≤ axisLength) (hratio : 0 ≤ ratio)
    (hpower : 0 ≤ power) (hdim : 0 ≤ dimension) (hroute : 0 ≤ routeFactor)
    (hsteps : steps ≤ (560+100*cV)*(N*(s*W))+
      ⌊initializedAxisTimeLedger cG cW cVPub cDB b N s p W total
        B D stage axisLength ratio power dimension routeFactor⌋₊) :
    (steps : ℝ) ≤ (initializedAxisTimeTrafficFactor cV cG cW cVPub cDB : ℕ)*(N*s*W : ℕ)+
      540*stage*(N*s*W : ℕ)*dimension*routeFactor+(8*(b : ℝ)+2624482)*(total : ℝ)+
      (2*B+D)*((N : ℝ)+1)*(axisLength*ratio)*power := by
  let ledger := initializedAxisTimeLedger cG cW cVPub cDB b N s p W total
    B D stage axisLength ratio power dimension routeFactor
  have hn : 0 ≤ ledger := by dsimp only [ledger,initializedAxisTimeLedger]; positivity
  have hsteps' : (steps : ℝ) ≤ ((560+100*cV)*(N*(s*W)) : ℕ)+(⌊ledger⌋₊ : ℝ) := by
    exact_mod_cast hsteps
  have hreal := hsteps'.trans (add_le_add le_rfl (Nat.floor_le hn))
  apply hreal.trans
  have hc := initializedAxisTime_le cV cG cW cVPub cDB b N s p W total
    B D stage (dimension*routeFactor) (axisLength*ratio*power) hPW hT hB hD (by positivity)
  convert hc using 1 <;> (try simp only [ledger,initializedAxisTimeLedger]) <;> push_cast <;> ring

end IntegerMultBounds.MathlibTM2.Cost
