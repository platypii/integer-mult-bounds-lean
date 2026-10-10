import IntegerMultBounds.Machine.CompactSpectatorLeafOriginal

/-! Paid setup and copies are charged to the original numeric descriptors.
This bound is valid even before those descriptors are instantiated with native
payload and fixed recursive arity; it does not hide unbounded caller metadata. -/
namespace IntegerMultBounds.Machine.CompactSpectatorLeafSetupBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorLeafSetup
open ButterflyAxisHeadersArithmetic

def scalar (s : Shape) (rows ell p rho left count slots right source target : ℕ) :=
  s.bits+s.axes+s.guard+s.chunk+s.active+s.payload+rows+ell+p+rho+left+count+slots+right+source+target+1

private theorem rounded_back (s : Shape) (hH : 0<s.H) (hK : 0<s.chunk) :
    RoundedRowDescriptor.rounded s.H s.chunk=s.H+s.B := by
  rw [RoundedRowDescriptor.rounded_eq_ceiling _ _ hH hK]
  have he := CompactGadgetReservationCapacity.back_exact s.axes s.guard s.chunk hK
  unfold Shape.H Shape.B CompactGadgetReservationCapacity.backChunks CompactGadgetReservationCapacity.chunks at *
  rw [Nat.mul_comm s.chunk]
  exact he.symm
private theorem rounded_front (s : Shape) (hH : 0<s.H) (hK : 0<s.chunk) :
    RoundedRowDescriptor.rounded (2*s.H) s.chunk=2*s.H+s.F := by
  rw [RoundedRowDescriptor.rounded_eq_ceiling _ _ (by omega) hK]
  have he := CompactGadgetReservationCapacity.front_exact s.axes s.guard s.chunk hK
  unfold Shape.H Shape.F CompactGadgetReservationCapacity.frontChunks CompactGadgetReservationCapacity.chunks at *
  rw [Nat.mul_comm s.chunk]
  exact he.symm


private def seed : List Op := [ButterflyAxisHeadersData.product ![2,1,13] (by decide)]++
  (ActivePrefixStageHeadersData.back++ActivePrefixStageHeadersData.front).map (fun op => .base (.existing op))
private def sum : List Op :=
  [ButterflyAxisHeadersData.product ![0,3,24] (by decide),ButterflyAxisHeadersData.cmd (.copy 13 16 (by decide)),
    ButterflyAxisHeadersData.cmd (.add 16 13 (by decide)),ButterflyAxisHeadersData.cmd (.add 16 13 (by decide)),
    ButterflyAxisHeadersData.cmd (.add 16 14 (by decide)),ButterflyAxisHeadersData.cmd (.add 16 15 (by decide)),
    ButterflyAxisHeadersData.cmd (.add 16 24 (by decide)),ButterflyAxisHeadersData.cmd (.erase 24)]
private def seeded (s : Shape) (rows ell p rho left count slots right source target : ℕ) (i : Fin 28) : Option ℕ :=
  match i.val with
  | 0 => some s.chunk | 1 => some s.axes | 2 => some s.guard | 3 => some s.active
  | 4 => some rows | 5 => some s.payload | 6 => some slots | 7 => some count | 8 => some left
  | 9 => some right | 10 => some rho | 11 => some source | 12 => some target
  | 13 => some s.H | 14 => some s.B | 15 => some s.F | 17 => some ell | 18 => some p | _ => none
private theorem seed_eval (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hH : 0<s.H) (hK : 0<s.chunk) :
    execute seed (raw s rows ell p rho left count slots right source target)=seeded s rows ell p rho left count slots right source target := by
  have hb := rounded_back s hH hK
  have hf := rounded_front s hH hK
  have hb' : RoundedRowDescriptor.rounded (s.axes*s.guard) s.chunk=s.H+s.B := by exact hb
  have hf' : RoundedRowDescriptor.rounded (s.axes*s.guard+s.axes*s.guard) s.chunk=2*s.H+s.F := by
    simpa only [Shape.H,CompactGadgetReservationCapacity.capacity,two_mul] using hf
  funext i
  fin_cases i <;> simp [seed,seeded,execute,eval,List.map,ActivePrefixStageHeadersData.back,
    ActivePrefixStageHeadersData.front,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,raw,Function.update,hb',hf',
    Shape.H,CompactGadgetReservationCapacity.capacity]
  all_goals omega
private theorem seed_cost (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hH : 0<s.H) (hK : 0<s.chunk) :
    scheduleCost seed (raw s rows ell p rho left count slots right source target)=
      4096*(3*s.H+s.B+s.F)+100*(14*s.H+2*s.B+2*s.F+7)+53*s.H+38 := by
  have hb := rounded_back s hH hK
  have hf := rounded_front s hH hK
  have hb' : RoundedRowDescriptor.rounded (s.axes*s.guard) s.chunk=s.H+s.B := by exact hb
  have hf' : RoundedRowDescriptor.rounded (s.axes*s.guard+s.axes*s.guard) s.chunk=2*s.H+s.F := by
    simpa only [Shape.H,CompactGadgetReservationCapacity.capacity,two_mul] using hf
  simp [seed,List.map,scheduleCost,cost,eval,ActivePrefixStageHeadersData.back,
    ActivePrefixStageHeadersData.front,CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,raw,Function.update,hb',hf',
    Shape.H,CompactGadgetReservationCapacity.capacity,two_mul]
  ring
private theorem sum_cost (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    scheduleCost sum (seeded s rows ell p rho left count slots right source target)=
      100*(15*s.H+3*s.B+2*s.F+2*(s.active*s.chunk)+7)+53*(s.active*s.chunk)+36 := by
  simp [sum,scheduleCost,cost,eval,CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,seeded,Function.update]
  ring
private theorem cost_append0 (xs ys : List Op) (st : ActiveRepairRankHeadersCommands.State) :
    scheduleCost (xs++ys) st=scheduleCost xs st+scheduleCost ys (execute xs st) := by
  induction xs generalizing st with
  | nil => simp [scheduleCost,execute]
  | cons x xs ih => simp only [List.cons_append,scheduleCost,execute,ih]; omega

theorem geometry_cost_eq (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hH : 0<s.H) (hK : 0<s.chunk) :
    scheduleCost geometry (raw s rows ell p rho left count slots right source target)=
      4096*(3*s.H+s.B+s.F)+100*(29*s.H+5*s.B+4*s.F+2*(s.active*s.chunk)+14)+
        53*(s.H+s.active*s.chunk)+74 := by
  rw [show geometry=seed++sum from rfl,cost_append0,seed_eval _ _ _ _ _ _ _ _ _ _ _ hH hK,
    seed_cost _ _ _ _ _ _ _ _ _ _ _ hH hK,sum_cost]
  ring

theorem geometry_cost (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hH : 0<s.H) (hK : 0<s.chunk) :
    scheduleCost geometry (raw s rows ell p rho left count slots right source target)≤
      50000*scalar s rows ell p rho left count slots right source target := by
  have hh : s.H≤s.bits := by unfold Shape.bits; omega
  have ha : s.active*s.chunk≤s.bits := by unfold Shape.bits; omega
  have hb : s.B≤s.bits := by unfold Shape.bits; omega
  have hf : s.F≤s.bits := by unfold Shape.bits; omega
  rw [geometry_cost_eq _ _ _ _ _ _ _ _ _ _ _ hH hK]
  unfold scalar
  omega

theorem reorderA_cost (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    scheduleCost reorderA (state 0 s rows ell p rho left count slots right source target)≤
      50000*scalar s rows ell p rho left count slots right source target := by
  simp [reorderA,move,scheduleCost,cost,eval,CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,state,Function.update]
  unfold scalar
  omega

theorem reorderB_cost (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    scheduleCost reorderB (state 1 s rows ell p rho left count slots right source target)≤
      50000*scalar s rows ell p rho left count slots right source target := by
  simp [reorderB,move,scheduleCost,cost,eval,CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,state,Function.update]
  unfold scalar
  omega

theorem reorderC_cost (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    scheduleCost reorderC (state 2 s rows ell p rho left count slots right source target)≤
      50000*scalar s rows ell p rho left count slots right source target := by
  simp [reorderC,move,List.map,scheduleCost,cost,eval,CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,state,Function.update]
  have hH : s.H≤s.bits := by unfold Shape.bits; omega
  have hB : s.B≤s.bits := by unfold Shape.bits; omega
  have hF : s.F≤s.bits := by unfold Shape.bits; omega
  unfold scalar
  omega

private theorem cost_append (xs ys : List Op) (st : ActiveRepairRankHeadersCommands.State) :
    scheduleCost (xs++ys) st=scheduleCost xs st+scheduleCost ys (execute xs st) := by
  induction xs generalizing st with
  | nil => simp [scheduleCost,execute]
  | cons x xs ih => simp only [List.cons_append,scheduleCost,execute,ih]; omega
private theorem execute_append (xs ys : List Op) (st : ActiveRepairRankHeadersCommands.State) :
    execute (xs++ys) st=execute ys (execute xs st) := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => exact ih (eval x st)

theorem cost_linear (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hH : 0<s.H) (hK : 0<s.chunk) :
    scheduleCost schedule (raw s rows ell p rho left count slots right source target)≤
      200000*scalar s rows ell p rho left count slots right source target := by
  rw [schedule,cost_append,cost_append,cost_append,execute_append,execute_append,execute_append,
    geometry_eval _ _ _ _ _ _ _ _ _ _ _ hH hK,reorderA_eval,reorderB_eval]
  have h0 := geometry_cost s rows ell p rho left count slots right source target hH hK
  have h1 := reorderA_cost s rows ell p rho left count slots right source target
  have h2 := reorderB_cost s rows ell p rho left count slots right source target
  have h3 := reorderC_cost s rows ell p rho left count slots right source target
  omega

end
end IntegerMultBounds.Machine.CompactSpectatorLeafSetupBudget
