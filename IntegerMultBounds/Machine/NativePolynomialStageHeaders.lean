import IntegerMultBounds.Machine.NativePolynomialStageShape
import IntegerMultBounds.Machine.CompactSpectatorLeafSetupBudget
import IntegerMultBounds.Machine.CompactNativeRoleHeaders

/-! The genuine native polynomial codec payload is computed from original
shape headers and retained ell/precision. Its original payload word is saved,
all arithmetic work is reclaimed, and the exact old caller can be restored.
No source coefficient is read, copied or changed by this numeric adapter. -/
namespace IntegerMultBounds.Machine.NativePolynomialStageHeaders
noncomputable section
open CompactGadgetReservationShape (Shape)
open ButterflyAxisHeadersArithmetic
open ButterflyAxisHeadersData (cmd product)
open ActiveRepairRankHeadersCommands (State put)
open CompactSpectatorLeafSetup (raw state geometry)
open NativePolynomialStageShape (shape payload width)
variable {a : ℕ}

def rest : List Op :=
  [.base (.constant 19 4),cmd (.copy 16 23 (by decide)),cmd (.add 23 16 (by decide)),
   cmd (.add 23 18 (by decide)),cmd (.add 23 19 (by decide)),.base (.constant 20 1),
   cmd (.add 23 20 (by decide)),cmd (.erase 19),.base (.constant 19 2),product ![19,23,24] (by decide),
   cmd (.erase 19),.power ![17,21] (by decide),product ![21,24,22] (by decide),
   .base (.constant 19 3),product ![19,22,25] (by decide),cmd (.copy 5 26 (by decide)),
   cmd (.erase 5),cmd (.copy 25 5 (by decide))]++
    ([13,14,15,16,19,20,21,22,23,24,25] : List (Fin 28)).map (fun i => cmd (.erase i))

def prepared (s : Shape) (rows ell p rho left count slots right source target : ℕ) : State :=
  put (raw (shape s ell p) rows ell p rho left count slots right source target) 26 s.payload

def restore : List Op := [cmd (.erase 5),cmd (.copy 26 5 (by decide)),cmd (.erase 26)]

theorem rest_eval (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    execute rest (state 0 s rows ell p rho left count slots right source target)=
      prepared s rows ell p rho left count slots right source target := by
  funext i
  fin_cases i
  all_goals simp [rest,execute,eval,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,put,state,prepared,raw,Function.update,
    shape,payload,width,ActivePrefixStageNativePolynomial.symbols,ButterflyGuard.width,ButterflyGuard.halfWidth]
  all_goals ring

theorem rest_valid (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    validSchedule rest (state 0 s rows ell p rho left count slots right source target) := by
  simp [rest,validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,put,state,Function.update]

theorem restore_eval (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    execute restore (prepared s rows ell p rho left count slots right source target)=
      raw s rows ell p rho left count slots right source target := by
  funext i
  fin_cases i <;> simp [restore,execute,eval,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,put,prepared,raw,Function.update,shape]

theorem restore_valid (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    validSchedule restore (prepared s rows ell p rho left count slots right source target) := by
  simp [restore,validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,put,prepared,raw,Function.update]

def program := (compile (a:=a) (geometry++rest)).2

def cost (s : Shape) (rows ell p rho left count slots right source target : ℕ) :=
  scheduleCost geometry (raw s rows ell p rho left count slots right source target)+
    scheduleCost rest (state 0 s rows ell p rho left count slots right source target)+1

theorem runs (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk) :
    HoareTime (program (a:=a))
      (fun z => z=ActiveRepairRankHeadersCommands.bank (raw s rows ell p rho left count slots right source target))
      (fun z => z=ActiveRepairRankHeadersCommands.bank (prepared s rows ell p rho left count slots right source target))
      (cost s rows ell p rho left count slots right source target) := by
  have hH : 0<s.H := by unfold Shape.H CompactGadgetReservationCapacity.capacity; positivity
  have hv : validSchedule (geometry++rest) (raw s rows ell p rho left count slots right source target) := by
    rw [CompactNativeRoleHeaders.validSchedule_append,
      CompactSpectatorLeafSetup.geometry_eval s rows ell p rho left count slots right source target hH hK]
    exact ⟨CompactSpectatorLeafSetup.geometry_valid s rows ell p rho left count slots right source target hG hA hK,
      rest_valid s rows ell p rho left count slots right source target⟩
  have h := schedule_runs (a:=a) (geometry++rest) _ hv
  rw [CompactNativeRoleHeaders.execute_append,
    CompactSpectatorLeafSetup.geometry_eval s rows ell p rho left count slots right source target hH hK,rest_eval] at h
  apply h.consequence (fun _ hz => hz) (fun _ hz => hz)
  unfold cost
  have he : scheduleCost (geometry++rest) (raw s rows ell p rho left count slots right source target)=
      scheduleCost geometry (raw s rows ell p rho left count slots right source target)+
      scheduleCost rest (state 0 s rows ell p rho left count slots right source target) := by
    have ha : ∀ (xs ys : List Op) (st : State), scheduleCost (xs++ys) st=
        scheduleCost xs st+scheduleCost ys (execute xs st) := by
      intro xs ys st
      induction xs generalizing st with
      | nil => simp [scheduleCost,execute]
      | cons x xs ih => simp only [List.cons_append,scheduleCost,execute,ih]; omega
    rw [ha,CompactSpectatorLeafSetup.geometry_eval s rows ell p rho left count slots right source target hH hK]
  omega

theorem restore_runs (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    HoareTime (compile (a:=a) restore).2
      (fun z => z=ActiveRepairRankHeadersCommands.bank (prepared s rows ell p rho left count slots right source target))
      (fun z => z=ActiveRepairRankHeadersCommands.bank (raw s rows ell p rho left count slots right source target))
      (scheduleCost restore (prepared s rows ell p rho left count slots right source target)) := by
  have h := schedule_runs (a:=a) restore _ (restore_valid s rows ell p rho left count slots right source target)
  rwa [restore_eval] at h

/-- The physically generated first thirteen words are literally the native
stage originals, with the derived codec payload in slot five. -/
theorem prepared_original {s : Shape} (v : ActivePrefixStageParameters.Stage s)
    (rows ell p : ℕ) (i : Fin 13) :
    prepared s rows ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val
      (Fin.castAdd 15 i)=some (ActivePrefixStageHeadersData.originalValues
        (NativePolynomialStageShape.stage v ell p) rows i) := by
  fin_cases i <;> simp [prepared,put,raw,Function.update,NativePolynomialStageShape.stage,
    ActivePrefixStageHeadersData.originalValues,shape]

theorem prepared_immutable (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    prepared s rows ell p rho left count slots right source target 17=some ell ∧
    prepared s rows ell p rho left count slots right source target 18=some p ∧
    prepared s rows ell p rho left count slots right source target 26=some s.payload := by
  simp [prepared,put,raw,Function.update]

theorem rest_cost_bound (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    scheduleCost rest (state 0 s rows ell p rho left count slots right source target)≤
      FixedBasePowerDescriptor.constant 2*2^ell+
        100000*(s.bits+p+2^ell+payload s ell p+s.payload+1) := by
  simp [rest,scheduleCost,ButterflyAxisHeadersArithmetic.cost,eval,CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,put,state,Function.update,RecursiveChildQuotientsConstant.cost]
  have h4 : (RecursiveChildQuotientsConstant.bits 4).length=3 := rfl
  have h1 : (RecursiveChildQuotientsConstant.bits 1).length=1 := rfl
  have h2 : (RecursiveChildQuotientsConstant.bits 2).length=2 := rfl
  have h3 : (RecursiveChildQuotientsConstant.bits 3).length=2 := rfl
  simp only [h4,h1,h2,h3]
  have hH : s.H≤s.bits := by unfold Shape.bits; omega
  have hB : s.B≤s.bits := by unfold Shape.bits; omega
  have hF : s.F≤s.bits := by unfold Shape.bits; omega
  have hR : 1≤2^ell := Nat.one_le_pow _ _ (by decide)
  unfold payload width ActivePrefixStageNativePolynomial.symbols ButterflyGuard.width ButterflyGuard.halfWidth
  nlinarith

theorem restore_cost_bound (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    scheduleCost restore (prepared s rows ell p rho left count slots right source target)≤
      400*(payload s ell p+s.payload+1) := by
  simp [restore,scheduleCost,ButterflyAxisHeadersArithmetic.cost,eval,CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,put,prepared,raw,Function.update,shape]
  omega

end
end IntegerMultBounds.Machine.NativePolynomialStageHeaders
