import IntegerMultBounds.Machine.CompactNativeRoleHeaders
import IntegerMultBounds.Machine.ActivePrefixStageTripleWords

/-! Construct the genuine scalar coefficient count from original native shape,
row and polynomial-exponent descriptors. All intermediate geometry and powers
are physically erased; no count or denominator is supplied as an input. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarCountHeaders
noncomputable section
open CompactGadgetReservationShape (Shape)
open ButterflyAxisHeadersArithmetic
open ButterflyAxisHeadersData (cmd product)
open ActiveRepairRankHeadersCommands (State put bank)
open CompactSpectatorLeafSetup (raw state geometry)

def rest : List Op := [.power ![16,20] (by decide),.power ![17,21] (by decide),
  product ![20,21,22] (by decide),product ![22,4,27] (by decide)]++
  ([13,14,15,16,20,21,22] : List (Fin 28)).map (fun i => cmd (.erase i))
def schedule := geometry++rest
def finished (s : Shape) (rows ell p rho left count slots right source target : ℕ) : State :=
  put (raw s rows ell p rho left count slots right source target) 27 (rows*2^s.bits*2^ell)
def program := (compile (a:=2) schedule).2

theorem rest_eval (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    execute rest (state 0 s rows ell p rho left count slots right source target)=
      finished s rows ell p rho left count slots right source target := by
  funext i
  fin_cases i <;> simp [rest,execute,eval,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,
    finished,state,raw,put,Function.update]
  all_goals ring

theorem rest_valid (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (_hr : 0<rows) : validSchedule rest (state 0 s rows ell p rho left count slots right source target) := by
  have hP : 0<(2:ℕ)^s.bits := by positivity
  have hR : 0<(2:ℕ)^ell := by positivity
  simp [rest,validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.valid,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,put,state,Function.update]

theorem execute_eq (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk) :
    execute schedule (raw s rows ell p rho left count slots right source target)=
      finished s rows ell p rho left count slots right source target := by
  rw [schedule,CompactNativeRoleHeaders.execute_append,
    CompactSpectatorLeafSetup.geometry_eval _ _ _ _ _ _ _ _ _ _ _ (Nat.mul_pos hA hG) hK,rest_eval]

theorem runs (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hr : 0<rows) (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk) :
    HoareTime program (fun v => v=bank (raw s rows ell p rho left count slots right source target))
      (fun v => v=bank (finished s rows ell p rho left count slots right source target))
      (scheduleCost schedule (raw s rows ell p rho left count slots right source target)) := by
  have hv : validSchedule schedule (raw s rows ell p rho left count slots right source target) := by
    rw [schedule,CompactNativeRoleHeaders.validSchedule_append]
    refine ⟨CompactSpectatorLeafSetup.geometry_valid _ _ _ _ _ _ _ _ _ _ _ hG hA hK,?_⟩
    rw [CompactSpectatorLeafSetup.geometry_eval _ _ _ _ _ _ _ _ _ _ _ (Nat.mul_pos hA hG) hK]
    exact rest_valid _ _ _ _ _ _ _ _ _ _ _ hr
  have h := schedule_runs (a:=2) schedule _ hv
  rwa [execute_eq _ _ _ _ _ _ _ _ _ _ _ hG hA hK] at h

/-- The constructed number is exactly the cardinality expected by native
polynomial flattening, rather than a serialization length or a denominator. -/
theorem native_count {s : Shape} (inp : ActivePrefixStageFullData.Inputs s) (ell : ℕ) :
    inp.rows*2^s.bits*2^ell=ActivePrefixStageTripleWords.count inp*2^ell := by
  simp only [ActivePrefixStageTripleWords.count,ActiveRepairLayoutRecordsShape.addressShape,
    Shape.recordWidth,Nat.mul_one]
  rfl

theorem endpoint (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    let v := bank (a:=2) (finished s rows ell p rho left count slots right source target)
    let original := bank (a:=2) (raw s rows ell p rho left count slots right source target)
    v.head 27=1 ∧ v.tape 27=RadixZeroFill.encodedBinary
      (RecursiveChildQuotientsConstant.bits (rows*2^s.bits*2^ell)) ∧
    (∀ i:Fin 43,i.val≠27 → v.head i=original.head i ∧ v.tape i=original.tape i) := by
  dsimp only
  refine ⟨rfl,rfl,?_⟩
  intro i hi
  induction i using Fin.addCases (m:=28) (n:=15) with
  | left i =>
    simp only [bank,CleanSubbank.bank,Tapes.append,Fin.addCases_left]
    have hn : i≠27 := by intro he; subst i; exact hi rfl
    simp [finished,put,ActiveRepairRankHeadersCommands.caller,Function.update_of_ne hn]
  | right i => simp only [bank,CleanSubbank.bank,Tapes.append,Fin.addCases_right,and_self]

/-- Compute role rows in private26 without changing the retained parent row4. -/
def roleRest (c : ℕ) : List Op :=
  [.base (.constant 19 c),.base (.quotient ![4,19,26] (by decide)),
    .power ![16,20] (by decide),.power ![17,21] (by decide),
    product ![20,21,22] (by decide),product ![22,26,27] (by decide)]++
    ([13,14,15,16,19,20,21,22,26] : List (Fin 28)).map (fun i => cmd (.erase i))
def roleSchedule (c : ℕ) := geometry++roleRest c
def roleFinished (c : ℕ) (s : Shape) (rows ell p rho left count slots right source target : ℕ) : State :=
  put (raw s rows ell p rho left count slots right source target) 27 ((rows/c)*2^s.bits*2^ell)
def roleProgram (c : ℕ) := (compile (a:=2) (roleSchedule c)).2

theorem role_rest_eval (c : ℕ) (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    execute (roleRest c) (state 0 s rows ell p rho left count slots right source target)=
      roleFinished c s rows ell p rho left count slots right source target := by
  funext i
  fin_cases i <;> simp [roleRest,execute,eval,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,
    roleFinished,state,raw,put,Function.update]
  all_goals ring

theorem role_rest_valid (c : ℕ) (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hc : 0<c) : validSchedule (roleRest c) (state 0 s rows ell p rho left count slots right source target) := by
  simp [roleRest,validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.valid,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,put,state,Function.update,hc]

theorem role_execute_eq (c : ℕ) (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk) :
    execute (roleSchedule c) (raw s rows ell p rho left count slots right source target)=
      roleFinished c s rows ell p rho left count slots right source target := by
  rw [roleSchedule,CompactNativeRoleHeaders.execute_append,
    CompactSpectatorLeafSetup.geometry_eval _ _ _ _ _ _ _ _ _ _ _ (Nat.mul_pos hA hG) hK,role_rest_eval]

theorem role_runs (c : ℕ) (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hc : 0<c) (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk) :
    HoareTime (roleProgram c) (fun v => v=bank (raw s rows ell p rho left count slots right source target))
      (fun v => v=bank (roleFinished c s rows ell p rho left count slots right source target))
      (scheduleCost (roleSchedule c) (raw s rows ell p rho left count slots right source target)) := by
  have hv : validSchedule (roleSchedule c) (raw s rows ell p rho left count slots right source target) := by
    rw [roleSchedule,CompactNativeRoleHeaders.validSchedule_append]
    refine ⟨CompactSpectatorLeafSetup.geometry_valid _ _ _ _ _ _ _ _ _ _ _ hG hA hK,?_⟩
    rw [CompactSpectatorLeafSetup.geometry_eval _ _ _ _ _ _ _ _ _ _ _ (Nat.mul_pos hA hG) hK]
    exact role_rest_valid _ _ _ _ _ _ _ _ _ _ _ _ hc
  have h := schedule_runs (a:=2) (roleSchedule c) _ hv
  rwa [role_execute_eq _ _ _ _ _ _ _ _ _ _ _ _ hG hA hK] at h

theorem role_endpoint (c : ℕ) (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    let v := bank (a:=2) (roleFinished c s rows ell p rho left count slots right source target)
    let original := bank (a:=2) (raw s rows ell p rho left count slots right source target)
    v.head 27=1 ∧ v.tape 27=RadixZeroFill.encodedBinary
      (RecursiveChildQuotientsConstant.bits ((rows/c)*2^s.bits*2^ell)) ∧
    (∀ i:Fin 43,i.val≠27 → v.head i=original.head i ∧ v.tape i=original.tape i) := by
  dsimp only
  refine ⟨rfl,rfl,?_⟩
  intro i hi
  induction i using Fin.addCases (m:=28) (n:=15) with
  | left i =>
    simp only [bank,CleanSubbank.bank,Tapes.append,Fin.addCases_left]
    have hn : i≠27 := by intro he; subst i; exact hi rfl
    simp [roleFinished,put,ActiveRepairRankHeadersCommands.caller,Function.update_of_ne hn]
  | right i => simp only [bank,CleanSubbank.bank,Tapes.append,Fin.addCases_right,and_self]

end
end IntegerMultBounds.Machine.CompactComplexScalarCountHeaders
