import IntegerMultBounds.Machine.CompactComplexNonleafRoleSplit
import IntegerMultBounds.Machine.CompactComplexNonleafRoleMerge
import IntegerMultBounds.Machine.CompactComplexControllerDenominatorEntry
import IntegerMultBounds.Machine.CompactComplexParentLiveStack

/-! Paid original-header child setup retains polynomial metadata and the true
inherited live denominator. No target is installed as live before the child. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleChildBank
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactComplexRecursiveGeometry
open CompactChildHeadersArithmetic
open ActiveRepairRankHeadersCommands (State put)
open CompactComplexChildHeadersData (parent child schedule)
open CompactComplexNativeCodec (raw)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)

variable {sh : Shape} {left k : ℕ}

/-- The existing child schedule also works with retained ell/p, which are
real live metadata rather than the blank initial-stage placeholders. -/
theorem raw_eval (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell p : ℕ) :
    execute (schedule coordinate) (raw (parent rho visit hactive pair) rows ell p)=
      raw (child rho visit hactive pair coordinate) rows ell p := by
  have hp : 0<arity := by decide
  have hd : arity^(k+1)/arity=arity^k := by rw [pow_succ,Nat.mul_div_cancel _ hp]
  have hpow : arity^(k+1)=arity*arity^k := by rw [pow_succ,Nat.mul_comm]
  funext i
  fin_cases i
  all_goals simp [schedule,execute,eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    raw,CompactNativeRoleConjugatedLifecycle.rawState,CompactSpectatorLeafSetup.raw,
    parent,child,CompactBinaryBasisSchedule.stage,node,Function.update,hd]
  all_goals rw [hpow]
  rw [Nat.mul_comm (arity^k) arity,Nat.add_comm (arity*arity^k)]

theorem raw_valid (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell p : ℕ) :
    validSchedule (schedule coordinate) (raw (parent rho visit hactive pair) rows ell p) := by
  have hp : 0<arity := by decide
  have hfp : 0<arity^(k+1) := pow_pos hp _
  have hd : arity^(k+1)/arity=arity^k := by rw [pow_succ,Nat.mul_div_cancel _ hp]
  have hfit := (Visit.child visit coordinate).fits
  simp [schedule,validSchedule,valid,eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,raw,CompactNativeRoleConjugatedLifecycle.rawState,
    CompactSpectatorLeafSetup.raw,parent,CompactBinaryBasisSchedule.stage,node,Function.update,hd,hp,hfp]
  rw [←pow_succ]
  simpa only [Nat.add_comm] using hfit

theorem raw_runs (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell p : ℕ) :
    HoareTime (compile (a:=2) (schedule coordinate)).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (raw (parent rho visit hactive pair) rows ell p))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (raw (child rho visit hactive pair coordinate) rows ell p))
      (scheduleCost (schedule coordinate) (raw (parent rho visit hactive pair) rows ell p)) := by
  have h := schedule_runs (a:=2) _ _ (raw_valid rho visit hactive pair coordinate rows ell p)
  rwa [raw_eval] at h

variable {s c siteCount : ℕ}
abbrev tapes (s c : ℕ) := CompactComplexNonleafRoleSplit.tapes (10+s) c

def numeric (i : Fin 43) : Fin (tapes s c) :=
  Fin.castAdd 7 (CompactComplexNonleafRoleEntry.numeric (s:=10+s) (c:=c) i)
def storage (i : Fin (10+s)) : Fin (tapes s c) :=
  Fin.castAdd 7 (Fin.castAdd 2 (CompactComplexSpectatorTargetBank.oldSlot (s:=10+s) (c:=c) i))
def control (i : Fin 43) : Fin (tapes s c) := ⟨i.val,by
  have hi := i.isLt
  unfold tapes CompactComplexNonleafRoleSplit.tapes CompactComplexNonleafRoleEntry.tapes
    CompactComplexNativeCodecFrame.permanentTapes CompactComplexNativeRoleBridge.publicTapes
    CompactComplexControllerNativeFrame.tapes
  omega⟩
def current : Fin (tapes s c) := storage ⟨7,by omega⟩
def target : Fin (tapes s c) := storage ⟨8,by omega⟩
def targetStack : Fin (tapes s c) := storage ⟨9,by omega⟩

private theorem storage_injective : Function.Injective (storage (s:=s) (c:=c)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem target_ne_stack : target (s:=s) (c:=c)≠targetStack := by
  intro h
  have hh := storage_injective h
  have hv := congrArg Fin.val hh
  norm_num [target,targetStack] at hv

private theorem current_ne_target : current (s:=s) (c:=c)≠target := by
  intro h
  have hv := congrArg Fin.val (storage_injective h)
  norm_num [current,target] at hv

private theorem current_ne_stack : current (s:=s) (c:=c)≠targetStack := by
  intro h
  have hv := congrArg Fin.val (storage_injective h)
  norm_num [current,targetStack] at hv

/-- Save the actual incoming parent target once, with no assertion that it
already denotes the new child's return exponent. -/
def targetSaved (v : Tapes (tapes s c) 2) (parentTarget : ℕ) :=
  setTape (setTape v targetStack
    (BinaryDescriptorStack.frame (v.tape targetStack) (v.head targetStack) (bits parentTarget))
    (v.head targetStack+1+(bits parentTarget).length)) target (fun _ => blank) 0

def targetSaveProgram (s c : ℕ) :=
  seq (BinaryDescriptorStackAt.pushProgram (a:=2) (target (s:=s) (c:=c)) targetStack target_ne_stack)
    (BinaryDescriptorCleanupList.oneProgram (a:=2) target)

theorem target_save_runs (v : Tapes (tapes s c) 2) (parentTarget : ℕ)
    (ht : v.tape target=BinaryDescriptorStack.descriptor (bits parentTarget)) (hh : v.head target=1) :
    HoareTime (targetSaveProgram s c) (fun w => w=v)
      (fun w => w=targetSaved v parentTarget) (4*(bits parentTarget).length+12) := by
  have h0 := BinaryDescriptorStackAt.push_hoare (target (s:=s) (c:=c)) targetStack target_ne_stack
    v (bits parentTarget) ht hh
  let saved := setTape v targetStack
    (BinaryDescriptorStack.frame (v.tape targetStack) (v.head targetStack) (bits parentTarget))
    (v.head targetStack+1+(bits parentTarget).length)
  have h1 := BinaryDescriptorCleanupList.one_hoare (target (s:=s) (c:=c)) saved (bits parentTarget)
    (by simpa [saved,setTape,Function.update_of_ne target_ne_stack] using ht)
    (by simpa [saved,setTape,Function.update_of_ne target_ne_stack] using hh)
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem target_saved_current (v : Tapes (tapes s c) 2) (parentTarget : ℕ) :
    (targetSaved v parentTarget).head current=v.head current ∧
      (targetSaved v parentTarget).tape current=v.tape current := by
  simp only [targetSaved,setTape,Function.update_of_ne current_ne_target,
    Function.update_of_ne current_ne_stack,and_self]

private theorem storage_outside (j : Fin (10+s)) (i : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    storage j≠CompactComplexNonleafRoleSplit.slot (s:=10+s) (c:=c) i := by
  intro h
  have hv := congrArg Fin.val h
  dsimp only [CompactComplexNonleafRoleSplit.slot] at hv
  simp only [storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  have hi := i.isLt
  have hj := j.isLt
  unfold CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at hv
  unfold CompactNativeRoleInstall.rawCount CompactNativeRoleDestructive.localCount at hi
  split_ifs at hv <;> omega

private theorem active_setTape (v : Tapes (tapes s c) 2) (j : Fin (10+s)) (f : ℤ → Fin 6) (h : ℤ) :
    Placement.active (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c))
      (setTape v (storage j) f h)=Placement.active CompactComplexNonleafRoleSplit.placement v := by
  simp only [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [setTape,Function.update_of_ne (Ne.symm (storage_outside j i))]

theorem target_saved_active (v : Tapes (tapes s c) 2) (parentTarget : ℕ) :
    Placement.active (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c)) (targetSaved v parentTarget)=
      Placement.active CompactComplexNonleafRoleSplit.placement v := by
  unfold targetSaved target targetStack
  rw [active_setTape,active_setTape]

def headerFocus (i : Fin 3) : Fin (tapes s c) := numeric (![7,8,9] i)
private theorem header_distinct (stack : Fin s) :
    ∀ i : Fin 3,headerFocus (s:=s) (c:=c) i≠storage (Fin.natAdd 10 stack) := by
  intro i h
  have hv := congrArg Fin.val h
  simp only [headerFocus,numeric,CompactComplexNonleafRoleEntry.numeric,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot,
    storage,CompactComplexSpectatorTargetBank.oldSlot,CompactComplexControllerNativeFrame.storageSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  have hi := (![7,8,9] i : Fin 43).isLt
  omega

def headersSaved (v : Tapes (tapes s c) 2) (stack : Fin s) (data : Fin 3 → List Bool) :=
  setTape v (storage (Fin.natAdd 10 stack))
    (CompactChildHeadersStack.frames (v.tape (storage (Fin.natAdd 10 stack)))
      (v.head (storage (Fin.natAdd 10 stack))) data)
    (CompactChildHeadersStack.top (v.head (storage (Fin.natAdd 10 stack))) data)
def headersSaveProgram (stack : Fin s) :=
  CompactChildHeadersStack.saveProgram (a:=2) (headerFocus (s:=s) (c:=c))
    (storage (Fin.natAdd 10 stack)) (header_distinct stack)

theorem headers_save_runs (v : Tapes (tapes s c) 2) (stack : Fin s) (data : Fin 3 → List Bool)
    (ht : ∀ i,v.tape (headerFocus i)=BinaryDescriptorStack.descriptor (data i))
    (hh : ∀ i,v.head (headerFocus i)=1) :
    HoareTime (headersSaveProgram (c:=c) stack) (fun w => w=v)
      (fun w => w=headersSaved v stack data) (CompactChildHeadersStack.cost data) :=
  CompactChildHeadersStack.save headerFocus _ (header_distinct stack) v data ht hh

def pcSaved (v : Tapes (tapes s c) 2) (stack : Fin s) (site : Fin siteCount) (coordinate : Fin arity) :=
  FiniteReturnStackAt.pushed (storage (Fin.natAdd 10 stack))
    (CompactComplexCallReturn.codeFor site coordinate) v
def pcSaveProgram (stack : Fin s) (site : Fin siteCount) (coordinate : Fin arity) :=
  FiniteReturnStackAt.pushProgram (a:=2) (storage (s:=s) (c:=c) (Fin.natAdd 10 stack))
    (CompactComplexCallReturn.codeFor site coordinate)

theorem pc_save_runs (v : Tapes (tapes s c) 2) (stack : Fin s) (site : Fin siteCount) (coordinate : Fin arity) :
    HoareTime (pcSaveProgram (c:=c) stack site coordinate) (fun w => w=v)
      (fun w => w=pcSaved v stack site coordinate) (CompactComplexCallReturn.addressWidth siteCount arity) :=
  FiniteReturnStackAt.push_hoare (storage (Fin.natAdd 10 stack))
    (CompactComplexCallReturn.codeFor site coordinate) v

theorem headers_saved_active (v : Tapes (tapes s c) 2) (stack : Fin s) (data : Fin 3 → List Bool) :
    Placement.active (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c)) (headersSaved v stack data)=
      Placement.active CompactComplexNonleafRoleSplit.placement v := by
  unfold headersSaved
  rw [active_setTape]

theorem pc_saved_active (v : Tapes (tapes s c) 2) (stack : Fin s) (site : Fin siteCount) (coordinate : Fin arity) :
    Placement.active (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c)) (pcSaved v stack site coordinate)=
      Placement.active CompactComplexNonleafRoleSplit.placement v := by
  unfold pcSaved FiniteReturnStackAt.pushed
  rw [active_setTape]

def exponentFocus (i : Fin 3) : Fin (tapes s c) := control (![1,28,29] i)
private theorem exponentFocus_injective : Function.Injective (exponentFocus (s:=s) (c:=c)) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [exponentFocus,control] at hv
  fin_cases i <;> fin_cases j <;> simp_all

private theorem exponent_size : 3+(tapes s c-3)=tapes s c := by
  unfold tapes CompactComplexNonleafRoleSplit.tapes CompactComplexNonleafRoleEntry.tapes
    CompactComplexNativeCodecFrame.permanentTapes CompactComplexNativeRoleBridge.publicTapes
    CompactComplexControllerNativeFrame.tapes
  omega

def exponentPlacement : Fin (3+(tapes s c-3)) ≃ Fin (tapes s c) :=
  InjectivePlacement.placement exponentFocus exponentFocus_injective exponent_size

def exponentProgram (s c : ℕ) := Placement.placed (CompactComplexExponentStep.program (a:=2))
  (exponentPlacement (s:=s) (c:=c))
def descended (v : Tapes (tapes s c) 2) (e : ℕ) :=
  setTape v (control 1) (BinaryDescriptorStack.descriptor (bits (e-1))) 1

theorem exponent_runs (v : Tapes (tapes s c) 2) (e : ℕ) (he : 0<e)
    (hi : Placement.active exponentPlacement v=CompactComplexExponentStep.bank e) :
    HoareTime (exponentProgram s c) (fun w => w=v) (fun w => w=descended v e)
      (20*(e+1)+100) := by
  have h := CompactComplexExponentStep.runs_at exponentPlacement v e he hi
  simpa only [exponentProgram,descended,exponentPlacement,InjectivePlacement.active_slot,exponentFocus,
    Matrix.cons_val_zero] using h

private theorem control_outside (j : Fin 43) (i : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    control j≠CompactComplexNonleafRoleSplit.slot (s:=10+s) (c:=c) i := by
  intro h
  have hv := congrArg Fin.val h
  dsimp only [control,CompactComplexNonleafRoleSplit.slot] at hv
  have hj := j.isLt
  have hi := i.isLt
  unfold CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at hv
  unfold CompactNativeRoleInstall.rawCount CompactNativeRoleDestructive.localCount at hi
  split_ifs at hv <;> omega

theorem descended_active (v : Tapes (tapes s c) 2) (e : ℕ) :
    Placement.active (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c)) (descended v e)=
      Placement.active CompactComplexNonleafRoleSplit.placement v := by
  simp only [descended,CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [setTape,Function.update_of_ne (Ne.symm (control_outside 1 i))]

def numericProgram (coordinate : Fin arity) := Placement.placed
  (extend (compile (a:=2) (schedule coordinate)).2 (CompactNativeRoleInstall.rawCount c))
  (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c))

theorem numeric_runs (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell p : ℕ) (payload : Tapes (1+c) 2)
    (v : Tapes (tapes s c) 2)
    (hi : Placement.active CompactComplexNonleafRoleSplit.placement v=
      CompactNativeRoleOriginal.bank (raw (parent rho visit hactive pair) rows ell p) payload) :
    HoareTime (numericProgram (s:=s) (c:=c) coordinate) (fun w => w=v)
      (fun w => w=Placement.replace CompactComplexNonleafRoleSplit.placement v
        (CompactNativeRoleOriginal.bank (raw (child rho visit hactive pair coordinate) rows ell p) payload))
      (scheduleCost (schedule coordinate) (raw (parent rho visit hactive pair) rows ell p)) := by
  have h := Placement.hoare_at
    (hoare_extend_eq (raw_runs rho visit hactive pair coordinate rows ell p) (CompactNativeRoleInstall.blankRaw payload))
    CompactComplexNonleafRoleSplit.placement v hi
  exact h.consequence (fun _ h => h) (by rintro z ⟨w,rfl,rfl⟩; rfl) le_rfl

private theorem storage_control (j : Fin (10+s)) (i : Fin 43) :
    storage (s:=s) (c:=c) j≠control i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [storage,CompactComplexSpectatorTargetBank.oldSlot,CompactComplexControllerNativeFrame.storageSlot,
    control,Fin.val_castAdd,Fin.val_natAdd] at hv
  have hi := i.isLt
  omega

private theorem exponent_setTape (v : Tapes (tapes s c) 2) (j : Fin (10+s)) (f : ℤ → Fin 6) (h : ℤ) :
    Placement.active exponentPlacement (setTape v (storage j) f h)=Placement.active exponentPlacement v := by
  simp only [exponentPlacement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [exponentFocus,setTape,Function.update_of_ne (Ne.symm (storage_control j _))]

theorem target_saved_exponent (v : Tapes (tapes s c) 2) (parentTarget : ℕ) :
    Placement.active exponentPlacement (targetSaved v parentTarget)=Placement.active exponentPlacement v := by
  unfold targetSaved target targetStack
  rw [exponent_setTape,exponent_setTape]

theorem headers_saved_exponent (v : Tapes (tapes s c) 2) (stack : Fin s) (data : Fin 3 → List Bool) :
    Placement.active exponentPlacement (headersSaved v stack data)=Placement.active exponentPlacement v := by
  unfold headersSaved
  rw [exponent_setTape]

theorem pc_saved_exponent (v : Tapes (tapes s c) 2) (stack : Fin s) (site : Fin siteCount) (coordinate : Fin arity) :
    Placement.active exponentPlacement (pcSaved v stack site coordinate)=Placement.active exponentPlacement v := by
  unfold pcSaved FiniteReturnStackAt.pushed
  rw [exponent_setTape]

private theorem header_slot (i : Fin 43) :
    CompactComplexNonleafRoleSplit.slot (s:=10+s) (c:=c) (Fin.castAdd _ i)=numeric i := by
  apply Fin.ext
  simp [CompactComplexNonleafRoleSplit.slot,numeric,CompactComplexNonleafRoleEntry.numeric,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot,i.isLt]
  omega

private theorem numeric_bank (v : Tapes (tapes s c) 2) (st : State) (payload : Tapes (1+c) 2)
    (hi : Placement.active CompactComplexNonleafRoleSplit.placement v=CompactNativeRoleOriginal.bank st payload)
    (i : Fin 43) :
    v.head (numeric i)=(ActiveRepairRankHeadersCommands.bank (a:=2) st).head i ∧
      v.tape (numeric i)=(ActiveRepairRankHeadersCommands.bank (a:=2) st).tape i := by
  have hh := congrArg (fun b : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => b.head (Fin.castAdd _ i)) hi
  have ht := congrArg (fun b : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => b.tape (Fin.castAdd _ i)) hi
  constructor
  · simpa [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_bank,header_slot,
      CompactNativeRoleOriginal.bank,Tapes.append] using hh
  · simpa [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_bank,header_slot,
      CompactNativeRoleOriginal.bank,Tapes.append] using ht

private theorem parent_header_ready (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell p : ℕ) (payload : Tapes (1+c) 2) (v : Tapes (tapes s c) 2)
    (hi : Placement.active CompactComplexNonleafRoleSplit.placement v=
      CompactNativeRoleOriginal.bank (raw (parent rho visit hactive pair) rows ell p) payload) :
    (∀ i,v.tape (headerFocus i)=BinaryDescriptorStack.descriptor
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair) i)) ∧
    (∀ i,v.head (headerFocus i)=1) := by
  constructor
  · intro i
    have h := (numeric_bank v _ payload hi (![7,8,9] i)).2
    fin_cases i
    all_goals simpa [headerFocus,raw,CompactNativeRoleConjugatedLifecycle.rawState,CompactSpectatorLeafSetup.raw,
      CompactComplexControllerChildPrefix.data,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
      ActiveRepairRankHeadersCommands.caller,Tapes.append,Fin.addCases,BinaryDescriptorStackRoundtrip.descriptor_encoded] using h
  · intro i
    have h := (numeric_bank v _ payload hi (![7,8,9] i)).1
    fin_cases i
    all_goals simpa [headerFocus,raw,CompactNativeRoleConjugatedLifecycle.rawState,CompactSpectatorLeafSetup.raw,
      ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,ActiveRepairRankHeadersCommands.caller,Tapes.append,Fin.addCases] using h

def coreProgram (headerStack pcStack : Fin s) (site : Fin siteCount) (coordinate : Fin arity) :=
  seq (seq (seq (headersSaveProgram (c:=c) headerStack) (pcSaveProgram (c:=c) pcStack site coordinate))
    (exponentProgram s c)) (numericProgram (s:=s) (c:=c) coordinate)

def coreOutput (v : Tapes (tapes s c) 2) (e : ℕ) (headerStack pcStack : Fin s)
    (site : Fin siteCount) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell p : ℕ) (payload : Tapes (1+c) 2) :=
  Placement.replace CompactComplexNonleafRoleSplit.placement
    (descended (pcSaved (headersSaved v headerStack
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair))) pcStack site coordinate) e)
    (CompactNativeRoleOriginal.bank (raw (child rho visit hactive pair coordinate) rows ell p) payload)

def coreCost (siteCount e : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell p : ℕ) :=
  CompactChildHeadersStack.cost (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair))+
    CompactComplexCallReturn.addressWidth siteCount arity+20*(e+1)+100+
    scheduleCost (schedule coordinate) (raw (parent rho visit hactive pair) rows ell p)+3

/-- Actual descriptor frames, literal saved PC bits, runtime exponent and
child raw metadata are composed on the same permanent role bank. -/
theorem core_runs (v : Tapes (tapes s c) 2) (e : ℕ) (he : 0<e)
    (headerStack pcStack : Fin s) (site : Fin siteCount)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell p : ℕ) (payload : Tapes (1+c) 2)
    (hi : Placement.active CompactComplexNonleafRoleSplit.placement v=
      CompactNativeRoleOriginal.bank (raw (parent rho visit hactive pair) rows ell p) payload)
    (hx : Placement.active exponentPlacement v=CompactComplexExponentStep.bank e) :
    HoareTime (coreProgram (c:=c) headerStack pcStack site coordinate) (fun w => w=v)
      (fun w => w=coreOutput v e headerStack pcStack site rho visit hactive pair coordinate rows ell p payload)
      (coreCost siteCount e rho visit hactive pair coordinate rows ell p) := by
  let data := CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)
  let hbank := headersSaved v headerStack data
  let pbank := pcSaved hbank pcStack site coordinate
  let dbank := descended pbank e
  have hready := parent_header_ready rho visit hactive pair rows ell p payload v hi
  have h0 := headers_save_runs v headerStack data hready.1 hready.2
  have h1 := pc_save_runs hbank pcStack site coordinate
  have h2 := exponent_runs pbank e he (by
    dsimp only [pbank,hbank]
    rw [pc_saved_exponent,headers_saved_exponent]
    exact hx)
  have h3 := numeric_runs rho visit hactive pair coordinate rows ell p payload dbank (by
    dsimp only [dbank,pbank,hbank]
    rw [descended_active,pc_saved_active,headers_saved_active]
    exact hi)
  exact (((h0.seq h1).seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h) (by
    unfold coreCost
    dsimp only [data]
    omega)

private def base (v : Tapes (tapes s c) 2) : Tapes (CompactComplexParentLiveStack.tapes s c) 2 :=
  ⟨fun i => v.head (Fin.castAdd 7 i),fun i => v.tape (Fin.castAdd 7 i)⟩
private def tail (v : Tapes (tapes s c) 2) : Tapes 7 2 :=
  ⟨fun i => v.head (Fin.natAdd (CompactComplexParentLiveStack.tapes s c) i),
    fun i => v.tape (Fin.natAdd (CompactComplexParentLiveStack.tapes s c) i)⟩
private theorem base_tail (v : Tapes (tapes s c) 2) : (base v).append (tail v)=v := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i => simp [base,tail]
  | right i => simp [base,tail]

def liveSaved (v : Tapes (tapes s c) 2) (stack : Fin s) (n : ℕ) :=
  setTape v (storage (Fin.natAdd 10 stack))
    (BinaryDescriptorStack.frame (v.tape (storage (Fin.natAdd 10 stack)))
      (v.head (storage (Fin.natAdd 10 stack))) (bits n))
    (v.head (storage (Fin.natAdd 10 stack))+1+(bits n).length)
def liveSaveProgram (stack : Fin s) := extend (CompactComplexParentLiveStack.saveProgram (c:=c) stack) 7

theorem live_save_runs (v : Tapes (tapes s c) 2) (stack : Fin s) (n : ℕ)
    (ht : v.tape current=BinaryDescriptorStack.descriptor (bits n)) (hh : v.head current=1) :
    HoareTime (liveSaveProgram (c:=c) stack) (fun w => w=v) (fun w => w=liveSaved v stack n)
      (2*(bits n).length+7) := by
  have h := hoare_extend_eq (CompactComplexParentLiveStack.save stack (base v) n ht hh) (tail v)
  apply h.consequence (fun _ h => h.trans (base_tail v).symm) _ le_rfl
  intro w hw
  rw [hw,CompactComplexParentLiveStack.saved,←SharedPlacementAlphabet.setTape_append_left]
  rw [base_tail]
  rfl

theorem live_saved_active (v : Tapes (tapes s c) 2) (stack : Fin s) (n : ℕ) :
    Placement.active (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c)) (liveSaved v stack n)=
      Placement.active CompactComplexNonleafRoleSplit.placement v := by
  unfold liveSaved
  rw [active_setTape]

theorem live_saved_exponent (v : Tapes (tapes s c) 2) (stack : Fin s) (n : ℕ) :
    Placement.active exponentPlacement (liveSaved v stack n)=Placement.active exponentPlacement v := by
  unfold liveSaved
  rw [exponent_setTape]

def program (headerStack pcStack liveStack : Fin s) (site : Fin siteCount) (coordinate : Fin arity) :=
  seq (seq (targetSaveProgram s c) (liveSaveProgram (c:=c) liveStack))
    (coreProgram (c:=c) headerStack pcStack site coordinate)

def output (v : Tapes (tapes s c) 2) (parentTarget n e : ℕ) (headerStack pcStack liveStack : Fin s)
    (site : Fin siteCount) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell p : ℕ) (payload : Tapes (1+c) 2) :=
  coreOutput (liveSaved (targetSaved v parentTarget) liveStack n) e headerStack pcStack
    site rho visit hactive pair coordinate rows ell p payload

def cost (siteCount parentTarget n e : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell p : ℕ) :=
  4*(bits parentTarget).length+12+(2*(bits n).length+7)+
    coreCost siteCount e rho visit hactive pair coordinate rows ell p+2

/-- Save the incoming parent target exactly once, physically save actual live7,
then save geometry/PC and enter the real child. Live7 remains inherited n. -/
theorem runs (v : Tapes (tapes s c) 2) (parentTarget n e : ℕ) (he : 0<e)
    (headerStack pcStack liveStack : Fin s) (site : Fin siteCount)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell p : ℕ) (payload : Tapes (1+c) 2)
    (hi : Placement.active CompactComplexNonleafRoleSplit.placement v=
      CompactNativeRoleOriginal.bank (raw (parent rho visit hactive pair) rows ell p) payload)
    (hx : Placement.active exponentPlacement v=CompactComplexExponentStep.bank e)
    (ht : v.tape target=BinaryDescriptorStack.descriptor (bits parentTarget)) (hh : v.head target=1)
    (hn : v.tape current=BinaryDescriptorStack.descriptor (bits n)) (hp : v.head current=1) :
    HoareTime (program (c:=c) headerStack pcStack liveStack site coordinate) (fun w => w=v)
      (fun w => w=output v parentTarget n e headerStack pcStack liveStack site rho visit hactive pair coordinate rows ell p payload)
      (cost siteCount parentTarget n e rho visit hactive pair coordinate rows ell p) := by
  have h0 := target_save_runs v parentTarget ht hh
  have hcurrent := target_saved_current v parentTarget
  have h1 := live_save_runs (targetSaved v parentTarget) liveStack n
    (hcurrent.2.trans hn) (hcurrent.1.trans hp)
  have h2 := core_runs (liveSaved (targetSaved v parentTarget) liveStack n) e he headerStack pcStack site
    rho visit hactive pair coordinate rows ell p payload (by
      rw [live_saved_active,target_saved_active]
      exact hi) (by
      rw [live_saved_exponent,target_saved_exponent]
      exact hx)
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

def splitInput (selected : Fin c) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell p : ℕ) (hd : c ∣ rows/c)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2) :=
  let stage := parent rho visit hactive pair
  CompactComplexNonleafRoleSplit.output selected sh rows ell p stage.rho stage.left stage.f stage.slots stage.right
    stage.source.val stage.target.val hd f v

/-- The genuine physical split endpoint supplies the entire child payload and
header invariant internally; the inherited current and incoming target are
literal descriptors on that endpoint. -/
theorem runs_from_split (selected : Fin c) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell p : ℕ) (hd : c ∣ rows/c)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (parentTarget n : ℕ) (headerStack pcStack liveStack : Fin s) (site : Fin siteCount)
    (hx : Placement.active exponentPlacement (splitInput selected rho visit hactive pair rows ell p hd f v)=
      CompactComplexExponentStep.bank (k+2))
    (ht : (splitInput selected rho visit hactive pair rows ell p hd f v).tape target=
      BinaryDescriptorStack.descriptor (bits parentTarget))
    (hh : (splitInput selected rho visit hactive pair rows ell p hd f v).head target=1)
    (hn : (splitInput selected rho visit hactive pair rows ell p hd f v).tape current=
      BinaryDescriptorStack.descriptor (bits n))
    (hp : (splitInput selected rho visit hactive pair rows ell p hd f v).head current=1) :
    HoareTime (program (c:=c) headerStack pcStack liveStack site coordinate)
      (fun w => w=splitInput selected rho visit hactive pair rows ell p hd f v)
      (fun w => w=output (splitInput selected rho visit hactive pair rows ell p hd f v) parentTarget n (k+2)
        headerStack pcStack liveStack site rho visit hactive pair coordinate (rows/c) ell p
        (CompactNativeRoleReservedBridge.rolePayload sh (rows/c) c ell hd f))
      (cost siteCount parentTarget n (k+2) rho visit hactive pair coordinate (rows/c) ell p) := by
  apply runs _ parentTarget n (k+2) (by omega) headerStack pcStack liveStack site
    rho visit hactive pair coordinate (rows/c) ell p _ _ hx ht hh hn hp
  exact CompactComplexNonleafRoleSplit.output_active selected sh rows ell p
    (parent rho visit hactive pair).rho (parent rho visit hactive pair).left (parent rho visit hactive pair).f
    (parent rho visit hactive pair).slots (parent rho visit hactive pair).right
    (parent rho visit hactive pair).source.val (parent rho visit hactive pair).target.val hd f v

private theorem replace_storage (v : Tapes (tapes s c) 2)
    (small : Tapes (43+CompactNativeRoleInstall.rawCount c) 2) (j : Fin (10+s)) :
    (Placement.replace CompactComplexNonleafRoleSplit.placement v small).head (storage j)=v.head (storage j) ∧
    (Placement.replace CompactComplexNonleafRoleSplit.placement v small).tape (storage j)=v.tape (storage j) := by
  obtain ⟨i,he⟩ := (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c)).surjective (storage j)
  rw [←he]
  induction i using Fin.addCases with
  | left i =>
    have hs : CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c) (Fin.castAdd _ i)=
        CompactComplexNonleafRoleSplit.slot i := by
      simp [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_slot]
    exact (storage_outside j i (he.symm.trans hs)).elim
  | right i =>
    simp only [Placement.replace,Placement.combine_head_extra,Placement.combine_tape_extra,Placement.extra]
    trivial

private theorem current_ne_future (j : Fin s) :
    current (s:=s) (c:=c)≠storage (Fin.natAdd 10 j) := by
  intro h
  have hv := congrArg Fin.val (storage_injective h)
  simp only [Fin.val_natAdd] at hv
  change 7=10+j.val at hv
  omega

/-- The child receives the physical parent denominator unchanged, regardless
of its future generated return target. -/
theorem output_current (v : Tapes (tapes s c) 2) (parentTarget n e : ℕ) (headerStack pcStack liveStack : Fin s)
    (site : Fin siteCount) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell p : ℕ) (payload : Tapes (1+c) 2) :
    (output v parentTarget n e headerStack pcStack liveStack site rho visit hactive pair coordinate rows ell p payload).head current=
      v.head current ∧
    (output v parentTarget n e headerStack pcStack liveStack site rho visit hactive pair coordinate rows ell p payload).tape current=
      v.tape current := by
  have h := replace_storage
    (descended (pcSaved (headersSaved (liveSaved (targetSaved v parentTarget) liveStack n) headerStack
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair))) pcStack site coordinate) e)
    (CompactNativeRoleOriginal.bank (raw (child rho visit hactive pair coordinate) rows ell p) payload)
    (⟨7,by omega⟩ : Fin (10+s))
  have hpc : storage (s:=s) (c:=c) (⟨7,by omega⟩ : Fin (10+s))≠storage (Fin.natAdd 10 pcStack) :=
    current_ne_future pcStack
  have hhead : storage (s:=s) (c:=c) (⟨7,by omega⟩ : Fin (10+s))≠storage (Fin.natAdd 10 headerStack) :=
    current_ne_future headerStack
  have hlive : storage (s:=s) (c:=c) (⟨7,by omega⟩ : Fin (10+s))≠storage (Fin.natAdd 10 liveStack) :=
    current_ne_future liveStack
  have htar : storage (s:=s) (c:=c) (⟨7,by omega⟩ : Fin (10+s))≠target := current_ne_target
  have hstack : storage (s:=s) (c:=c) (⟨7,by omega⟩ : Fin (10+s))≠targetStack := current_ne_stack
  constructor
  · apply h.1.trans
    simp only [descended,pcSaved,FiniteReturnStackAt.pushed,headersSaved,liveSaved,targetSaved,setTape]
    rw [Function.update_of_ne (storage_control (s:=s) (c:=c) ⟨7,by omega⟩ 1)]
    rw [Function.update_of_ne hpc,Function.update_of_ne hhead,Function.update_of_ne hlive,
      Function.update_of_ne htar,Function.update_of_ne hstack]
    rfl
  · apply h.2.trans
    simp only [descended,pcSaved,FiniteReturnStackAt.pushed,headersSaved,liveSaved,targetSaved,setTape]
    rw [Function.update_of_ne (storage_control (s:=s) (c:=c) ⟨7,by omega⟩ 1)]
    rw [Function.update_of_ne hpc,Function.update_of_ne hhead,Function.update_of_ne hlive,
      Function.update_of_ne htar,Function.update_of_ne hstack]
    rfl

theorem output_active (v : Tapes (tapes s c) 2) (parentTarget n e : ℕ) (headerStack pcStack liveStack : Fin s)
    (site : Fin siteCount) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell p : ℕ) (payload : Tapes (1+c) 2) :
    Placement.active CompactComplexNonleafRoleSplit.placement
      (output v parentTarget n e headerStack pcStack liveStack site rho visit hactive pair coordinate rows ell p payload)=
      CompactNativeRoleOriginal.bank (raw (child rho visit hactive pair coordinate) rows ell p) payload :=
  Placement.active_replace _ _ _

/-- With separate fixed geometry and PC stacks, the pushed true live word is
still the exact recoverable top frame at child entry. -/
theorem output_live_stack (v : Tapes (tapes s c) 2) (parentTarget n e : ℕ) (headerStack pcStack liveStack : Fin s)
    (hhead : liveStack≠headerStack) (hpc : liveStack≠pcStack)
    (site : Fin siteCount) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell p : ℕ) (payload : Tapes (1+c) 2) :
    (output v parentTarget n e headerStack pcStack liveStack site rho visit hactive pair coordinate rows ell p payload).head
        (storage (Fin.natAdd 10 liveStack))=v.head (storage (Fin.natAdd 10 liveStack))+1+(bits n).length ∧
    (output v parentTarget n e headerStack pcStack liveStack site rho visit hactive pair coordinate rows ell p payload).tape
        (storage (Fin.natAdd 10 liveStack))=
      BinaryDescriptorStack.frame (v.tape (storage (Fin.natAdd 10 liveStack)))
        (v.head (storage (Fin.natAdd 10 liveStack))) (bits n) := by
  have hpci : storage (s:=s) (c:=c) (Fin.natAdd 10 liveStack)≠storage (Fin.natAdd 10 pcStack) := by
    intro h
    apply hpc
    apply Fin.ext
    have hv := congrArg Fin.val (storage_injective h)
    simp only [Fin.val_natAdd] at hv
    omega
  have hheadi : storage (s:=s) (c:=c) (Fin.natAdd 10 liveStack)≠storage (Fin.natAdd 10 headerStack) := by
    intro h
    apply hhead
    apply Fin.ext
    have hv := congrArg Fin.val (storage_injective h)
    simp only [Fin.val_natAdd] at hv
    omega
  have htar : storage (s:=s) (c:=c) (Fin.natAdd 10 liveStack)≠target := by
    intro h
    have hv := congrArg Fin.val (storage_injective h)
    change 10+liveStack.val=8 at hv
    omega
  have hstack : storage (s:=s) (c:=c) (Fin.natAdd 10 liveStack)≠targetStack := by
    intro h
    have hv := congrArg Fin.val (storage_injective h)
    change 10+liveStack.val=9 at hv
    omega
  have h := replace_storage
    (descended (pcSaved (headersSaved (liveSaved (targetSaved v parentTarget) liveStack n) headerStack
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair))) pcStack site coordinate) e)
    (CompactNativeRoleOriginal.bank (raw (child rho visit hactive pair coordinate) rows ell p) payload)
    (Fin.natAdd 10 liveStack)
  constructor
  · apply h.1.trans
    simp only [descended,pcSaved,FiniteReturnStackAt.pushed,headersSaved,liveSaved,targetSaved,setTape]
    rw [Function.update_of_ne (storage_control (s:=s) (c:=c) (Fin.natAdd 10 liveStack) 1)]
    rw [Function.update_of_ne hpci,Function.update_of_ne hheadi,Function.update_self]
    simp only [Function.update_of_ne htar,Function.update_of_ne hstack]
  · apply h.2.trans
    simp only [descended,pcSaved,FiniteReturnStackAt.pushed,headersSaved,liveSaved,targetSaved,setTape]
    rw [Function.update_of_ne (storage_control (s:=s) (c:=c) (Fin.natAdd 10 liveStack) 1)]
    rw [Function.update_of_ne hpci,Function.update_of_ne hheadi,Function.update_self]
    simp only [Function.update_of_ne htar,Function.update_of_ne hstack]

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleChildBank
