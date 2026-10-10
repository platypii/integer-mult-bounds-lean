import IntegerMultBounds.Machine.CompactComplexNonleafRoleChildBank
import IntegerMultBounds.Machine.CompactChildHeadersStack
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-! Physical parent geometry restoration on the same raw-role child bank.
The child row count, retained ell/p, live denominator, target and payloads stay
unchanged. Only three geometric words, their real stack and exponent are touched. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleParentBank
noncomputable section
open CompactComplexNonleafRoleChildBank (tapes numeric storage control headerFocus)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}

def stackSlot (stack : Fin s) : Fin (tapes s c) := storage (Fin.natAdd 10 stack)

private theorem header_injective : Function.Injective (headerFocus (s:=s) (c:=c)) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [headerFocus,numeric,CompactComplexNonleafRoleEntry.numeric,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  fin_cases i <;> fin_cases j <;> simp_all

private theorem header_stack (stack : Fin s) :
    ∀ i : Fin 3,headerFocus (s:=s) (c:=c) i≠stackSlot stack := by
  intro i h
  have hv := congrArg Fin.val h
  simp only [headerFocus,numeric,CompactComplexNonleafRoleEntry.numeric,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot,
    stackSlot,storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  have hi := (![7,8,9] i : Fin 43).isLt
  omega

private theorem header_ne (i j : Fin 3) (h : i≠j) :
    headerFocus (s:=s) (c:=c) i≠headerFocus j := fun he => h (header_injective he)

private theorem control_header (i : Fin 43) (j : Fin 3) :
    control (s:=s) (c:=c) i≠headerFocus j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [CompactComplexNonleafRoleChildBank.control,headerFocus,numeric,CompactComplexNonleafRoleEntry.numeric,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  have hi := i.isLt
  omega

private theorem control_stack (i : Fin 43) (stack : Fin s) :
    control (s:=s) (c:=c) i≠stackSlot stack := by
  intro h
  have hv := congrArg Fin.val h
  simp only [CompactComplexNonleafRoleChildBank.control,stackSlot,storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  have hi := i.isLt
  omega

def cleared (v : Tapes (tapes s c) 2) :=
  setTape (setTape (setTape v (headerFocus 0) (fun _ => blank) 0)
    (headerFocus 1) (fun _ => blank) 0) (headerFocus 2) (fun _ => blank) 0

def clearProgram (s c : ℕ) :=
  seq (seq (BinaryDescriptorCleanupList.oneProgram (a:=2) (headerFocus (s:=s) (c:=c) 0))
    (BinaryDescriptorCleanupList.oneProgram (a:=2) (headerFocus 1)))
    (BinaryDescriptorCleanupList.oneProgram (a:=2) (headerFocus 2))

theorem clear_runs (v : Tapes (tapes s c) 2) (words : Fin 3 → List Bool)
    (ht : ∀ i,v.tape (headerFocus i)=BinaryDescriptorStack.descriptor (words i))
    (hh : ∀ i,v.head (headerFocus i)=1) :
    HoareTime (clearProgram s c) (fun w => w=v) (fun w => w=cleared v)
      (2*((words 0).length+(words 1).length+(words 2).length)+14) := by
  have h01 := header_ne (s:=s) (c:=c) 1 0 (by decide)
  have h20 := header_ne (s:=s) (c:=c) 2 0 (by decide)
  have h21 := header_ne (s:=s) (c:=c) 2 1 (by decide)
  have h0 := BinaryDescriptorCleanupList.one_hoare (headerFocus (s:=s) (c:=c) 0) v (words 0) (ht 0) (hh 0)
  have h1 := BinaryDescriptorCleanupList.one_hoare (headerFocus (s:=s) (c:=c) 1)
    (setTape v (headerFocus 0) (fun _ => blank) 0) (words 1)
    (by simpa only [setTape,Function.update_of_ne h01] using ht 1)
    (by simpa only [setTape,Function.update_of_ne h01] using hh 1)
  have h2 := BinaryDescriptorCleanupList.one_hoare (headerFocus (s:=s) (c:=c) 2)
    (setTape (setTape v (headerFocus 0) (fun _ => blank) 0) (headerFocus 1) (fun _ => blank) 0) (words 2)
    (by simpa only [setTape,Function.update_of_ne h20,Function.update_of_ne h21] using ht 2)
    (by simpa only [setTape,Function.update_of_ne h20,Function.update_of_ne h21] using hh 2)
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

def restored (v : Tapes (tapes s c) 2) (stack : Fin s) (f : ℤ → Fin 6) (p : ℤ)
    (data : Fin 3 → List Bool) :=
  setTape (setTape (setTape (setTape (cleared v) (stackSlot stack) f p)
    (headerFocus 2) (BinaryDescriptorStack.descriptor (data 2)) 1)
    (headerFocus 1) (BinaryDescriptorStack.descriptor (data 1)) 1)
    (headerFocus 0) (BinaryDescriptorStack.descriptor (data 0)) 1

def restoreProgram (stack : Fin s) := seq (clearProgram s c)
  (CompactChildHeadersStack.restoreProgram (a:=2) (headerFocus (s:=s) (c:=c))
    (stackSlot stack) (header_stack stack))

theorem restore_runs (v : Tapes (tapes s c) 2) (stack : Fin s)
    (f : ℤ → Fin 6) (p : ℤ) (data words : Fin 3 → List Bool)
    (ht : v.tape (stackSlot stack)=CompactChildHeadersStack.frames f p data)
    (hp : v.head (stackSlot stack)=CompactChildHeadersStack.top p data)
    (hd : ∀ i,v.tape (headerFocus i)=BinaryDescriptorStack.descriptor (words i))
    (hh : ∀ i,v.head (headerFocus i)=1) (hb : ∀ z,p≤z → f z=blank) :
    HoareTime (restoreProgram (c:=c) stack) (fun w => w=v)
      (fun w => w=restored v stack f p data)
      (2*((words 0).length+(words 1).length+(words 2).length)+14+
        CompactChildHeadersStack.cost data+1) := by
  have h0 := clear_runs v words hd hh
  have h1 := CompactChildHeadersStack.restore headerFocus header_injective (stackSlot stack)
    (header_stack stack) (cleared v) f p data
    (by simpa only [cleared,setTape,Function.update_of_ne (header_stack stack 0).symm,
      Function.update_of_ne (header_stack stack 1).symm,Function.update_of_ne (header_stack stack 2).symm] using ht)
    (by simpa only [cleared,setTape,Function.update_of_ne (header_stack stack 0).symm,
      Function.update_of_ne (header_stack stack 1).symm,Function.update_of_ne (header_stack stack 2).symm] using hp)
    (by intro i; fin_cases i <;> simp [cleared,setTape,headerFocus,numeric,
      CompactComplexNonleafRoleEntry.numeric,CompactComplexNativeCodecFrame.headerSlot,
      CompactComplexControllerNativeFrame.nativeSlot])
    (by intro i; fin_cases i <;> simp [cleared,setTape,headerFocus,numeric,
      CompactComplexNonleafRoleEntry.numeric,CompactComplexNativeCodecFrame.headerSlot,
      CompactComplexControllerNativeFrame.nativeSlot]) hb
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by omega)

def ascended (v : Tapes (tapes s c) 2) (e : ℕ) :=
  setTape v (control 1) (BinaryDescriptorStack.descriptor (bits e)) 1

def program (stack : Fin s) := seq (restoreProgram (c:=c) stack)
  (CompactComplexExponentStep.ascendProgram (a:=2) (control (s:=s) (c:=c) 1))

def output (v : Tapes (tapes s c) 2) (stack : Fin s) (f : ℤ → Fin 6) (p : ℤ)
    (data : Fin 3 → List Bool) (e : ℕ) := ascended (restored v stack f p data) e

theorem restored_control (v : Tapes (tapes s c) 2) (stack : Fin s) (f : ℤ → Fin 6)
    (p : ℤ) (data : Fin 3 → List Bool) (i : Fin 43) :
    (restored v stack f p data).head (control i)=v.head (control i) ∧
      (restored v stack f p data).tape (control i)=v.tape (control i) := by
  simp only [restored,cleared,setTape,Function.update_of_ne (control_header i 0),
    Function.update_of_ne (control_header i 1),Function.update_of_ne (control_header i 2),
    Function.update_of_ne (control_stack i stack),and_self]

theorem runs (v : Tapes (tapes s c) 2) (stack : Fin s)
    (f : ℤ → Fin 6) (p : ℤ) (data words : Fin 3 → List Bool) (e : ℕ) (he : 0<e)
    (ht : v.tape (stackSlot stack)=CompactChildHeadersStack.frames f p data)
    (hp : v.head (stackSlot stack)=CompactChildHeadersStack.top p data)
    (hd : ∀ i,v.tape (headerFocus i)=BinaryDescriptorStack.descriptor (words i))
    (hh : ∀ i,v.head (headerFocus i)=1) (hb : ∀ z,p≤z → f z=blank)
    (hx : v.tape (control 1)=BinaryDescriptorStack.descriptor (bits (e-1))) (hhx : v.head (control 1)=1) :
    HoareTime (program (c:=c) stack) (fun w => w=v) (fun w => w=output v stack f p data e)
      (2*((words 0).length+(words 1).length+(words 2).length)+14+
        CompactChildHeadersStack.cost data+1+2*(e+1)+1) := by
  have h0 := restore_runs v stack f p data words ht hp hd hh hb
  have hcontrol := restored_control v stack f p data 1
  have h1 := CompactComplexExponentStep.ascend_parent (control (s:=s) (c:=c) 1)
    (restored v stack f p data) e he (hcontrol.2.trans hx) (hcontrol.1.trans hhx)
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- Every other complete tape and its actual head are preserved literally. -/
theorem output_frame (v : Tapes (tapes s c) 2) (stack : Fin s) (f : ℤ → Fin 6)
    (p : ℤ) (data : Fin 3 → List Bool) (e : ℕ) (i : Fin (tapes s c))
    (hx : i≠control 1) (hs : i≠stackSlot stack) (hh : ∀ j,i≠headerFocus j) :
    (output v stack f p data e).head i=v.head i ∧
      (output v stack f p data e).tape i=v.tape i := by
  simp only [output,ascended,restored,cleared,setTape,Function.update_of_ne hx,
    Function.update_of_ne hs,Function.update_of_ne (hh 0),Function.update_of_ne (hh 1),
    Function.update_of_ne (hh 2),and_self]

private theorem restored_eq (v : Tapes (tapes s c) 2) (stack : Fin s) (f : ℤ → Fin 6)
    (p : ℤ) (data : Fin 3 → List Bool) :
    restored v stack f p data=
      setTape (setTape (setTape (setTape v (stackSlot stack) f p)
        (headerFocus 2) (BinaryDescriptorStack.descriptor (data 2)) 1)
        (headerFocus 1) (BinaryDescriptorStack.descriptor (data 1)) 1)
        (headerFocus 0) (BinaryDescriptorStack.descriptor (data 0)) 1 := by
  unfold restored cleared
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [setTape,Function.update_apply]
  all_goals split_ifs <;> rfl

private theorem active_setTape_slot {l u t a : ℕ} (placement : Fin (l+u) ≃ Fin t)
    (v : Tapes t a) (i : Fin l) (f : ℤ → Fin (a+4)) (p : ℤ) :
    Placement.active placement (setTape v (placement (Fin.castAdd u i)) f p)=
      setTape (Placement.active placement v) i f p := by
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals simp only [Placement.active,setTape,Function.update_apply]
  all_goals
    by_cases hj : j=i
    · subst j
      simp
    · have hj' : j.val≠i.val := fun h => hj (Fin.ext h)
      simp [hj,placement.injective.eq_iff,Fin.ext_iff,hj']

private theorem active_setTape_outside {l u t a : ℕ} (placement : Fin (l+u) ≃ Fin t)
    (v : Tapes t a) (slot : Fin t) (f : ℤ → Fin (a+4)) (p : ℤ)
    (hs : ∀ i : Fin l,placement (Fin.castAdd u i)≠slot) :
    Placement.active placement (setTape v slot f p)=Placement.active placement v := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [setTape,Function.update_of_ne (hs i)]

private theorem numeric_slot (i : Fin 43) :
    CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c)
      (Fin.castAdd _ (Fin.castAdd (CompactNativeRoleInstall.rawCount c) i))=numeric i := by
  rw [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_slot]
  apply Fin.ext
  simp [CompactComplexNonleafRoleSplit.slot,numeric,CompactComplexNonleafRoleEntry.numeric,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot,i.isLt]
  omega

private theorem control_outside (j : Fin 43) (i : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c) (Fin.castAdd _ i)≠control j := by
  rw [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_slot]
  intro h
  have hv := congrArg Fin.val h
  dsimp only [CompactComplexNonleafRoleSplit.slot,CompactComplexNonleafRoleChildBank.control] at hv
  have hj := j.isLt
  have hi := i.isLt
  unfold CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at hv
  unfold CompactNativeRoleInstall.rawCount CompactNativeRoleDestructive.localCount at hi
  split_ifs at hv <;> omega

private theorem storage_outside (j : Fin (10+s)) (i : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c) (Fin.castAdd _ i)≠storage j := by
  rw [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_slot]
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

private theorem raw_bank_put (st : ActiveRepairRankHeadersCommands.State) (payload : Tapes (1+c) 2)
    (i : Fin 28) (n : ℕ) :
    setTape (CompactNativeRoleOriginal.bank st payload)
      (Fin.castAdd (CompactNativeRoleInstall.rawCount c) (Fin.castAdd 15 i))
      (BinaryDescriptorStack.descriptor (bits n)) 1=
      CompactNativeRoleOriginal.bank (ActiveRepairRankHeadersCommands.put st i n) payload := by
  unfold CompactNativeRoleOriginal.bank
  rw [SharedPlacementAlphabet.setTape_append_left,BinaryDescriptorStackRoundtrip.descriptor_encoded]
  unfold ActiveRepairRankHeadersCommands.bank CleanSubbank.bank
  rw [SharedPlacementAlphabet.setTape_append_left,←ActiveRepairRankHeadersCommands.put_caller]

open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactComplexChildHeadersData (parent child)
open CompactComplexNativeCodec (raw)
variable {sh : Shape} {left k : ℕ}

private theorem raw_reparent (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell p : ℕ) :
    ActiveRepairRankHeadersCommands.put
      (ActiveRepairRankHeadersCommands.put
        (ActiveRepairRankHeadersCommands.put (raw (child rho visit hactive pair coordinate) rows ell p)
          9 (parent rho visit hactive pair).right) 8 (parent rho visit hactive pair).left)
      7 (parent rho visit hactive pair).f = raw (parent rho visit hactive pair) rows ell p := by
  funext i
  fin_cases i <;> simp [raw,CompactNativeRoleConjugatedLifecycle.rawState,CompactSpectatorLeafSetup.raw,
    ActiveRepairRankHeadersCommands.put,parent,child,CompactBinaryBasisSchedule.stage,node]

/-- Parent geometry returns with the actual child row count and retained ell/p;
physical row restoration belongs to the separate parent-only continuation. -/
theorem output_active (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell precision : ℕ) (payload : Tapes (1+c) 2)
    (v : Tapes (tapes s c) 2) (stack : Fin s) (f : ℤ → Fin 6) (p : ℤ) (e : ℕ)
    (hi : Placement.active (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c)) v=
      CompactNativeRoleOriginal.bank (raw (child rho visit hactive pair coordinate) rows ell precision) payload) :
    Placement.active (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c))
      (output v stack f p (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)) e)=
      CompactNativeRoleOriginal.bank (raw (parent rho visit hactive pair) rows ell precision) payload := by
  unfold output ascended
  rw [active_setTape_outside _ _ _ _ _ (control_outside 1)]
  rw [restored_eq]
  rw [show headerFocus (s:=s) (c:=c) 0=numeric 7 from rfl,
    show headerFocus (s:=s) (c:=c) 1=numeric 8 from rfl,
    show headerFocus (s:=s) (c:=c) 2=numeric 9 from rfl]
  rw [←numeric_slot 7,←numeric_slot 8,←numeric_slot 9]
  rw [active_setTape_slot,active_setTape_slot,active_setTape_slot]
  unfold stackSlot
  rw [active_setTape_outside _ _ _ _ _ (storage_outside (Fin.natAdd 10 stack)),hi]
  rw [show CompactComplexControllerChildPrefix.data (parent rho visit hactive pair) 0=
      bits (parent rho visit hactive pair).f from rfl,
    show CompactComplexControllerChildPrefix.data (parent rho visit hactive pair) 1=
      bits (parent rho visit hactive pair).left from rfl,
    show CompactComplexControllerChildPrefix.data (parent rho visit hactive pair) 2=
      bits (parent rho visit hactive pair).right from rfl]
  rw [show (9 : Fin 43)=Fin.castAdd 15 (9 : Fin 28) from rfl,
    show (8 : Fin 43)=Fin.castAdd 15 (8 : Fin 28) from rfl,
    show (7 : Fin 43)=Fin.castAdd 15 (7 : Fin 28) from rfl]
  rw [raw_bank_put (c:=c) (i:=9),raw_bank_put (c:=c) (i:=8),
    raw_bank_put (c:=c) (i:=7),raw_reparent]

private theorem numeric_bank (v : Tapes (tapes s c) 2)
    (st : ActiveRepairRankHeadersCommands.State) (payload : Tapes (1+c) 2)
    (hi : Placement.active (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c)) v=
      CompactNativeRoleOriginal.bank st payload) (i : Fin 43) :
    v.head (numeric i)=(ActiveRepairRankHeadersCommands.bank (a:=2) st).head i ∧
      v.tape (numeric i)=(ActiveRepairRankHeadersCommands.bank (a:=2) st).tape i := by
  have hh := congrArg (fun b : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 =>
    b.head (Fin.castAdd _ i)) hi
  have ht := congrArg (fun b : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 =>
    b.tape (Fin.castAdd _ i)) hi
  constructor
  · simpa only [Placement.active,numeric_slot,CompactNativeRoleOriginal.bank,Tapes.append,
      Fin.addCases_left] using hh
  · simpa only [Placement.active,numeric_slot,CompactNativeRoleOriginal.bank,Tapes.append,
      Fin.addCases_left] using ht

private theorem header_ready (stage : ActivePrefixStageParameters.Stage sh)
    (rows ell precision : ℕ) (payload : Tapes (1+c) 2) (v : Tapes (tapes s c) 2)
    (hi : Placement.active (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c)) v=
      CompactNativeRoleOriginal.bank (raw stage rows ell precision) payload) :
    (∀ i,v.tape (headerFocus i)=BinaryDescriptorStack.descriptor
      (CompactComplexControllerChildPrefix.data stage i)) ∧
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

/-- Actual raw child geometry supplies every erased word, while literal saved
parent frames supply the restored words. No ell/p reset or live installation occurs. -/
theorem raw_runs (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell precision : ℕ) (payload : Tapes (1+c) 2)
    (v : Tapes (tapes s c) 2) (stack : Fin s) (f : ℤ → Fin 6) (p : ℤ) (e : ℕ) (he : 0<e)
    (hi : Placement.active (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c)) v=
      CompactNativeRoleOriginal.bank (raw (child rho visit hactive pair coordinate) rows ell precision) payload)
    (ht : v.tape (stackSlot stack)=CompactChildHeadersStack.frames f p
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)))
    (hp : v.head (stackSlot stack)=CompactChildHeadersStack.top p
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)))
    (hb : ∀ z,p≤z → f z=blank)
    (hx : v.tape (control 1)=BinaryDescriptorStack.descriptor (bits (e-1))) (hhx : v.head (control 1)=1) :
    HoareTime (program (c:=c) stack) (fun w => w=v)
      (fun w => w=output v stack f p (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)) e)
      (2*((CompactComplexControllerChildPrefix.data (child rho visit hactive pair coordinate) 0).length+
        (CompactComplexControllerChildPrefix.data (child rho visit hactive pair coordinate) 1).length+
        (CompactComplexControllerChildPrefix.data (child rho visit hactive pair coordinate) 2).length)+14+
        CompactChildHeadersStack.cost (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair))+1+
        2*(e+1)+1) := by
  have hready := header_ready (child rho visit hactive pair coordinate) rows ell precision payload v hi
  exact runs v stack f p _ _ e he ht hp hready.1 hready.2 hb hx hhx

private theorem storage_injective : Function.Injective (storage (s:=s) (c:=c)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem storage_numeric (j : Fin (10+s)) (i : Fin 43) :
    storage (s:=s) (c:=c) j≠numeric i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,numeric,CompactComplexNonleafRoleEntry.numeric,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  have hi := i.isLt
  omega

private theorem storage_control (j : Fin (10+s)) (i : Fin 43) :
    storage (s:=s) (c:=c) j≠control i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,CompactComplexNonleafRoleChildBank.control,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  have hi := i.isLt
  omega

/-- All storage outside the popped geometric stack retains its true changed
child values, including current live7, target8, target-stack9 and payload stacks. -/
theorem output_storage (v : Tapes (tapes s c) 2) (stack : Fin s) (f : ℤ → Fin 6)
    (p : ℤ) (data : Fin 3 → List Bool) (e : ℕ) (j : Fin (10+s))
    (hj : j≠Fin.natAdd 10 stack) :
    (output v stack f p data e).head (storage j)=v.head (storage j) ∧
      (output v stack f p data e).tape (storage j)=v.tape (storage j) := by
  apply output_frame
  · exact storage_control j 1
  · exact fun h => hj (storage_injective h)
  · intro i
    exact storage_numeric j (![7,8,9] i)

theorem output_current (v : Tapes (tapes s c) 2) (stack : Fin s) (f : ℤ → Fin 6)
    (p : ℤ) (data : Fin 3 → List Bool) (e : ℕ) :
    (output v stack f p data e).head CompactComplexNonleafRoleChildBank.current=
      v.head CompactComplexNonleafRoleChildBank.current ∧
    (output v stack f p data e).tape CompactComplexNonleafRoleChildBank.current=
      v.tape CompactComplexNonleafRoleChildBank.current := by
  apply output_storage v stack f p data e ⟨7,by omega⟩
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_natAdd] at hv
  omega

theorem output_target (v : Tapes (tapes s c) 2) (stack : Fin s) (f : ℤ → Fin 6)
    (p : ℤ) (data : Fin 3 → List Bool) (e : ℕ) :
    (output v stack f p data e).head CompactComplexNonleafRoleChildBank.target=
      v.head CompactComplexNonleafRoleChildBank.target ∧
    (output v stack f p data e).tape CompactComplexNonleafRoleChildBank.target=
      v.tape CompactComplexNonleafRoleChildBank.target := by
  apply output_storage v stack f p data e ⟨8,by omega⟩
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_natAdd] at hv
  omega

private theorem replace_outside {l u t a : ℕ} (placement : Fin (l+u) ≃ Fin t)
    (v : Tapes t a) (small : Tapes l a) (slot : Fin t)
    (hs : ∀ i : Fin l,placement (Fin.castAdd u i)≠slot) :
    (Placement.replace placement v small).head slot=v.head slot ∧
      (Placement.replace placement v small).tape slot=v.tape slot := by
  obtain ⟨j,rfl⟩ := placement.surjective slot
  induction j using Fin.addCases with
  | left j => exact (hs j rfl).elim
  | right j => simp only [Placement.replace,Placement.combine_head_extra,
      Placement.combine_tape_extra,Placement.extra,and_self]

private theorem stack_ne_small (stack : Fin s) (i : Fin (10+s)) (hi : i.val<10) :
    storage (s:=s) (c:=c) (Fin.natAdd 10 stack)≠storage i := by
  intro h
  have hv := congrArg Fin.val (storage_injective h)
  simp only [Fin.val_natAdd] at hv
  omega

/-- The real forward child entry leaves precisely the parent geometry frames
that this reverse programme consumes, without supplying a fabricated stack. -/
theorem entered_header_stack (v : Tapes (tapes s c) 2) (parentTarget n e : ℕ)
    (headerStack pcStack liveStack : Fin s) (site : Fin siteCount)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell precision : ℕ) (payload : Tapes (1+c) 2)
    (hpc : headerStack≠pcStack) (hlive : headerStack≠liveStack) :
    let entered := CompactComplexNonleafRoleChildBank.output v parentTarget n e headerStack pcStack liveStack
      site rho visit hactive pair coordinate rows ell precision payload
    entered.tape (stackSlot headerStack)=CompactChildHeadersStack.frames
      (v.tape (stackSlot headerStack)) (v.head (stackSlot headerStack))
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)) ∧
    entered.head (stackSlot headerStack)=CompactChildHeadersStack.top
      (v.head (stackSlot headerStack)) (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)) := by
  dsimp only
  unfold CompactComplexNonleafRoleChildBank.output CompactComplexNonleafRoleChildBank.coreOutput
  let before := CompactComplexNonleafRoleChildBank.descended
    (CompactComplexNonleafRoleChildBank.pcSaved
      (CompactComplexNonleafRoleChildBank.headersSaved
        (CompactComplexNonleafRoleChildBank.liveSaved
          (CompactComplexNonleafRoleChildBank.targetSaved v parentTarget) liveStack n)
        headerStack (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)))
      pcStack site coordinate) e
  have hr := replace_outside (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c)) before
    (CompactNativeRoleOriginal.bank (raw (child rho visit hactive pair coordinate) rows ell precision) payload)
    (stackSlot headerStack) (storage_outside (c:=c) (Fin.natAdd 10 headerStack))
  rw [hr.1,hr.2]
  dsimp only [before]
  have hpc' : storage (s:=s) (c:=c) (Fin.natAdd 10 headerStack)≠storage (Fin.natAdd 10 pcStack) := by
    intro h
    have hv := congrArg Fin.val (storage_injective h)
    simp only [Fin.val_natAdd] at hv
    exact hpc (Fin.ext (by omega))
  have hlive' : storage (s:=s) (c:=c) (Fin.natAdd 10 headerStack)≠storage (Fin.natAdd 10 liveStack) := by
    intro h
    have hv := congrArg Fin.val (storage_injective h)
    simp only [Fin.val_natAdd] at hv
    exact hlive (Fin.ext (by omega))
  unfold stackSlot CompactComplexNonleafRoleChildBank.descended CompactComplexNonleafRoleChildBank.pcSaved
    FiniteReturnStackAt.pushed CompactComplexNonleafRoleChildBank.headersSaved
    CompactComplexNonleafRoleChildBank.liveSaved CompactComplexNonleafRoleChildBank.targetSaved
    CompactComplexNonleafRoleChildBank.target CompactComplexNonleafRoleChildBank.targetStack
  simp only [setTape,Function.update_self,Function.update_of_ne hpc',Function.update_of_ne hlive',
    Function.update_of_ne (storage_control (Fin.natAdd 10 headerStack) 1),
    Function.update_of_ne (stack_ne_small headerStack ⟨8,by omega⟩ (by change (8:ℕ)<10; decide)),
    Function.update_of_ne (stack_ne_small headerStack ⟨9,by omega⟩ (by change (9:ℕ)<10; decide)),and_self]

theorem output_stack (v : Tapes (tapes s c) 2) (stack : Fin s) (f : ℤ → Fin 6)
    (p : ℤ) (data : Fin 3 → List Bool) (e : ℕ) :
    (output v stack f p data e).head (stackSlot stack)=p ∧
      (output v stack f p data e).tape (stackSlot stack)=f := by
  simp only [output,ascended,restored,setTape,Function.update_of_ne (control_stack 1 stack).symm,
    Function.update_of_ne (header_stack stack 0).symm,Function.update_of_ne (header_stack stack 1).symm,
    Function.update_of_ne (header_stack stack 2).symm,Function.update_self,and_self]

theorem output_exponent (v : Tapes (tapes s c) 2) (stack : Fin s) (f : ℤ → Fin 6)
    (p : ℤ) (data : Fin 3 → List Bool) (e : ℕ) :
    (output v stack f p data e).head (control 1)=1 ∧
      (output v stack f p data e).tape (control 1)=BinaryDescriptorStack.descriptor (bits e) := by
  simp only [output,ascended,setTape,Function.update_self,and_self]

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleParentBank
