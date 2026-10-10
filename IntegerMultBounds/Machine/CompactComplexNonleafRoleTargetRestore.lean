import IntegerMultBounds.Machine.CompactComplexNonleafRoleChildBankBudget

/-! Restore the parent's saved node target only after the returned child and
spectators have installed their common live denominator and cleared target8.
The actual saved frame comes from physical child entry, not a fabricated word.
No live word or coefficient payload is changed by this final parent step. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleTargetRestore
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactComplexNonleafRoleChildBank (tapes target targetStack storage control)
open CompactComplexChildHeadersData (parent)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ} {sh : Shape} {left k : ℕ}

private theorem storage_injective : Function.Injective (storage (s:=s) (c:=c)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem target_stack : target (s:=s) (c:=c)≠targetStack := by
  intro h
  have hv := congrArg Fin.val (storage_injective h)
  change 8=9 at hv
  omega

private theorem stack_future (j : Fin s) :
    targetStack (s:=s) (c:=c)≠storage (Fin.natAdd 10 j) := by
  intro h
  have hv := congrArg Fin.val (storage_injective h)
  simp only [Fin.val_natAdd] at hv
  change 9=10+j.val at hv
  omega

private theorem stack_control : targetStack (s:=s) (c:=c)≠control 1 := by
  intro h
  have hv := congrArg Fin.val h
  simp only [targetStack,storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,CompactComplexNonleafRoleChildBank.control,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem stack_outside (i : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c) (Fin.castAdd _ i)≠targetStack := by
  rw [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_slot]
  intro h
  have hv := congrArg Fin.val h
  dsimp only [CompactComplexNonleafRoleSplit.slot] at hv
  simp only [targetStack,storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  have hi := i.isLt
  unfold CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at hv
  unfold CompactNativeRoleInstall.rawCount CompactNativeRoleDestructive.localCount at hi
  split_ifs at hv <;> omega

private theorem replace_stack (v : Tapes (tapes s c) 2)
    (small : Tapes (43+CompactNativeRoleInstall.rawCount c) 2) :
    (Placement.replace CompactComplexNonleafRoleSplit.placement v small).head targetStack=v.head targetStack ∧
      (Placement.replace CompactComplexNonleafRoleSplit.placement v small).tape targetStack=v.tape targetStack := by
  obtain ⟨i,he⟩ := (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c)).surjective targetStack
  rw [←he]
  induction i using Fin.addCases with
  | left i => exact (stack_outside i he).elim
  | right i => simp only [Placement.replace,Placement.combine_head_extra,
      Placement.combine_tape_extra,Placement.extra,and_self]

/-- The literal physical child entry saves the original parent target once
and preserves its complete frame through all geometric/live/PC setup. -/
theorem entered_stack (v : Tapes (tapes s c) 2) (parentTarget n e : ℕ)
    (headerStack pcStack liveStack : Fin s) (site : Fin siteCount)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell p : ℕ) (payload : Tapes (1+c) 2) :
    let entered := CompactComplexNonleafRoleChildBank.output v parentTarget n e headerStack pcStack liveStack
      site rho visit hactive pair coordinate rows ell p payload
    entered.tape targetStack=BinaryDescriptorStack.frame (v.tape targetStack) (v.head targetStack) (bits parentTarget) ∧
      entered.head targetStack=v.head targetStack+1+(bits parentTarget).length := by
  dsimp only
  unfold CompactComplexNonleafRoleChildBank.output CompactComplexNonleafRoleChildBank.coreOutput
  rw [(replace_stack _ _).1,(replace_stack _ _).2]
  unfold CompactComplexNonleafRoleChildBank.descended CompactComplexNonleafRoleChildBank.pcSaved
    FiniteReturnStackAt.pushed CompactComplexNonleafRoleChildBank.headersSaved
    CompactComplexNonleafRoleChildBank.liveSaved CompactComplexNonleafRoleChildBank.targetSaved
  simp only [setTape,Function.update_of_ne stack_control,
    Function.update_of_ne (stack_future pcStack),Function.update_of_ne (stack_future headerStack),
    Function.update_of_ne (stack_future liveStack),Function.update_of_ne target_stack.symm,
    Function.update_self,and_self]

def program (s c : ℕ) := BinaryDescriptorStackAt.popProgram (a:=2)
  (targetStack (s:=s) (c:=c)) target target_stack.symm

def output (v : Tapes (tapes s c) 2) (f : ℤ → Fin 6) (p : ℤ) (n : ℕ) :=
  setTape (setTape v targetStack f p) target (BinaryDescriptorStack.descriptor (bits n)) 1

theorem runs (v : Tapes (tapes s c) 2) (f : ℤ → Fin 6) (p : ℤ) (n : ℕ)
    (ht : v.tape targetStack=BinaryDescriptorStack.frame f p (bits n))
    (hh : v.head targetStack=p+1+(bits n).length)
    (hb : v.tape target=(fun _ => blank)) (hp : v.head target=0)
    (hf : ∀ z,p≤z → z<p+1+(bits n).length → f z=blank) :
    HoareTime (program s c) (fun z => z=v) (fun z => z=output v f p n) (2*(bits n).length+7) :=
  BinaryDescriptorStackAt.pop_hoare targetStack target target_stack.symm v f p (bits n) ht hh hb hp hf

theorem output_ports (v : Tapes (tapes s c) 2) (f : ℤ → Fin 6) (p : ℤ) (n : ℕ) :
    (output v f p n).head target=1 ∧
    (output v f p n).tape target=BinaryDescriptorStack.descriptor (bits n) ∧
    (output v f p n).head targetStack=p ∧ (output v f p n).tape targetStack=f := by
  simp only [output,setTape,Function.update_self,Function.update_of_ne target_stack.symm,and_self]

theorem output_frame (v : Tapes (tapes s c) 2) (f : ℤ → Fin 6) (p : ℤ) (n : ℕ)
    (i : Fin (tapes s c)) (ht : i≠target) (hs : i≠targetStack) :
    (output v f p n).head i=v.head i ∧ (output v f p n).tape i=v.tape i := by
  simp only [output,setTape,Function.update_of_ne ht,Function.update_of_ne hs,and_self]

def timeConstant : ℕ := 11

theorem cost_linear (rows ell metadataP n targetN left exponent : ℕ)
    (ledger : CompactComplexNonleafRoleChildBankBudget.Ledger sh metadataP n targetN left exponent)
    (hr : 0<rows) :
    2*(bits targetN).length+7≤timeConstant*CompactNativeRoleTransferBudget.volume rows sh ell metadataP := by
  have hl := (CompactComplexNonleafRoleChildBankBudget.header_lengths metadataP n targetN left exponent
    rows ell ledger hr).2
  have hv : 0<CompactNativeRoleTransferBudget.volume rows sh ell metadataP :=
    Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell metadataP)
  unfold timeConstant
  omega

theorem runs_linear (v : Tapes (tapes s c) 2) (f : ℤ → Fin 6) (p : ℤ)
    (rows ell metadataP n targetN left exponent : ℕ)
    (ledger : CompactComplexNonleafRoleChildBankBudget.Ledger sh metadataP n targetN left exponent) (hr : 0<rows)
    (ht : v.tape targetStack=BinaryDescriptorStack.frame f p (bits targetN))
    (hh : v.head targetStack=p+1+(bits targetN).length)
    (hb : v.tape target=(fun _ => blank)) (hp : v.head target=0)
    (hf : ∀ z,p≤z → z<p+1+(bits targetN).length → f z=blank) :
    HoareTime (program s c) (fun z => z=v) (fun z => z=output v f p targetN)
      (timeConstant*CompactNativeRoleTransferBudget.volume rows sh ell metadataP) :=
  (runs v f p targetN ht hh hb hp hf).consequence (fun _ h => h) (fun _ h => h)
    (cost_linear rows ell metadataP n targetN left exponent ledger hr)


/-- Recover the parent node target from the exact entry frame retained by
child execution and the subsequent payload/spectator handoff. Target8 is
required blank because shared-live commit must have happened first. -/
theorem after_child (v u : Tapes (tapes s c) 2) (parentTarget n e : ℕ)
    (headerStack pcStack liveStack : Fin s) (site : Fin siteCount)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell p : ℕ) (payload : Tapes (1+c) 2)
    (ht : u.tape targetStack=(CompactComplexNonleafRoleChildBank.output v parentTarget n e
      headerStack pcStack liveStack site rho visit hactive pair coordinate rows ell p payload).tape targetStack)
    (hh : u.head targetStack=(CompactComplexNonleafRoleChildBank.output v parentTarget n e
      headerStack pcStack liveStack site rho visit hactive pair coordinate rows ell p payload).head targetStack)
    (hb : u.tape target=(fun _ => blank)) (hp : u.head target=0)
    (hf : ∀ z,v.head targetStack≤z → z<v.head targetStack+1+(bits parentTarget).length → v.tape targetStack z=blank) :
    HoareTime (program s c) (fun z => z=u)
      (fun z => z=output u (v.tape targetStack) (v.head targetStack) parentTarget)
      (2*(bits parentTarget).length+7) := by
  have hs := entered_stack v parentTarget n e headerStack pcStack liveStack site rho visit hactive pair
    coordinate rows ell p payload
  exact runs u (v.tape targetStack) (v.head targetStack) parentTarget (ht.trans hs.1) (hh.trans hs.2) hb hp hf

theorem output_current (v : Tapes (tapes s c) 2) (f : ℤ → Fin 6) (p : ℤ) (n : ℕ) :
    (output v f p n).head CompactComplexNonleafRoleChildBank.current=v.head CompactComplexNonleafRoleChildBank.current ∧
      (output v f p n).tape CompactComplexNonleafRoleChildBank.current=v.tape CompactComplexNonleafRoleChildBank.current := by
  apply output_frame
  · intro h
    have hv := congrArg Fin.val (storage_injective h)
    change 7=8 at hv
    omega
  · intro h
    have hv := congrArg Fin.val (storage_injective h)
    change 7=9 at hv
    omega

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleTargetRestore
