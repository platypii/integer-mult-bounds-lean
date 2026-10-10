import IntegerMultBounds.Machine.CompactComplexSourceReadyLeaf
import IntegerMultBounds.Machine.CompactComplexNonleafRoleChildBank
import IntegerMultBounds.Machine.CompactNativeDenominatorTarget

/-! Physical stopped-leaf target construction and live installation on the
fixed source-ready bank plus leaf work and ten dedicated private tapes. The
actual retained volume is read, not supplied as a target word. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyLeafDenominator
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}

abbrev publicTapes (s c : ℕ) := CompactComplexNonleafRoleChildBank.tapes s c
abbrev leafTapes := CompactComplexSourceReadyLeafPhase.privateTapes
abbrev tapes (s c : ℕ) := publicTapes s c+leafTapes+10

def current : Fin (tapes s c) := Fin.castAdd 10 (Fin.castAdd leafTapes CompactComplexNonleafRoleChildBank.current)
def target : Fin (tapes s c) := Fin.castAdd 10 (Fin.castAdd leafTapes CompactComplexNonleafRoleChildBank.target)
def volume : Fin (tapes s c) := Fin.castAdd 10 (Fin.castAdd leafTapes (CompactComplexNonleafRoleChildBank.numeric 7))
def work : Fin (tapes s c) := Fin.natAdd (publicTapes s c+leafTapes) 0

def slots : Fin 4 → Fin (tapes s c) := ![current,volume,target,work]
private theorem slots_injective : Function.Injective (slots (s:=s) (c:=c)) := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals first | rfl |
    have hv := congrArg Fin.val h
    simp [slots,current,target,volume,work,CompactComplexNonleafRoleChildBank.current,
      CompactComplexNonleafRoleChildBank.target,CompactComplexNonleafRoleChildBank.storage,
      CompactComplexNonleafRoleChildBank.numeric,CompactComplexNonleafRoleEntry.numeric,
      CompactComplexNativeCodecFrame.headerSlot,CompactComplexSpectatorTargetBank.oldSlot,
      CompactComplexControllerNativeFrame.storageSlot,CompactComplexControllerNativeFrame.nativeSlot,
      publicTapes,CompactComplexNonleafRoleChildBank.tapes,CompactComplexNonleafRoleSplit.tapes,
      CompactComplexNonleafRoleEntry.tapes,CompactComplexNativeCodecFrame.permanentTapes,
      CompactComplexNativeRoleBridge.publicTapes,CompactComplexControllerNativeFrame.tapes] at hv
  all_goals omega

def placement := InjectivePlacement.placement (slots (s:=s) (c:=c)) slots_injective
  (by unfold tapes;omega : 4+(tapes s c-4)=tapes s c)
def installProgram := Placement.placed CompactNativeDenominatorTarget.leafProgram (placement (s:=s) (c:=c))
def installed (v : Tapes (tapes s c) 2) (n : ℕ) := setTape v target (RadixZeroFill.encodedBinary (bits n)) 1

private theorem current_target : current (s:=s) (c:=c)≠target := by
  intro h
  have hh := slots_injective (show slots (s:=s) (c:=c) 0=slots 2 from h)
  exact (by decide : (0:Fin 4)≠2) hh

def copySlots : Fin 2 → Fin (tapes s c) := ![target,current]
private theorem copy_injective : Function.Injective (copySlots (s:=s) (c:=c)) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [copySlots,current_target,Ne.symm current_target]
def commitProgram := seq (BinaryDescriptorCleanupList.oneProgram (a:=2) (current (s:=s) (c:=c)))
  (seq (BinaryDescriptorCopyPlaced.program (a:=2) copySlots copy_injective)
    (BinaryDescriptorCleanupList.oneProgram (a:=2) target))
def output (v : Tapes (tapes s c) 2) (n : ℕ) :=
  setTape (setTape v current (RadixZeroFill.encodedBinary (bits n)) 1) target (fun _ => blank) 0

def program := seq (installProgram (s:=s) (c:=c)) commitProgram

theorem active (v : Tapes (tapes s c) 2) (n fullVolume : ℕ)
    (hn : v.head current=1 ∧ v.tape current=RadixZeroFill.encodedBinary (bits n))
    (hv : v.head volume=1 ∧ v.tape volume=RadixZeroFill.encodedBinary (bits fullVolume))
    (ht : v.head target=0 ∧ v.tape target=(fun _ => blank))
    (hw : v.head work=0 ∧ v.tape work=(fun _ => blank)) :
    Placement.active placement v=CompactNativeDenominatorTarget.input n fullVolume := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [placement,InjectivePlacement.active_slot,slots,hn.1,hn.2,hv.1,hv.2,ht.1,ht.2,hw.1,hw.2]

theorem install (v : Tapes (tapes s c) 2) (n fullVolume : ℕ)
    (ha : Placement.active placement v=CompactNativeDenominatorTarget.input n fullVolume) :
    HoareTime installProgram (fun z => z=v) (fun z => z=installed v (n+fullVolume))
      (CompactNativeDenominatorTarget.leafCost n fullVolume) := by
  have h := Placement.hoare_at (CompactNativeDenominatorTarget.leaf_runs n fullVolume) placement v ha
  apply h.consequence (fun _ hz => hz) _ le_rfl
  rintro z ⟨w,rfl,rfl⟩
  have he : CompactNativeDenominatorTarget.bank n fullVolume (some (n+fullVolume))=
      setTape (CompactNativeDenominatorTarget.input n fullVolume) (2:Fin 4)
        (RadixZeroFill.encodedBinary (bits (n+fullVolume))) 1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he,←ha,PlacedDescriptorConstruction.replace_setTape]
  simp only [placement,InjectivePlacement.active_slot,slots,Matrix.cons_val_two,installed]
  rfl

theorem commit (v : Tapes (tapes s c) 2) (n targetN : ℕ)
    (hc : v.tape current=RadixZeroFill.encodedBinary (bits n)) (hch : v.head current=1)
    (ht : v.tape target=RadixZeroFill.encodedBinary (bits targetN)) (hth : v.head target=1) :
    HoareTime commitProgram (fun z => z=v) (fun z => z=output v targetN)
      (2*(bits n).length+4*(bits targetN).length+15) := by
  let erased := setTape v current (fun _ => blank) 0
  let copied := setTape erased current (RadixZeroFill.encodedBinary (bits targetN)) 1
  have h0 := BinaryDescriptorCleanupList.one_hoare current v (bits n)
    (hc.trans (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm) hch
  have h1 := BinaryDescriptorCopyPlaced.copies erased copySlots copy_injective (bits targetN) (by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals dsimp only [BinaryDescriptorCopy.encodedInput]
    all_goals simp [erased,copySlots,setTape,Ne.symm current_target,ht,hth,Copy.cfg])
  have h2 := BinaryDescriptorCleanupList.one_hoare target copied (bits targetN)
    (by simp only [copied,erased,setTape,Function.update_of_ne (Ne.symm current_target),ht];
        exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm)
    (by simp [copied,erased,setTape,Ne.symm current_target,hth])
  apply (h0.seq (h1.seq h2)).consequence (fun _ hz => hz) _ (by omega)
  rintro z rfl
  simp only [copied,erased,SharedPlacementAlphabet.setTape_setTape,output]

theorem runs (v : Tapes (tapes s c) 2) (n fullVolume : ℕ)
    (hn : v.head current=1 ∧ v.tape current=RadixZeroFill.encodedBinary (bits n))
    (hv : v.head volume=1 ∧ v.tape volume=RadixZeroFill.encodedBinary (bits fullVolume))
    (ht : v.head target=0 ∧ v.tape target=(fun _ => blank))
    (hw : v.head work=0 ∧ v.tape work=(fun _ => blank)) :
    HoareTime program (fun z => z=v) (fun z => z=output v (n+fullVolume))
      (CompactNativeDenominatorTarget.leafCost n fullVolume+
        2*(bits n).length+4*(bits (n+fullVolume)).length+16) := by
  have h0 := install v n fullVolume (active v n fullVolume hn hv ht hw)
  have h1 := commit (installed v (n+fullVolume)) n (n+fullVolume)
    (by simpa only [installed,setTape,Function.update_of_ne current_target] using hn.2)
    (by simpa only [installed,setTape,Function.update_of_ne current_target] using hn.1)
    (by simp [installed,setTape]) (by simp [installed,setTape])
  have h := h0.seq h1
  apply h.consequence (fun _ hz => hz) _ (by omega)
  rintro z rfl
  simp only [output,installed]
  apply congrArg₂ Tapes.mk <;> funext i <;>
    by_cases hi : i=current <;> by_cases hj : i=target <;> simp_all [setTape]

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyLeafDenominator
