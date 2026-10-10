import IntegerMultBounds.Machine.CompactNativeDenominatorTarget
import IntegerMultBounds.Machine.CompactComplexControllerChildPrefix

/-! Physical return-target synthesis in the actual persistent controller bank.
The original true denominator is read from storage7 and retained, the full
child volume is read from native7 and retained, storage8 starts blank and
receives the generated target, and storage0 is borrowed and reclaimed.
Every other tape, including the live denominator and target stack, is framed.
These bodies do not choose a stopping decision externally. Their eventual
runtime stop-branch wiring is a separate controller obligation. -/
namespace IntegerMultBounds.Machine.CompactComplexControllerDenominatorTarget
noncomputable section
open CompactComplexControllerNativeFrame (nativeSlot storageSlot)
open CompactComplexControllerDenominator (size current target stack)
open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)
variable {s : ℕ}

def work : Fin (size s) := storageSlot ⟨0,by omega⟩
def volume : Fin (size s) := nativeSlot 7
def slots : Fin 4 → Fin (size s) := ![current,volume,target,work]

private theorem slots_injective : Function.Injective (slots (s:=s)) := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals first | rfl |
    have hv := congrArg Fin.val h
    simp [slots,current,target,volume,work,nativeSlot,storageSlot] at hv

def placement := InjectivePlacement.placement (slots (s:=s)) slots_injective
  (by unfold size CompactComplexControllerNativeFrame.tapes; omega : 4+(size s-4)=size s)
def leafProgram := Placement.placed CompactNativeDenominatorTarget.leafProgram (placement (s:=s))
def networkProgram := Placement.placed CompactNativeDenominatorTarget.networkProgram (placement (s:=s))
def installed (v : Tapes (size s) 2) (targetN : ℕ) :=
  setTape v target (RadixZeroFill.encodedBinary (bits targetN)) 1

/-- The generated port has exactly the representation required by the real
target-stack save routine; no conversion or supplied descriptor is needed. -/
theorem installed_ready (v : Tapes (size s) 2) (targetN : ℕ) :
    (installed v targetN).tape target=BinaryDescriptorStack.descriptor (bits targetN) ∧
      (installed v targetN).head target=1 := by
  simp only [installed,setTape,Function.update_self]
  exact ⟨(BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm,True.intro⟩

theorem leaf_cost_le (n fullVolume : ℕ) :
    CompactNativeDenominatorTarget.leafCost n fullVolume≤4*n+17*fullVolume+45 := by
  have hn := ActiveRepairRankHeadersCommands.bits_length n
  have hv := ActiveRepairRankHeadersCommands.bits_length fullVolume
  unfold CompactNativeDenominatorTarget.leafCost CompactNativeDenominatorTarget.addCost
  omega

theorem network_cost_le (n fullVolume : ℕ) :
    CompactNativeDenominatorTarget.networkCost n fullVolume≤6*n+36*fullVolume+83 := by
  have h0 := leaf_cost_le n fullVolume
  have hn := ActiveRepairRankHeadersCommands.bits_length (n+fullVolume)
  have hv := ActiveRepairRankHeadersCommands.bits_length fullVolume
  unfold CompactNativeDenominatorTarget.networkCost CompactNativeDenominatorTarget.addCost
  omega

/-- Port readiness requires only actual input descriptors and clean target/work
ports. In particular no target number or computed gap is an input word. -/
theorem active_of_headers (v : Tapes (size s) 2) (n fullVolume : ℕ)
    (hn : v.tape current=RadixZeroFill.encodedBinary (bits n) ∧ v.head current=1)
    (hv : v.tape volume=RadixZeroFill.encodedBinary (bits fullVolume) ∧ v.head volume=1)
    (ht : v.tape target=(fun _ => blank) ∧ v.head target=0)
    (hw : v.tape work=(fun _ => blank) ∧ v.head work=0) :
    Placement.active placement v=CompactNativeDenominatorTarget.input n fullVolume := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [placement,InjectivePlacement.active_slot,slots,
    hn.1,hn.2,hv.1,hv.2,ht.1,ht.2,hw.1,hw.2]

private theorem small_output (n fullVolume targetN : ℕ) :
    CompactNativeDenominatorTarget.bank n fullVolume (some targetN)=
      setTape (CompactNativeDenominatorTarget.input n fullVolume) (2:Fin 4)
        (RadixZeroFill.encodedBinary (bits targetN)) 1 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem replace_output (v : Tapes (size s) 2) (n fullVolume targetN : ℕ)
    (ha : Placement.active placement v=CompactNativeDenominatorTarget.input n fullVolume) :
    Placement.replace placement v (CompactNativeDenominatorTarget.bank n fullVolume (some targetN))=
      installed v targetN := by
  rw [small_output,←ha,PlacedDescriptorConstruction.replace_setTape]
  simp only [placement,InjectivePlacement.active_slot,slots,Matrix.cons_val_two,installed]
  rfl

/-- The actual leaf body constructs its own target in storage8 and restores
the work port; every other original root tape is exactly unchanged. -/
theorem leaf_runs (v : Tapes (size s) 2) (n fullVolume : ℕ)
    (ha : Placement.active placement v=CompactNativeDenominatorTarget.input n fullVolume) :
    HoareTime leafProgram (fun w => w=v) (fun w => w=installed v (n+fullVolume))
      (CompactNativeDenominatorTarget.leafCost n fullVolume) := by
  have h := Placement.hoare_at (CompactNativeDenominatorTarget.leaf_runs n fullVolume)
    placement v ha
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨small,rfl,rfl⟩
  exact replace_output v n fullVolume (n+fullVolume) ha

/-- The actual internal body physically adds the child volume twice. -/
theorem network_runs (v : Tapes (size s) 2) (n fullVolume : ℕ)
    (ha : Placement.active placement v=CompactNativeDenominatorTarget.input n fullVolume) :
    HoareTime networkProgram (fun w => w=v) (fun w => w=installed v (n+2*fullVolume))
      (CompactNativeDenominatorTarget.networkCost n fullVolume) := by
  have h := Placement.hoare_at (CompactNativeDenominatorTarget.network_runs n fullVolume)
    placement v ha
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨small,rfl,rfl⟩
  exact replace_output v n fullVolume (n+2*fullVolume) ha

theorem frame (v : Tapes (size s) 2) (targetN : ℕ) (i : Fin (size s)) (hi : i≠target) :
    (installed v targetN).head i=v.head i ∧ (installed v targetN).tape i=v.tape i := by
  simp only [installed,setTape,Function.update_of_ne hi,and_self]

theorem current_frame (v : Tapes (size s) 2) (targetN : ℕ) :
    (installed v targetN).head current=v.head current ∧
      (installed v targetN).tape current=v.tape current := by
  apply frame v targetN current
  intro h
  have hv := congrArg Fin.val h
  simp [current,target,storageSlot] at hv

theorem stack_frame (v : Tapes (size s) 2) (targetN : ℕ) :
    (installed v targetN).head stack=v.head stack ∧
      (installed v targetN).tape stack=v.tape stack := by
  apply frame v targetN stack
  intro h
  have hv := congrArg Fin.val h
  simp [stack,target,storageSlot] at hv

open CompactComplexRecursiveGeometry
open CompactGadgetReservationShape (Shape)
open CompactComplexControllerChildPrefix (native)

def parentBank {sh : Shape} (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (rows : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (tail : Tapes 23 2)
    (storage : Tapes (10+s) 2) :=
  CompactComplexControllerNativeFrame.bank control queue
    (native (CompactComplexChildHeadersData.parent rho visit hactive pair) rows tail) storage

/-- The target constructor reads the genuine parent header. This is the full
volume of one selected child, before the paid child prefix divides native7. -/
theorem parent_volume {sh : Shape} (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (rows : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (tail : Tapes 23 2)
    (storage : Tapes (10+s) 2) :
    (parentBank rho visit hactive pair rows control queue tail storage).tape volume=
        RadixZeroFill.encodedBinary (bits (arity^(k+1))) ∧
      (parentBank rho visit hactive pair rows control queue tail storage).head volume=1 := by
  exact ⟨rfl,rfl⟩

theorem active_parent {sh : Shape} (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (rows : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (tail : Tapes 23 2)
    (storage : Tapes (10+s) 2) (n : ℕ)
    (hn : storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits n) ∧
      storage.head ⟨7,by omega⟩=1)
    (ht : storage.tape ⟨8,by omega⟩=(fun _ => blank) ∧ storage.head ⟨8,by omega⟩=0)
    (hw : storage.tape ⟨0,by omega⟩=(fun _ => blank) ∧ storage.head ⟨0,by omega⟩=0) :
    Placement.active placement (parentBank rho visit hactive pair rows control queue tail storage)=
      CompactNativeDenominatorTarget.input n (arity^(k+1)) := by
  apply active_of_headers
  · simpa only [current,storageSlot,parentBank,CompactComplexControllerNativeFrame.bank,
      Tapes.append,Fin.addCases_right] using hn
  · exact parent_volume rho visit hactive pair rows control queue tail storage
  · simpa only [target,storageSlot,parentBank,CompactComplexControllerNativeFrame.bank,
      Tapes.append,Fin.addCases_right] using ht
  · simpa only [work,storageSlot,parentBank,CompactComplexControllerNativeFrame.bank,
      Tapes.append,Fin.addCases_right] using hw

/-- Stopped-child synthesis uses the actual child axis count arity^(k+1),
and returns exactly the proved leaf policy. This theorem does not identify
the parent's original denominator with a valid target. -/
theorem leaf_parent_runs {sh : Shape} (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (rows : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (tail : Tapes 23 2)
    (storage : Tapes (10+s) 2) (n : ℕ)
    (ha : Placement.active placement (parentBank rho visit hactive pair rows control queue tail storage)=
      CompactNativeDenominatorTarget.input n (arity^(k+1))) :
    HoareTime leafProgram
      (fun v => v=parentBank rho visit hactive pair rows control queue tail storage)
      (fun v => v=installed (parentBank rho visit hactive pair rows control queue tail storage)
        (CompactComplexDenominatorPolicy.leafTarget n (k+1)))
      (CompactNativeDenominatorTarget.leafCost n (arity^(k+1))) :=
  leaf_runs _ n (arity^(k+1)) ha

/-- Internal-child synthesis uses the same genuine full-volume descriptor
and returns the actual framed-network endpoint policy. -/
theorem network_parent_runs {sh : Shape} (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (rows : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (tail : Tapes 23 2)
    (storage : Tapes (10+s) 2) (n : ℕ)
    (ha : Placement.active placement (parentBank rho visit hactive pair rows control queue tail storage)=
      CompactNativeDenominatorTarget.input n (arity^(k+1))) :
    HoareTime networkProgram
      (fun v => v=parentBank rho visit hactive pair rows control queue tail storage)
      (fun v => v=installed (parentBank rho visit hactive pair rows control queue tail storage)
        (CompactComplexDenominatorPolicy.networkTarget n k))
      (CompactNativeDenominatorTarget.networkCost n (arity^(k+1))) :=
  network_runs _ n (arity^(k+1)) ha

end
end IntegerMultBounds.Machine.CompactComplexControllerDenominatorTarget
