import IntegerMultBounds.Machine.CompactComplexNonleafRoleParentContinuation
import IntegerMultBounds.Machine.CompactComplexNonleafRoleParentBankBudget
import IntegerMultBounds.Machine.CompactComplexParentLiveStackBudget

/-! After restoring parent geometry and rows, physically retain the child's
normalized live word as the pending target and pop the real parent event live
word. The bank remains mixed until the separate spectator promotion runs. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleParentLiveContinuation
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactComplexChildHeadersData (parent child)
open CompactComplexNativeCodec (raw)
open CompactComplexNonleafRoleChildBank (tapes control storage current target)
open CompactComplexNonleafRoleParentContinuation (placement)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ} {sh : Shape} {left k : ℕ}

private theorem storage_outside (j : Fin (10+s)) (i : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    placement (s:=s) (c:=c) (Fin.castAdd _ i)≠storage j := by
  unfold placement
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

private theorem replaced_storage (v : Tapes (tapes s c) 2)
    (small : Tapes (43+CompactNativeRoleInstall.rawCount c) 2) (j : Fin (10+s)) :
    (Placement.replace placement v small).head (storage j)=v.head (storage j) ∧
      (Placement.replace placement v small).tape (storage j)=v.tape (storage j) := by
  obtain ⟨i,he⟩ := (placement (s:=s) (c:=c)).surjective (storage j)
  rw [←he]
  induction i using Fin.addCases with
  | left i => exact (storage_outside j i he).elim
  | right i => simp only [Placement.replace,Placement.combine_head_extra,
      Placement.combine_tape_extra,Placement.extra,and_self]

/-- Actual live/controller values are preserved through both geometry and
row restoration, not supplied as freshly prepared continuation words. -/
theorem parent_output_storage (v : Tapes (tapes s c) 2) (stack : Fin s)
    (f : ℤ → Fin 6) (p : ℤ) (e : ℕ) (rho : Fin sh.chunk)
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (rows ell precision : ℕ)
    (payload : Tapes (1+c) 2) (j : Fin (10+s)) (hj : j≠Fin.natAdd 10 stack) :
    (CompactComplexNonleafRoleParentContinuation.output v stack f p e rho visit hactive pair
      rows ell precision payload).head (storage j)=v.head (storage j) ∧
    (CompactComplexNonleafRoleParentContinuation.output v stack f p e rho visit hactive pair
      rows ell precision payload).tape (storage j)=v.tape (storage j) := by
  have h0 := replaced_storage (s:=s) (c:=c)
    (CompactComplexNonleafRoleParentBank.output v stack f p
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)) e)
    (CompactNativeRoleOriginal.bank (raw (parent rho visit hactive pair) rows ell precision) payload) j
  have h1 := CompactComplexNonleafRoleParentBank.output_storage v stack f p
    (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)) e j hj
  exact ⟨h0.1.trans h1.1,h0.2.trans h1.2⟩

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

def liveProgram (stack : Fin s) := extend (CompactComplexParentLiveStack.restoreWithTargetProgram (c:=c) stack) 7

def liveOutput (v : Tapes (tapes s c) 2) (stack : Fin s) (f : ℤ → Fin 6)
    (p : ℤ) (parent child : ℕ) :=
  setTape (setTape (setTape v target (BinaryDescriptorStack.descriptor (bits child)) 1)
    (storage (Fin.natAdd 10 stack)) f p) current (BinaryDescriptorStack.descriptor (bits parent)) 1

theorem live_runs (v : Tapes (tapes s c) 2) (stack : Fin s) (f : ℤ → Fin 6)
    (p : ℤ) (parent child : ℕ)
    (ht : v.tape (storage (Fin.natAdd 10 stack))=BinaryDescriptorStack.frame f p (bits parent))
    (hp : v.head (storage (Fin.natAdd 10 stack))=p+1+(bits parent).length)
    (hc : v.tape current=BinaryDescriptorStack.descriptor (bits child)) (hch : v.head current=1)
    (hb : v.tape target=(fun _ => blank)) (hbh : v.head target=0)
    (hf : ∀ z,p≤z → z<p+1+(bits parent).length → f z=blank) :
    HoareTime (liveProgram (c:=c) stack) (fun z => z=v)
      (fun z => z=liveOutput v stack f p parent child)
      (4*(bits child).length+2*(bits parent).length+18) := by
  have h := hoare_extend_eq (CompactComplexParentLiveStack.restore_with_target stack (base v) f p
    parent child ht hp hc hch hb hbh hf) (tail v)
  apply h.consequence (fun _ h => h.trans (base_tail v).symm) _ le_rfl
  intro w hw
  rw [hw,CompactComplexParentLiveStack.restoredWithTarget,
    ←SharedPlacementAlphabet.setTape_append_left,←SharedPlacementAlphabet.setTape_append_left,
    ←SharedPlacementAlphabet.setTape_append_left,base_tail]
  rfl

def program (headerStack liveStack : Fin s) := seq
  (CompactComplexNonleafRoleParentContinuation.program (c:=c) headerStack) (liveProgram (c:=c) liveStack)

def output (v : Tapes (tapes s c) 2) (headerStack liveStack : Fin s)
    (f : ℤ → Fin 6) (p : ℤ) (liveFrame : ℤ → Fin 6) (liveHead : ℤ)
    (e parentLive childLive : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell precision : ℕ) (payload : Tapes (1+c) 2) :=
  liveOutput (CompactComplexNonleafRoleParentContinuation.output v headerStack f p e rho visit hactive pair
    rows ell precision payload) liveStack liveFrame liveHead parentLive childLive


/-- Full physical geometry/row/live restoration derives all intermediate
live-stack readiness from the real changed child-return bank. -/
theorem runs (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell precision : ℕ) (payload : Tapes (1+c) 2)
    (v : Tapes (tapes s c) 2) (headerStack liveStack : Fin s) (hstacks : headerStack≠liveStack)
    (f : ℤ → Fin 6) (p : ℤ) (e : ℕ) (he : 0<e) (hr : 0<rows/c) (hd : c ∣ rows)
    (hi : Placement.active placement v=
      CompactNativeRoleOriginal.bank (raw (child rho visit hactive pair coordinate) (rows/c) ell precision) payload)
    (ht : v.tape (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=CompactChildHeadersStack.frames f p
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)))
    (hp : v.head (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=CompactChildHeadersStack.top p
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)))
    (hb : ∀ z,p≤z → f z=blank)
    (hx : v.tape (control 1)=BinaryDescriptorStack.descriptor (bits (e-1))) (hhx : v.head (control 1)=1)
    (liveFrame : ℤ → Fin 6) (liveHead : ℤ) (parentLive childLive : ℕ)
    (hstack : v.tape (storage (Fin.natAdd 10 liveStack))=BinaryDescriptorStack.frame liveFrame liveHead (bits parentLive))
    (hstackHead : v.head (storage (Fin.natAdd 10 liveStack))=liveHead+1+(bits parentLive).length)
    (hcurrent : v.tape current=BinaryDescriptorStack.descriptor (bits childLive)) (hcurrentHead : v.head current=1)
    (htarget : v.tape target=(fun _ => blank)) (htargetHead : v.head target=0)
    (hfree : ∀ z,liveHead≤z → z<liveHead+1+(bits parentLive).length → liveFrame z=blank) :
    HoareTime (program (c:=c) headerStack liveStack) (fun z => z=v)
      (fun z => z=output v headerStack liveStack f p liveFrame liveHead e parentLive childLive
        rho visit hactive pair rows ell precision payload)
      ((CompactComplexNonleafRoleParentContinuation.geometryCost rho visit hactive pair coordinate e+
        1+1000*(c+1)*rows)+1+(4*(bits childLive).length+2*(bits parentLive).length+18)) := by
  have h0 := CompactComplexNonleafRoleParentContinuation.runs rho visit hactive pair coordinate
    rows ell precision payload v headerStack f p e he hr hd hi ht hp hb hx hhx
  let next := CompactComplexNonleafRoleParentContinuation.output v headerStack f p e rho visit hactive pair
    rows ell precision payload
  have h7 := parent_output_storage v headerStack f p e rho visit hactive pair rows ell precision payload
    (⟨7,by omega⟩ : Fin (10+s)) (by intro h; have hv := congrArg Fin.val h; simp only [Fin.val_natAdd] at hv; omega)
  have h8 := parent_output_storage v headerStack f p e rho visit hactive pair rows ell precision payload
    (⟨8,by omega⟩ : Fin (10+s)) (by intro h; have hv := congrArg Fin.val h; simp only [Fin.val_natAdd] at hv; omega)
  have hs := parent_output_storage v headerStack f p e rho visit hactive pair rows ell precision payload
    (Fin.natAdd 10 liveStack) (by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd] at hv
      exact hstacks (Fin.ext (by omega)))
  have h1 := live_runs next liveStack liveFrame liveHead parentLive childLive
    (hs.2.trans hstack) (hs.1.trans hstackHead) (h7.2.trans hcurrent) (h7.1.trans hcurrentHead)
    (h8.2.trans htarget) (h8.1.trans htargetHead) hfree
  exact h0.seq h1

private theorem active_set_storage (v : Tapes (tapes s c) 2) (j : Fin (10+s))
    (f : ℤ → Fin 6) (p : ℤ) :
    Placement.active placement (setTape v (storage j) f p)=Placement.active placement v := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [setTape,Function.update_of_ne (storage_outside j i)]

/-- The real returned child payload and restored parent raw descriptors are
unchanged by live-word preparation. No common-grid assertion is made here. -/
theorem output_active (v : Tapes (tapes s c) 2) (headerStack liveStack : Fin s)
    (f : ℤ → Fin 6) (p : ℤ) (liveFrame : ℤ → Fin 6) (liveHead : ℤ)
    (e parentLive childLive : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell precision : ℕ) (payload : Tapes (1+c) 2) :
    Placement.active placement (output v headerStack liveStack f p liveFrame liveHead e parentLive childLive
      rho visit hactive pair rows ell precision payload)=
      CompactNativeRoleOriginal.bank (raw (parent rho visit hactive pair) rows ell precision) payload := by
  unfold output liveOutput current target
  rw [active_set_storage,active_set_storage,active_set_storage]
  exact CompactComplexNonleafRoleParentContinuation.output_active v headerStack f p e rho visit hactive pair
    rows ell precision payload


/-- Both denominator words and the older live-stack frame have exact literal
endpoints. The pending target is the value read from the child, not its parent. -/
theorem live_output_ports (v : Tapes (tapes s c) 2) (stack : Fin s)
    (f : ℤ → Fin 6) (p : ℤ) (parent child : ℕ) :
    let out := liveOutput v stack f p parent child
    (out.head current=1 ∧ out.tape current=BinaryDescriptorStack.descriptor (bits parent)) ∧
    (out.head target=1 ∧ out.tape target=BinaryDescriptorStack.descriptor (bits child)) ∧
    (out.head (storage (Fin.natAdd 10 stack))=p ∧ out.tape (storage (Fin.natAdd 10 stack))=f) := by
  have hct : current (s:=s) (c:=c)≠target := fun h =>
    CompactComplexParentLiveStack.current_target (Fin.castAdd_injective _ _ h)
  have hcs : current (s:=s) (c:=c)≠storage (Fin.natAdd 10 stack) := fun h =>
    CompactComplexParentLiveStack.current_stack stack (Fin.castAdd_injective _ _ h)
  have hts : target (s:=s) (c:=c)≠storage (Fin.natAdd 10 stack) := fun h =>
    CompactComplexParentLiveStack.target_stack stack (Fin.castAdd_injective _ _ h)
  dsimp only
  simp only [liveOutput,setTape,Function.update_self,Function.update_of_ne hct.symm,
    Function.update_of_ne hcs.symm,Function.update_of_ne hts, and_self]

theorem live_output_frame (v : Tapes (tapes s c) 2) (stack : Fin s)
    (f : ℤ → Fin 6) (p : ℤ) (parent child : ℕ) (i : Fin (tapes s c))
    (hc : i≠current) (ht : i≠target) (hs : i≠storage (Fin.natAdd 10 stack)) :
    (liveOutput v stack f p parent child).head i=v.head i ∧
      (liveOutput v stack f p parent child).tape i=v.tape i := by
  simp only [liveOutput,setTape,Function.update_of_ne hc,Function.update_of_ne ht,
    Function.update_of_ne hs,and_self]


def timeConstant (c : ℕ) := 244+1000*(c+1)

/-- The genuine parent/child live-progress ledger pays the entire physical
continuation, including geometry, row arithmetic, live preparation and joins. -/
theorem cost_linear (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell precision parentLive completed childLive : ℕ)
    (hr : 0<rows) (hG : 1≤sh.guard)
    (progress : CompactComplexChildAlignmentBudget.Progress sh precision parentLive completed childLive) :
    ((CompactComplexNonleafRoleParentContinuation.geometryCost rho visit hactive pair coordinate (k+2)+
      1+1000*(c+1)*rows)+1+(4*(bits childLive).length+2*(bits parentLive).length+18))≤
      timeConstant c*CompactNativeRoleTransferBudget.volume rows sh ell precision := by
  have hg := CompactComplexNonleafRoleParentBankBudget.cost_linear rho visit hactive pair coordinate
    rows ell precision hr hG
  change CompactComplexNonleafRoleParentContinuation.geometryCost rho visit hactive pair coordinate (k+2)≤
    212*CompactNativeRoleTransferBudget.volume rows sh ell precision at hg
  have hl := CompactComplexParentLiveStackBudget.restore_cost_linear sh rows ell precision
    parentLive completed childLive progress hr
  have hrows : rows≤CompactNativeRoleTransferBudget.volume rows sh ell precision :=
    Nat.le_mul_of_pos_right rows (CompactNativeRoleTransferBudget.symbols_pos sh ell precision)
  have hv : 0<CompactNativeRoleTransferBudget.volume rows sh ell precision :=
    Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell precision)
  unfold CompactComplexParentLiveStackBudget.restoreConstant at hl
  unfold timeConstant
  nlinarith

/-- Uniform volume bound attached to the actual complete physical continuation. -/
theorem runs_linear (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell precision : ℕ) (payload : Tapes (1+c) 2)
    (v : Tapes (tapes s c) 2) (headerStack liveStack : Fin s) (hstacks : headerStack≠liveStack)
    (f : ℤ → Fin 6) (p : ℤ) (e : ℕ) (he : 0<e) (hr : 0<rows/c) (hd : c ∣ rows) (heq : e=k+2) (hG : 1≤sh.guard)
    (hi : Placement.active placement v=
      CompactNativeRoleOriginal.bank (raw (child rho visit hactive pair coordinate) (rows/c) ell precision) payload)
    (ht : v.tape (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=CompactChildHeadersStack.frames f p
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)))
    (hp : v.head (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=CompactChildHeadersStack.top p
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)))
    (hb : ∀ z,p≤z → f z=blank)
    (hx : v.tape (control 1)=BinaryDescriptorStack.descriptor (bits (e-1))) (hhx : v.head (control 1)=1)
    (liveFrame : ℤ → Fin 6) (liveHead : ℤ) (parentLive childLive completed : ℕ)
    (progress : CompactComplexChildAlignmentBudget.Progress sh precision parentLive completed childLive)
    (hstack : v.tape (storage (Fin.natAdd 10 liveStack))=BinaryDescriptorStack.frame liveFrame liveHead (bits parentLive))
    (hstackHead : v.head (storage (Fin.natAdd 10 liveStack))=liveHead+1+(bits parentLive).length)
    (hcurrent : v.tape current=BinaryDescriptorStack.descriptor (bits childLive)) (hcurrentHead : v.head current=1)
    (htarget : v.tape target=(fun _ => blank)) (htargetHead : v.head target=0)
    (hfree : ∀ z,liveHead≤z → z<liveHead+1+(bits parentLive).length → liveFrame z=blank) :
    HoareTime (program (c:=c) headerStack liveStack) (fun z => z=v)
      (fun z => z=output v headerStack liveStack f p liveFrame liveHead e parentLive childLive
        rho visit hactive pair rows ell precision payload)
      (timeConstant c*CompactNativeRoleTransferBudget.volume rows sh ell precision) := by
  subst e
  have h := runs rho visit hactive pair coordinate rows ell precision payload v headerStack liveStack hstacks
    f p (k+2) he hr hd hi ht hp hb hx hhx liveFrame liveHead parentLive childLive
    hstack hstackHead hcurrent hcurrentHead htarget htargetHead hfree
  exact h.consequence (fun _ h => h) (fun _ h => h)
    (cost_linear rho visit hactive pair coordinate rows ell precision parentLive completed childLive
      (by have := Nat.div_le_self rows c; omega) hG progress)

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleParentLiveContinuation
