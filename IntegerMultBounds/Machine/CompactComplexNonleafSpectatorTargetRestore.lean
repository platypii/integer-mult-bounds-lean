import IntegerMultBounds.Machine.CompactComplexNonleafSpectatorPlacement
import IntegerMultBounds.Machine.CompactComplexNonleafRoleTargetRestore

/-! The saved parent node target is popped only after actual spectator promotion
and shared-live commit. The advanced live word, aligned payloads and all nineteen
fixed frame/work tapes survive this final boundary. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafSpectatorTargetRestore
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexNativeCodecFrame (bank permanentTapes)
open CompactComplexNonleafSpectatorPlacement (full)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Width)
open CompactComplexNonleafEventProgress (aligned)
open CompactComplexNonleafSpectatorHandoff (returnedPayload)
open CompactComplexStoppedGridHandoff (payload)
open ActiveRepairRankHeadersCommands (State)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}

private theorem entry_count : CompactComplexNonleafRoleChildBank.tapes s c=permanentTapes (10+s) c+9 := by
  unfold CompactComplexNonleafRoleChildBank.tapes CompactComplexNonleafRoleSplit.tapes
    CompactComplexNonleafRoleEntry.tapes
  omega

def entryEquiv (s c : ℕ) := finCongr (entry_count (s:=s) (c:=c))
def entry (v : Tapes (permanentTapes (10+s) c) 2) (frame : Tapes 9 2) :=
  (v.append frame).reindex (entryEquiv s c).symm

private theorem entry_roundtrip (v : Tapes (permanentTapes (10+s) c) 2) (frame : Tapes 9 2) :
    (entry v frame).reindex (entryEquiv s c)=v.append frame := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [entry,Tapes.reindex,Equiv.symm_symm,Equiv.apply_symm_apply,Tapes.append]

private theorem entry_target : entryEquiv s c (CompactComplexNonleafRoleChildBank.target (s:=s) (c:=c))=
    Fin.castAdd 9 (CompactComplexSpectatorTargetBank.oldSlot (s:=10+s) (c:=c) ⟨8,by omega⟩) := by
  apply Fin.ext
  rfl
private theorem entry_stack : entryEquiv s c (CompactComplexNonleafRoleChildBank.targetStack (s:=s) (c:=c))=
    Fin.castAdd 9 (CompactComplexSpectatorTargetBank.oldSlot (s:=10+s) (c:=c) ⟨9,by omega⟩) := by
  apply Fin.ext
  rfl

private theorem setTape_reindex {l u a : ℕ} (e : Fin l ≃ Fin u) (v : Tapes l a)
    (i : Fin l) (f : ℤ → Fin (a+4)) (p : ℤ) :
    (setTape v i f p).reindex e=setTape (v.reindex e) (e i) f p := by
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals obtain ⟨j,rfl⟩ := e.surjective j
  all_goals simp [setTape,Tapes.reindex,Function.update_apply,e.injective.eq_iff]

def restorePermanent (v : Tapes (permanentTapes (10+s) c) 2) (f : ℤ → Fin 6) (p : ℤ) (n : ℕ) :=
  setTape (setTape v (CompactComplexSpectatorTargetBank.oldSlot ⟨9,by omega⟩) f p)
    (CompactComplexSpectatorTargetBank.oldSlot ⟨8,by omega⟩) (BinaryDescriptorStack.descriptor (bits n)) 1

private theorem output_reindex (v : Tapes (permanentTapes (10+s) c) 2) (frame : Tapes 9 2)
    (f : ℤ → Fin 6) (p : ℤ) (n : ℕ) :
    (CompactComplexNonleafRoleTargetRestore.output (entry v frame) f p n).reindex (entryEquiv s c)=
      (restorePermanent v f p n).append frame := by
  unfold CompactComplexNonleafRoleTargetRestore.output
  rw [setTape_reindex,setTape_reindex,entry_roundtrip,entry_target,entry_stack]
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left]
  rfl

def popProgram (s c : ℕ) := extend
  (reindex (CompactComplexNonleafRoleTargetRestore.program s c) (entryEquiv s c)) 10

def program (selected : Fin c) := seq
  (CompactComplexNonleafSpectatorPlacement.program (s:=s) selected) (popProgram s c)

/-- Reindexed and extended target restoration preserves the exact literal
permanent/frame9/private10 layout with its paid parent-target ledger. -/
theorem pop_runs_linear {sh : Shape} (v : Tapes (permanentTapes (10+s) c) 2) (frame : Tapes 9 2)
    (f : ℤ → Fin 6) (p : ℤ) (rows ell metadataP ledgerN parentTarget left exponent : ℕ)
    (ledger : CompactComplexNonleafRoleChildBankBudget.Ledger sh metadataP ledgerN parentTarget left exponent)
    (hr : 0<rows)
    (ht : v.tape (CompactComplexSpectatorTargetBank.oldSlot ⟨9,by omega⟩)=BinaryDescriptorStack.frame f p (bits parentTarget))
    (hh : v.head (CompactComplexSpectatorTargetBank.oldSlot ⟨9,by omega⟩)=p+1+(bits parentTarget).length)
    (hb : v.tape (CompactComplexSpectatorTargetBank.oldSlot ⟨8,by omega⟩)=fun _ => blank)
    (hp : v.head (CompactComplexSpectatorTargetBank.oldSlot ⟨8,by omega⟩)=0)
    (hf : ∀ z,p≤z → z<p+1+(bits parentTarget).length → f z=blank) :
    HoareTime (popProgram s c) (fun z => z=full v frame)
      (fun z => z=full (restorePermanent v f p parentTarget) frame)
      (CompactComplexNonleafRoleTargetRestore.timeConstant*CompactNativeRoleTransferBudget.volume rows sh ell metadataP) := by
  have hs : (entry v frame).tape CompactComplexNonleafRoleChildBank.targetStack=
      v.tape (CompactComplexSpectatorTargetBank.oldSlot ⟨9,by omega⟩) ∧
      (entry v frame).head CompactComplexNonleafRoleChildBank.targetStack=
      v.head (CompactComplexSpectatorTargetBank.oldSlot ⟨9,by omega⟩) := by
    simp only [entry,Tapes.reindex,Equiv.symm_symm,entry_stack,Tapes.append,Fin.addCases_left,and_self]
  have ht' : (entry v frame).tape CompactComplexNonleafRoleChildBank.target=
      v.tape (CompactComplexSpectatorTargetBank.oldSlot ⟨8,by omega⟩) ∧
      (entry v frame).head CompactComplexNonleafRoleChildBank.target=
      v.head (CompactComplexSpectatorTargetBank.oldSlot ⟨8,by omega⟩) := by
    simp only [entry,Tapes.reindex,Equiv.symm_symm,entry_target,Tapes.append,Fin.addCases_left,and_self]
  have h := CompactComplexNonleafRoleTargetRestore.runs_linear (entry v frame) f p rows ell metadataP ledgerN
    parentTarget left exponent ledger hr (hs.1.trans ht) (hs.2.trans hh) (ht'.1.trans hb) (ht'.2.trans hp) hf
  have he := hoare_reindex_eq h (entryEquiv s c)
  rw [entry_roundtrip,output_reindex] at he
  exact hoare_extend_eq he (SharedBank.empty 10 2)

private theorem bank_setTape (control : Tapes 43 2) (queue : Tapes 1 2) (scalar stage : State)
    (tail : Tapes 22 2) (storage : Tapes (10+s) 2) (pay : Tapes (1+c) 2)
    (i : Fin (10+s)) (f : ℤ → Fin 6) (p : ℤ) :
    setTape (bank control queue scalar stage tail storage pay)
      (CompactComplexSpectatorTargetBank.oldSlot i) f p=
      bank control queue scalar stage tail (setTape storage i f p) pay := by
  unfold bank CompactComplexNativeRoleBridge.bank CompactComplexControllerNativeFrame.bank
    CompactComplexSpectatorTargetBank.oldSlot CompactComplexControllerNativeFrame.storageSlot
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_left]

def restoredStorage (storage : Tapes (10+s) 2) (advanced : ℕ) (f : ℤ → Fin 6) (p : ℤ) (parentTarget : ℕ) :=
  setTape (setTape (CompactComplexStoppedAlignedCall.committed storage advanced) ⟨9,by omega⟩ f p)
    ⟨8,by omega⟩ (BinaryDescriptorStack.descriptor (bits parentTarget)) 1

private theorem committed_stack (storage : Tapes (10+s) 2) (advanced : ℕ) :
    (CompactComplexStoppedAlignedCall.committed storage advanced).head ⟨9,by omega⟩=storage.head ⟨9,by omega⟩ ∧
    (CompactComplexStoppedAlignedCall.committed storage advanced).tape ⟨9,by omega⟩=storage.tape ⟨9,by omega⟩ := by
  simp [CompactComplexStoppedAlignedCall.committed,setTape]

private theorem committed_target (storage : Tapes (10+s) 2) (advanced : ℕ) :
    (CompactComplexStoppedAlignedCall.committed storage advanced).head ⟨8,by omega⟩=0 ∧
    (CompactComplexStoppedAlignedCall.committed storage advanced).tape ⟨8,by omega⟩=fun _ => blank := by
  simp [CompactComplexStoppedAlignedCall.committed,setTape]

def constant (c : ℕ) := CompactComplexChildAlignmentBudget.promotionConstant c+
  CompactComplexNonleafRoleTargetRestore.timeConstant+1

/-- Actual spectator shifts and shared-live commit precede the saved parent
target pop. Its blank destination and retained stack frame are derived from
that committed endpoint; both programs and their join are paid in native volume. -/
theorem runs_linear (sh : Shape) (rows ell metadataP n completed k : ℕ)
    (v : ActivePrefixStageParameters.Stage sh) (selected : Fin c)
    (progress : CompactComplexChildAlignmentBudget.Progress sh metadataP n completed (n+2*arity^(k+1)))
    (hc : 0<c) (hr : 0<rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (before : Fin c → Array sh (rows/c) ell) (child : Array sh (rows/c) ell)
    (hw : ∀ j,Width sh (rows/c) ell (metadataP-2*sh.bits) (before j))
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (source : ℤ → Fin 6) (head : ℤ)
    (hcurrent : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits n))
    (htarget : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=
      RadixZeroFill.encodedBinary (bits (n+2*arity^(k+1))))
    (frame : Tapes 9 2)
    (f : ℤ → Fin 6) (p : ℤ) (ledgerN parentTarget ledgerLeft ledgerExponent : ℕ)
    (ledger : CompactComplexNonleafRoleChildBankBudget.Ledger sh metadataP ledgerN parentTarget ledgerLeft ledgerExponent)
    (hstack : storage.tape ⟨9,by omega⟩=BinaryDescriptorStack.frame f p (bits parentTarget))
    (hstackHead : storage.head ⟨9,by omega⟩=p+1+(bits parentTarget).length)
    (hf : ∀ z,p≤z → z<p+1+(bits parentTarget).length → f z=blank) :
    HoareTime (program (s:=s) selected)
      (fun z => z=full
        (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell metadataP) tail storage
          (returnedPayload sh (rows/c) ell selected source head before child)) frame)
      (fun z => z=full
        (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell metadataP) tail
          (restoredStorage storage (n+2*arity^(k+1)) f p parentTarget)
          (payload sh (rows/c) ell source head (aligned sh (rows/c) ell k selected before child))) frame)
      (constant c*CompactNativeRoleTransferBudget.volume rows sh ell metadataP) := by
  let stage := CompactComplexNativeCodec.raw v rows ell metadataP
  let advanced := n+2*arity^(k+1)
  let pay := payload sh (rows/c) ell source head (aligned sh (rows/c) ell k selected before child)
  let endpoint := bank control queue scalar stage tail (CompactComplexStoppedAlignedCall.committed storage advanced) pay
  have hs := CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail
    (CompactComplexStoppedAlignedCall.committed storage advanced) pay ⟨9,by omega⟩
  have ht := CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail
    (CompactComplexStoppedAlignedCall.committed storage advanced) pay ⟨8,by omega⟩
  have hpop := pop_runs_linear endpoint frame f p rows ell metadataP ledgerN parentTarget
    ledgerLeft ledgerExponent ledger hr
    (hs.2.trans ((committed_stack storage advanced).2.trans hstack))
    (hs.1.trans ((committed_stack storage advanced).1.trans hstackHead))
    (ht.2.trans (committed_target storage advanced).2)
    (ht.1.trans (committed_target storage advanced).1) hf
  have he : restorePermanent endpoint f p parentTarget=
      bank control queue scalar stage tail (restoredStorage storage advanced f p parentTarget) pay := by
    unfold restorePermanent endpoint restoredStorage
    rw [bank_setTape,bank_setTape]
  rw [he] at hpop
  have hhand := CompactComplexNonleafSpectatorPlacement.runs_linear sh rows ell metadataP n completed k
    v selected progress hc hr hgroup hG hA hK before child hw control queue scalar tail storage
    source head hcurrent htarget frame
  have h := hhand.seq hpop
  exact h.consequence (fun _ h => h) (fun _ h => h) (by
    have hV : 0<CompactNativeRoleTransferBudget.volume rows sh ell metadataP :=
      Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell metadataP)
    unfold constant
    rw [Nat.add_mul,Nat.add_mul]
    omega)

/-- Final target restoration retains the already committed advanced live word
and returns the exact saved parent target and its older stack frame. -/
theorem restoredStorage_ports (storage : Tapes (10+s) 2) (advanced : ℕ)
    (f : ℤ → Fin 6) (p : ℤ) (parentTarget : ℕ) :
    (restoredStorage storage advanced f p parentTarget).head ⟨7,by omega⟩=1 ∧
    (restoredStorage storage advanced f p parentTarget).tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (bits advanced) ∧
    (restoredStorage storage advanced f p parentTarget).head ⟨8,by omega⟩=1 ∧
    (restoredStorage storage advanced f p parentTarget).tape ⟨8,by omega⟩=
      BinaryDescriptorStack.descriptor (bits parentTarget) ∧
    (restoredStorage storage advanced f p parentTarget).head ⟨9,by omega⟩=p ∧
    (restoredStorage storage advanced f p parentTarget).tape ⟨9,by omega⟩=f := by
  simp [restoredStorage,CompactComplexStoppedAlignedCall.committed,setTape]

/-- Every other original storage tape retains its complete literal cells and
head, including geometry, PC and parent live stack. -/
theorem restoredStorage_frame (storage : Tapes (10+s) 2) (advanced : ℕ)
    (f : ℤ → Fin 6) (p : ℤ) (parentTarget : ℕ) (i : Fin (10+s))
    (h7 : i≠⟨7,by omega⟩) (h8 : i≠⟨8,by omega⟩) (h9 : i≠⟨9,by omega⟩) :
    (restoredStorage storage advanced f p parentTarget).head i=storage.head i ∧
    (restoredStorage storage advanced f p parentTarget).tape i=storage.tape i := by
  simp only [restoredStorage,CompactComplexStoppedAlignedCall.committed,setTape,
    Function.update_of_ne h7,Function.update_of_ne h8,Function.update_of_ne h9,and_self]

end
end IntegerMultBounds.Machine.CompactComplexNonleafSpectatorTargetRestore
