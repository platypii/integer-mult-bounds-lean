import IntegerMultBounds.Machine.CompactComplexNormalizedSpectatorHandoff
import IntegerMultBounds.Machine.CompactComplexNonleafSpectatorTargetRestore
import IntegerMultBounds.Machine.CompactComplexNonleafRoleTargetRestore

/-! The saved parent node target is popped only after actual spectator promotion
and shared-live commit. The advanced live word, aligned payloads and all nineteen
fixed frame/work tapes survive this final boundary. -/
namespace IntegerMultBounds.Machine.CompactComplexNormalizedSpectatorTargetRestore
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexNativeCodecFrame (bank permanentTapes)
open CompactComplexNonleafSpectatorPlacement (full)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Width)
open CompactComplexNormalizedSpectatorHandoff (aligned)
open CompactComplexNormalizedSpectatorHandoff (returnedPayload)
open CompactComplexStoppedGridHandoff (payload)
open ActiveRepairRankHeadersCommands (State)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}

open CompactComplexNonleafSpectatorPlacement (program lift_runs)
open CompactComplexNonleafSpectatorTargetRestore (restorePermanent restoredStorage pop_runs_linear constant)
/-- The actual normalized promotion and final live commit run with all nine
incoming Entry tapes retained and exactly the original linear time bound. -/
theorem placement_runs_linear (sh : Shape) (rows ell metadataP n completed gap : ℕ)
    (v : ActivePrefixStageParameters.Stage sh) (selected : Fin c)
    (progress : CompactComplexChildAlignmentBudget.Progress sh metadataP n completed (n+gap))
    (hc : 0<c) (hr : 0<rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (before : Fin c → Array sh (rows/c) ell) (child : Array sh (rows/c) ell)
    (hw : ∀ j,Width sh (rows/c) ell (metadataP-2*sh.bits) (before j))
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (source : ℤ → Fin 6) (head : ℤ)
    (hcurrent : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits n))
    (htarget : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=
      RadixZeroFill.encodedBinary (bits (n+gap)))
    (frame : Tapes 9 2) :
    HoareTime (program (s:=s) selected)
      (fun z => z=(fun z => full z frame)
        (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell metadataP) tail storage
          (returnedPayload sh (rows/c) ell selected source head before child)))
      (fun z => z=(fun z => full z frame)
        (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell metadataP) tail
          (CompactComplexStoppedAlignedCall.committed storage (n+gap))
          (payload sh (rows/c) ell source head (aligned sh (rows/c) ell gap selected before child))))
      (CompactComplexChildAlignmentBudget.promotionConstant c*
        CompactNativeRoleTransferBudget.volume rows sh ell metadataP) := by
  exact lift_runs (CompactComplexNormalizedSpectatorHandoff.runs_linear sh rows ell metadataP n completed gap
    v selected progress hc hr hgroup hG hA hK before child hw control queue scalar tail storage
    source head hcurrent htarget) frame

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

private theorem committed_stack (storage : Tapes (10+s) 2) (advanced : ℕ) :
    (CompactComplexStoppedAlignedCall.committed storage advanced).head ⟨9,by omega⟩=storage.head ⟨9,by omega⟩ ∧
    (CompactComplexStoppedAlignedCall.committed storage advanced).tape ⟨9,by omega⟩=storage.tape ⟨9,by omega⟩ := by
  simp [CompactComplexStoppedAlignedCall.committed,setTape]

private theorem committed_target (storage : Tapes (10+s) 2) (advanced : ℕ) :
    (CompactComplexStoppedAlignedCall.committed storage advanced).head ⟨8,by omega⟩=0 ∧
    (CompactComplexStoppedAlignedCall.committed storage advanced).tape ⟨8,by omega⟩=fun _ => blank := by
  simp [CompactComplexStoppedAlignedCall.committed,setTape]

/-- Actual spectator shifts and shared-live commit precede the saved parent
target pop. Its blank destination and retained stack frame are derived from
that committed endpoint; both programs and their join are paid in native volume. -/
theorem runs_linear (sh : Shape) (rows ell metadataP n completed gap : ℕ)
    (v : ActivePrefixStageParameters.Stage sh) (selected : Fin c)
    (progress : CompactComplexChildAlignmentBudget.Progress sh metadataP n completed (n+gap))
    (hc : 0<c) (hr : 0<rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (before : Fin c → Array sh (rows/c) ell) (child : Array sh (rows/c) ell)
    (hw : ∀ j,Width sh (rows/c) ell (metadataP-2*sh.bits) (before j))
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (source : ℤ → Fin 6) (head : ℤ)
    (hcurrent : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits n))
    (htarget : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=
      RadixZeroFill.encodedBinary (bits (n+gap)))
    (frame : Tapes 9 2)
    (f : ℤ → Fin 6) (p : ℤ) (ledgerN parentTarget ledgerLeft ledgerExponent : ℕ)
    (ledger : CompactComplexNonleafRoleChildBankBudget.Ledger sh metadataP ledgerN parentTarget ledgerLeft ledgerExponent)
    (hstack : storage.tape ⟨9,by omega⟩=BinaryDescriptorStack.frame f p (bits parentTarget))
    (hstackHead : storage.head ⟨9,by omega⟩=p+1+(bits parentTarget).length)
    (hf : ∀ z,p≤z → z<p+1+(bits parentTarget).length → f z=blank) :
    HoareTime (CompactComplexNonleafSpectatorTargetRestore.program (s:=s) selected)
      (fun z => z=full
        (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell metadataP) tail storage
          (returnedPayload sh (rows/c) ell selected source head before child)) frame)
      (fun z => z=full
        (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell metadataP) tail
          (restoredStorage storage (n+gap) f p parentTarget)
          (payload sh (rows/c) ell source head (aligned sh (rows/c) ell gap selected before child))) frame)
      (constant c*CompactNativeRoleTransferBudget.volume rows sh ell metadataP) := by
  let stage := CompactComplexNativeCodec.raw v rows ell metadataP
  let advanced := n+gap
  let pay := payload sh (rows/c) ell source head (aligned sh (rows/c) ell gap selected before child)
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
  have hhand := placement_runs_linear sh rows ell metadataP n completed gap
    v selected progress hc hr hgroup hG hA hK before child hw control queue scalar tail storage
    source head hcurrent htarget frame
  have h := hhand.seq hpop
  exact h.consequence (fun _ h => h) (fun _ h => h) (by
    have hV : 0<CompactNativeRoleTransferBudget.volume rows sh ell metadataP :=
      Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell metadataP)
    unfold constant
    rw [Nat.add_mul,Nat.add_mul]
    omega)


end
end IntegerMultBounds.Machine.CompactComplexNormalizedSpectatorTargetRestore
