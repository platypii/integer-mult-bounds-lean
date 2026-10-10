import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalPath
import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientationInvariants

/-! Literal emitted source and retained saved-call storage at the actual
current-node merger endpoint; the post selector can therefore decode the same
saved call after contraction and merging. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalPorts
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexNativeCodecFrame (permanentTapes)
open CompactComplexSourceReadyWorkspace (tapes)
variable {s c : ℕ}

def endpoint (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2) :=
  CompactComplexSourceReadyWorkspace.bank
    ((CompactComplexNonleafRoleMergeCurrent.bank sh rows ell p rho left count slots right src dst f v).append
      (SharedBank.empty 7 2)) leaf (SharedBank.empty 10 2)

theorem source (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2) :
    (endpoint sh rows ell p rho left count slots right src dst f v leaf).tape
        CompactComplexSourceReadyOrientation.source=NativeZeroPadding.word (NativeZeroPaddingArray.word f) ∧
    (endpoint sh rows ell p rho left count slots right src dst f v leaf).head
        CompactComplexSourceReadyOrientation.source=0 := by
  have h := CompactComplexNonleafRoleMergeCurrent.output_source sh rows ell p rho left count slots right src dst f v
  rw [CompactComplexNonleafRoleMergeCurrent.output_eq_append] at h
  simpa only [endpoint,CompactComplexSourceReadyOrientation.source,NativePolynomialConjugationWorkspace.source,
    CompactComplexSourceReadyWorkspace.bank,Tapes.append,Fin.addCases_left] using h.symm

theorem storage (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2) (j : Fin (10+s)) :
    let slot : Fin (tapes s c) := Fin.castAdd 10
      (Fin.castAdd CompactComplexSourceReadyWorkspace.leafTapes (CompactComplexNonleafRoleChildBank.storage j))
    (endpoint sh rows ell p rho left count slots right src dst f v leaf).head slot=
      v.head (Fin.castAdd 2 (CompactComplexSpectatorTargetBank.oldSlot j)) ∧
    (endpoint sh rows ell p rho left count slots right src dst f v leaf).tape slot=
      v.tape (Fin.castAdd 2 (CompactComplexSpectatorTargetBank.oldSlot j)) := by
  have h := CompactComplexNonleafRoleMergeCurrent.output_storage sh rows ell p rho left count slots right src dst f v
    (Fin.castAdd 43 j)
  rw [CompactComplexNonleafRoleMergeCurrent.output_eq_append] at h
  simpa only [endpoint,CompactComplexSourceReadyWorkspace.bank,CompactComplexNonleafRoleChildBank.storage,
    CompactComplexSpectatorTargetBank.oldSlot,Tapes.append,Fin.addCases_left] using h

theorem committed_saved (storage : Tapes (10+s) 2) (target : ℕ) (pcStack : Fin s) :
    (CompactComplexControllerExactReturn.committed storage target).head (Fin.natAdd 10 pcStack)=
      storage.head (Fin.natAdd 10 pcStack) ∧
    (CompactComplexControllerExactReturn.committed storage target).tape (Fin.natAdd 10 pcStack)=
      storage.tape (Fin.natAdd 10 pcStack) := by
  have h7 : Fin.natAdd 10 pcStack≠(⟨7,by omega⟩ : Fin (10+s)) := by intro h; have h:=congrArg Fin.val h; simp only [Fin.val_natAdd] at h; omega
  have h8 : Fin.natAdd 10 pcStack≠(⟨8,by omega⟩ : Fin (10+s)) := by intro h; have h:=congrArg Fin.val h; simp only [Fin.val_natAdd] at h; omega
  simp only [CompactComplexControllerExactReturn.committed,SharedPlacementAlphabet.setTape,
    Function.update_of_ne h7,Function.update_of_ne h8,and_self]


theorem saved (sh : Shape) (rows ell p rho left count slots right src dst target : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar stage : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (store : Tapes (10+s) 2) (payload : Tapes (1+c) 2)
    (frame : Tapes 2 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2) (pcStack : Fin s) :
    let v := (CompactComplexNativeCodecFrame.bank control queue scalar stage tail
      (CompactComplexControllerExactReturn.committed store target) payload).append frame
    let w := endpoint sh rows ell p rho left count slots right src dst f v leaf
    w.head (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack)=store.head (Fin.natAdd 10 pcStack) ∧
    w.tape (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack)=store.tape (Fin.natAdd 10 pcStack) := by
  have h := storage sh rows ell p rho left count slots right src dst f
    ((CompactComplexNativeCodecFrame.bank control queue scalar stage tail
      (CompactComplexControllerExactReturn.committed store target) payload).append frame)
    leaf (Fin.natAdd 10 pcStack)
  have hb := CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail
    (CompactComplexControllerExactReturn.committed store target) payload (Fin.natAdd 10 pcStack)
  have hc := committed_saved store target pcStack
  simp only [Tapes.append,Fin.addCases_left] at h
  exact ⟨h.1.trans (hb.1.trans hc.1),h.2.trans (hb.2.trans hc.2)⟩

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalPorts
