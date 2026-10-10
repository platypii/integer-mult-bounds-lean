import IntegerMultBounds.Machine.CompactComplexFixedNodeSavedReturnPath
import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedActualTable

/-! The actual corrected table pops a literal saved frame from the public
storage bank. All source, role, controller and private suffix tapes retain
exactly their original contents and heads; no continuation run is assumed. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedSavedReturnPath
noncomputable section
open Networks
open CompactComplexSourceReadyScalarWorkspace (roles tapes scratch)
open CompactComplexSourceReadyStoppedLeaf (publicTapes ready)
open CompactComplexSourceReadyCorrectedActualTable (controls classify savedStackSlot)
open SharedPlacementAlphabet (setTape)
variable {s : ℕ}
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites
  CompactComplexCompletedLiveLower.schedule CompactComplexRolePhaseSite.roleCount
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth

/-- The saved-PC port before the three private suffixes are appended. -/
def publicSaved (pcStack : Fin s) : Fin (publicTapes s roles) :=
  CompactComplexNonleafRoleChildBank.storage (Fin.natAdd 10 pcStack)

theorem ready_saved (pcStack : Fin s) (v : Tapes (publicTapes s roles) 2)
    (scalar : Tapes scratch 2) :
    ((ready v).append scalar).head (savedStackSlot pcStack)=v.head (publicSaved pcStack) ∧
    ((ready v).append scalar).tape (savedStackSlot pcStack)=v.tape (publicSaved pcStack) := by
  simp only [savedStackSlot,CompactComplexSourceReadyActualTable.savedStackSlot,
    CompactComplexSourceReadyOrientationInvariants.savedSlot,publicSaved,
    ready,CompactComplexSourceReadyLeafPhase.ready,Tapes.append,Fin.addCases_left]
  exact ⟨True.intro,True.intro⟩

/-- The physical pop restores the public storage port and retains every suffix. -/
theorem restored_ready (pcStack : Fin s) (v : Tapes (publicTapes s roles) 2)
    (scalar : Tapes scratch 2) (older : ℤ → Fin 6) (origin : ℤ) :
    setTape ((ready v).append scalar) (savedStackSlot pcStack) older origin=
      (ready (setTape v (publicSaved pcStack) older origin)).append scalar := by
  unfold savedStackSlot CompactComplexSourceReadyActualTable.savedStackSlot
    CompactComplexSourceReadyOrientationInvariants.savedSlot publicSaved
    ready CompactComplexSourceReadyLeafPhase.ready
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left,
    SharedPlacementAlphabet.setTape_append_left]

theorem positive (pcStack : Fin s) : 0<tapes s roles :=
  Nat.zero_lt_of_lt (savedStackSlot pcStack).isLt

/-- Paths in the unchanged actual corrected cyclic table. -/
def path (headerStack pcStack liveStack : Fin s) :=
  CompactComplexFixedNodePaths.nodePath (positive pcStack) (savedStackSlot pcStack)
    (CompactComplexSourceReadyActualTable.childReturn headerStack liveStack) (controls pcStack)
    (CompactComplexSourceReadyActualTable.event headerStack pcStack liveStack) (classify pcStack)

/-- The blank interval erased by pop comes from the older stack's unused tail. -/
theorem blank_interval (older : ℤ → Fin 6) (origin : ℤ)
    (hblank : ∀ z,origin≤z → older z=blank) :
    ∀ j<(CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)),older (origin+j)=blank := by
  intro j _
  exact hblank _ (by omega)

/-- An arbitrary actual full caller bank returns through the genuine saved
frame, preserving even nonempty leaf, work and scalar suffixes. -/
theorem full_return_path (headerStack pcStack liveStack : Fin s)
    (call : ComplexRecursiveCallSchema.Call) (v : Tapes (tapes s roles) 2)
    (older : ℤ → Fin 6) (origin : ℤ)
    (hstack : FiniteReturnStack.bank (v.tape (savedStackSlot pcStack))
      (v.head (savedStackSlot pcStack))=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older origin
        (CompactComplexCallReturn.code call) (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (origin+(CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3))))
    (hblank : ∀ z,origin≤z → older z=blank) :
    path headerStack pcStack liveStack 0 v ((CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3))+5)
      (CompactComplexScheduledPCDecode.savedPC call)
      (setTape v (savedStackSlot pcStack) older origin) := by
  have hw : 0<(CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) := by
    rw [←CompactComplexSourceReadyDirection.width_eq]
    exact CompactComplexSourceReadyOrientation.width_positive call
  have hs := congrArg (fun z : Tapes 1 2 => z.tape 0) hstack
  have hh := congrArg (fun z : Tapes 1 2 => z.head 0) hstack
  exact CompactComplexFixedNodeSavedReturnPath.saved_return_path
    (positive pcStack) (savedStackSlot pcStack)
    (CompactComplexSourceReadyActualTable.childReturn headerStack liveStack) (controls pcStack)
    (CompactComplexSourceReadyActualTable.event headerStack pcStack liveStack) (classify pcStack)
    call v older origin hw hs hh (blank_interval older origin hblank)

/-- Literal public saved word and head determine the actual fixed-table pop. -/
theorem ready_return_path (headerStack pcStack liveStack : Fin s)
    (call : ComplexRecursiveCallSchema.Call) (v : Tapes (publicTapes s roles) 2)
    (scalar : Tapes scratch 2) (older : ℤ → Fin 6) (origin : ℤ)
    (hs : v.tape (publicSaved pcStack)=FiniteReturnStack.wordPart older origin
      (CompactComplexCallReturn.code call) (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
    (hh : v.head (publicSaved pcStack)=origin+(CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)))
    (hblank : ∀ z,origin≤z → older z=blank) :
    path headerStack pcStack liveStack 0 ((ready v).append scalar)
      ((CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3))+5) (CompactComplexScheduledPCDecode.savedPC call)
      ((ready (setTape v (publicSaved pcStack) older origin)).append scalar) := by
  have hw : 0<(CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) := by
    rw [←CompactComplexSourceReadyDirection.width_eq]
    exact CompactComplexSourceReadyOrientation.width_positive call
  have hp := ready_saved pcStack v scalar
  have h := CompactComplexFixedNodeSavedReturnPath.saved_return_path
    (positive pcStack) (savedStackSlot pcStack)
    (CompactComplexSourceReadyActualTable.childReturn headerStack liveStack) (controls pcStack)
    (CompactComplexSourceReadyActualTable.event headerStack pcStack liveStack) (classify pcStack)
    call ((ready v).append scalar) older origin
    hw
    (hp.2.trans hs) (hp.1.trans hh) (blank_interval older origin hblank)
  rw [restored_ready] at h
  exact h

/-- A canonical physical push followed by the actual guard/pop restores the
entire original ready bank. The erased interval is derived from its blank tail. -/
theorem pushed_return_path (headerStack pcStack liveStack : Fin s)
    (call : ComplexRecursiveCallSchema.Call) (v : Tapes (publicTapes s roles) 2)
    (scalar : Tapes scratch 2)
    (hblank : ∀ z,v.head (publicSaved pcStack)≤z → v.tape (publicSaved pcStack) z=blank) :
    path headerStack pcStack liveStack 0
      ((ready (FiniteReturnStackAt.pushed (publicSaved pcStack) (CompactComplexCallReturn.code call) v)).append scalar)
      ((CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3))+5) (CompactComplexScheduledPCDecode.savedPC call)
      ((ready v).append scalar) := by
  have h := ready_return_path headerStack pcStack liveStack call
    (FiniteReturnStackAt.pushed (publicSaved pcStack) (CompactComplexCallReturn.code call) v)
    scalar (v.tape (publicSaved pcStack)) (v.head (publicSaved pcStack))
    (by simp only [FiniteReturnStackAt.pushed,setTape,Function.update_self])
    (by simp only [FiniteReturnStackAt.pushed,setTape,Function.update_self]) hblank
  simpa only [FiniteReturnStackAt.pushed,SharedPlacementAlphabet.setTape_setTape,
    SharedPlacementAlphabet.setTape_self] using h

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedSavedReturnPath
