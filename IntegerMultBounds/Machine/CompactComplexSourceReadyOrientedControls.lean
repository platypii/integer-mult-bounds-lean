import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientationInvariants
import IntegerMultBounds.Machine.CompactComplexSourceReadyNodeControls
import IntegerMultBounds.Machine.CompactComplexSourceReadyScalarWorkspace

/-! Actual oriented control blocks: pre-conjugation precedes the stopping
marker and post-conjugation follows the complete forward stopped body. The
post block executes before return-PC guard/pop. All blocks are widened over
the dedicated scalar suffix, with that bank retained literally. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControls
noncomputable section
open CompactComplexSourceReadyWorkspace (tapes)
open CompactComplexSourceReadyOrientationInvariants (savedSlot)
variable {s c q B : ℕ}
attribute [local irreducible] CompactComplexSourceReadyDirection.width
  CompactComplexSourceReadyGuard.setupProgram CompactComplexSourceReadyGuard.setupProgramFor

private def stateCount {t q a : ℕ} (_ : Program t q a) := q

def orientation (pcStack : Fin s) := CompactComplexSourceReadyOrientation.program (savedSlot (c:=c) pcStack)
def nodeEntry (pcStack : Fin s) : Σ q,Program (tapes s c) q 2 :=
  ⟨_,seq (orientation pcStack) (CompactComplexSourceReadyNodeControls.entry (s:=s) (c:=c)).2⟩
def nodeStopped (pcStack : Fin s) : Σ q,Program (tapes s c) q 2 :=
  ⟨_,seq (CompactComplexSourceReadyStoppedLeafDispatch.program (s:=s) (c:=c) .forward)
    (orientation pcStack)⟩

def widen (M : Program (tapes s c) q 2) :
    Program (CompactComplexSourceReadyScalarWorkspace.tapes s c) q 2 :=
  extend M CompactComplexSourceReadyScalarWorkspace.scratch

def preProgram (pcStack : Fin s) := widen (orientation (c:=c) pcStack)
def postProgram (pcStack : Fin s) := preProgram (c:=c) pcStack

def entry (pcStack : Fin s) : Σ q,Program (CompactComplexSourceReadyScalarWorkspace.tapes s c) q 2 :=
  ⟨(nodeEntry (c:=c) pcStack).1,widen (nodeEntry (c:=c) pcStack).2⟩
def stopped (pcStack : Fin s) : Σ q,Program (CompactComplexSourceReadyScalarWorkspace.tapes s c) q 2 :=
  ⟨(nodeStopped (c:=c) pcStack).1,widen (nodeStopped (c:=c) pcStack).2⟩

/-- Append the identical post selector to a genuine contraction/rejoin block. -/
def finish (pcStack : Fin s) (M : Program (CompactComplexSourceReadyScalarWorkspace.tapes s c) q 2) :=
  seq M (postProgram (c:=c) pcStack)

def isStopped (pcStack : Fin s) : Fin (entry (c:=c) pcStack).1 → Bool :=
  Fin.addCases (fun _ => false) (CompactComplexSourceReadyNodeControls.isStopped (s:=s) (c:=c))

def stoppedState (pcStack : Fin s) : Fin (entry (c:=c) pcStack).1 :=
  Fin.natAdd (stateCount (orientation (c:=c) pcStack))
    (CompactComplexSourceReadyNodeControls.stoppedState (s:=s) (c:=c))
def nonleafState (pcStack : Fin s) : Fin (entry (c:=c) pcStack).1 :=
  Fin.natAdd (stateCount (orientation (c:=c) pcStack))
    (CompactComplexSourceReadyNodeControls.nonleafState (s:=s) (c:=c))

theorem classify_stopped (pcStack : Fin s) : isStopped (c:=c) pcStack (stoppedState pcStack)=true := by
  simp only [isStopped,stoppedState,stateCount,Fin.addCases_right,CompactComplexSourceReadyNodeControls.classify_stopped]
theorem classify_nonleaf (pcStack : Fin s) : isStopped (c:=c) pcStack (nonleafState pcStack)=false := by
  simp only [isStopped,nonleafState,stateCount,Fin.addCases_right,CompactComplexSourceReadyNodeControls.classify_nonleaf]

/-- Widening retains an arbitrary scalar suffix, including an in-progress
caller bank; no cleaned suffix premise is imposed by control selection. -/
theorem widen_runs {M : Program (tapes s c) q 2} {v w : Tapes (tapes s c) 2}
    (h : HoareTime M (fun z => z=v) (fun z => z=w) B)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2) :
    HoareTime (widen M) (fun z => z=v.append scalar) (fun z => z=w.append scalar) B :=
  hoare_extend_eq h scalar

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControls
