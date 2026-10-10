import IntegerMultBounds.Machine.CompactComplexNonleafSpectatorHandoff

/-! A fixed spectator-handoff bank preserves all nine Entry payload/clock and
role scratch tapes. Its private ten tapes follow that retained frame, with no
depth-dependent workspace and no additional physical transition cost. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafSpectatorPlacement
noncomputable section
variable {P q b : ℕ}

/-- Move only the handoff's ten private tapes after the nine retained tapes. -/
def placement (P : ℕ) : Fin ((P+10)+9) ≃ Fin ((P+9)+10) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _)).trans
      ((Equiv.sumAssoc _ _ _).trans
        ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans
          ((Equiv.sumAssoc _ _ _).symm.trans
            ((Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv)))))

theorem permanent_slot (i : Fin P) :
    placement P (Fin.castAdd 9 (Fin.castAdd 10 i))=Fin.castAdd 10 (Fin.castAdd 9 i) := by
  simp [placement]

theorem work_slot (i : Fin 10) :
    placement P (Fin.castAdd 9 (Fin.natAdd P i))=Fin.natAdd (P+9) i := by
  simp [placement]

theorem frame_slot (i : Fin 9) :
    placement P (Fin.natAdd (P+10) i)=Fin.castAdd 10 (Fin.natAdd P i) := by
  simp [placement]

abbrev tapes (P : ℕ) := (P+9)+10

def full (v : Tapes P 2) (frame : Tapes 9 2) : Tapes (tapes P) 2 :=
  (v.append frame).append (SharedBank.empty 10 2)

/-- The exact physical permutation retains every frame tape in its original
Entry+7 position and installs blank private handoff tapes after it. -/
theorem combine_eq (v : Tapes P 2) (frame : Tapes 9 2) :
    Placement.combine (placement P) (v.append (SharedBank.empty 10 2)) frame=full v frame := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals obtain ⟨i,rfl⟩ := (placement P).surjective i
  all_goals simp only [Equiv.symm_apply_apply]
  all_goals induction i using Fin.addCases (m:=P+10) (n:=9) with
  | left i =>
    induction i using Fin.addCases (m:=P) (n:=10) with
    | left i =>
      simp only [Tapes.append,permanent_slot,Fin.addCases_left]
    | right i =>
      simp only [Tapes.append,work_slot,Fin.addCases_left,Fin.addCases_right]
  | right i =>
    simp only [Tapes.append,frame_slot,Fin.addCases_left,Fin.addCases_right]

/-- Any exact handoff on the permanent bank lifts with an arbitrary nonblank
nine-tape Entry frame and unchanged runtime. -/
theorem lift_runs {M : Program (P+10) q 2} {v w : Tapes P 2}
    (h : HoareTime M (fun z => z=v.append (SharedBank.empty 10 2))
      (fun z => z=w.append (SharedBank.empty 10 2)) b) (frame : Tapes 9 2) :
    HoareTime (Placement.placed M (placement P)) (fun z => z=full v frame)
      (fun z => z=full w frame) b := by
  have hh := hoare_place h (placement P) frame
  change HoareTime (Placement.placed M (placement P))
    (fun z => z=Placement.combine (placement P) (v.append (SharedBank.empty 10 2)) frame)
    (fun z => z=Placement.combine (placement P) (w.append (SharedBank.empty 10 2)) frame) b at hh
  simpa only [combine_eq] using hh

/-- Retained Entry payload stack, clock and all seven role workspace tapes
have exactly their incoming cells and heads at every lifted endpoint. -/
theorem full_frame (v : Tapes P 2) (frame : Tapes 9 2) (i : Fin 9) :
    (full v frame).head (Fin.castAdd 10 (Fin.natAdd P i))=frame.head i ∧
    (full v frame).tape (Fin.castAdd 10 (Fin.natAdd P i))=frame.tape i := by
  simp [full,Tapes.append]

theorem full_work (v : Tapes P 2) (frame : Tapes 9 2) (i : Fin 10) :
    (full v frame).head (Fin.natAdd (P+9) i)=0 ∧
    (full v frame).tape (Fin.natAdd (P+9) i)=fun _ => blank := by
  simp [full,Tapes.append,SharedBank.empty]

open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid
open CompactComplexRecursiveGeometry (arity)
open CompactComplexNonleafEventProgress (aligned)
open CompactComplexStoppedGridHandoff (payload)
open CompactComplexNativeCodecFrame (bank permanentTapes)
open ActiveRepairRankHeadersCommands (State)
open RecursiveChildQuotientsConstant (bits)
open CompactComplexNonleafSpectatorHandoff (returnedPayload)
variable {s c : ℕ}

abbrev nodeTapes (s c : ℕ) := tapes (permanentTapes (10+s) c)

def program (selected : Fin c) := Placement.placed
  (CompactComplexStoppedAlignedCall.rawProgram (s:=s) c selected)
  (placement (permanentTapes (10+s) c))

/-- The actual nonleaf promotion and final live commit run with all nine
incoming Entry tapes retained and exactly the original linear time bound. -/
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
    (frame : Tapes 9 2) :
    HoareTime (program (s:=s) selected)
      (fun z => z=(fun z => full z frame)
        (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell metadataP) tail storage
          (returnedPayload sh (rows/c) ell selected source head before child)))
      (fun z => z=(fun z => full z frame)
        (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell metadataP) tail
          (CompactComplexStoppedAlignedCall.committed storage (n+2*arity^(k+1)))
          (payload sh (rows/c) ell source head (aligned sh (rows/c) ell k selected before child))))
      (CompactComplexChildAlignmentBudget.promotionConstant c*
        CompactNativeRoleTransferBudget.volume rows sh ell metadataP) := by
  exact lift_runs (CompactComplexNonleafSpectatorHandoff.runs_linear sh rows ell metadataP n completed k
    v selected progress hc hr hgroup hG hA hK before child hw control queue scalar tail storage
    source head hcurrent htarget) frame

/-- Physical placement retains the same named scalar-prefix and true live
ledger conclusions, together with its exact nonblank Entry frame. -/
theorem prefix_runs (sh : Shape) (rows ell metadataP n completed k : ℕ)
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
    (g baselineP C axes : ℕ) (ha : 0<sh.active) (hp : baselineP+2*sh.bits≤metadataP)
    (haxes : axes+2*arity^(k+1)≤sh.bits)
    (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+CompactComplexScalarIntegerRows.guardBits≤sh.chunk)
    (hg : ∀ role,Grid sh (rows/c) ell (metadataP-2*sh.bits) n
      (CompactFramedScalarGrid.bound g (CompactRecursiveGridBudget.bound baselineP C progress.parentLevels
        (progress.parentFrames+2*progress.parentReturned+axes))) (before role))
    (inputIndex : Networks.ComplexFramedExecution.Wire → CompactComplexNonleafEventProgress.Address k →
      CompactComplexNonleafEventProgress.Index sh (rows/c) ell)
    (outputWire : CompactComplexNonleafEventProgress.Index sh (rows/c) ell → Networks.ComplexFramedExecution.Wire)
    (outputAddress : CompactComplexNonleafEventProgress.Index sh (rows/c) ell → CompactComplexNonleafEventProgress.Address k)
    (hcompleted : ∀ i,decoded sh (rows/c) ell (metadataP-2*sh.bits) (n+2*arity^(k+1)) child i=
      Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (arity^k))
        (fun wire address => decoded sh (rows/c) ell (metadataP-2*sh.bits) n
          (before selected) (inputIndex wire address)) (outputWire i) (outputAddress i))
    (frame : Tapes 9 2) :
    HoareTime (program (s:=s) selected)
      (fun z => z=(fun z => full z frame)
        (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell metadataP) tail storage
          (returnedPayload sh (rows/c) ell selected source head before child)))
      (fun z => z=(fun z => full z frame)
        (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell metadataP) tail
          (CompactComplexStoppedAlignedCall.committed storage (n+2*arity^(k+1)))
          (payload sh (rows/c) ell source head (aligned sh (rows/c) ell k selected before child))))
      (CompactComplexChildAlignmentBudget.promotionConstant c*
        CompactNativeRoleTransferBudget.volume rows sh ell metadataP) ∧
    (∀ role,Grid sh (rows/c) ell (metadataP-2*sh.bits) (n+2*arity^(k+1))
      (CompactFramedScalarGrid.bound g (CompactRecursiveGridBudget.bound baselineP C progress.parentLevels
        (progress.parentFrames+2*(progress.parentReturned+arity^(k+1))+axes)))
      (aligned sh (rows/c) ell k selected before child role)) ∧
    (∀ role,role≠selected → decoded sh (rows/c) ell (metadataP-2*sh.bits) (n+2*arity^(k+1))
      (aligned sh (rows/c) ell k selected before child role)=
      decoded sh (rows/c) ell (metadataP-2*sh.bits) n (before role)) ∧
    n+2*arity^(k+1)≤CompactComplexDenominatorCapacity.ledger progress.R progress.baseline
      progress.parentLevels progress.parentFrames (progress.parentReturned+arity^(k+1)) progress.parentUsed := by
  have h := CompactComplexNonleafSpectatorHandoff.prefix_runs sh rows ell metadataP n completed k
    v selected progress hc hr hgroup hG hA hK before child hw control queue scalar tail storage
    source head hcurrent htarget g baselineP C axes ha hp haxes hC hroom hg
    inputIndex outputWire outputAddress hcompleted
  exact ⟨lift_runs h.1 frame,h.2⟩

end
end IntegerMultBounds.Machine.CompactComplexNonleafSpectatorPlacement
