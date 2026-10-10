import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeaf
import IntegerMultBounds.Machine.CompactComplexSourceReadyGuard
import IntegerMultBounds.Machine.CompactComplexNonleafSpectatorPlacement

/-! One fixed shared source-ready bank for node execution. Public routines
preserve the leaf and denominator suffix; spectator handoffs borrow only its
last ten tapes. Neither tape layout nor any lifted state count depends on depth. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyWorkspace
noncomputable section
variable {s c q b : ℕ}

abbrev publicTapes (s c : ℕ) := CompactComplexNonleafRoleChildBank.tapes s c
abbrev leafTapes := CompactSpectatorLeafOriginal.tapes
abbrev tapes (s c : ℕ) := (publicTapes s c+leafTapes)+10

def bank (v : Tapes (publicTapes s c) 2) (leaf : Tapes leafTapes 2) (work : Tapes 10 2) :=
  (v.append leaf).append work

def ready (v : Tapes (publicTapes s c) 2) :=
  bank v (SharedBank.empty leafTapes 2) (SharedBank.empty 10 2)

theorem ready_leaf (v : Tapes (publicTapes s c) 2) :
    ready v=CompactComplexSourceReadyStoppedLeaf.ready v := rfl

def publicProgram (M : Program (publicTapes s c) q 2) : Program (tapes s c) q 2 :=
  extend (extend M leafTapes) 10

/-- An actual public routine lifts with every leaf/work cell and head retained,
at its original runtime, including simultaneous controller-frame changes. -/
theorem public_runs {M : Program (publicTapes s c) q 2} {v w : Tapes (publicTapes s c) 2}
    (h : HoareTime M (fun z => z=v) (fun z => z=w) b)
    (leaf : Tapes leafTapes 2) (work : Tapes 10 2) :
    HoareTime (publicProgram M) (fun z => z=bank v leaf work)
      (fun z => z=bank w leaf work) b :=
  hoare_extend_eq (hoare_extend_eq h leaf) work

theorem public_ready_runs {M : Program (publicTapes s c) q 2} {v w : Tapes (publicTapes s c) 2}
    (h : HoareTime M (fun z => z=v) (fun z => z=w) b) :
    HoareTime (publicProgram M) (fun z => z=ready v) (fun z => z=ready w) b :=
  public_runs h _ _

/-- Partial guard paths and nonhalting continuation starts lift as well. -/
theorem public_run (M : Program (publicTapes s c) q 2)
    (leaf : Tapes leafTapes 2) (work : Tapes 10 2)
    {x y : Config (publicTapes s c) q 2} {n : ℕ} (h : run M n x=some y) :
    run (publicProgram M) n ((x.extend leaf).extend work)=some ((y.extend leaf).extend work) :=
  extend_run (extend M leafTapes) work (extend_run M leaf h)

/-- Entry and permanent payload-return routines retain their seven-tape Entry
frame before the common leaf/work suffix. -/
def entryProgram (M : Program (CompactComplexNonleafRoleEntry.tapes (10+s) c) q 2) :=
  publicProgram (extend M 7)

theorem entry_runs {M : Program (CompactComplexNonleafRoleEntry.tapes (10+s) c) q 2}
    {v w : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2}
    (h : HoareTime M (fun z => z=v) (fun z => z=w) b)
    (frame : Tapes 7 2) (leaf : Tapes leafTapes 2) (work : Tapes 10 2) :
    HoareTime (entryProgram M) (fun z => z=bank (v.append frame) leaf work)
      (fun z => z=bank (w.append frame) leaf work) b :=
  public_runs (hoare_extend_eq h frame) leaf work

/-- Swap the already fixed spectator work10 past the leaf workspace. -/
def spectatorPlacement (N : ℕ) : Fin ((N+10)+leafTapes) ≃ Fin ((N+leafTapes)+10) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _)).trans
      ((Equiv.sumAssoc _ _ _).trans
        ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans
          ((Equiv.sumAssoc _ _ _).symm.trans
            ((Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv)))))

theorem spectator_public_slot (i : Fin N) :
    spectatorPlacement N (Fin.castAdd leafTapes (Fin.castAdd 10 i))=
      Fin.castAdd 10 (Fin.castAdd leafTapes i) := by simp [spectatorPlacement]
theorem spectator_work_slot (i : Fin 10) :
    spectatorPlacement N (Fin.castAdd leafTapes (Fin.natAdd N i))=
      Fin.natAdd (N+leafTapes) i := by simp [spectatorPlacement]
theorem spectator_leaf_slot (i : Fin leafTapes) :
    spectatorPlacement N (Fin.natAdd (N+10) i)=
      Fin.castAdd 10 (Fin.natAdd N i) := by simp [spectatorPlacement]

theorem spectator_combine (v : Tapes (publicTapes s c) 2)
    (leaf : Tapes leafTapes 2) (work : Tapes 10 2) :
    Placement.combine (spectatorPlacement (publicTapes s c)) (v.append work) leaf=bank v leaf work := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals obtain ⟨i,rfl⟩ := (spectatorPlacement (publicTapes s c)).surjective i
  all_goals simp only [Equiv.symm_apply_apply]
  all_goals induction i using Fin.addCases (m:=publicTapes s c+10) (n:=leafTapes) with
  | left i =>
    induction i using Fin.addCases (m:=publicTapes s c) (n:=10) with
    | left i => simp only [Tapes.append,spectator_public_slot,Fin.addCases_left]
    | right i => simp only [Tapes.append,spectator_work_slot,Fin.addCases_left,Fin.addCases_right]
  | right i => simp only [Tapes.append,spectator_leaf_slot,Fin.addCases_left,Fin.addCases_right]

def spectatorProgram (M : Program (publicTapes s c+10) q 2) :=
  Placement.placed M (spectatorPlacement (publicTapes s c))

/-- Genuine spectator execution uses only the final ten tapes, returning them
blank and preserving arbitrary leaf-work contents with unchanged time. -/
theorem spectator_runs {M : Program (publicTapes s c+10) q 2}
    {v w : Tapes (publicTapes s c) 2}
    (h : HoareTime M (fun z => z=v.append (SharedBank.empty 10 2))
      (fun z => z=w.append (SharedBank.empty 10 2)) b) (leaf : Tapes leafTapes 2) :
    HoareTime (spectatorProgram M) (fun z => z=bank v leaf (SharedBank.empty 10 2))
      (fun z => z=bank w leaf (SharedBank.empty 10 2)) b := by
  have hh := hoare_place h (spectatorPlacement (publicTapes s c)) leaf
  change HoareTime (spectatorProgram M)
    (fun z => z=Placement.combine (spectatorPlacement (publicTapes s c)) (v.append (SharedBank.empty 10 2)) leaf)
    (fun z => z=Placement.combine (spectatorPlacement (publicTapes s c)) (w.append (SharedBank.empty 10 2)) leaf) b at hh
  simpa only [spectator_combine] using hh

theorem public_frame (v : Tapes (publicTapes s c) 2) (leaf : Tapes leafTapes 2)
    (work : Tapes 10 2) (i : Fin (publicTapes s c)) :
    (bank v leaf work).head (Fin.castAdd 10 (Fin.castAdd leafTapes i))=v.head i ∧
    (bank v leaf work).tape (Fin.castAdd 10 (Fin.castAdd leafTapes i))=v.tape i := by
  simp [bank,Tapes.append]
theorem leaf_frame (v : Tapes (publicTapes s c) 2) (leaf : Tapes leafTapes 2)
    (work : Tapes 10 2) (i : Fin leafTapes) :
    (bank v leaf work).head (Fin.castAdd 10 (Fin.natAdd (publicTapes s c) i))=leaf.head i ∧
    (bank v leaf work).tape (Fin.castAdd 10 (Fin.natAdd (publicTapes s c) i))=leaf.tape i := by
  simp [bank,Tapes.append]
theorem work_frame (v : Tapes (publicTapes s c) 2) (leaf : Tapes leafTapes 2)
    (work : Tapes 10 2) (i : Fin 10) :
    (bank v leaf work).head (Fin.natAdd (publicTapes s c+leafTapes) i)=work.head i ∧
    (bank v leaf work).tape (Fin.natAdd (publicTapes s c+leafTapes) i)=work.tape i := by
  simp [bank,Tapes.append]

/-- Named original payload-return and spectator tables on exactly the same bank. -/
def returnProgram (selected : Fin c) :=
  publicProgram (CompactComplexNonleafRoleSourceReturn.program (s:=10+s) selected)
def nodeSpectatorProgram (selected : Fin c) :=
  spectatorProgram (CompactComplexNonleafSpectatorPlacement.program (s:=s) selected)

def quotientProgram := publicProgram (CompactComplexNonleafRolePreparation.quotientProgram (10+s) c)

theorem spectator_ready_runs {selected : Fin c} {v w : Tapes (publicTapes s c) 2}
    (h : HoareTime (CompactComplexNonleafSpectatorPlacement.program (s:=s) selected)
      (fun z => z=v.append (SharedBank.empty 10 2))
      (fun z => z=w.append (SharedBank.empty 10 2)) b) :
    HoareTime (nodeSpectatorProgram selected) (fun z => z=ready v)
      (fun z => z=ready w) b :=
  spectator_runs h (SharedBank.empty leafTapes 2)

theorem ready_leaf_blank (v : Tapes (publicTapes s c) 2) (i : Fin leafTapes) :
    (ready v).head (Fin.castAdd 10 (Fin.natAdd (publicTapes s c) i))=0 ∧
    (ready v).tape (Fin.castAdd 10 (Fin.natAdd (publicTapes s c) i))=(fun _ => blank) :=
  leaf_frame v _ _ i

theorem ready_work_blank (v : Tapes (publicTapes s c) 2) (i : Fin 10) :
    (ready v).head (Fin.natAdd (publicTapes s c+leafTapes) i)=0 ∧
    (ready v).tape (Fin.natAdd (publicTapes s c+leafTapes) i)=(fun _ => blank) :=
  work_frame v _ _ i

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyWorkspace
