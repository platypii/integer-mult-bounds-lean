import IntegerMultBounds.Machine.CompactComplexControllerStopCleanup
import IntegerMultBounds.Machine.Branch

/-! The finite controller reads the physically computed stop flag. Each branch
first reclaims the stop workspace, then enters its own finite continuation.
The selection transition itself depends solely on the scanned runtime symbol. -/
namespace IntegerMultBounds.Machine.CompactComplexControllerStopBranch
noncomputable section
variable {a w r q s : ℕ}
open CompactComplexControllerStopSetup (tapes bank)

def test (sy : Fin (tapes w r) → Fin (a+4)) : Bool :=
  sy (ContiguousBankPlacement.focus (8 : Fin 10))==bitSymbol true

def program (leaf : Program (tapes w r) q a) (recurse : Program (tapes w r) s a) :=
  branch test (seq CompactComplexControllerStopCleanup.placed leaf)
    (seq CompactComplexControllerStopCleanup.placed recurse)

theorem decision (caller : Tapes (110+w) a) (persist : Tapes r a) (D e : ℕ) :
    test (bank caller (CompactComplexStopRun.output CompactComplexStopThreshold.base D
      (RecursiveChildQuotientsConstant.bits D) (RecursiveChildQuotientsConstant.bits e)) persist).reads=
      Networks.ComplexRecursiveCallSchema.stopped D e := by
  unfold test
  rw [CompactComplexControllerStopSetup.flag]
  cases Networks.ComplexRecursiveCallSchema.stopped D e <;> simp [bitSymbol,Fin.ext_iff]

/-- Runtime leaf selection enters cleanup; no stopping decision is a machine parameter. -/
theorem enters_leaf (leaf : Program (tapes w r) q a) (recurse : Program (tapes w r) s a)
    (caller : Tapes (110+w) a) (persist : Tapes r a) (D e : ℕ)
    (hs : Networks.ComplexRecursiveCallSchema.stopped D e=true) :
    let v := bank caller (CompactComplexStopRun.output CompactComplexStopThreshold.base D
      (RecursiveChildQuotientsConstant.bits D) (RecursiveChildQuotientsConstant.bits e)) persist
    step (program leaf recurse) (v.start (program leaf recurse)) =
      some ((v.start (seq CompactComplexControllerStopCleanup.placed leaf)).mapState
        (leftState (15+q) (15+s))) := by
  dsimp only
  exact branch_step_enter_true test _ _ _ ((decision caller persist D e).trans hs)

/-- Runtime recursive selection enters cleanup before touching the child routine. -/
theorem enters_recurse (leaf : Program (tapes w r) q a) (recurse : Program (tapes w r) s a)
    (caller : Tapes (110+w) a) (persist : Tapes r a) (D e : ℕ)
    (hs : Networks.ComplexRecursiveCallSchema.stopped D e=false) :
    let v := bank caller (CompactComplexStopRun.output CompactComplexStopThreshold.base D
      (RecursiveChildQuotientsConstant.bits D) (RecursiveChildQuotientsConstant.bits e)) persist
    step (program leaf recurse) (v.start (program leaf recurse)) =
      some ((v.start (seq CompactComplexControllerStopCleanup.placed recurse)).mapState
        (rightState (15+q) (15+s))) := by
  dsimp only
  exact branch_step_enter_false test _ _ _ ((decision caller persist D e).trans hs)

private theorem clean_enters (next : Program (tapes w r) q a)
    (caller : Tapes (110+w) a) (persist : Tapes r a) (B D e : ℕ) :
    let before := bank caller (CompactComplexStopRun.output B D
      (RecursiveChildQuotientsConstant.bits D) (RecursiveChildQuotientsConstant.bits e)) persist
    let after := bank caller (SharedBank.empty 10 a) persist
    ∃ k, k ≤ BinaryDescriptorCleanupList.cost CompactComplexControllerStopCleanup.descriptors
        (CompactComplexControllerStopCleanup.words B D e)+3 ∧
      run (seq CompactComplexControllerStopCleanup.placed next) k
        (before.start (seq CompactComplexControllerStopCleanup.placed next)) =
        some ((after.start next).mapState (Fin.natAdd 15)) := by
  dsimp only
  obtain ⟨k,c,hk,hr,hh,hp⟩ :=
    CompactComplexControllerStopCleanup.placed_cleanup caller persist B D e _ rfl
  have hzero : run next 0 { state := next.start, head := c.head, tape := c.tape } =
      some ((bank caller (SharedBank.empty 10 a) persist).start next) := by
    cases c
    cases hp
    rfl
  exact ⟨k+1,by omega,seq_run _ _ hr hh hzero⟩

/-- A genuine run reaches the selected leaf start with every stop tape reclaimed.
No correctness or execution hypothesis about the leaf is needed. -/
theorem leaf_ready (leaf : Program (tapes w r) q a) (recurse : Program (tapes w r) s a)
    (caller : Tapes (110+w) a) (persist : Tapes r a) (D e : ℕ)
    (hs : Networks.ComplexRecursiveCallSchema.stopped D e=true) :
    let before := bank caller (CompactComplexStopRun.output CompactComplexStopThreshold.base D
      (RecursiveChildQuotientsConstant.bits D) (RecursiveChildQuotientsConstant.bits e)) persist
    let after := bank caller (SharedBank.empty 10 a) persist
    ∃ k, k ≤ 4*D+2*e+25 ∧ run (program leaf recurse) k (before.start (program leaf recurse))=
      some (((after.start leaf).mapState (Fin.natAdd 15)).mapState
        (leftState (15+q) (15+s))) := by
  dsimp only
  obtain ⟨k,hk,hr⟩ := clean_enters leaf caller persist CompactComplexStopThreshold.base D e
  have hc := CompactComplexControllerStopCleanup.cost_le CompactComplexStopThreshold.base D e
    CompactComplexStopThreshold.base_ge_two
  refine ⟨1+k,by omega,?_⟩
  rw [run_add,run_one,enters_leaf leaf recurse caller persist D e hs]
  simp only [Option.bind_some]
  exact run_simulation _ _ (Config.mapState (leftState (15+q) (15+s)))
    (fun c d h => by unfold program; rw [branch_step_left,h]; rfl) hr

/-- A genuine run reaches the selected internal start with its private workspace blank. -/
theorem recurse_ready (leaf : Program (tapes w r) q a) (recurse : Program (tapes w r) s a)
    (caller : Tapes (110+w) a) (persist : Tapes r a) (D e : ℕ)
    (hs : Networks.ComplexRecursiveCallSchema.stopped D e=false) :
    let before := bank caller (CompactComplexStopRun.output CompactComplexStopThreshold.base D
      (RecursiveChildQuotientsConstant.bits D) (RecursiveChildQuotientsConstant.bits e)) persist
    let after := bank caller (SharedBank.empty 10 a) persist
    ∃ k, k ≤ 4*D+2*e+25 ∧ run (program leaf recurse) k (before.start (program leaf recurse))=
      some (((after.start recurse).mapState (Fin.natAdd 15)).mapState
        (rightState (15+q) (15+s))) := by
  dsimp only
  obtain ⟨k,hk,hr⟩ := clean_enters recurse caller persist CompactComplexStopThreshold.base D e
  have hc := CompactComplexControllerStopCleanup.cost_le CompactComplexStopThreshold.base D e
    CompactComplexStopThreshold.base_ge_two
  refine ⟨1+k,by omega,?_⟩
  rw [run_add,run_one,enters_recurse leaf recurse caller persist D e hs]
  simp only [Option.bind_some]
  exact run_simulation _ _ (Config.mapState (rightState (15+q) (15+s)))
    (fun c d h => by unfold program; rw [branch_step_right,h]; rfl) hr

end
end IntegerMultBounds.Machine.CompactComplexControllerStopBranch
