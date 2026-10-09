import IntegerMultBounds.Machine.ActivePrefixStageRuntimeProgram

/-! Physical execution of the complete runtime-selected stage. The two branch
proofs justify the same fixed program; no branch is supplied to its input. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageRuntimeRun
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActiveRepairLayoutRecordsData (Array)
open ActivePrefixStageRuntimeData
open ActivePrefixStageRuntimeProgram
open ActivePrefixDirtyControlConjugationData (Kind)
variable {s : Shape}

theorem packed_branch (a b c e : Kind) (m n r : ActivePrefixDirtyControlLoadProducer.Mode)
    (d : Inputs s) (x y : Array s d.rows) (B : ℕ) (hw : 1<d.stage.f)
    (h : HoareTime (ActivePrefixStageDispatchRun.programFor a b c e m n)
      (fun v => v=ActivePrefixStageDispatchRun.bank d x)
      (fun v => v=ActivePrefixStageDispatchRun.bank d y) B) :
    HoareTime (programFor a b c e m n r) (fun v => v=bank d x) (fun v => v=bank d y)
      (ActivePrefixStageWidthSelector.cost (RecursiveChildQuotientsConstant.bits d.stage.f)+B+4) :=
  ActivePrefixStageWidthBranch.packed_runs focus focus_injective _ _ _ _ _ d.stage.f
    (sources d x) (RecursiveChildQuotientsConstant.bits_value _) hw (packed_runs a b c e m n d x y B h)

theorem singleton_branch (a b c e : Kind) (m n r : ActivePrefixDirtyControlLoadProducer.Mode)
    (d : Inputs s) (x y : Array s d.rows) (B : ℕ) (hw : d.stage.f=1)
    (h : HoareTime (ActivePrefixStageSingletonDispatch.programFor r)
      (fun v => v=ActivePrefixStageSingletonDispatch.bank d x)
      (fun v => v=ActivePrefixStageSingletonDispatch.bank d y) B) :
    HoareTime (programFor a b c e m n r) (fun v => v=bank d x) (fun v => v=bank d y)
      (ActivePrefixStageWidthSelector.cost (RecursiveChildQuotientsConstant.bits d.stage.f)+B+4) :=
  ActivePrefixStageWidthBranch.singleton_runs focus focus_injective _ _ _ _ _
    (sources d x) ((RecursiveChildQuotientsConstant.bits_value _).trans hw) (singleton_runs r d x y B h)

theorem runs (D : ℕ) (d : Inputs s) (x : Array s d.rows) (hp : 1<d.stage.f → Packed d D) :
    HoareTime program (fun v => v=bank d x) (fun v => v=bank d (result d x)) (cost D d hp) := by
  by_cases hw : 1<d.stage.f
  · have p := hp hw
    have h := ActivePrefixStageDispatchRun.runs d x (by omega) p.guard p.chunk
      p.earlyRecord p.lateRecord D p.earlyDensity p.lateDensity
    have hh := packed_branch .tPure .tNegative .uPure .uNegative .pure .pure .pure d x _ _ hw h
    have hr : result d x=ActivePrefixStageDispatchData.result d x := dite_eq_left hw
    have hc : cost D d hp=ActivePrefixStageWidthSelector.cost (RecursiveChildQuotientsConstant.bits d.stage.f)+
        ActivePrefixStageDispatchRun.cost D d (by omega) p.guard+4 := by rw [cost,dite_eq_left hw]
    exact hh.consequence (fun _ hv => hv) (fun _ hv => hv.trans (congrArg (bank d) hr.symm)) hc.symm.le
  · have h := ActivePrefixStageSingletonDispatch.runs (singleton d hw) x
    have hh := singleton_branch .tPure .tNegative .uPure .uNegative .pure .pure .pure d x _ _
      (singleton d hw).singleton h
    have hr : result d x=ActivePrefixStageSingletonDispatch.result (singleton d hw) x := dite_eq_right hw
    have hc : cost D d hp=ActivePrefixStageWidthSelector.cost (RecursiveChildQuotientsConstant.bits d.stage.f)+
        ActivePrefixStageSingletonDispatch.cost (singleton d hw)+4 := by rw [cost,dite_eq_right hw]
    exact hh.consequence (fun _ hv => hv) (fun _ hv => hv.trans (congrArg (bank d) hr.symm)) hc.symm.le

end
end IntegerMultBounds.Machine.ActivePrefixStageRuntimeRun
