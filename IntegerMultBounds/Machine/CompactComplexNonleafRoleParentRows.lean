import IntegerMultBounds.Machine.CompactComplexNonleafRoleTransferBudget

/-! Parent-only row restoration after a decoded child return. This block is
separate from current-node role merging: a completed root must retain its own
row count. The complete complementary bank, including source and live stacks,
is preserved and every header-arithmetic transition is paid. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleParentRows
noncomputable section
open CompactGadgetReservationShape (Shape)
open ButterflyAxisHeadersArithmetic
open ButterflyAxisHeadersData (cmd product)
open CompactSpectatorLeafSetup (raw)
open CompactComplexNonleafRoleEntry
variable {s c : ℕ}

private theorem numeric_injective : Function.Injective (numeric (s:=s) (c:=c)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [numeric,CompactComplexNativeCodecFrame.headerSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem numeric_size : 43+(tapes s c-43)=tapes s c := by
  unfold tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes
  omega

abbrev schedule (c : ℕ) := CompactComplexNonleafRoleMerge.restoreSchedule c

theorem schedule_valid (c : ℕ) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ) (hr : 0<rows) :
    validSchedule (schedule c) (raw sh rows ell p rho left count slots right src dst) := by
  simp [schedule,CompactComplexNonleafRoleMerge.restoreSchedule,validSchedule,valid,eval,
    CompactChildHeadersArithmetic.valid,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,raw,hr]

theorem schedule_eval (c : ℕ) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ) :
    execute (schedule c) (raw sh rows ell p rho left count slots right src dst)=
      raw sh (rows*c) ell p rho left count slots right src dst := by
  funext i
  fin_cases i <;> simp [schedule,CompactComplexNonleafRoleMerge.restoreSchedule,execute,eval,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,raw,Nat.mul_comm]

def program (s c : ℕ) := headerProgram (s:=s) (c:=c) (schedule c)

def output (v : Tapes (tapes s c) 2) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ) :=
  Placement.replace headerPlacement v (ActiveRepairRankHeadersCommands.bank
    (raw sh (rows*c) ell p rho left count slots right src dst))

theorem runs (v : Tapes (tapes s c) 2) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ) (hr : 0<rows)
    (hh : Placement.active headerPlacement v=ActiveRepairRankHeadersCommands.bank
      (raw sh rows ell p rho left count slots right src dst)) :
    HoareTime (program s c) (fun z => z=v)
      (fun z => z=output v sh rows ell p rho left count slots right src dst)
      (scheduleCost (schedule c) (raw sh rows ell p rho left count slots right src dst)) := by
  have h := schedule_runs (a:=2) (schedule c)
    (raw sh rows ell p rho left count slots right src dst)
    (schedule_valid c sh rows ell p rho left count slots right src dst hr)
  rw [schedule_eval] at h
  exact (Placement.hoare_at h headerPlacement v hh).consequence
    (fun _ h => h) (by rintro z ⟨w,rfl,rfl⟩; rfl) le_rfl

theorem output_headers (v : Tapes (tapes s c) 2) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ) :
    Placement.active headerPlacement (output v sh rows ell p rho left count slots right src dst)=
      ActiveRepairRankHeadersCommands.bank
        (raw sh (rows*c) ell p rho left count slots right src dst) :=
  Placement.active_replace _ _ _

theorem output_frame (v : Tapes (tapes s c) 2) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (i : Fin (tapes s c)) (hi : ∀ j,i≠numeric j) :
    (output v sh rows ell p rho left count slots right src dst).head i=v.head i ∧
      (output v sh rows ell p rho left count slots right src dst).tape i=v.tape i := by
  obtain ⟨i,rfl⟩ := (headerPlacement (s:=s) (c:=c)).surjective i
  induction i using Fin.addCases with
  | left i =>
    have he := InjectivePlacement.active_slot (numeric (s:=s) (c:=c)) numeric_injective numeric_size i
    exact (hi i he).elim
  | right i =>
    simp only [output,Placement.replace,Placement.combine_head_extra,
      Placement.combine_tape_extra,Placement.extra]
    trivial

/-- The actual descendant row descriptor is multiplied exactly once. -/
theorem parent_runs (v : Tapes (tapes s c) 2) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ) (hr : 0<rows/c) (hd : c ∣ rows)
    (hh : Placement.active headerPlacement v=ActiveRepairRankHeadersCommands.bank
      (raw sh (rows/c) ell p rho left count slots right src dst)) :
    HoareTime (program s c) (fun z => z=v)
      (fun z => z=Placement.replace headerPlacement v (ActiveRepairRankHeadersCommands.bank
        (raw sh rows ell p rho left count slots right src dst)))
      (1000*(c+1)*rows) := by
  have h := runs v sh (rows/c) ell p rho left count slots right src dst hr hh
  rw [output,Nat.div_mul_cancel hd] at h
  exact h.consequence (fun _ h => h) (fun _ h => h)
    (CompactComplexNonleafRoleTransferBudget.restore_linear c sh rows ell p rho left count
    slots right src dst (by have := Nat.div_le_self rows c; omega) hd)

/-- Appending private workspace does not alter this parent's row restoration. -/
theorem extended_runs (v : Tapes (tapes s c) 2) (work : Tapes 7 2) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ) (hr : 0<rows/c) (hd : c ∣ rows)
    (hh : Placement.active headerPlacement v=ActiveRepairRankHeadersCommands.bank
      (raw sh (rows/c) ell p rho left count slots right src dst)) :
    HoareTime (extend (program s c) 7) (fun z => z=v.append work)
      (fun z => z=(Placement.replace headerPlacement v (ActiveRepairRankHeadersCommands.bank
        (raw sh rows ell p rho left count slots right src dst))).append work)
      (1000*(c+1)*rows) :=
  hoare_extend_eq (parent_runs v sh rows ell p rho left count slots right src dst hr hd hh) work

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleParentRows
