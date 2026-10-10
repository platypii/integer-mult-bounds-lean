import IntegerMultBounds.Machine.CompactComplexNonleafRoleMerge

/-! Physical child splitting and reverse merging have uniform parent-volume
costs. Both actual row arithmetic schedules and every join are included.
These are local transfer bounds, not a recursive execution assumption. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleTransferBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open ButterflyAxisHeadersArithmetic
open CompactSpectatorLeafSetup (raw)
open RecursiveChildQuotientsConstant (bits)
open CompactNativeRoleTransferBudget (volume)

theorem quotient_cost (c : ℕ) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ) :
    scheduleCost (CompactComplexNonleafRoleSplit.quotientSchedule c)
      (raw sh rows ell p rho left count slots right src dst)=
      BinaryDescriptorDivision.cost (bits rows) (bits c)+3*(bits c).length+
        100*rows+200*(rows/c)+100*c+412 := by
  simp [CompactComplexNonleafRoleSplit.quotientSchedule,scheduleCost,cost,eval,
    CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,raw,RecursiveChildQuotientsConstant.cost,
    ButterflyAxisHeadersData.cmd]
  ring

theorem restore_cost (c : ℕ) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ) :
    scheduleCost (CompactComplexNonleafRoleMerge.restoreSchedule c)
      (raw sh rows ell p rho left count slots right src dst)=
      253*(c*rows)+100*rows+100*c+3*(bits c).length+440 := by
  simp [CompactComplexNonleafRoleMerge.restoreSchedule,scheduleCost,cost,eval,
    CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,raw,RecursiveChildQuotientsConstant.cost,
    ButterflyAxisHeadersData.cmd,ButterflyAxisHeadersData.product]
  ring

theorem quotient_linear (c : ℕ) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ) (hr : 0<rows) :
    scheduleCost (CompactComplexNonleafRoleSplit.quotientSchedule c)
      (raw sh rows ell p rho left count slots right src dst)≤11000*(c+1)*rows := by
  rw [quotient_cost]
  have hq := CompactNativeRoleHeaderBudget.quotient_linear rows c hr
  have hb := ActiveRepairRankHeadersCommands.bits_length c
  have hd := Nat.div_le_self rows c
  have hc := Nat.le_mul_of_pos_right c hr
  nlinarith

theorem restore_linear (c : ℕ) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ) (hr : 0<rows) (hd : c ∣ rows) :
    scheduleCost (CompactComplexNonleafRoleMerge.restoreSchedule c)
      (raw sh (rows/c) ell p rho left count slots right src dst)≤1000*(c+1)*rows := by
  rw [restore_cost, Nat.mul_div_cancel' hd]
  have hb := ActiveRepairRankHeadersCommands.bits_length c
  have hq := Nat.div_le_self rows c
  have hc := Nat.le_mul_of_pos_right c hr
  nlinarith

def constant (c : ℕ) := CompactNativeRoleOriginalBudget.constant c+11000*(c+1)+1

theorem transfer_linear (merge : Bool) (c : ℕ) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (hc : 0<c) (hr : 0<rows/c) (hd : c ∣ rows/c) (hparent : c ∣ rows)
    (hA : 0<sh.axes) (hG : 0<sh.guard) (hK : 0<sh.chunk) :
    (if merge then CompactComplexNonleafRoleMerge.cost c sh rows ell p rho left count slots right src dst
      else CompactComplexNonleafRoleSplit.cost c sh rows ell p rho left count slots right src dst)≤
      constant c*volume rows sh ell p := by
  have hn : 0<(rows/c)/c := Nat.div_pos (Nat.le_of_dvd hr hd) hc
  have hrows : 0<rows := lt_of_lt_of_le hr (Nat.div_le_self rows c)
  have hV : 0<volume rows sh ell p :=
    Nat.mul_pos hrows (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  have hv : volume (rows/c) sh ell p≤volume rows sh ell p :=
    Nat.mul_le_mul_right _ (Nat.div_le_self rows c)
  have hrV : rows≤volume rows sh ell p :=
    Nat.le_mul_of_pos_right _ (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  have ht := CompactNativeRoleOriginalBudget.cost_linear merge ((rows/c)/c) c sh ell p
    rho left count slots right src dst hc hn hA hG hK
  rw [Nat.div_mul_cancel hd] at ht
  have ht' := ht.trans (Nat.mul_le_mul_left _ hv)
  have hq := quotient_linear c sh rows ell p rho left count slots right src dst hrows
  have hm := restore_linear c sh rows ell p rho left count slots right src dst hrows hparent
  have hqV := Nat.mul_le_mul_left (11000*(c+1)) hrV
  have hmV := Nat.mul_le_mul_left (1000*(c+1)) hrV
  cases merge <;> simp only [Bool.false_eq_true,ite_false,ite_true] at *
  · unfold CompactComplexNonleafRoleSplit.cost constant
    nlinarith
  · unfold CompactComplexNonleafRoleMerge.cost constant
    nlinarith

section
open CompactComplexNonleafRoleSplit (program output)
variable {s c : ℕ}
/-- Uniform runtime for the actual entered-source splitter. -/
theorem split_runs_linear (selected : Fin c) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (hc : 0<c) (hr : 0<rows/c) (hd : c ∣ rows/c) (hparent : c ∣ rows)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (hf : v.tape (CompactComplexNonleafRoleEntry.roleTape selected)=
      NativeZeroPadding.word (NativeZeroPaddingArray.word f)) :
    HoareTime (program s c)
      (fun z => z=(CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).append
        (SharedBank.empty 7 2))
      (fun z => z=output selected sh rows ell p rho left count slots right src dst hd f v)
      (constant c*volume rows sh ell p) := by
  have h := CompactComplexNonleafRoleSplit.actual_runs selected sh rows ell p rho left count slots right src dst
    hc hr hd hG hA hK f hw v hf
  exact h.consequence (fun _ hh => hh) (fun _ hh => hh)
    (transfer_linear false c sh rows ell p rho left count slots right src dst hc hr hd hparent hA hG hK)
end

section
open CompactComplexNonleafRoleMerge (program output)
variable {s c : ℕ}
/-- Uniform runtime for the arbitrary actual returned child array merger. -/
theorem merge_runs_linear (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hc : 0<c) (hr : 0<rows/c) (hd : c ∣ rows/c) (hparent : c ∣ rows)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (hh : Placement.active CompactComplexNonleafRoleEntry.headerPlacement v=
      ActiveRepairRankHeadersCommands.bank (raw sh (rows/c) ell p rho left count slots right src dst))
    (hs : v.head CompactComplexNonleafRoleEntry.source=0 ∧
      v.tape CompactComplexNonleafRoleEntry.source=fun _ => blank)
    (hroles : ∀ j : Fin c,v.head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      v.tape (CompactComplexNonleafRoleEntry.roleTape j)=
        NativeZeroPadding.word (NativeZeroPaddingArray.word
          (CompactNativeRoleReservedBridge.role sh (rows/c) c ell hd f j))) :
    HoareTime (program s c) (fun z => z=v.append (SharedBank.empty 7 2))
      (fun z => z=output sh rows ell p rho left count slots right src dst f v)
      (constant c*volume rows sh ell p) := by
  have h := CompactComplexNonleafRoleMerge.actual_runs sh rows ell p rho left count slots right src dst
    hc hr hd hparent hG hA hK f hw v hh hs hroles
  exact h.consequence (fun _ hh => hh) (fun _ hh => hh)
    (transfer_linear true c sh rows ell p rho left count slots right src dst hc hr hd hparent hA hG hK)
end

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleTransferBudget
