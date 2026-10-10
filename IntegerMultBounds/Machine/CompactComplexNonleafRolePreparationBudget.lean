import IntegerMultBounds.Machine.CompactComplexNonleafRolePreparation
import IntegerMultBounds.Machine.CompactComplexNonleafRoleEntryBudget
import IntegerMultBounds.Machine.CompactComplexNonleafRoleChildBankBudget
import IntegerMultBounds.Machine.CompactComplexNonleafRoleMergeCurrentBudget

/-! Uniform actual budgets for source-ready child entry and its later nonleaf
role split. Entry parks payloads, divides rows once and constructs child control;
only the nonleaf branch splits those already-quotiented current rows. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRolePreparationBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexChildHeadersData (parent child)
open CompactNativeRoleTransferBudget (volume)
open RecursiveChildQuotientsConstant (bits)
open CompactSpectatorLeafSetup (raw)
open CompactComplexNonleafRolePreparation
open CompactComplexNonleafRoleChildBankBudget (Ledger)
variable {sh : Shape} {left k s c siteCount : ℕ}

theorem quotient_cost_eq (c : ℕ) (sh : Shape)
    (rows ell p rho lo count slots right src dst : ℕ) :
    quotientCost c sh rows ell p rho lo count slots right src dst=
      BinaryDescriptorDivision.cost (bits rows) (bits c)+3*(bits c).length+
        100*rows+200*(rows/c)+100*c+412 := by
  simp [quotientCost,CompactComplexNonleafRoleSplit.quotientSchedule,
    ButterflyAxisHeadersArithmetic.scheduleCost,ButterflyAxisHeadersArithmetic.cost,
    ButterflyAxisHeadersArithmetic.eval,CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,raw,RecursiveChildQuotientsConstant.cost]
  ring

def quotientConstant (c : ℕ) := 10000*(c+1)+103*(c+1)+1000

theorem quotient_cost_linear (c : ℕ) (sh : Shape)
    (rows ell p rho lo count slots right src dst : ℕ) (hr : 0<rows) :
    quotientCost c sh rows ell p rho lo count slots right src dst≤
      quotientConstant c*volume rows sh ell p := by
  have hq := CompactNativeRoleHeaderBudget.quotient_linear rows c hr
  have hb := ActiveRepairRankHeadersCommands.bits_length c
  have hd := Nat.div_le_self rows c
  have hfixed := Nat.le_mul_of_pos_right (103*(c+1)+700) hr
  have hrow : rows≤volume rows sh ell p := Nat.le_mul_of_pos_right rows
    (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  have h : quotientCost c sh rows ell p rho lo count slots right src dst≤quotientConstant c*rows := by
    rw [quotient_cost_eq]
    unfold quotientConstant
    nlinarith
  exact h.trans (Nat.mul_le_mul_left (quotientConstant c) hrow)

def constant (c siteCount : ℕ) := CompactComplexNonleafRoleEntryBudget.constant c+
  quotientConstant c+CompactComplexNonleafRoleChildBankBudget.constant siteCount+2

def childEntryCost (selected : Fin c) (parentTarget n : ℕ) (rho : Fin sh.chunk)
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (coordinate : Fin arity) (rows ell p : ℕ) :=
  entryCost (10+s) selected sh rows ell p
      (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
      (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
      (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
      (parent rho visit hactive pair).target.val+
    quotientCost c sh rows ell p
      (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
      (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
      (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
      (parent rho visit hactive pair).target.val+1+
    CompactComplexNonleafRoleChildBank.cost siteCount parentTarget n (k+2)
      rho visit hactive pair coordinate (rows/c) ell p+1

theorem child_entry_cost_linear (selected : Fin c) (parentTarget n : ℕ) (rho : Fin sh.chunk)
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (coordinate : Fin arity) (rows ell p : ℕ)
    (ledger : Ledger sh p n parentTarget left (k+2))
    (hr : 0<rows) (hgroup : 0<rows/c) (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) :
    childEntryCost (s:=s) (siteCount:=siteCount) selected parentTarget n rho visit hactive pair coordinate rows ell p≤
      constant c siteCount*volume rows sh ell p := by
  have he := CompactComplexNonleafRoleEntryBudget.cost_linear (s:=10+s) selected sh rows ell p
    (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
    (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
    (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
    (parent rho visit hactive pair).target.val hr hA hG hK
  have hq := quotient_cost_linear c sh rows ell p
    (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
    (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
    (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
    (parent rho visit hactive pair).target.val hr
  have hc := CompactComplexNonleafRoleChildBankBudget.quotient_cost_linear siteCount parentTarget n
    rho visit hactive pair coordinate rows ell p ledger hgroup hG
  have hV : 0<volume rows sh ell p := Nat.mul_pos hr
    (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  change entryCost (10+s) selected sh rows ell p _ _ _ _ _ _ _≤_ at he
  unfold childEntryCost constant
  nlinarith

/-- Full paid source-ready entry from the literal original caller. The stopped
branch still sees the intact selected source; no role split occurs here. -/
theorem child_entry_from_caller_linear (selected : Fin c) (rho : Fin sh.chunk)
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (coordinate : Fin arity)
    (rows ell p : ℕ) (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (parentTarget n : ℕ) (headerStack pcStack liveStack : Fin s) (site : Fin siteCount)
    (ledger : Ledger sh p n parentTarget left (k+2))
    (hx : Placement.active CompactComplexNonleafRoleChildBank.exponentPlacement
      (v.append (SharedBank.empty 7 2))=CompactComplexExponentStep.bank (k+2))
    (ht : v.tape (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨8,by omega⟩)=
      BinaryDescriptorStack.descriptor (bits parentTarget))
    (hh : v.head (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨8,by omega⟩)=1)
    (hn : v.tape (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨7,by omega⟩)=
      BinaryDescriptorStack.descriptor (bits n))
    (hp : v.head (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨7,by omega⟩)=1)
    (hc : 0<c) (hr : 0<rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hraw : Placement.active CompactComplexNonleafRoleEntry.headerPlacement v=
      ActiveRepairRankHeadersCommands.bank
        (raw sh rows ell p (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
          (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
          (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
          (parent rho visit hactive pair).target.val))
    (hclock : v.head CompactComplexNonleafRoleEntry.clock=0 ∧
      v.tape CompactComplexNonleafRoleEntry.clock=(fun _ => blank))
    (hsource : v.head CompactComplexNonleafRoleEntry.source=0 ∧
      RoleArrayStack.Supported (v.tape CompactComplexNonleafRoleEntry.source)
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p false))
    (hroles : ∀ j,v.head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      RoleArrayStack.Supported (v.tape (CompactComplexNonleafRoleEntry.roleTape j))
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p true))
    (hf : v.tape (CompactComplexNonleafRoleEntry.roleTape selected)=
      NativeZeroPadding.word (NativeZeroPaddingArray.word f)) :
    HoareTime (childEntryProgram selected headerStack pcStack liveStack site coordinate)
      (fun w => w=v.append (SharedBank.empty 7 2))
      (fun w => w=CompactComplexNonleafRoleChildBank.output
        (sourceReady selected rho visit hactive pair rows ell p f v) parentTarget n (k+2)
        headerStack pcStack liveStack site rho visit hactive pair coordinate (rows/c) ell p
        (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell f c))
      (constant c siteCount*volume rows sh ell p) := by
  have h := child_entry_from_caller_runs selected rho visit hactive pair coordinate rows ell p f v
    parentTarget n headerStack pcStack liveStack site hx ht hh hn hp hc hr hgroup hG hA hK
    hraw hclock hsource hroles hf
  exact h.consequence (fun _ h => h) (fun _ h => h)
    (child_entry_cost_linear (s:=s) (siteCount:=siteCount) selected parentTarget n rho visit hactive pair
      coordinate rows ell p ledger hr hgroup hG hA hK)

/-- A genuine parent Path leaves the child's own current rows positive and
divisible by c. Splitting them consumes no second row quotient. -/
theorem child_dimensions (p n parentTarget d K : ℕ)
    (ledger : Ledger sh p n parentTarget left (k+2))
    (hc : 0<c) (hK : 0<K) (hactive : sh.active≤d) :
    0<CompactGlobalRowPadding.rowsAt c arity d K ledger.levels/c ∧
      c ∣ CompactGlobalRowPadding.rowsAt c arity d K ledger.levels/c := by
  have hdepth := CompactComplexNonleafRoleMergeCurrentBudget.path_depth ledger.path d hactive
  exact CompactComplexNonleafRoleSplit.descendant_divides c arity d K ledger.levels hc hK (by omega)

theorem split_cost_linear (c : ℕ) (sh : Shape)
    (rows ell p rho lo count slots right src dst : ℕ)
    (hc : 0<c) (hr : 0<rows) (hd : c ∣ rows)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) :
    CompactNativeRoleOriginal.cost false (rows/c) c sh ell p rho lo count slots right src dst≤
      CompactNativeRoleOriginalBudget.constant c*volume rows sh ell p := by
  have h := CompactNativeRoleOriginalBudget.cost_linear false (rows/c) c sh ell p rho lo count slots
    right src dst hc (Nat.div_pos (Nat.le_of_dvd hr hd) hc) hA hG hK
  rw [Nat.div_mul_cancel hd] at h
  exact h

/-- Only the nonleaf branch executes this paid Original role split, on the
literal source-ready current child bank with rows unchanged. -/
theorem split_current_linear (w : Tapes (CompactComplexNonleafRoleChildBank.tapes s c) 2)
    (parentTarget n e : ℕ) (headerStack pcStack liveStack : Fin s) (site : Fin siteCount)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (coordinate : Fin arity) (rows ell p : ℕ)
    (hc : 0<c) (hr : 0<rows) (hd : c ∣ rows) (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p) :
    let bank := CompactComplexNonleafRoleChildBank.output w parentTarget n e headerStack pcStack liveStack site
      rho visit hactive pair coordinate rows ell p (CompactNativeRoleReservedBridge.sourcePayload sh rows ell f c)
    let stage := child rho visit hactive pair coordinate
    HoareTime (splitCurrentProgram s c) (fun z => z=bank)
      (fun z => z=Placement.replace CompactComplexNonleafRoleSplit.placement bank
        (CompactNativeRoleOriginal.bank (CompactComplexNativeCodec.raw stage rows ell p)
          (CompactNativeRoleReservedBridge.rolePayload sh rows c ell hd f)))
      (CompactNativeRoleOriginalBudget.constant c*volume rows sh ell p) := by
  have h := split_current_runs w parentTarget n e headerStack pcStack liveStack site
    rho visit hactive pair coordinate rows ell p hc hr hd hG hA hK f hw
  exact h.consequence (fun _ h => h) (fun _ h => h)
    (split_cost_linear c sh rows ell p (child rho visit hactive pair coordinate).rho
      (child rho visit hactive pair coordinate).left (child rho visit hactive pair coordinate).f
      (child rho visit hactive pair coordinate).slots (child rho visit hactive pair coordinate).right
      (child rho visit hactive pair coordinate).source.val (child rho visit hactive pair coordinate).target.val
      hc hr hd hG hA hK)

/-- At the actual descendant rows, the parent dependency Path discharges all
grouping and positivity premises of the paid physical current-child split. -/
theorem split_current_from_path_linear (w : Tapes (CompactComplexNonleafRoleChildBank.tapes s c) 2)
    (parentTarget n : ℕ) (headerStack pcStack liveStack : Fin s) (site : Fin siteCount)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (coordinate : Fin arity) (d K ell p : ℕ)
    (ledger : Ledger sh p n parentTarget left (k+2))
    (hc : 0<c) (hK : 0<K) (horiginal : sh.active≤d)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hchunk : 0<sh.chunk)
    (f : CompactSpectatorVisitGeometry.Array sh
      (CompactGlobalRowPadding.rowsAt c arity d K ledger.levels/c) ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p) :
    let rows := CompactGlobalRowPadding.rowsAt c arity d K ledger.levels/c
    let hd := (child_dimensions p n parentTarget d K ledger hc hK horiginal).2
    let bank := CompactComplexNonleafRoleChildBank.output w parentTarget n (k+2)
      headerStack pcStack liveStack site rho visit hactive pair coordinate rows ell p
      (CompactNativeRoleReservedBridge.sourcePayload sh rows ell f c)
    let stage := child rho visit hactive pair coordinate
    HoareTime (splitCurrentProgram s c) (fun z => z=bank)
      (fun z => z=Placement.replace CompactComplexNonleafRoleSplit.placement bank
        (CompactNativeRoleOriginal.bank (CompactComplexNativeCodec.raw stage rows ell p)
          (CompactNativeRoleReservedBridge.rolePayload sh rows c ell hd f)))
      (CompactNativeRoleOriginalBudget.constant c*volume rows sh ell p) :=
  split_current_linear w parentTarget n (k+2) headerStack pcStack liveStack site rho visit hactive pair
    coordinate _ ell p hc (child_dimensions p n parentTarget d K ledger hc hK horiginal).1
    (child_dimensions p n parentTarget d K ledger hc hK horiginal).2 hG hA hchunk f hw

end
end IntegerMultBounds.Machine.CompactComplexNonleafRolePreparationBudget
