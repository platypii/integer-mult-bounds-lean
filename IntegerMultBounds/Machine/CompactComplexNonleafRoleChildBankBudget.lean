import IntegerMultBounds.Machine.CompactComplexNonleafRoleChildBank
import IntegerMultBounds.Machine.CompactComplexNonleafRolePreparation
import IntegerMultBounds.Machine.CompactComplexDenominatorCapacity

/-! Complete physical child-bank entry costs from the original retained
geometry and a true denominator ledger on the actual parent dependency Path.
Target/live saves, geometry/PC frames, exponent descent, child metadata and all
joins are charged; no aggregate runtime or descriptor-length allowance is used. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleChildBankBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactRecursiveDependencyBudget (Path)
open CompactNativeRoleTransferBudget (volume)
open CompactComplexSpectatorVolumeHeaders (streamVolume)
open CompactComplexChildHeadersData (parent child schedule)
open CompactComplexNativeCodec (raw)
open RecursiveChildQuotientsConstant (bits)
open CompactComplexNonleafRoleChildBank
variable {sh : Shape} {left k : ℕ} {s c siteCount : ℕ}

/-- The actual parent's numerical precision invariant, including the pending
return target saved on targetStack9. Its Path is tied to that parent's geometry. -/
structure Ledger (sh : Shape) (p n target left exponent : ℕ) where
  R : ℕ
  baseline : ℕ
  levels : ℕ
  frames : ℕ
  returned : ℕ
  used : ℕ
  path : Path sh.active left exponent levels frames returned
  metadata : 2*sh.bits≤p
  base : baseline≤p-2*sh.bits
  room : CompactComplexDenominatorCapacity.room R≤sh.chunk
  used_le : used≤R
  live : n≤CompactComplexDenominatorCapacity.ledger R baseline levels frames returned used
  target_growth : target≤n+2*arity^exponent

theorem header_volumes (p n target left exponent rows ell : ℕ)
    (ledger : Ledger sh p n target left exponent) (hr : 0<rows) :
    n≤volume rows sh ell p ∧ target≤volume rows sh ell p := by
  have hn := CompactComplexDenominatorCapacity.target_volume ledger.path ledger.R ledger.baseline
    (p-2*sh.bits) ledger.used n n rows ell ledger.base ledger.used_le ledger.room ledger.live
    (Nat.le_add_right _ _) hr
  have ht := CompactComplexDenominatorCapacity.target_volume ledger.path ledger.R ledger.baseline
    (p-2*sh.bits) ledger.used n target rows ell ledger.base ledger.used_le ledger.room ledger.live
    ledger.target_growth hr
  have hv := CompactComplexSpectatorVolumeHeaders.volume_semantic sh 1 rows ell p false ledger.metadata
  change streamVolume sh 1 rows ell p false=ButterflySpectatorGeometry.Size rows sh.bits (2^ell)*
    (2*(CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)+2)) at hv
  rw [←hv] at hn ht
  constructor
  · simpa only [streamVolume,CompactComplexSpectatorVolumeHeaders.roleRows,Bool.false_eq_true,ite_false,
      volume,CompactNativeRoleOriginal.symbols,CompactNativeRoleOriginal.inner,
      CompactNativeRoleHeaders.recordWidth,Nat.mul_assoc] using hn
  · simpa only [streamVolume,CompactComplexSpectatorVolumeHeaders.roleRows,Bool.false_eq_true,ite_false,
      volume,CompactNativeRoleOriginal.symbols,CompactNativeRoleOriginal.inner,
      CompactNativeRoleHeaders.recordWidth,Nat.mul_assoc] using ht

theorem header_lengths (p n target left exponent rows ell : ℕ)
    (ledger : Ledger sh p n target left exponent) (hr : 0<rows) :
    (bits n).length≤volume rows sh ell p+1 ∧
      (bits target).length≤volume rows sh ell p+1 := by
  obtain ⟨hn, ht⟩ := header_volumes p n target left exponent rows ell ledger hr
  exact ⟨(ActiveRepairRankHeadersCommands.bits_length n).trans (by omega),
    (ActiveRepairRankHeadersCommands.bits_length target).trans (by omega)⟩

/-- Retained polynomial metadata does not add any reads to child geometry
arithmetic: its six consumed descriptors are the actual parent stage values. -/
theorem numeric_bound (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell p : ℕ) :
    CompactChildHeadersArithmetic.scheduleCost (schedule coordinate)
      (raw (parent rho visit hactive pair) rows ell p)≤
      CompactComplexChildHeadersUniform.constant*(sh.axes+1)^2 := by
  have hb := CompactComplexChildHeadersBudget.cost_le coordinate
    (raw (parent rho visit hactive pair) rows ell p)
    sh.active arity (arity^(k+1)) left (sh.active-(left+arity^(k+2)))
    rfl rfl rfl rfl rfl
  have hf := visit.fits
  have hpow : arity^(k+1)≤arity^(k+2) :=
    Nat.pow_le_pow_right (by decide : 0<arity) (by omega)
  have hw : arity^(k+1)≤sh.axes := by omega
  have hl : left≤sh.axes := by omega
  have hr : sh.active-(left+arity^(k+2))≤sh.axes := (Nat.sub_le _ _).trans hactive
  have hs := coordinate.isLt
  have hsum : sh.active+arity+arity^(k+1)+left+(sh.active-(left+arity^(k+2)))+
      coordinate.val+1≤(2*arity+5)*(sh.axes+1) := by nlinarith
  calc
    _ ≤ 100000*(sh.active+arity+arity^(k+1)+left+(sh.active-(left+arity^(k+2)))+
        coordinate.val+1)^2 := hb
    _ ≤ 100000*((2*arity+5)*(sh.axes+1))^2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 2)
    _ = _ := by unfold CompactComplexChildHeadersUniform.constant; ring

def coreConstant (siteCount : ℕ) :=
  CompactComplexChildHeadersUniform.constant+CompactComplexCallReturn.addressWidth siteCount arity+152

theorem core_bound (siteCount : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell p : ℕ) :
    coreCost siteCount (k+2) rho visit hactive pair coordinate rows ell p≤
      coreConstant siteCount*(sh.axes+1)^2 := by
  have hf := CompactComplexControllerChildBudget.frame_cost (parent rho visit hactive pair) hactive
  have he := CompactComplexControllerChildBudget.exponent_bound visit hactive
  have hn := numeric_bound rho visit hactive pair coordinate rows ell p
  have hs : sh.axes+1≤(sh.axes+1)^2 := by nlinarith
  have h1 : 1≤(sh.axes+1)^2 := by nlinarith
  have hW := Nat.mul_le_mul_left (CompactComplexCallReturn.addressWidth siteCount arity) h1
  unfold coreCost coreConstant
  nlinarith

def constant (siteCount : ℕ) := 4*coreConstant siteCount+33

theorem cost_linear (siteCount parentTarget n : ℕ) (rho : Fin sh.chunk)
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (coordinate : Fin arity) (rows ell p : ℕ)
    (ledger : Ledger sh p n parentTarget left (k+2)) (hr : 0<rows) (hG : 0<sh.guard) :
    cost siteCount parentTarget n (k+2) rho visit hactive pair coordinate rows ell p≤
      constant siteCount*volume rows sh ell p := by
  obtain ⟨hbn, hbt⟩ := header_lengths p n parentTarget left (k+2) rows ell ledger hr
  have hcore := core_bound siteCount rho visit hactive pair coordinate rows ell p
  have hsq := CompactComplexControllerChildBudget.dimension_square_le_volume (s:=sh) rows ell p hr (by omega)
  have hm := Nat.mul_le_mul_left (coreConstant siteCount) hsq
  have hV : 0<volume rows sh ell p := Nat.mul_pos hr
    (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  unfold cost constant
  nlinarith

/-- The complete actual child-entry program has the bound on its exact literal
endpoint, including target/live pushes and generated child metadata cleanup. -/
theorem runs_linear (v : Tapes (tapes s c) 2) (parentTarget n : ℕ)
    (headerStack pcStack liveStack : Fin s) (site : Fin siteCount)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell p : ℕ) (payload : Tapes (1+c) 2)
    (ledger : Ledger sh p n parentTarget left (k+2)) (hr : 0<rows) (hG : 0<sh.guard)
    (hi : Placement.active CompactComplexNonleafRoleSplit.placement v=
      CompactNativeRoleOriginal.bank (raw (parent rho visit hactive pair) rows ell p) payload)
    (hx : Placement.active exponentPlacement v=CompactComplexExponentStep.bank (k+2))
    (ht : v.tape target=BinaryDescriptorStack.descriptor (bits parentTarget)) (hh : v.head target=1)
    (hn : v.tape current=BinaryDescriptorStack.descriptor (bits n)) (hp : v.head current=1) :
    HoareTime (program (c:=c) headerStack pcStack liveStack site coordinate) (fun w => w=v)
      (fun w => w=output v parentTarget n (k+2) headerStack pcStack liveStack
        site rho visit hactive pair coordinate rows ell p payload)
      (constant siteCount*volume rows sh ell p) := by
  have h := runs v parentTarget n (k+2) (by omega) headerStack pcStack liveStack site
    rho visit hactive pair coordinate rows ell p payload hi hx ht hh hn hp
  exact h.consequence (fun _ h => h) (fun _ h => h)
    (cost_linear siteCount parentTarget n rho visit hactive pair coordinate rows ell p ledger hr hG)

/-- Source-ready child headers are paid by the parent's actual native volume;
this derives the comparison from the genuine row quotient, not an allowance. -/
theorem quotient_cost_linear (siteCount parentTarget n : ℕ) (rho : Fin sh.chunk)
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (coordinate : Fin arity) (rows ell p : ℕ)
    (ledger : Ledger sh p n parentTarget left (k+2)) (hr : 0<rows/c) (hG : 0<sh.guard) :
    cost siteCount parentTarget n (k+2) rho visit hactive pair coordinate (rows/c) ell p≤
      constant siteCount*volume rows sh ell p := by
  have h := cost_linear siteCount parentTarget n rho visit hactive pair coordinate (rows/c) ell p ledger hr hG
  have hv := Nat.mul_le_mul_right (CompactNativeRoleOriginal.symbols sh ell p) (Nat.div_le_self rows c)
  exact h.trans (Nat.mul_le_mul_left (constant siteCount) hv)

/-- The source-ready quotient endpoint supplies child-entry readiness from
the original caller's actual exponent, live7 and pending target8 descriptors. -/
theorem source_ready_from_parent_linear (selected : Fin c) (rho : Fin sh.chunk)
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (coordinate : Fin arity)
    (rows ell p : ℕ) (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (parentTarget n : ℕ) (headerStack pcStack liveStack : Fin s) (site : Fin siteCount)
    (ledger : Ledger sh p n parentTarget left (k+2)) (hr : 0<rows/c) (hG : 0<sh.guard)
    (hx : Placement.active exponentPlacement (v.append (SharedBank.empty 7 2))=
      CompactComplexExponentStep.bank (k+2))
    (ht : v.tape (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨8,by omega⟩)=
      BinaryDescriptorStack.descriptor (bits parentTarget))
    (hh : v.head (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨8,by omega⟩)=1)
    (hn : v.tape (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨7,by omega⟩)=
      BinaryDescriptorStack.descriptor (bits n))
    (hp : v.head (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨7,by omega⟩)=1) :
    HoareTime (program (c:=c) headerStack pcStack liveStack site coordinate)
      (fun w => w=CompactComplexNonleafRolePreparation.sourceReady
        selected rho visit hactive pair rows ell p f v)
      (fun w => w=output (CompactComplexNonleafRolePreparation.sourceReady
        selected rho visit hactive pair rows ell p f v) parentTarget n (k+2)
        headerStack pcStack liveStack site rho visit hactive pair coordinate (rows/c) ell p
        (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell f c))
      (constant siteCount*volume rows sh ell p) := by
  have h := CompactComplexNonleafRolePreparation.child_entry_from_parent_runs selected rho visit hactive
    pair coordinate rows ell p f v parentTarget n headerStack pcStack liveStack site hx ht hh hn hp
  exact h.consequence (fun _ h => h) (fun _ h => h)
    (quotient_cost_linear siteCount parentTarget n rho visit hactive pair coordinate rows ell p ledger hr hG)

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleChildBankBudget
