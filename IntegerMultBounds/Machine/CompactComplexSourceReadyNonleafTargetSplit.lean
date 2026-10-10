import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafTarget
import IntegerMultBounds.Machine.CompactComplexNonleafRolePreparationBudget
import IntegerMultBounds.Machine.CompactComplexSourceReadyScalarWorkspace

/-! Actual tag2 body: synthesize the original full-node return target before
splitting the current rows. The split retains the stored target literally. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafTargetSplit
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexSourceReadyWorkspace (publicTapes ready publicProgram)
open CompactComplexSourceReadyNonleafTarget (targeted)
open CompactComplexNonleafRoleSourceReturn (base)
open CompactComplexNonleafRoleEntry (headerPlacement)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}
attribute [local irreducible] CompactComplexNonleafRolePreparation.splitCurrentProgram
  CompactComplexSourceReadyNonleafTarget.program CompactNativeRoleOriginal.splitProgram
  ButterflyAxisHeadersArithmetic.compile

def splitProgram : Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s c) q 2 :=
  ⟨_,publicProgram (Placement.placed (CompactNativeRoleOriginal.splitProgram c)
    (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c)))⟩
def program : Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s c) q 2 :=
  ⟨_,seq (CompactComplexSourceReadyNonleafTarget.program (s:=s) (c:=c)) (splitProgram (s:=s) (c:=c)).2⟩
def constant (c : ℕ) := CompactComplexSourceReadyNonleafTarget.constant+CompactNativeRoleOriginalBudget.constant c+1

private theorem target_outside (i : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    CompactComplexNonleafRoleSplit.slot (s:=10+s) (c:=c) i≠CompactComplexNonleafRoleChildBank.target := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [CompactComplexNonleafRoleSplit.slot,CompactComplexNonleafRoleChildBank.target,
    CompactComplexNonleafRoleChildBank.storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  unfold CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at hv
  split_ifs at hv <;> omega

theorem active_targeted (v : Tapes (publicTapes s c) 2) (n : ℕ) :
    Placement.active CompactComplexNonleafRoleSplit.placement (targeted v n)=
      Placement.active CompactComplexNonleafRoleSplit.placement v := by
  simp only [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [targeted,SharedPlacementAlphabet.setTape,Function.update_of_ne (target_outside i)]

theorem runs_native_linear (sh : Shape) (rows ell p : ℕ)
    (rho : Fin sh.chunk) (left k right src dst n : ℕ)
    (v : Tapes (publicTapes s c) 2)
    (hraw : Placement.active headerPlacement (base v)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) arity right src dst))
    (hn : v.head CompactComplexNonleafRoleChildBank.current=1 ∧
      v.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits n))
    (ht : v.head CompactComplexNonleafRoleChildBank.target=0 ∧
      v.tape CompactComplexNonleafRoleChildBank.target=fun _ => blank)
    (hc : 0<c) (hr : 0<rows) (hd : c ∣ rows)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hP : 2*sh.bits≤p)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hi : Placement.active CompactComplexNonleafRoleSplit.placement v=
      CompactNativeRoleOriginal.bank
        (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) arity right src dst)
        (CompactNativeRoleReservedBridge.sourcePayload sh rows ell f c))
    {levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left (k+1) levels frames returned)
    (R baseline usedRows : ℕ) (hb : baseline≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : n≤CompactComplexDenominatorCapacity.ledger R baseline levels frames returned usedRows) :
    HoareTime (program (s:=s) (c:=c)).2 (fun z => z=ready v)
      (fun z => z=ready (Placement.replace CompactComplexNonleafRoleSplit.placement
        (targeted v (n+2*arity^(k+1)))
        (CompactNativeRoleOriginal.bank
          (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) arity right src dst)
          (CompactNativeRoleReservedBridge.rolePayload sh rows c ell hd f))))
      (constant c*CompactNativeRoleTransferBudget.volume rows sh ell p) := by
  have htarg := CompactComplexSourceReadyNonleafTarget.runs sh rows ell p rho.val left k right src dst n v hraw hn ht
  have hsplit := CompactNativeRoleReservedBridge.splits sh rows c ell p rho.val left (arity^k) arity right src dst
    hc hr hd hG hA hK f hw
  have hplaced := Placement.hoare_at hsplit CompactComplexNonleafRoleSplit.placement
    (targeted v (n+2*arity^(k+1))) ((active_targeted _ _).trans hi)
  have hplaced' := hplaced.consequence (post' := fun z => z=Placement.replace
    CompactComplexNonleafRoleSplit.placement (targeted v (n+2*arity^(k+1)))
    (CompactNativeRoleOriginal.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) arity right src dst)
      (CompactNativeRoleReservedBridge.rolePayload sh rows c ell hd f)))
    (fun _ h => h) (by rintro z ⟨a,rfl,rfl⟩; rfl) le_rfl
  have hready := CompactComplexSourceReadyWorkspace.public_ready_runs hplaced'
  change HoareTime (splitProgram (s:=s) (c:=c)).2 _ _ _ at hready
  have hseq := htarg.seq hready
  have htbound := CompactComplexSourceReadyNonleafTarget.cost_native path rows ell p rho right src dst n R baseline usedRows
    hr hK hP hb hu hroom hlive
  have hsbound := CompactComplexNonleafRolePreparationBudget.split_cost_linear c sh rows ell p rho.val left
    (arity^k) arity right src dst hc hr hd hG hA hK
  have hV : 0<CompactNativeRoleTransferBudget.volume rows sh ell p :=
    Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  exact hseq.consequence (fun _ h => h) (fun _ h => h) (by unfold constant; nlinarith)

/-- The same actual setup block on the scalar-inclusive fixed bank. -/
def fullProgram : Σ q,Program (CompactComplexSourceReadyScalarWorkspace.tapes s c) q 2 :=
  ⟨(program (s:=s) (c:=c)).1,
    extend (program (s:=s) (c:=c)).2 CompactComplexSourceReadyScalarWorkspace.scratch⟩

/-- Physical setup retains every cell and head of an arbitrary scalar suffix. -/
theorem widen_runs {v w : Tapes (CompactComplexSourceReadyWorkspace.tapes s c) 2} {B : ℕ}
    (h : HoareTime (program (s:=s) (c:=c)).2 (fun z => z=v) (fun z => z=w) B)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2) :
    HoareTime (fullProgram (s:=s) (c:=c)).2
      (fun z => z=v.append scalar) (fun z => z=w.append scalar) B :=
  hoare_extend_eq h scalar

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafTargetSplit
