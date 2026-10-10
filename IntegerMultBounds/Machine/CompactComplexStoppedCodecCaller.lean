import IntegerMultBounds.Machine.CompactComplexNativeCodecFrame
import IntegerMultBounds.Machine.CompactComplexStoppedCallFrame
import IntegerMultBounds.Machine.SharedBankFrames

/-! Actual retained-original codec preparation, stopped child execution and
codec erasure form one fixed caller. The original13 child metadata, immutable
original scalar bank and all existing controller/stack tapes are restored. -/
namespace IntegerMultBounds.Machine.CompactComplexStoppedCodecCaller
noncomputable section
open CompactComplexRolePhaseSite (roleCount role)
open CompactComplexNativeCodecFrame (permanentTapes bank)
open CompactNativeRoleGuardedChildCaller (setRole resultWord)
open CompactComplexRecursiveGeometry
open CompactRecursiveDependencyBudget (Path)
open Networks.ComplexRecursiveCallSchema (Call)
open SharedPlacementAlphabet (setTape)
variable {s c : ℕ}
attribute [local irreducible] Networks.ComplexPhaseBudget.edges

/-- The selected role output preserves the actual source word/head; it is
exactly the bank consumed by codec erasure, with every other role retained. -/
theorem bank_setRole (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes s 2) (payload : Tapes (1+c) 2) (j : Fin c) (g : ℤ → Fin 6) :
    bank control queue scalar stage tail storage (setRole payload j g)=
      setTape (bank control queue scalar stage tail storage payload)
        (CompactComplexNativeRoleBridge.roleSlot j) g 0 := by
  have h0 : (0 : Fin (1+c))≠Fin.natAdd 1 j := by
    intro h;have hv := congrArg Fin.val h;simp only [Fin.val_natAdd,Fin.val_zero] at hv;omega
  have hs : CompactComplexNativeRoleBridge.single (setRole payload j g)=
      CompactComplexNativeRoleBridge.single payload := by
    apply congrArg₂ Tapes.mk <;> funext i
    all_goals simp only [setRole,setTape,Function.update_of_ne h0]
  have hr : CompactNativeRoleSourcePorts.roles (setRole payload j g)=
      setTape (CompactNativeRoleSourcePorts.roles payload) j g 0 := by
    apply congrArg₂ Tapes.mk <;> funext i
    all_goals have he : (⟨i.val+1,by omega⟩ : Fin (1+c))=Fin.natAdd 1 i := Fin.ext (by simp only [Fin.val_natAdd];omega)
    all_goals simp [CompactNativeRoleSourcePorts.roles,he,setRole,setTape,Function.update]
  unfold bank CompactComplexNativeRoleBridge.bank CompactComplexNativeRoleBridge.native
    CompactComplexNativeRoleBridge.roleSlot
  rw [SharedPlacementAlphabet.setTape_append_right,hr,hs]

abbrev publicTapes (s : ℕ) := permanentTapes s roleCount
abbrev childTapes (s : ℕ) := CompactComplexStoppedCallFrame.tapes (s+43)
abbrev tapes (s : ℕ) := (publicTapes s+86)+childTapes s

def childProgram (s : ℕ) (call : Call) :=
  Placement.placed (CompactComplexStoppedCallFrame.program (s+43) call)
    (CleanSubbank.placement (Fin.castAdd CompactComplexStoppedCallFrame.privateTapes)
      (Fin.castAdd 86 : Fin (publicTapes s) → Fin (publicTapes s+86)) (Fin.castAdd_injective _ _))

def program (m s : ℕ) (call : Call) :=
  seq (seq (extend (CompactComplexNativeCodecFrame.program roleCount m s) (childTapes s))
    (childProgram s call))
    (extend (CompactComplexNativeCodecFrame.cleanupProgram s roleCount) (childTapes s))

def ready (v : Tapes (publicTapes s) 2) : Tapes (tapes s) 2 :=
  (v.append (SharedBank.empty 86 2)).append (SharedBank.empty (childTapes s) 2)

/-- A proved actual stopped run borrows only permanent tapes and its private
workspace; the already cleaned codec workspace is retained literally. -/
private theorem child_runs (call : Call) (v w : Tapes (publicTapes s) 2) (time : ℕ)
    (h : HoareTime (CompactComplexStoppedCallFrame.program (s+43) call)
      (fun z => z=CleanSubbank.bank (s:=CompactComplexStoppedCallFrame.privateTapes) v)
      (fun z => z=CleanSubbank.bank (s:=CompactComplexStoppedCallFrame.privateTapes) w) time) :
    HoareTime (childProgram s call) (fun z => z=ready v) (fun z => z=ready w) time := by
  apply CleanSubbank.realizes _ (Fin.castAdd CompactComplexStoppedCallFrame.privateTapes)
    (Fin.castAdd 86) (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _)
    (v.append (SharedBank.empty 86 2)) (w.append (SharedBank.empty 86 2)) _ _ _
    ?_ ?_ (CleanSubbank.strip_bank _) (CleanSubbank.strip_bank _) ?_ h
  · rw [CleanSubbank.payload_bank]
    exact (CleanSubbank.payload_bank v).symm
  · rw [CleanSubbank.payload_bank]
    exact (CleanSubbank.payload_bank w).symm
  · change SharedBank.strip (v.append (SharedBank.empty 86 2)) (fun i => Fin.castAdd 86 (id i))=
      SharedBank.strip (w.append (SharedBank.empty 86 2)) (fun i => Fin.castAdd 86 (id i))
    rw [SharedBankFrames.strip_append_left,SharedBankFrames.strip_append_left,
      SharedBankFrames.strip_identity,SharedBankFrames.strip_identity]

def constant (m : ℕ) := CompactReservationPaddingHeaderBudget.constant roleCount m+5000+
  2*CompactNativeRoleStoppedChildBudget.constant roleCount+2

/-- A single fixed caller physically prepares from original descriptors,
executes the actual stopped Call and restores the initial13 child metadata.
The true selected role output survives both cleanups; no phase callback exists. -/
theorem actual_runs (m d D G K0 ell q level : ℕ) (hm : 2≤m)
    (hDd : D≤d) (hd : 0<d) (hG : 0<G) (hK : 0<K0) (hDp : 0<D)
    (hD : CompactGlobalReservation.reservedAxes roleCount m d G K0≤D)
    (hj : level<CompactGlobalRowPadding.depth m d)
    (rho : Fin (CompactReservationNativeRows.shape roleCount m d D G K0).chunk)
    {left k levels frames returned : ℕ}
    (path : Path (CompactReservationNativeRows.shape roleCount m d D G K0).active
      left (k+2) levels frames returned)
    (hstop : Networks.ComplexRecursiveCallSchema.stopped d (k+1)=true)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Call)
    (control : Tapes 43 2) (queue : Tapes 1 2) (tail : Tapes 22 2) (storage : Tapes s 2)
    (f : CompactSpectatorVisitGeometry.Array (CompactReservationNativeRows.shape roleCount m d D G K0)
      (CompactGlobalRowPadding.rowsAt roleCount m d K0 level) ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth
      (CompactReservationNativeRows.shape roleCount m d D G K0)
      (CompactNativeRoleReservedBridge.precision roleCount m d D K0 q) ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth
      (CompactReservationNativeRows.shape roleCount m d D G K0)
      (CompactNativeRoleReservedBridge.precision roleCount m d D K0 q)) :
    let sh := CompactReservationNativeRows.shape roleCount m d D G K0
    let rows := CompactGlobalRowPadding.rowsAt roleCount m d K0 level
    let p := CompactNativeRoleReservedBridge.precision roleCount m d D K0 q
    let ha := CompactNativeRoleStoppedChildBudget.actual_active roleCount m d D G K0 hDd
    let child := CompactComplexChildHeadersData.child rho path.visit ha pair call.slot
    let scalar := CompactReservedHeaders.initial D K0 rho.val ell q d G
    ∃ (hdiv : roleCount∣rows) (time : ℕ),
      let payload := CompactNativeRoleReservedBridge.rolePayload sh rows roleCount ell hdiv f
      let g := resultWord (CompactComplexStoppedCallSite.direction call) sh rows roleCount ell p rho
        (Visit.child path.visit call.slot) hdiv f (role call.site)
      HoareTime (program m s call)
        (fun z => z=ready (bank control queue scalar (ActivePrefixStageHeadersData.initial child rows) tail storage payload))
        (fun z => z=ready (bank control queue scalar (ActivePrefixStageHeadersData.initial child rows) tail storage
          (setRole payload (role call.site) g))) time ∧
      time≤constant m*CompactFallbackAxisRun.volume D K0 ell q*(arity^(k+1)) := by
  dsimp only
  let sh := CompactReservationNativeRows.shape roleCount m d D G K0
  let rows := CompactGlobalRowPadding.rowsAt roleCount m d K0 level
  let p := CompactNativeRoleReservedBridge.precision roleCount m d D K0 q
  let ha := CompactNativeRoleStoppedChildBudget.actual_active roleCount m d D G K0 hDd
  let child := CompactComplexChildHeadersData.child rho path.visit ha pair call.slot
  let scalar := CompactReservedHeaders.initial D K0 rho.val ell q d G
  obtain ⟨hdiv,childTime,_,hc,hbound,_⟩ := CompactComplexStoppedCallFrame.actual_runs m d D G K0 ell q level
    hDd hd hG hK hD hj rho path hstop pair call control queue tail
    (storage.append (ActiveRepairRankHeadersCommands.bank scalar)) f hw
  let payload := CompactNativeRoleReservedBridge.rolePayload sh rows roleCount ell hdiv f
  let g := resultWord (CompactComplexStoppedCallSite.direction call) sh rows roleCount ell p rho
    (Visit.child path.visit call.slot) hdiv f (role call.site)
  have hrow : CompactGlobalRowPadding.rowAxes roleCount m d≤D := by
    unfold CompactGlobalReservation.reservedAxes at hD;omega
  have hprepare := hoare_extend_eq (CompactComplexNativeCodecFrame.prepare_runs roleCount m D K0 rho.val ell q d G
    (by decide) hm hd hK hrow hDp child rows control queue tail storage payload)
    (SharedBank.empty (childTapes s) 2)
  have hraw := CompactComplexNativeCodecFrame.raw_child rho path.visit ha pair call.slot rows ell p
  have hchild := child_runs call _ _ childTime hc
  have hcleanup := hoare_extend_eq (CompactComplexNativeCodecFrame.cleanup_runs scalar child rows ell p
    control queue tail storage (setRole payload (role call.site) g)) (SharedBank.empty (childTapes s) 2)
  rw [hraw] at hprepare hcleanup
  have hout := bank_setRole control queue scalar
    (CompactNativeRoleStoppedChildCaller.nodeState sh rows ell p rho (Visit.child path.visit call.slot) ha pair)
    tail storage payload (role call.site) g
  have hchild' := hchild.consequence (fun _ h => h)
    (fun _ h => h.trans (congrArg ready hout.symm)) le_rfl
  have hrun := (hprepare.seq hchild').seq hcleanup
  refine ⟨hdiv,_,hrun,?_⟩
  have hlife := CompactComplexNativeCodec.lifecycle_linear roleCount m D K0 rho.val ell q d G
    (by decide) hm hd hG hK hD
  have hN : 0<arity^(k+1) := pow_pos (by decide) _
  have hV : 0<CompactFallbackAxisRun.volume D K0 ell q :=
    ButterflyAxisHeadersInstall.volume_pos _ _ _ (pow_pos (by decide) ell)
  have hlift := Nat.le_mul_of_pos_right
    (CompactComplexNativeCodec.prepareCost roleCount m D K0 rho.val ell q d G+
      CompactComplexNativeCodec.cleanupCost ell p) hN
  have hscale := Nat.mul_le_mul_right (arity^(k+1)) hlife
  have hVN := Nat.mul_pos hV hN
  dsimp only [p] at hlift ⊢
  unfold constant
  simp only [Nat.add_mul,Nat.mul_assoc] at hscale hlift hbound ⊢
  omega

end
end IntegerMultBounds.Machine.CompactComplexStoppedCodecCaller
