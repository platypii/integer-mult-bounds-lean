import IntegerMultBounds.Machine.CompactComplexControllerChildStopTarget
import IntegerMultBounds.Machine.CompactComplexControllerDenominatorEntry
import IntegerMultBounds.Machine.CompactComplexStoppedCodecCaller

/-! Stopped calls on the permanent bank, with actual runtime target selection,
physical entry, codec lifecycle and exact stack restoration. The old common
live denominator is retained until the untouched roles have been promoted. -/
namespace IntegerMultBounds.Machine.CompactComplexStoppedLedgerRoundtrip
noncomputable section
open CompactComplexRolePhaseSite (roleCount role)
open CompactComplexRecursiveGeometry
open CompactRecursiveDependencyBudget (Path)
open Networks.ComplexRecursiveCallSchema (Call)
open SharedPlacementAlphabet (setTape)
open ActiveRepairRankHeadersCommands (State put)
open RecursiveChildQuotientsConstant (bits)
variable {s : ℕ}
attribute [local irreducible] Networks.ComplexPhaseBudget.edges CompactComplexStopThreshold.base

abbrev rootTapes (s : ℕ) := CompactComplexControllerDenominator.size (s+43)
abbrev baseTapes (s : ℕ) := CompactComplexStoppedCodecCaller.tapes (10+s)
abbrev privateTapes (s : ℕ) := CompactComplexControllerChildStopTarget.total (s+43)
abbrev tapes (s : ℕ) := baseTapes s+privateTapes s

def rootReady (v : Tapes (rootTapes s) 2) (roles : Tapes roleCount 2) : Tapes (baseTapes s) 2 :=
  ((v.append roles).append (SharedBank.empty 86 2)).append
    (SharedBank.empty (CompactComplexStoppedCodecCaller.childTapes (10+s)) 2)
def ready (v : Tapes (CompactComplexStoppedCodecCaller.publicTapes (10+s)) 2) : Tapes (tapes s) 2 :=
  (CompactComplexStoppedCodecCaller.ready v).append (SharedBank.empty (privateTapes s) 2)
def rootSlots (i : Fin (rootTapes s)) : Fin (baseTapes s) :=
  Fin.castAdd (CompactComplexStoppedCodecCaller.childTapes (10+s))
    (Fin.castAdd 86 (Fin.castAdd roleCount i))
private theorem rootSlots_injective : Function.Injective (rootSlots (s:=s)) :=
  (Fin.castAdd_injective _ _).comp ((Fin.castAdd_injective _ _).comp (Fin.castAdd_injective _ _))

def rootProgram {q : ℕ} (M : Program (rootTapes s) q 2) :=
  extend (extend (extend (extend M roleCount) 86)
    (CompactComplexStoppedCodecCaller.childTapes (10+s))) (privateTapes s)
private theorem root_runs {q time : ℕ} (M : Program (rootTapes s) q 2)
    (v w : Tapes (rootTapes s) 2) (roles : Tapes roleCount 2)
    (h : HoareTime M (fun z => z=v) (fun z => z=w) time) :
    HoareTime (rootProgram M)
      (fun z => z=(rootReady v roles).append (SharedBank.empty (privateTapes s) 2))
      (fun z => z=(rootReady w roles).append (SharedBank.empty (privateTapes s) 2)) time :=
  hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq h roles)
    (SharedBank.empty 86 2))
    (SharedBank.empty (CompactComplexStoppedCodecCaller.childTapes (10+s)) 2))
    (SharedBank.empty (privateTapes s) 2)

private theorem root_payload (v : Tapes (rootTapes s) 2) (roles : Tapes roleCount 2) :
    SharedBank.payload (rootReady v roles) rootSlots=v := by
  unfold rootReady rootSlots
  rw [SharedBankFrames.payload_append_left,SharedBankFrames.payload_append_left]
  change SharedBank.payload (v.append roles) (fun i => Fin.castAdd roleCount (id i))=v
  rw [SharedBankFrames.payload_append_left,SharedBankFrames.payload_identity]
private theorem root_strip (v w : Tapes (rootTapes s) 2) (roles : Tapes roleCount 2) :
    SharedBank.strip (rootReady v roles) rootSlots=SharedBank.strip (rootReady w roles) rootSlots := by
  unfold rootReady rootSlots
  rw [SharedBankFrames.strip_append_left,SharedBankFrames.strip_append_left,
    SharedBankFrames.strip_append_left,SharedBankFrames.strip_append_left,
    ]
  change ((SharedBank.strip (v.append roles) (fun i => Fin.castAdd roleCount (id i))).append _).append _=
    ((SharedBank.strip (w.append roles) (fun i => Fin.castAdd roleCount (id i))).append _).append _
  rw [SharedBankFrames.strip_append_left,SharedBankFrames.strip_append_left,
    SharedBankFrames.strip_identity,SharedBankFrames.strip_identity]

private theorem stop_bank (v : Tapes (rootTapes s) 2) :
    CompactComplexControllerChildStopTarget.bank v (SharedBank.empty 10 2)=
      CleanSubbank.bank (s:=10) v := by
  unfold CompactComplexControllerChildStopTarget.bank ContiguousBankPlacement.bank CleanSubbank.bank
  rw [SharedBankFrames.empty_append]


def targetProgram (s : ℕ) := Placement.placed
  (CompactComplexControllerChildStopTarget.program (s:=s+43))
  (CleanSubbank.placement (Fin.castAdd 10) rootSlots rootSlots_injective)
private theorem target_runs (v w : Tapes (rootTapes s) 2) (roles : Tapes roleCount 2) (time : ℕ)
    (h : HoareTime (CompactComplexControllerChildStopTarget.program (s:=s+43))
      (fun z => z=CompactComplexControllerChildStopTarget.bank v (SharedBank.empty 10 2))
      (fun z => z=CompactComplexControllerChildStopTarget.bank w (SharedBank.empty 10 2)) time) :
    HoareTime (targetProgram s)
      (fun z => z=(rootReady v roles).append (SharedBank.empty (privateTapes s) 2))
      (fun z => z=(rootReady w roles).append (SharedBank.empty (privateTapes s) 2)) time := by
  rw [stop_bank,stop_bank] at h
  apply CleanSubbank.realizes _ (Fin.castAdd 10) rootSlots (Fin.castAdd_injective _ _)
    rootSlots_injective _ _ _ _ _ ?_ ?_ (CleanSubbank.strip_bank _) (CleanSubbank.strip_bank _)
    (root_strip v w roles) h
  · rw [CleanSubbank.payload_bank,root_payload]
  · rw [CleanSubbank.payload_bank,root_payload]

/-- Physically pop the saved occurrence/coordinate using the real binary
return dispatcher. Its fixed continuation halts immediately. -/
def pcProgram {siteCount : ℕ} (stack : Fin (10+(s+43))) :=
  (CompactComplexControllerReturnStack.dispatcher (siteCount:=siteCount) (base:=arity) stack
    (fun _ => 1) (fun _ => skip (rootTapes s) 2 (by unfold rootTapes CompactComplexControllerDenominator.size CompactComplexControllerNativeFrame.tapes; omega))).2
private theorem pc_runs {siteCount : ℕ} (stack : Fin (10+(s+43)))
    (site : Fin siteCount) (slot : Fin arity) (control : Tapes 43 2) (queue : Tapes 1 2)
    (native : Tapes 66 2) (storage : Tapes (10+(s+43)) 2)
    (hb : ∀ j<CompactComplexCallReturn.addressWidth siteCount arity,
      storage.tape stack (storage.head stack+j)=blank) :
    HoareTime (pcProgram (s:=s) (siteCount:=siteCount) stack)
      (fun z => z=CompactComplexControllerNativeFrame.bank control queue native
        (CompactComplexControllerReturnStack.saved storage stack site slot))
      (fun z => z=CompactComplexControllerNativeFrame.bank control queue native storage)
      (CompactComplexCallReturn.addressWidth siteCount arity+2) := by
  exact CompactComplexControllerReturnStack.dispatch stack _ _ site slot control queue native storage 0 _ hb
    (skip_hoare _ _)

/-- The target port is installed on the old ledger; it never denotes a new
common precision before the spectator-family execution. -/
def targeted (storage : Tapes (10+s) 2) (n : ℕ) :=
  setTape storage (⟨8,by omega⟩ : Fin (10+s)) (RadixZeroFill.encodedBinary (bits n)) 1
/-- Every old ledger/stack tape except the pending target survives exactly. -/
theorem targeted_frame (storage : Tapes (10+s) 2) (n : ℕ) (i : Fin (10+s))
    (hi : i≠⟨8,by omega⟩) :
    (targeted storage n).head i=storage.head i ∧ (targeted storage n).tape i=storage.tape i := by
  simp only [targeted,setTape,Function.update_of_ne hi,and_self]
theorem targeted_ready (storage : Tapes (10+s) 2) (n : ℕ) :
    (targeted storage n).head ⟨8,by omega⟩=1 ∧
      (targeted storage n).tape ⟨8,by omega⟩=RadixZeroFill.encodedBinary (bits n) := by
  simp only [targeted,setTape,Function.update_self,and_self]
theorem live_frame (storage : Tapes (10+s) 2) (n : ℕ) :
    (targeted storage n).head ⟨7,by omega⟩=storage.head ⟨7,by omega⟩ ∧
      (targeted storage n).tape ⟨7,by omega⟩=storage.tape ⟨7,by omega⟩ :=
  targeted_frame storage n _ (by intro h;have hv := congrArg Fin.val h;norm_num at hv)

private theorem targeted_append (storage : Tapes (10+s) 2) (scalar : Tapes 43 2) (n : ℕ) :
    targeted (s:=s+43) (storage.append scalar) n=(targeted storage n).append scalar := by
  change setTape (storage.append scalar) (Fin.castAdd 43 (⟨8,by omega⟩ : Fin (10+s))) _ _=_
  exact SharedPlacementAlphabet.setTape_append_left _ _ _ _ _
private theorem targets_append (storage : Tapes (10+s) 2) (scalar : Tapes 43 2) (n : ℕ) :
    CompactComplexControllerDenominatorEntry.targets (s:=s+43) (storage.append scalar) n=
      (CompactComplexControllerDenominatorEntry.targets storage n).append scalar := by
  have ht : (storage.append scalar).tape (⟨9,by omega⟩ : Fin (10+(s+43)))=storage.tape ⟨9,by omega⟩ := by
    change (storage.append scalar).tape (Fin.castAdd 43 (⟨9,by omega⟩ : Fin (10+s)))=_
    simp only [Tapes.append,Fin.addCases_left]
  have hh : (storage.append scalar).head (⟨9,by omega⟩ : Fin (10+(s+43)))=storage.head ⟨9,by omega⟩ := by
    change (storage.append scalar).head (Fin.castAdd 43 (⟨9,by omega⟩ : Fin (10+s)))=_
    simp only [Tapes.append,Fin.addCases_left]
  unfold CompactComplexControllerDenominatorEntry.targets
  rw [ht,hh]
  change setTape (setTape (storage.append scalar) (Fin.castAdd 43 (⟨9,by omega⟩ : Fin (10+s)))
    _ _) (Fin.castAdd 43 (⟨8,by omega⟩ : Fin (10+s))) _ _=_
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left]
private theorem header_append (storage : Tapes (10+s) 2) (scalar : Tapes 43 2)
    (stack : Fin (10+s)) (data : Fin 3 → List Bool) :
    CompactComplexControllerHeaderStack.saved (storage.append scalar) (Fin.castAdd 43 stack) data=
      (CompactComplexControllerHeaderStack.saved storage stack data).append scalar := by
  unfold CompactComplexControllerHeaderStack.saved
  rw [SharedPlacementAlphabet.setTape_append_left]
  simp only [Tapes.append,Fin.addCases_left]
private theorem pc_append {siteCount : ℕ} (storage : Tapes (10+s) 2) (scalar : Tapes 43 2)
    (stack : Fin (10+s)) (site : Fin siteCount) (slot : Fin arity) :
    CompactComplexControllerReturnStack.saved (storage.append scalar) (Fin.castAdd 43 stack) site slot=
      (CompactComplexControllerReturnStack.saved storage stack site slot).append scalar := by
  unfold CompactComplexControllerReturnStack.saved
  rw [SharedPlacementAlphabet.setTape_append_left]
  simp only [Tapes.append,Fin.addCases_left]

private theorem old_ne (i : Fin s) (j : ℕ) (hj : j<10) :
    Fin.natAdd 10 i≠(⟨j,by omega⟩ : Fin (10+s)) := by
  intro h;have hv := congrArg Fin.val h;simp only [Fin.val_natAdd] at hv;omega
private theorem restored_target (storage : Tapes (10+s) 2) (n : ℕ) :
    CompactComplexControllerDenominatorEntry.restored
      (CompactComplexControllerDenominatorEntry.targets (targeted storage n) n)
      (storage.tape ⟨9,by omega⟩) (storage.head ⟨9,by omega⟩) n=targeted storage n := by
  unfold CompactComplexControllerDenominatorEntry.restored
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases h8 : i=(⟨8,by omega⟩ : Fin (10+s))
  all_goals first | subst i; simp [CompactComplexControllerDenominatorEntry.targets,targeted,setTape,
      BinaryDescriptorStackRoundtrip.descriptor_encoded] |
    by_cases h9 : i=(⟨9,by omega⟩ : Fin (10+s))
  all_goals first | subst i; simp [CompactComplexControllerDenominatorEntry.targets,targeted,setTape] |
    simp [CompactComplexControllerDenominatorEntry.targets,targeted,setTape,h8,h9]
private theorem restored_append (storage : Tapes (10+s) 2) (scalar : Tapes 43 2)
    (f : ℤ → Fin 6) (p : ℤ) (n : ℕ) :
    CompactComplexControllerDenominatorEntry.restored (s:=s+43) (storage.append scalar) f p n=
      (CompactComplexControllerDenominatorEntry.restored storage f p n).append scalar := by
  unfold CompactComplexControllerDenominatorEntry.restored
  change setTape (setTape (storage.append scalar) (Fin.castAdd 43 (⟨9,by omega⟩ : Fin (10+s)))
    _ _) (Fin.castAdd 43 (⟨8,by omega⟩ : Fin (10+s))) _ _=_
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left]

private theorem stack_cast (i : Fin s) :
    Fin.natAdd 10 (Fin.castAdd 43 i)=Fin.castAdd 43 (Fin.natAdd 10 i) := Fin.ext rfl

private theorem saved_append {siteCount : ℕ} {sh : CompactGadgetReservationShape.Shape}
    (storage : Tapes (10+s) 2) (scalar : Tapes 43 2) (headerStack pcStack : Fin s)
    (site : Fin siteCount) (slot : Fin arity) (parent : ActivePrefixStageParameters.Stage sh) :
    CompactComplexControllerChildPrefix.saved (storage.append scalar)
      (Fin.natAdd 10 (Fin.castAdd 43 headerStack)) (Fin.natAdd 10 (Fin.castAdd 43 pcStack)) site slot parent=
      (CompactComplexControllerChildPrefix.saved storage (Fin.natAdd 10 headerStack)
        (Fin.natAdd 10 pcStack) site slot parent).append scalar := by
  unfold CompactComplexControllerChildPrefix.saved
  rw [stack_cast headerStack,stack_cast pcStack,header_append,pc_append]

def returnProgram (headerStack pcStack : Fin s) := seq
  (pcProgram (siteCount:=Networks.ComplexRecursiveCallSchema.sites.length)
    (Fin.natAdd 10 (Fin.castAdd 43 pcStack)))
  (CompactComplexControllerDenominatorEntry.returnProgram (Fin.castAdd 43 headerStack))

/-- Restore the real saved PC, parent geometry and semantic target, leaving
both original stack tails and the old live exponent literally unchanged. -/
theorem return_runs {sh : CompactGadgetReservationShape.Shape} (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left (k+2)) (ha : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Call) (rows : ℕ)
    (headerStack pcStack : Fin s) (hne : pcStack≠headerStack) (st : State) (h1 : st 1=some (k+2))
    (queue : Tapes 1 2) (tail : Tapes 23 2) (storage : Tapes (10+s) 2) (scalar : Tapes 43 2) (targetN : ℕ)
    (hbH : ∀ z,storage.head (Fin.natAdd 10 headerStack)≤z → storage.tape (Fin.natAdd 10 headerStack) z=blank)
    (hbP : ∀ j<CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length arity,
      storage.tape (Fin.natAdd 10 pcStack) (storage.head (Fin.natAdd 10 pcStack)+j)=blank)
    (hb9 : ∀ z,storage.head ⟨9,by omega⟩≤z → z<storage.head ⟨9,by omega⟩+1+(bits targetN).length →
      storage.tape ⟨9,by omega⟩ z=blank) :
    let parent := CompactComplexChildHeadersData.parent rho visit ha pair
    let stores := CompactComplexControllerDenominatorEntry.targets (targeted storage targetN) targetN
    HoareTime (returnProgram headerStack pcStack)
      (fun z => z=CompactComplexControllerNativeFrame.bank (ActiveRepairRankHeadersCommands.bank (put st 1 (k+1))) queue
        (CompactComplexControllerChildPrefix.native (CompactComplexChildHeadersData.child rho visit ha pair call.slot) rows tail)
        ((CompactComplexControllerChildPrefix.saved stores (Fin.natAdd 10 headerStack) (Fin.natAdd 10 pcStack)
          call.site call.slot parent).append scalar))
      (fun z => z=CompactComplexControllerNativeFrame.bank (ActiveRepairRankHeadersCommands.bank st) queue
        (CompactComplexControllerChildPrefix.native parent rows tail) ((targeted storage targetN).append scalar))
      (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length arity+3+
        (CompactComplexControllerChildBudget.returnCost rho visit ha pair call.slot+2*(bits targetN).length+8)) := by
  dsimp only
  let parent := CompactComplexChildHeadersData.parent rho visit ha pair
  let stores := CompactComplexControllerDenominatorEntry.targets (targeted storage targetN) targetN
  let headers := CompactComplexControllerHeaderStack.saved stores (Fin.natAdd 10 headerStack)
    (CompactComplexControllerChildPrefix.data parent)
  have hPH : Fin.natAdd 10 pcStack≠Fin.natAdd 10 headerStack := fun h => hne (Fin.natAdd_injective _ _ h)
  have hH8 := old_ne headerStack 8 (by omega)
  have hH9 := old_ne headerStack 9 (by omega)
  have hP8 := old_ne pcStack 8 (by omega)
  have hP9 := old_ne pcStack 9 (by omega)
  have hpc := pc_runs (s:=s) (Fin.castAdd 43 (Fin.natAdd 10 pcStack)) call.site call.slot
    (ActiveRepairRankHeadersCommands.bank (put st 1 (k+1))) queue
    (CompactComplexControllerChildPrefix.native (CompactComplexChildHeadersData.child rho visit ha pair call.slot) rows tail)
    (headers.append scalar) (by
      intro j hj
      simpa only [Tapes.append,Fin.addCases_left,headers,CompactComplexControllerHeaderStack.saved,
        stores,CompactComplexControllerDenominatorEntry.targets,targeted,setTape,
        Function.update_of_ne hPH,Function.update_of_ne hP8,Function.update_of_ne hP9] using hbP j hj)
  have hret := CompactComplexControllerDenominatorEntry.return_restore (s:=s+43)
    rho visit ha pair call.slot rows (Fin.castAdd 43 headerStack) st h1 queue tail (stores.append scalar)
    (by
      intro z hz
      change (stores.append scalar).tape (Fin.castAdd 43 (Fin.natAdd 10 headerStack)) z=blank
      change (stores.append scalar).head (Fin.castAdd 43 (Fin.natAdd 10 headerStack))≤z at hz
      simp only [Tapes.append,Fin.addCases_left,stores,CompactComplexControllerDenominatorEntry.targets,
        targeted,setTape,Function.update_of_ne hH8,Function.update_of_ne hH9] at hz ⊢
      exact hbH z hz)
    (storage.tape ⟨9,by omega⟩) (storage.head ⟨9,by omega⟩) targetN
    (by change (stores.append scalar).tape (Fin.castAdd 43 (⟨9,by omega⟩ : Fin (10+s)))=_
        simp only [Tapes.append,Fin.addCases_left]
        simp [stores,CompactComplexControllerDenominatorEntry.targets,targeted,setTape])
    (by change (stores.append scalar).head (Fin.castAdd 43 (⟨9,by omega⟩ : Fin (10+s)))=_
        simp only [Tapes.append,Fin.addCases_left]
        simp [stores,CompactComplexControllerDenominatorEntry.targets,targeted,setTape])
    (by change (stores.append scalar).tape (Fin.castAdd 43 (⟨8,by omega⟩ : Fin (10+s)))=_
        simp only [Tapes.append,Fin.addCases_left]
        simp [stores,CompactComplexControllerDenominatorEntry.targets,setTape])
    (by change (stores.append scalar).head (Fin.castAdd 43 (⟨8,by omega⟩ : Fin (10+s)))=_
        simp only [Tapes.append,Fin.addCases_left]
        simp [stores,CompactComplexControllerDenominatorEntry.targets,setTape]) hb9
  rw [restored_append,restored_target] at hret
  rw [stack_cast,header_append] at hret
  have hpc' := hpc.consequence (fun _ h => h) (fun _ h => h) le_rfl
  rw [pc_append headers scalar (Fin.natAdd 10 pcStack) call.site (call.slot : Fin arity)] at hpc'
  unfold returnProgram
  rw [stack_cast pcStack]
  apply (hpc'.seq hret).consequence (fun _ h => h) (fun _ h => h)
  omega

private theorem installed_bank (control : Tapes 43 2) (queue : Tapes 1 2) (native : Tapes 66 2)
    (storage : Tapes (10+s) 2) (n : ℕ) :
    CompactComplexControllerDenominatorTarget.installed
      (CompactComplexControllerNativeFrame.bank control queue native storage) n=
      CompactComplexControllerNativeFrame.bank control queue native (targeted storage n) := by
  unfold CompactComplexControllerDenominatorTarget.installed CompactComplexControllerDenominator.target
    CompactComplexControllerNativeFrame.storageSlot CompactComplexControllerNativeFrame.bank targeted
  rw [SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_right]
private theorem single_setRole {c : ℕ} (payload : Tapes (1+c) 2) (j : Fin c) (g : ℤ → Fin 6) :
    CompactComplexNativeRoleBridge.single (CompactNativeRoleGuardedChildCaller.setRole payload j g)=
      CompactComplexNativeRoleBridge.single payload := by
  have h0 : (0 : Fin (1+c))≠Fin.natAdd 1 j := by
    intro h;have hv := congrArg Fin.val h;simp only [Fin.val_natAdd,Fin.val_zero] at hv;omega
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [CompactNativeRoleGuardedChildCaller.setRole,setTape,Function.update_of_ne h0]

def program (m s : ℕ) (headerStack pcStack : Fin s) (call : Call) := seq (seq (seq
  (targetProgram s)
  (rootProgram (CompactComplexControllerDenominatorEntry.program
    (Fin.castAdd 43 headerStack) (Fin.castAdd 43 pcStack) call.site call.slot)))
  (extend (CompactComplexStoppedCodecCaller.program m (10+s) call) (privateTapes s)))
  (rootProgram (returnProgram headerStack pcStack))

attribute [local irreducible] targetProgram rootProgram returnProgram
  CompactComplexStoppedCodecCaller.program CompactComplexControllerDenominatorEntry.program
  CompactComplexControllerChildStopTarget.program role roleCount
  CompactComplexNativeRoleBridge.single CompactNativeRoleGuardedChildCaller.setRole
  CompactNativeRoleReservedBridge.rolePayload CompactNativeRoleSourcePorts.roles

/-- A fixed stopped-call roundtrip constructs the return target with the
actual runtime stopping test, saves it, enters the real child, executes its
proved original-descriptor codec lifecycle and restores the actual PC,
parent geometry and target stack. No execution callback is a premise. -/
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
    (headerStack pcStack : Fin s) (hne : pcStack≠headerStack)
    (st : State) (h1 : st 1=some (k+2)) (queue : Tapes 1 2) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (n : ℕ)
    (hn : storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits n) ∧ storage.head ⟨7,by omega⟩=1)
    (ht : storage.tape ⟨8,by omega⟩=(fun _ => blank) ∧ storage.head ⟨8,by omega⟩=0)
    (hw0 : storage.tape ⟨0,by omega⟩=(fun _ => blank) ∧ storage.head ⟨0,by omega⟩=0)
    (hbH : ∀ z,storage.head (Fin.natAdd 10 headerStack)≤z → storage.tape (Fin.natAdd 10 headerStack) z=blank)
    (hbP : ∀ j<CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length arity,
      storage.tape (Fin.natAdd 10 pcStack) (storage.head (Fin.natAdd 10 pcStack)+j)=blank)
    (hb9 : ∀ z,storage.head ⟨9,by omega⟩≤z →
      z<storage.head ⟨9,by omega⟩+1+(bits (CompactComplexDenominatorPolicy.leafTarget n (k+1))).length →
      storage.tape ⟨9,by omega⟩ z=blank)
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
    let scalar := CompactReservedHeaders.initial D K0 rho.val ell q d G
    let parent := CompactComplexChildHeadersData.parent rho path.visit ha pair
    let targetN := CompactComplexDenominatorPolicy.leafTarget n (k+1)
    ∃ (hdiv : roleCount∣rows) (time : ℕ),
      let payload := CompactNativeRoleReservedBridge.rolePayload sh rows roleCount ell hdiv f
      let g := CompactNativeRoleGuardedChildCaller.resultWord (CompactComplexStoppedCallSite.direction call)
        sh rows roleCount ell p rho (Visit.child path.visit call.slot) hdiv f (role call.site)
      HoareTime (program m s headerStack pcStack call)
        (fun z => z=ready (CompactComplexNativeCodecFrame.bank (ActiveRepairRankHeadersCommands.bank st) queue scalar
          (ActivePrefixStageHeadersData.initial parent rows) tail storage payload))
        (fun z => z=ready (CompactComplexNativeCodecFrame.bank (ActiveRepairRankHeadersCommands.bank st) queue scalar
          (ActivePrefixStageHeadersData.initial parent rows) tail (targeted storage targetN)
          (CompactNativeRoleGuardedChildCaller.setRole payload (role call.site) g))) time ∧
      time≤CompactComplexControllerChildStopTarget.cost d (k+2) n (arity^(k+1))+
        (4*(bits targetN).length+13+CompactComplexControllerChildBudget.entryCost
          Networks.ComplexRecursiveCallSchema.sites.length rho path.visit ha pair call.slot rows)+
        CompactComplexStoppedCodecCaller.constant m*CompactFallbackAxisRun.volume D K0 ell q*(arity^(k+1))+
        (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length arity+3+
          (CompactComplexControllerChildBudget.returnCost rho path.visit ha pair call.slot+2*(bits targetN).length+8))+3 := by
  dsimp only
  let sh := CompactReservationNativeRows.shape roleCount m d D G K0
  let rows := CompactGlobalRowPadding.rowsAt roleCount m d K0 level
  let p := CompactNativeRoleReservedBridge.precision roleCount m d D K0 q
  let ha := CompactNativeRoleStoppedChildBudget.actual_active roleCount m d D G K0 hDd
  let scalar := CompactReservedHeaders.initial D K0 rho.val ell q d G
  let parent := CompactComplexChildHeadersData.parent rho path.visit ha pair
  let targetN := CompactComplexDenominatorPolicy.leafTarget n (k+1)
  let stores := CompactComplexControllerDenominatorEntry.targets (targeted storage targetN) targetN
  let saved := CompactComplexControllerChildPrefix.saved stores (Fin.natAdd 10 headerStack)
    (Fin.natAdd 10 pcStack) call.site call.slot parent
  obtain ⟨hdiv,codecTime,hcodec,hcodecBound⟩ := CompactComplexStoppedCodecCaller.actual_runs
    m d D G K0 ell q level hm hDd hd hG hK hDp hD hj rho path hstop pair call
    (ActiveRepairRankHeadersCommands.bank (put st 1 (k+1))) queue tail saved f hw
  let payload := CompactNativeRoleReservedBridge.rolePayload sh rows roleCount ell hdiv f
  let g := CompactNativeRoleGuardedChildCaller.resultWord (CompactComplexStoppedCallSite.direction call)
    sh rows roleCount ell p rho (Visit.child path.visit call.slot) hdiv f (role call.site)
  let scalarBank := ActiveRepairRankHeadersCommands.bank (a:=2) scalar
  let sourceTail := tail.append (CompactComplexNativeRoleBridge.single payload)
  let caller := CompactComplexControllerNativeFrame.bank (ActiveRepairRankHeadersCommands.bank st) queue
    (CompactComplexControllerChildPrefix.native parent rows sourceTail) (storage.append scalarBank)
  have htarget := CompactComplexControllerChildStopTarget.parent_runs (s:=s+43) rho path.visit ha pair rows st h1
    queue sourceTail (storage.append scalarBank) n
    (by
      change (storage.append scalarBank).tape (Fin.castAdd 43 (⟨7,by omega⟩ : Fin (10+s)))=_ ∧
        (storage.append scalarBank).head (Fin.castAdd 43 (⟨7,by omega⟩ : Fin (10+s)))=1
      simpa only [Tapes.append,Fin.addCases_left] using hn)
    (by
      change (storage.append scalarBank).tape (Fin.castAdd 43 (⟨8,by omega⟩ : Fin (10+s)))=_ ∧
        (storage.append scalarBank).head (Fin.castAdd 43 (⟨8,by omega⟩ : Fin (10+s)))=0
      simpa only [Tapes.append,Fin.addCases_left] using ht)
    (by
      change (storage.append scalarBank).tape (Fin.castAdd 43 (⟨0,by omega⟩ : Fin (10+s)))=_ ∧
        (storage.append scalarBank).head (Fin.castAdd 43 (⟨0,by omega⟩ : Fin (10+s)))=0
      simpa only [Tapes.append,Fin.addCases_left] using hw0)
  have haxes : (CompactReservationNativeRows.shape roleCount m d D G K0).axes=d := rfl
  simp only [haxes,hstop,ite_true] at htarget
  have htarget' := target_runs _ _ (CompactNativeRoleSourcePorts.roles payload) _ htarget
  unfold CompactComplexControllerDenominatorTarget.parentBank at htarget'
  rw [installed_bank,targeted_append] at htarget'
  have hentry := CompactComplexControllerDenominatorEntry.entry (s:=s+43) rho path.visit ha pair call.slot rows
    (Fin.castAdd 43 headerStack) (Fin.castAdd 43 pcStack) call.site st h1 queue sourceTail
    ((targeted storage targetN).append scalarBank) targetN
    (by
      change ((targeted storage targetN).append scalarBank).tape
        (Fin.castAdd 43 (⟨8,by omega⟩ : Fin (10+s)))=_
      simp only [Tapes.append,Fin.addCases_left,targeted,setTape,Function.update_self]
      exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm)
    (by
      change ((targeted storage targetN).append scalarBank).head
        (Fin.castAdd 43 (⟨8,by omega⟩ : Fin (10+s)))=1
      simp only [Tapes.append,Fin.addCases_left,targeted,setTape,Function.update_self])
  rw [targets_append] at hentry
  rw [saved_append stores scalarBank headerStack pcStack call.site (call.slot : Fin arity) parent] at hentry
  have hentry' := root_runs _ _ _ (CompactNativeRoleSourcePorts.roles payload) hentry
  have hcodec' := hoare_extend_eq hcodec (SharedBank.empty (privateTapes s) 2)
  rw [CompactComplexNativeCodecFrame.initial_bank,CompactComplexNativeCodecFrame.initial_bank,single_setRole] at hcodec'
  have hreturn := return_runs rho path.visit ha pair call rows headerStack pcStack hne st h1 queue
    (tail.append (CompactComplexNativeRoleBridge.single (CompactNativeRoleGuardedChildCaller.setRole payload (role call.site) g)))
    storage scalarBank targetN hbH hbP hb9
  have hreturn' := root_runs _ _ _
    (CompactNativeRoleSourcePorts.roles (CompactNativeRoleGuardedChildCaller.setRole payload (role call.site) g)) hreturn
  rw [single_setRole] at hreturn'
  have hrun := ((htarget'.seq hentry').seq hcodec').seq hreturn'
  let totalTime := CompactComplexControllerChildStopTarget.cost d (k+2) n (arity^(k+1))+1+
    (4*(bits targetN).length+13+CompactComplexControllerChildBudget.entryCost
      Networks.ComplexRecursiveCallSchema.sites.length rho path.visit ha pair call.slot rows)+1+codecTime+1+
    (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length arity+3+
      (CompactComplexControllerChildBudget.returnCost rho path.visit ha pair call.slot+2*(bits targetN).length+8))
  refine ⟨hdiv,totalTime,?_,?_⟩
  · apply hrun.consequence
    · rintro z rfl
      simp only [ready,CompactComplexStoppedCodecCaller.ready,CompactComplexNativeCodecFrame.initial_bank,
        rootReady,sourceTail,scalarBank,scalar,payload,sh,rows]
    · rintro z rfl
      simp only [ready,CompactComplexStoppedCodecCaller.ready,CompactComplexNativeCodecFrame.initial_bank,
        rootReady,single_setRole,scalarBank,scalar,payload,g,sh,rows,p,targetN]
    · exact le_rfl
  · dsimp only [totalTime,targetN,rows,ha] at hcodecBound ⊢
    omega

end
end IntegerMultBounds.Machine.CompactComplexStoppedLedgerRoundtrip
