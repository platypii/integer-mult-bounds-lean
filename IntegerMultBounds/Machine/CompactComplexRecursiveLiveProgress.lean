import IntegerMultBounds.Machine.CompactComplexScalarLifecycleGrid
import IntegerMultBounds.Machine.CompactComplexStoppedAlignedCall
import IntegerMultBounds.Machine.CompactComplexDenominatorCapacity

/-! Physical scalar and stopped-call events propagate the true-denominator
ledger on the permanent caller bank. These are execution steps, not a supplied
recursive callback. The unstopped recursive dispatcher remains a separate
assembly obligation. -/
namespace IntegerMultBounds.Machine.CompactComplexRecursiveLiveProgress
noncomputable section
open CompactComplexRecursiveGeometry
open CompactComplexRolePhaseSite (roleCount role)
open Networks.ComplexRecursiveCallSchema (Call)
open CompactRecursiveDependencyBudget (Path)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexScalarCountLifecycle (Realizes)
open CompactComplexScalarIntegerRows (RowIndex)
open ButterflyStreamData (Coefficient)
open ActiveRepairRankHeadersCommands (State)
open RecursiveChildQuotientsConstant (bits)
open CompactSpectatorInheritedGrid (Grid decoded)
open CompactComplexDenominatorCapacity (ledger scalarRows)
variable {s : ℕ}
attribute [local irreducible] roleCount role Networks.ComplexFramedExecution.rows

def liveSlot (hs : 7<s) : Fin (CompactComplexScalarCountLifecycle.publicTapes s) :=
  CompactComplexScalarCountRootBank.countSlot ⟨7,hs⟩

/-- Literal common denominator, including its physical head position. -/
def Live {t : ℕ} (v : Tapes t 2) (slot : Fin t) (n : ℕ) : Prop :=
  v.head slot=1 ∧ v.tape slot=RadixZeroFill.encodedBinary (bits n)

/-- The true physical header is bounded by the explicit dependency ledger. -/
def Progress {t : ℕ} (v : Tapes t 2) (slot : Fin t)
    (baseline levels frames returned usedRows : ℕ) : Prop :=
  ∃ n,Live v slot n ∧ n≤ledger scalarRows baseline levels frames returned usedRows

theorem live_raw {k t : ℕ} (v : Tapes k 2) (slot : Fin k) (hk : k≤t) (n : ℕ)
    (h : Live v slot n) :
    Live (SharedBankStageInput.raw v t) ⟨slot.val,lt_of_lt_of_le slot.isLt hk⟩ n := by
  simpa only [Live,SharedBankStageInput.raw,dite_eq_left slot.isLt] using h

theorem bank_live (hs : 7<s) (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : State) (tail : Tapes 22 2) (storage : Tapes s 2)
    (payload : Tapes (1+roleCount) 2) (n : ℕ) (h : Live storage ⟨7,hs⟩ n) :
    Live (bank control queue scalar stage tail storage payload) (liveSlot hs) n := by
  have he := CompactComplexScalarCountRootBank.count_bank (c:=roleCount) ⟨7,hs⟩
    control queue scalar stage tail storage payload
  exact ⟨he.1.trans h.1,he.2.trans h.2⟩

theorem scalar_output_live {N : ℕ} (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (v : Tapes (CompactComplexScalarCountLifecycle.publicTapes s) 2)
    (data : Fin CompactComplexScalarRowBlock.wireCount → Fin N → Coefficient) (n : ℕ) :
    Live (CompactComplexScalarCountLifecycle.output hs header v data n) (liveSlot hs) n := by
  have h := CompactComplexScalarRolePorts.output_live
    (CompactComplexScalarCountLifecycle.liveProof hs)
    (CompactComplexScalarCountLifecycle.storedHeader header)
    (CompactComplexScalarCountLifecycle.header_ne_live header hh)
    (CompactComplexScalarCountLifecycle.counted header v N) data n
  have hne : CompactComplexScalarCountRootBank.countSlot (c:=roleCount) header≠liveSlot hs := by
    intro he
    have hv := congrArg Fin.val he
    simp only [CompactComplexScalarCountRootBank.countSlot,liveSlot,
      CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
    exact hh (by omega)
  change Live (CompactComplexScalarCountLifecycle.scalarOutput hs header
    (CompactComplexScalarCountLifecycle.counted header v N) data n) (liveSlot hs) n at h
  unfold Live CompactComplexScalarCountLifecycle.output SharedPlacementAlphabet.setTape
  exact ⟨(Function.update_of_ne hne.symm _ _).trans h.1,
    (Function.update_of_ne hne.symm _ _).trans h.2⟩

theorem scalar_tapes_le : CompactComplexScalarCountLifecycle.publicTapes s≤
    CompactComplexScalarCountLifecycle.totalTapes s :=
  (Nat.le_add_right _ 43).trans (Nat.le_add_right _ _)

/-- A genuine scalar segment advances the prefix ledger by exactly the
number of completed rows, irrespective of intervening child calls. -/
theorem scalar_segment_bound (baseline levels frames returned usedRows n : ℕ)
    (ops : List RowIndex) (h : n≤ledger scalarRows baseline levels frames returned usedRows) :
    n+ops.length≤ledger scalarRows baseline levels frames returned (usedRows+ops.length) := by
  unfold ledger at *
  omega

theorem scalar_runs {sh : CompactGadgetReservationShape.Shape}
    (inp : ActivePrefixStageFullData.Inputs sh) (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (ops : List RowIndex) (ell p w d : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes s 2)
    (payload : Tapes (1+CompactComplexRolePhaseSite.roleCount) 2)
    (xs : Fin CompactComplexScalarRowBlock.wireCount →
      Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=w ∧ (xs a i j).2.length=w)
    (hblank : storage.head header=0 ∧ storage.tape header=(fun _ => blank))
    (hsource : ∀ a,
      (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage inp.rows ell p) tail storage payload).head
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=0 ∧
      (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage inp.rows ell p) tail storage payload).tape
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=
          SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
            (ActivePrefixStageNativePolynomial.rows inp (xs a) (hw a)))))
    (hlive : storage.head ⟨7,hs⟩=1 ∧ storage.tape ⟨7,hs⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits d))
    (baseline levels frames returned usedRows : ℕ)
    (hledger : d≤ledger scalarRows baseline levels frames returned usedRows) :
    let v := bank control queue scalar (CompactComplexNativeCodec.raw inp.stage inp.rows ell p) tail storage payload
    let data := fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a)
    Realizes (CompactComplexScalarCountLifecycle.program hs header hh ops) v
      (CompactComplexScalarCountLifecycle.output hs header v
        (CompactComplexScalarPolynomialSequence.execute ops data) (d+ops.length))
      (CompactComplexScalarCountLifecycle.cost ops (ActivePrefixStageTripleWords.count inp*2^ell) w d) ∧
    Progress (CompactComplexScalarCountLifecycle.output hs header v
      (CompactComplexScalarPolynomialSequence.execute ops data) (d+ops.length)) (liveSlot hs)
      baseline levels frames returned (usedRows+ops.length) := by
  dsimp only
  have hrun := CompactComplexScalarCountLifecycle.runs inp hs header hh ops ell p w d
    control queue scalar tail storage payload xs hw hblank hsource hlive
  exact ⟨hrun,d+ops.length,scalar_output_live hs header hh _ _ _,
    scalar_segment_bound baseline levels frames returned usedRows d ops hledger⟩

open CompactComplexScalarCountLifecycle (program output)
open CompactComplexScalarIntegerRows (guardBits)
open CompactComplexScalarSequenceSemantics (circuit values)
open CompactComplexScalarPathGuard (budget)
open CompactSpectatorInheritedGrid (dependencyCoefficient)
open Networks.GaussianPrecision (BoundedGrid)

/-- A genuine contiguous scalar segment retains one node growth allowance,
physically advances the live word, and remains inside the original Path ledger.
Its retained-field capacity is derived from that ledger, not supplied. -/
theorem scalar_prefix_runs {sh : CompactGadgetReservationShape.Shape}
    {left k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (inp : ActivePrefixStageFullData.Inputs sh) (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (ops : List RowIndex) (ell p C axes metadataP n : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes s 2)
    (payload : Tapes (1+CompactComplexRolePhaseSite.roleCount) 2)
    (xs : Fin CompactComplexScalarRowBlock.wireCount →
      Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (xs a i j).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1)
    (hblank : storage.head header=0 ∧ storage.tape header=(fun _ => blank))
    (hsource : ∀ a,
      (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage inp.rows ell metadataP) tail storage payload).head
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=0 ∧
      (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage inp.rows ell metadataP) tail storage payload).tape
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=
          SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
            (ActivePrefixStageNativePolynomial.rows inp (xs a) (hw a)))))
    (hlive : storage.head ⟨7,hs⟩=1 ∧ storage.tape ⟨7,hs⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits n))
    (ha : 0<sh.active) (hp : p+2*sh.bits≤metadataP) (haxes : axes≤sh.bits)
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+ops.length*guardBits≤sh.chunk)
    (before after : List (Networks.Circuit.Gate CompactComplexScalarIntegerRows.Wire ℂ))
    (hsegment : before++circuit ops++after=
      Networks.RationalScalarGrid.castRows Networks.ComplexFramedExecution.rows)
    (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hgrid : ∀ wire i,BoundedGrid n
      (Networks.GaussianPrecision.scalarBound 1 52 before
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
      (values (ButterflyGuard.halfWidth metadataP sh.bits) n
        (fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a)) i wire))
    (baseline usedRows : ℕ) (hbase : baseline≤p)
    (hused : usedRows=before.length)
    (hdenRoom : CompactComplexDenominatorCapacity.room scalarRows≤sh.chunk)
    (hledger : n≤ledger scalarRows baseline levels frames returned usedRows) :
    let v := bank control queue scalar (CompactComplexNativeCodec.raw inp.stage inp.rows ell metadataP) tail storage payload
    let data := fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a)
    Realizes (program hs header hh ops) v (output hs header v
        (CompactComplexScalarPolynomialSequence.execute ops data) (n+ops.length))
      (CompactComplexScalarCountLifecycle.timeConstant ops*
        (ActivePrefixStageTripleWords.count inp*2^ell)*(ButterflyGuard.halfWidth metadataP sh.bits+2)) ∧
    (∀ i wire,BoundedGrid (n+ops.length)
      (budget p C levels frames returned axes)
      (values (ButterflyGuard.halfWidth metadataP sh.bits) (n+ops.length)
        (CompactComplexScalarPolynomialSequence.execute ops data) i wire)) ∧
    Progress (output hs header v (CompactComplexScalarPolynomialSequence.execute ops data)
      (n+ops.length)) (liveSlot hs) baseline levels frames returned (usedRows+ops.length) ∧
    usedRows+ops.length≤scalarRows := by
  dsimp only
  have hlength := congrArg List.length hsegment
  simp only [List.length_append,circuit,List.length_map,
    Networks.RationalScalarGrid.castRows] at hlength
  have hprefix : usedRows+ops.length≤scalarRows := by
    unfold scalarRows
    omega
  have hcapacity := CompactComplexDenominatorCapacity.target_capacity path scalarRows baseline
    (metadataP-2*sh.bits) usedRows n n (by omega) (by omega) hdenRoom hledger
    (by omega)
  have hfield : n≤ButterflyGuard.halfWidth metadataP sh.bits+1 := by
    unfold CompactSpectatorInheritedGrid.half ButterflyGuard.halfWidth at hcapacity
    unfold ButterflyGuard.halfWidth
    omega
  obtain ⟨hrun,hgridOut⟩ := CompactComplexScalarLifecycleGrid.runs_prefix_linear_from_path
    path inp hs header hh ops ell p C axes metadataP n control queue scalar tail storage payload
    xs hw hblank hsource hlive ha hp haxes hroom hfield before after hsegment hC hgrid
  exact ⟨hrun,hgridOut,⟨n+ops.length,scalar_output_live hs header hh _ _ _,
    scalar_segment_bound baseline levels frames returned usedRows n ops hledger⟩,hprefix⟩

/-- The saved target, parent header frames and real return PC do not touch
storage7. This is the actual physical child-entry storage endpoint. -/
theorem entered_live {sh : CompactGadgetReservationShape.Shape}
    (storage : Tapes (10+s) 2) (targetN n : ℕ) (headerStack pcStack : Fin s)
    (call : Call) (parent : ActivePrefixStageParameters.Stage sh)
    (h : Live storage ⟨7,by omega⟩ n) :
    Live (CompactComplexControllerChildPrefix.saved
      (CompactComplexControllerDenominatorEntry.targets storage targetN)
      (Fin.natAdd 10 headerStack) (Fin.natAdd 10 pcStack) call.site call.slot parent)
      ⟨7,by omega⟩ n := by
  have hH : (⟨7,by omega⟩ : Fin (10+s))≠Fin.natAdd 10 headerStack := by
    intro he;have hv := congrArg Fin.val he; simp only [Fin.val_natAdd] at hv;omega
  have hP : (⟨7,by omega⟩ : Fin (10+s))≠Fin.natAdd 10 pcStack := by
    intro he;have hv := congrArg Fin.val he; simp only [Fin.val_natAdd] at hv;omega
  have h8 : (⟨7,by omega⟩ : Fin (10+s))≠⟨8,by omega⟩ := by
    intro he;have hv : (7:ℕ)=8 := congrArg Fin.val he;omega
  have h9 : (⟨7,by omega⟩ : Fin (10+s))≠⟨9,by omega⟩ := by
    intro he;have hv : (7:ℕ)=9 := congrArg Fin.val he;omega
  simpa only [Live,CompactComplexControllerChildPrefix.saved,
    CompactComplexControllerReturnStack.saved,CompactComplexControllerHeaderStack.saved,
    CompactComplexControllerDenominatorEntry.targets,SharedPlacementAlphabet.setTape,
    Function.update_of_ne hH,Function.update_of_ne hP,
    Function.update_of_ne h8,Function.update_of_ne h9] using h

/-- Entering a real call occurrence physically preserves the live word and
moves its bound onto precisely the genuine child dependency Path. -/
theorem child_entry_runs {sh : CompactGadgetReservationShape.Shape}
    (rho : Fin sh.chunk) {left k levels frames returned : ℕ}
    (path : Path sh.active left (k+2) levels frames returned) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Call) (rows : ℕ)
    (headerStack pcStack : Fin s) (st : State) (h1 : st 1=some (k+2))
    (queue : Tapes 1 2) (tail : Tapes 23 2) (storage : Tapes (10+s) 2)
    (targetN n baseline usedRows : ℕ)
    (ht : storage.tape ⟨8,by omega⟩=BinaryDescriptorStack.descriptor (bits targetN))
    (hh : storage.head ⟨8,by omega⟩=1)
    (hlive : Live storage ⟨7,by omega⟩ n) (hprefix : usedRows≤scalarRows)
    (hledger : n≤ledger scalarRows baseline levels frames
      (returned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(k+1)) usedRows) :
    let parent := CompactComplexChildHeadersData.parent rho path.visit hactive pair
    let child := CompactComplexChildHeadersData.child rho path.visit hactive pair call.slot
    let saved := CompactComplexControllerChildPrefix.saved
      (CompactComplexControllerDenominatorEntry.targets storage targetN)
      (Fin.natAdd 10 headerStack) (Fin.natAdd 10 pcStack) call.site call.slot parent
    HoareTime (CompactComplexControllerDenominatorEntry.program headerStack pcStack call.site call.slot)
      (fun v => v=CompactComplexControllerNativeFrame.bank (ActiveRepairRankHeadersCommands.bank st) queue
        (CompactComplexControllerChildPrefix.native parent rows tail) storage)
      (fun v => v=CompactComplexControllerNativeFrame.bank
        (ActiveRepairRankHeadersCommands.bank (ActiveRepairRankHeadersCommands.put st 1 (k+1))) queue
        (CompactComplexControllerChildPrefix.native child rows tail) saved ∧
        Progress v (CompactComplexControllerNativeFrame.storageSlot ⟨7,by omega⟩)
          baseline (levels+1) (frames+arity^(k+2))
          (returned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(k+1)) 0)
      (4*(bits targetN).length+13+CompactComplexControllerChildBudget.entryCost
        Networks.ComplexRecursiveCallSchema.sites.length rho path.visit hactive pair call.slot rows) := by
  dsimp only
  have hrun := CompactComplexControllerDenominatorEntry.entry rho path.visit hactive pair call.slot rows
    headerStack pcStack call.site st h1 queue tail storage targetN ht hh
  apply hrun.consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  refine ⟨rfl,n,?_,CompactComplexDenominatorCapacity.child_entry scalarRows baseline levels frames
    returned usedRows n (k+1) call hprefix hledger⟩
  have h := entered_live storage targetN n headerStack pcStack call
    (CompactComplexChildHeadersData.parent rho path.visit hactive pair) hlive
  simpa only [Live,CompactComplexControllerNativeFrame.bank,
    CompactComplexControllerNativeFrame.storageSlot,Tapes.append,Fin.addCases_right] using h

theorem committed_live (storage : Tapes (10+s) 2) (n : ℕ) :
    Live (CompactComplexStoppedAlignedCall.committed storage n) ⟨7,by omega⟩ n := by
  have hne : (⟨7,by omega⟩ : Fin (10+s))≠⟨8,by omega⟩ := by
    intro he;have hv : (7:ℕ)=8 := congrArg Fin.val he;omega
  simp only [Live,CompactComplexStoppedAlignedCall.committed,SharedPlacementAlphabet.setTape,
    Function.update_of_ne hne,Function.update_self,and_self]

open CompactComplexStoppedAlignedCall (ready committed roundtripAllowance alignmentAllowance)
attribute [local irreducible] CompactNativeRoleReservedBridge.role
  CompactNativeRoleReservedBridge.rolePayload CompactComplexChildGridPromoted.aligned
  CompactComplexStoppedGridHandoff.payload

/-- The genuine stopped child executes, physically aligns all spectators,
installs its new shared denominator and propagates the completed-call ledger.
Neither a prepared execution callback nor an abstract return is assumed. -/
theorem stopped_runs (m d D G K0 ell q level : ℕ) (hm : 2≤m)
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
      (CompactNativeRoleReservedBridge.precision roleCount m d D K0 q))
    (pBase C : ℕ) (hC : 1≤C) (hpBase : pBase≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤K0)
    (hfgrid : Grid (CompactReservationNativeRows.shape CompactComplexRolePhaseSite.roleCount m d D G K0)
      (CompactGlobalRowPadding.rowsAt CompactComplexRolePhaseSite.roleCount m d K0 level) ell
      (CompactNativeRoleReservedBridge.precision CompactComplexRolePhaseSite.roleCount m d D K0 q-
        2*(CompactReservationNativeRows.shape CompactComplexRolePhaseSite.roleCount m d D G K0).bits) n
      (CompactRecursiveGridBudget.bound pBase C levels (frames+2*returned)) f)
    (baseline usedRows : ℕ)
    (hledger : n≤ledger scalarRows baseline levels frames
      (returned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(k+1)) usedRows) :
    let sh := CompactReservationNativeRows.shape roleCount m d D G K0
    let rows := CompactGlobalRowPadding.rowsAt roleCount m d K0 level
    let metadataP := CompactNativeRoleReservedBridge.precision roleCount m d D K0 q
    let ha := CompactNativeRoleStoppedChildBudget.actual_active roleCount m d D G K0 hDd
    let scalar := CompactReservedHeaders.initial D K0 rho.val ell q d G
    let parent := CompactComplexChildHeadersData.parent rho path.visit ha pair
    let targetN := CompactComplexDenominatorPolicy.leafTarget n (k+1)
    ∃ (hdiv : roleCount∣rows) (time : ℕ),
      let before := fun j => CompactNativeRoleReservedBridge.role sh rows roleCount ell hdiv f j
      let after := CompactComplexChildGridPromoted.aligned sh (rows/roleCount) ell (metadataP-2*sh.bits)
        rho (Visit.child path.visit call.slot) (CompactComplexStoppedCallSite.direction call) (role call.site) before
      HoareTime (CompactComplexStoppedAlignedCall.program m s headerStack pcStack call)
        (fun z => z=ready (bank (ActiveRepairRankHeadersCommands.bank st) queue scalar
          (ActivePrefixStageHeadersData.initial parent rows) tail storage
          (CompactNativeRoleReservedBridge.rolePayload sh rows roleCount ell hdiv f)))
        (fun z => z=ready (bank (ActiveRepairRankHeadersCommands.bank st) queue scalar
          (ActivePrefixStageHeadersData.initial parent rows) tail (committed storage targetN)
          (CompactComplexStoppedGridHandoff.payload sh (rows/roleCount) ell (fun _ => blank) 0 after))) time ∧
      time≤roundtripAllowance m d D K0 ell q n rho path.visit ha pair call rows+
        alignmentAllowance sh roleCount m d D G K0 ell q rows n (k+1) rho parent (role call.site)+1 ∧
      (∀ j,Grid sh (rows/roleCount) ell (metadataP-2*sh.bits) targetN
        (CompactRecursiveGridBudget.bound pBase C (levels+1)
          ((frames+arity^(k+2))+2*(returned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(k+1)+arity^(k+1))))
        (after j)) ∧
      (∀ j,j≠role call.site → decoded sh (rows/roleCount) ell (metadataP-2*sh.bits) targetN (after j)=
        decoded sh (rows/roleCount) ell (metadataP-2*sh.bits) n (before j)) ∧
      Progress (bank (ActiveRepairRankHeadersCommands.bank st) queue scalar
        (ActivePrefixStageHeadersData.initial parent rows) tail (committed storage targetN)
        (CompactComplexStoppedGridHandoff.payload sh (rows/roleCount) ell (fun _ => blank) 0 after))
        (liveSlot (s:=10+s) (by omega)) baseline levels frames
        (returned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(k+1)+arity^(k+1)) usedRows := by
  dsimp only
  obtain ⟨hdiv,time,hrun,hcost,hgrid,hvalues⟩ := CompactComplexStoppedAlignedCall.actual_runs
    m d D G K0 ell q level hm hDd hd hG hK hDp hD hj rho path hstop pair call
    headerStack pcStack hne st h1 queue tail storage n hn ht hw0 hbH hbP hb9 f hw
    pBase C hC hpBase hchunk hfgrid
  refine ⟨hdiv,time,hrun,hcost,hgrid,hvalues,
    CompactComplexDenominatorPolicy.leafTarget n (k+1),?_,?_⟩
  · exact bank_live (by omega) _ _ _ _ _ _ _ _ (committed_live storage _)
  · exact CompactComplexDenominatorCapacity.returned_advance scalarRows baseline levels frames
      (returned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(k+1)) usedRows n
      (CompactComplexDenominatorPolicy.leafTarget n (k+1)) (arity^(k+1)) hledger
      (by unfold CompactComplexDenominatorPolicy.leafTarget;omega)

end
end IntegerMultBounds.Machine.CompactComplexRecursiveLiveProgress
