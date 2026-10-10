import IntegerMultBounds.Machine.CompactComplexSourceReadyPrefixGeometry
import IntegerMultBounds.Machine.CompactComplexSourceReadyFullChildPaths

/-! Concrete child-entry premises at the corrected scalar endpoint. Parent raw
rows remain in the native metadata while the actual role words use privately
computed quotient rows. All stream, stack and descriptor facts are derived from
the literal caller, rather than a supplied prepared bank or local execution. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyScalarChildReadiness
noncomputable section
open CompactComplexNativeCodecFrame (bank permanentTapes)
open CompactComplexScalarCallerEndpoint (storageOutput nativePayload)
open CompactComplexSpectatorTargetBank (roleSlot oldSlot numericSlot)
open CompactComplexScalarRolePorts (roleIndex)
open CompactComplexScalarRowBlock (wireCount)
open CompactComplexRolePhaseSite (roleCount)
open CompactComplexScalarIntegerRows (RowIndex)
open CompactComplexSourceReadyPrefixReadiness (BlankAfter)
open CompactComplexSourceReadyPrefixGeometry (nextArray)
open ButterflyStreamData (Coefficient)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}

/-- Scalar replacement retains the two real payload-stack/clock tapes. -/
def entryBank (next : Tapes (permanentTapes s c) 2) (aux : Tapes 2 2) :
    Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2 := next.append aux

theorem entry_prefix (next : Tapes (permanentTapes s c) 2) (aux : Tapes 2 2)
    (i : Fin (permanentTapes s c)) :
    (entryBank next aux).head (Fin.castAdd 2 i)=next.head i ∧
      (entryBank next aux).tape (Fin.castAdd 2 i)=next.tape i := by
  simp only [entryBank,Tapes.append,Fin.addCases_left,and_self]

theorem entry_aux (next : Tapes (permanentTapes s c) 2) (aux : Tapes 2 2) (i : Fin 2) :
    (entryBank next aux).head (Fin.natAdd (permanentTapes s c) i)=aux.head i ∧
      (entryBank next aux).tape (Fin.natAdd (permanentTapes s c) i)=aux.tape i := by
  simp only [entryBank,Tapes.append,Fin.addCases_right,and_self]

private def replacePrefix {P N : ℕ} (v : Tapes N 2) (w : Tapes P 2) : Tapes N 2 :=
  ⟨fun i => if h : i.val<P then w.head ⟨i.val,h⟩ else v.head i,
   fun i => if h : i.val<P then w.tape ⟨i.val,h⟩ else v.tape i⟩

private theorem replace_nested {P A F L W : ℕ}
    (before next : Tapes P 2) (aux : Tapes A 2) (frame : Tapes F 2)
    (leaf : Tapes L 2) (work : Tapes W 2) :
    replacePrefix ((((before.append aux).append frame).append leaf).append work) next=
      (((next.append aux).append frame).append leaf).append work := by
  apply Placement.Tapes.ext' <;> intro i
  all_goals
    induction i using Fin.addCases (m:=((P+A)+F)+L) (n:=W) with
    | right i =>
      have hn : ¬(((P+A)+F)+L+i.val<P) := by omega
      simp only [replacePrefix,Fin.val_natAdd,hn,↓reduceDIte,Tapes.append,Fin.addCases_right]
    | left i =>
      induction i using Fin.addCases (m:=(P+A)+F) (n:=L) with
      | right i =>
        have hn : ¬((P+A)+F+i.val<P) := by omega
        simp only [replacePrefix,Fin.val_castAdd,Fin.val_natAdd,hn,↓reduceDIte,Tapes.append,
          Fin.addCases_left,Fin.addCases_right]
      | left i =>
        induction i using Fin.addCases (m:=P+A) (n:=F) with
        | right i =>
          have hn : ¬(P+A+i.val<P) := by omega
          simp only [replacePrefix,Fin.val_castAdd,Fin.val_natAdd,hn,↓reduceDIte,Tapes.append,
            Fin.addCases_left,Fin.addCases_right]
        | left i =>
          induction i using Fin.addCases (m:=P) (n:=A) with
          | right i =>
            have hn : ¬(P+i.val<P) := by omega
            simp only [replacePrefix,Fin.val_castAdd,Fin.val_natAdd,hn,↓reduceDIte,Tapes.append,
              Fin.addCases_left,Fin.addCases_right]
          | left i =>
            simp only [replacePrefix,Fin.val_castAdd,i.isLt,↓reduceDIte,Tapes.append,Fin.addCases_left]

/-- The scalar lifecycle's actual full-bank output is exactly the child
caller's bank with the original payload stack, clock and node work retained. -/
theorem scalar_output_bank
    (before next : Tapes (CompactComplexSourceReadyScalarWorkspace.permanentTapes s c) 2)
    (aux : Tapes 2 2) (frame : Tapes 7 2)
    (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2) (work : Tapes 10 2) :
    CompactComplexSourceReadyScalarWorkspace.output
      (CompactComplexSourceReadyWorkspace.bank ((before.append aux).append frame) leaf work) next=
    CompactComplexSourceReadyWorkspace.bank ((next.append aux).append frame) leaf work :=
  replace_nested before next aux frame leaf work

/-- Direct original numeric43 view; every numeric head is retained literally. -/
theorem entry_headers (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes s 2) (payload : Tapes (1+c) 2) (aux : Tapes 2 2) :
    Placement.active CompactComplexNonleafRoleEntry.headerPlacement
      (entryBank (bank control queue scalar stage tail storage payload) aux)=
      ActiveRepairRankHeadersCommands.bank stage := by
  simp only [CompactComplexNonleafRoleEntry.headerPlacement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i
  · exact (entry_prefix _ aux _).1.trans
      (CompactComplexScalarCountRootBank.header_bank control queue scalar stage tail storage payload i).1
  · exact (entry_prefix _ aux _).2.trans
      (CompactComplexScalarCountRootBank.header_bank control queue scalar stage tail storage payload i).2

theorem entry_clock (next : Tapes (permanentTapes s c) 2) (aux : Tapes 2 2)
    (h : aux.head 1=0 ∧ aux.tape 1=(fun _ => blank)) :
    (entryBank next aux).head CompactComplexNonleafRoleEntry.clock=0 ∧
      (entryBank next aux).tape CompactComplexNonleafRoleEntry.clock=(fun _ => blank) :=
  ⟨(entry_aux next aux 1).1.trans h.1,(entry_aux next aux 1).2.trans h.2⟩

theorem entry_free (next : Tapes (permanentTapes s c) 2) (aux : Tapes 2 2)
    (h : BlankAfter aux 0) (selected : Fin c) (masterVolume roleVolume : ℕ) :
    CompactComplexNonleafRoleReturn.Free selected masterVolume roleVolume (entryBank next aux) := by
  apply CompactComplexSourceReadyPrefixReadiness.blankAfter_free
  intro z hz
  have hf := entry_aux next aux 0
  change (entryBank next aux).tape (Fin.natAdd (permanentTapes s c) 0) z=blank
  change (entryBank next aux).head (Fin.natAdd (permanentTapes s c) 0) ≤ z at hz
  rw [hf.2]
  exact h z (hf.1 ▸ hz)

theorem entry_control (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2)
    (aux : Tapes 2 2) (frame : Tapes 7 2) (i : Fin 43) :
    ((entryBank (bank control queue scalar stage tail storage payload) aux).append frame).head
      (CompactComplexNonleafRoleChildBank.control i)=control.head i ∧
    ((entryBank (bank control queue scalar stage tail storage payload) aux).append frame).tape
      (CompactComplexNonleafRoleChildBank.control i)=control.tape i := by
  change ((entryBank (bank control queue scalar stage tail storage payload) aux).append frame).head
      (Fin.castAdd 7 (Fin.castAdd 2 (Fin.castAdd c (CompactComplexControllerNativeFrame.controllerSlot i))))=control.head i ∧
    ((entryBank (bank control queue scalar stage tail storage payload) aux).append frame).tape
      (Fin.castAdd 7 (Fin.castAdd 2 (Fin.castAdd c (CompactComplexControllerNativeFrame.controllerSlot i))))=control.tape i
  simp only [entryBank,bank,CompactComplexNativeRoleBridge.bank,CompactComplexControllerNativeFrame.bank,
    CompactComplexControllerNativeFrame.controllerSlot,Tapes.append,Fin.addCases_left,and_self]

private theorem exponent_view {T : ℕ} (z : Tapes T 2) (control : Tapes 43 2)
    (ports : Fin 43 → Fin T)
    (h : ∀ i,z.head (ports i)=control.head i ∧ z.tape (ports i)=control.tape i)
    (e : ℕ) (he : control.head 1=1 ∧ control.tape 1=BinaryDescriptorStack.descriptor (bits e))
    (h28 : control.head 28=0 ∧ control.tape 28=(fun _ => blank))
    (h29 : control.head 29=0 ∧ control.tape 29=(fun _ => blank)) :
    (⟨fun i => z.head (ports (![1,28,29] i)),fun i => z.tape (ports (![1,28,29] i))⟩ : Tapes 3 2)=
      CompactComplexExponentStep.bank e := by
  apply Placement.Tapes.ext' <;> intro i <;> fin_cases i
  · exact (h 1).1.trans he.1
  · exact (h 28).1.trans h28.1
  · exact (h 29).1.trans h29.1
  · exact (h 1).2.trans he.2
  · exact (h 28).2.trans h28.2
  · exact (h 29).2.trans h29.2

/-- The actual descendant exponent view follows from the retained controller
words; neither a prepared exponent bank nor an intermediate equality is needed. -/
theorem entry_exponent (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2)
    (aux : Tapes 2 2) (frame : Tapes 7 2) (e : ℕ)
    (he : control.head 1=1 ∧ control.tape 1=BinaryDescriptorStack.descriptor (bits e))
    (h28 : control.head 28=0 ∧ control.tape 28=(fun _ => blank))
    (h29 : control.head 29=0 ∧ control.tape 29=(fun _ => blank)) :
    Placement.active CompactComplexNonleafRoleChildBank.exponentPlacement
      ((entryBank (bank control queue scalar stage tail storage payload) aux).append frame)=
      CompactComplexExponentStep.bank e := by
  simp only [CompactComplexNonleafRoleChildBank.exponentPlacement,InjectivePlacement.active_bank]
  exact exponent_view _ control CompactComplexNonleafRoleChildBank.control
    (entry_control control queue scalar stage tail storage payload aux frame) e he h28 h29


private theorem support_transport {f g : ℤ → Fin 6} {n : ℕ}
    (he : f=g) (h : RoleArrayStack.Supported g n) : RoleArrayStack.Supported f n := by
  intro z hz
  exact (congrFun he z).trans (h z hz)

section Scalar
variable {sh : CompactGadgetReservationShape.Shape} {ell p : ℕ}
variable (inp : ActivePrefixStageFullData.Inputs sh) (rows : ℕ)
variable (hrows : inp.rows=rows/roleCount) (hs : 7<s)
variable (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
variable (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+roleCount) 2)
variable (ops : List RowIndex)
variable (xs : Fin wireCount → Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient)
variable (hw : ∀ a i j,(xs a i j).1.length=ButterflyGuard.halfWidth p sh.bits+1 ∧
  (xs a i j).2.length=ButterflyGuard.halfWidth p sh.bits+1) (d : ℕ) (aux : Tapes 2 2)

/-- Literal corrected endpoint consumed by the genuine child-entry machine. -/
def nextCaller := entryBank
  (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage rows ell p) tail
    (storageOutput hs storage d) (nativePayload inp ops xs hw payload)) aux

theorem next_raw :
    Placement.active CompactComplexNonleafRoleEntry.headerPlacement
      (nextCaller inp rows hs control queue scalar tail storage payload ops xs hw d aux)=
      ActiveRepairRankHeadersCommands.bank
        (CompactSpectatorLeafSetup.raw sh rows ell p inp.stage.rho inp.stage.left inp.stage.f inp.stage.slots
          inp.stage.right inp.stage.source.val inp.stage.target.val) :=
  entry_headers _ _ _ _ _ _ _ _

theorem next_source
    (h : payload.head 0=0 ∧ RoleArrayStack.Supported (payload.tape 0)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh roleCount rows ell p false)) :
    (nextCaller inp rows hs control queue scalar tail storage payload ops xs hw d aux).head
      CompactComplexNonleafRoleEntry.source=0 ∧
    RoleArrayStack.Supported
      ((nextCaller inp rows hs control queue scalar tail storage payload ops xs hw d aux).tape
        CompactComplexNonleafRoleEntry.source)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh roleCount rows ell p false) := by
  have hp := entry_prefix
    (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage rows ell p) tail
      (storageOutput hs storage d) (nativePayload inp ops xs hw payload)) aux (numericSlot 65)
  have hb := CompactComplexSourceReadyPrefixReadiness.source_bank control queue scalar
    (CompactComplexNativeCodec.raw inp.stage rows ell p) tail (storageOutput hs storage d)
    (nativePayload inp ops xs hw payload)
  have hf := CompactComplexScalarCallerEndpoint.native_payload_source inp ops xs hw payload
  exact ⟨hp.1.trans (hb.1.trans (hf.1.trans h.1)),support_transport (hp.2.trans (hb.2.trans hf.2)) h.2⟩

theorem next_roles (hrows : inp.rows=rows/roleCount) :
    ∀ j,(nextCaller inp rows hs control queue scalar tail storage payload ops xs hw d aux).head
      (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
    RoleArrayStack.Supported
      ((nextCaller inp rows hs control queue scalar tail storage payload ops xs hw d aux).tape
        (CompactComplexNonleafRoleEntry.roleTape j))
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh roleCount rows ell p true) := by
  intro j
  have hp := entry_prefix
    (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage rows ell p) tail
      (storageOutput hs storage d) (nativePayload inp ops xs hw payload)) aux (roleSlot j)
  have hr := CompactComplexSourceReadyPrefixReadiness.next_role inp hs control queue scalar
    (CompactComplexNativeCodec.raw inp.stage rows ell p) tail storage payload ops xs hw d (roleIndex.symm j)
  have hh : (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage rows ell p) tail
      (storageOutput hs storage d) (nativePayload inp ops xs hw payload)).head (roleSlot j)=0 := by
    simpa only [Equiv.apply_symm_apply] using hr.1
  have hsupp := CompactComplexSourceReadyPrefixReadiness.next_role_supported inp hs control queue scalar
    (CompactComplexNativeCodec.raw inp.stage rows ell p) tail storage payload ops xs hw d (roleIndex.symm j)
  rw [CompactComplexSourceReadyPrefixReadiness.native_role_volume inp rows ell p roleCount hrows] at hsupp
  have hsupp' : RoleArrayStack.Supported
      ((bank control queue scalar (CompactComplexNativeCodec.raw inp.stage rows ell p) tail
        (storageOutput hs storage d) (nativePayload inp ops xs hw payload)).tape (roleSlot j))
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh roleCount rows ell p true) := by
    simpa only [Equiv.apply_symm_apply] using hsupp
  exact ⟨hp.1.trans hh,support_transport hp.2 hsupp'⟩

theorem next_selected (selected : Fin roleCount) :
    (nextCaller inp rows hs control queue scalar tail storage payload ops xs hw d aux).tape
      (CompactComplexNonleafRoleEntry.roleTape selected)=
      NativeZeroPadding.word (NativeZeroPaddingArray.word
        (nextArray inp (rows/roleCount) ell hrows ops xs (roleIndex.symm selected))) := by
  have hp := entry_prefix
    (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage rows ell p) tail
      (storageOutput hs storage d) (nativePayload inp ops xs hw payload)) aux (roleSlot selected)
  have hr := CompactComplexSourceReadyPrefixReadiness.next_role inp hs control queue scalar
    (CompactComplexNativeCodec.raw inp.stage rows ell p) tail storage payload ops xs hw d (roleIndex.symm selected)
  have he := CompactComplexSourceReadyPrefixGeometry.array_word inp (rows/roleCount) ell _ hrows
    (CompactComplexScalarNativeEndpoint.executed ops xs (roleIndex.symm selected))
    (CompactComplexScalarNativeEndpoint.executed_width ops xs hw (roleIndex.symm selected))
  have hr' := hr.2.trans he.symm
  simp only [Equiv.apply_symm_apply] at hr'
  exact hp.2.trans hr'

theorem next_storage (i : Fin s) (hi : i.val≠7) :
    (nextCaller inp rows hs control queue scalar tail storage payload ops xs hw d aux).head
      (CompactComplexNonleafRoleReturnFrame.oldSlot i)=storage.head i ∧
    (nextCaller inp rows hs control queue scalar tail storage payload ops xs hw d aux).tape
      (CompactComplexNonleafRoleReturnFrame.oldSlot i)=storage.tape i := by
  have hp := entry_prefix
    (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage rows ell p) tail
      (storageOutput hs storage d) (nativePayload inp ops xs hw payload)) aux (oldSlot i)
  have hb := CompactComplexSpectatorTargetBank.old_bank control queue scalar
    (CompactComplexNativeCodec.raw inp.stage rows ell p) tail
    (storageOutput hs storage d) (nativePayload inp ops xs hw payload) i
  have hf := CompactComplexScalarCallerEndpoint.storage_frame hs storage d i hi
  exact ⟨hp.1.trans (hb.1.trans hf.1),hp.2.trans (hb.2.trans hf.2)⟩

theorem next_live :
    (nextCaller inp rows hs control queue scalar tail storage payload ops xs hw d aux).head
      (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨7,hs⟩)=1 ∧
    (nextCaller inp rows hs control queue scalar tail storage payload ops xs hw d aux).tape
      (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨7,hs⟩)=BinaryDescriptorStack.descriptor (bits d) := by
  have hp := entry_prefix
    (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage rows ell p) tail
      (storageOutput hs storage d) (nativePayload inp ops xs hw payload)) aux (oldSlot ⟨7,hs⟩)
  have hb := CompactComplexSpectatorTargetBank.old_bank control queue scalar
    (CompactComplexNativeCodec.raw inp.stage rows ell p) tail
    (storageOutput hs storage d) (nativePayload inp ops xs hw payload) ⟨7,hs⟩
  have hh : (storageOutput hs storage d).head ⟨7,hs⟩=1 := by simp [storageOutput,SharedPlacementAlphabet.setTape]
  have ht : (storageOutput hs storage d).tape ⟨7,hs⟩=BinaryDescriptorStack.descriptor (bits d) := by
    simp only [storageOutput,SharedPlacementAlphabet.setTape,Function.update_self,
      BinaryDescriptorStackRoundtrip.descriptor_encoded]
  exact ⟨hp.1.trans (hb.1.trans hh),hp.2.trans (hb.2.trans ht)⟩

theorem next_target (h8 : 8<s) (target : ℕ)
    (h : storage.head ⟨8,h8⟩=1 ∧ storage.tape ⟨8,h8⟩=BinaryDescriptorStack.descriptor (bits target)) :
    (nextCaller inp rows hs control queue scalar tail storage payload ops xs hw d aux).head
      (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨8,h8⟩)=1 ∧
    (nextCaller inp rows hs control queue scalar tail storage payload ops xs hw d aux).tape
      (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨8,h8⟩)=BinaryDescriptorStack.descriptor (bits target) := by
  have hf := next_storage inp rows hs control queue scalar tail storage payload ops xs hw d aux ⟨8,h8⟩ (by simp)
  exact ⟨hf.1.trans h.1,hf.2.trans h.2⟩

/-- Readiness for the next selected child is derived jointly from one literal
scalar endpoint and its genuine executed numerical grid. -/
theorem next_selected_ready (hrows : inp.rows=rows/roleCount) (hp : 2*sh.bits≤p)
    (selected : Fin roleCount) (M : ℕ)
    (hgrid : ∀ i wire,Networks.GaussianPrecision.BoundedGrid d M
      (CompactComplexScalarSequenceSemantics.values (ButterflyGuard.halfWidth p sh.bits) d
        (fun a => ActivePrefixStageNativePolynomial.flattenArray
          (CompactComplexScalarNativeEndpoint.executed ops xs a)) i wire))
    (hclock : aux.head 1=0 ∧ aux.tape 1=(fun _ => blank)) (hfree : BlankAfter aux 0)
    (hmaster : payload.head 0=0 ∧ RoleArrayStack.Supported (payload.tape 0)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh roleCount rows ell p false)) :
    let caller := nextCaller inp rows hs control queue scalar tail storage payload ops xs hw d aux
    let f := nextArray inp (rows/roleCount) ell hrows ops xs (roleIndex.symm selected)
    (caller.head CompactComplexNonleafRoleEntry.clock=0 ∧
      caller.tape CompactComplexNonleafRoleEntry.clock=(fun _ => blank)) ∧
    (caller.head CompactComplexNonleafRoleEntry.source=0 ∧
      RoleArrayStack.Supported (caller.tape CompactComplexNonleafRoleEntry.source)
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh roleCount rows ell p false)) ∧
    (∀ j,caller.head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      RoleArrayStack.Supported (caller.tape (CompactComplexNonleafRoleEntry.roleTape j))
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh roleCount rows ell p true)) ∧
    caller.tape (CompactComplexNonleafRoleEntry.roleTape selected)=
      NativeZeroPadding.word (NativeZeroPaddingArray.word f) ∧
    CompactComplexNonleafRoleReturn.Free selected
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh roleCount rows ell p false)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh roleCount rows ell p true) caller ∧
    CompactSpectatorInheritedGrid.Width sh (rows/roleCount) ell (p-2*sh.bits) f ∧
    CompactSpectatorInheritedGrid.Grid sh (rows/roleCount) ell (p-2*sh.bits) d M f := by
  exact ⟨entry_clock _ aux hclock,
    next_source inp rows hs control queue scalar tail storage payload ops xs hw d aux hmaster,
    next_roles inp rows hs control queue scalar tail storage payload ops xs hw d aux hrows,
    next_selected inp rows hrows hs control queue scalar tail storage payload ops xs hw d aux selected,
    entry_free _ aux hfree selected _ _,
    CompactComplexSourceReadyPrefixGeometry.nextArray_width inp (rows/roleCount) ell p hrows hp ops xs hw _,
    CompactComplexSourceReadyPrefixGeometry.nextArray_grid inp (rows/roleCount) ell p d M hrows hp ops xs hgrid _⟩

end Scalar

section Canonical
variable {sh : CompactGadgetReservationShape.Shape} {left k : ℕ}

/-- Actual parent-stage input for the scalar's genuine quotient-row arrays.
The record-capacity condition is geometric input data, not a tape equality. -/
def canonicalInput (rho : Fin sh.chunk)
    (visit : CompactComplexRecursiveGeometry.Visit sh.active left (k+2))
    (hactive : sh.active ≤ sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin CompactComplexRecursiveGeometry.arity))
    (rows : ℕ) (hgroup : 0<rows/roleCount)
    (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (hrecord : sh.bits+1≤sh.payload) :
    ActivePrefixStageFullData.Inputs sh where
  stage := CompactComplexChildHeadersData.parent rho visit hactive pair
  rows := rows/roleCount
  hG := hG
  hGK := hGK
  hr := hgroup
  hrecord := hrecord

theorem canonical_rows (rho : Fin sh.chunk)
    (visit : CompactComplexRecursiveGeometry.Visit sh.active left (k+2))
    (hactive : sh.active ≤ sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin CompactComplexRecursiveGeometry.arity))
    (rows : ℕ) (hgroup : 0<rows/roleCount)
    (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (hrecord : sh.bits+1≤sh.payload) :
    (canonicalInput rho visit hactive pair rows hgroup hG hGK hrecord).rows=rows/roleCount := rfl

/-- Literal child-entry raw metadata for the actual canonical parent, with
no assumed equality to a separately prepared header bank. -/
theorem canonical_next_raw (rho : Fin sh.chunk)
    (visit : CompactComplexRecursiveGeometry.Visit sh.active left (k+2))
    (hactive : sh.active ≤ sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin CompactComplexRecursiveGeometry.arity))
    (rows ell p : ℕ) (hgroup : 0<rows/roleCount)
    (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (hrecord : sh.bits+1≤sh.payload)
    (hs : 7<s) (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes s 2) (payload : Tapes (1+roleCount) 2) (ops : List RowIndex)
    (xs : Fin wireCount → Fin (ActivePrefixStageTripleWords.count
      (canonicalInput rho visit hactive pair rows hgroup hG hGK hrecord)) → Fin (2^ell) → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=ButterflyGuard.halfWidth p sh.bits+1 ∧
      (xs a i j).2.length=ButterflyGuard.halfWidth p sh.bits+1) (d : ℕ) (aux : Tapes 2 2) :
    let inp := canonicalInput rho visit hactive pair rows hgroup hG hGK hrecord
    let parent := CompactComplexChildHeadersData.parent rho visit hactive pair
    Placement.active CompactComplexNonleafRoleEntry.headerPlacement
      (nextCaller inp rows hs control queue scalar tail storage payload ops xs hw d aux)=
      ActiveRepairRankHeadersCommands.bank
        (CompactSpectatorLeafSetup.raw sh rows ell p parent.rho parent.left parent.f parent.slots
          parent.right parent.source.val parent.target.val) :=
  next_raw _ rows hs control queue scalar tail storage payload ops xs hw d aux

end Canonical
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyScalarChildReadiness
