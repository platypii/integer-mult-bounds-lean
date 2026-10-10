import IntegerMultBounds.Machine.CompactComplexSourceReadyScalarEventPath
import IntegerMultBounds.Machine.CompactComplexNonleafRoleMergeReturn

/-! Physical readiness inherited from the literal next scalar caller. The raw
metadata and retained master are read from their actual ports; named role words
are the genuine executed polynomial rows, rather than supplied input codecs. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyPrefixReadiness
noncomputable section
open CompactComplexNativeCodecFrame (bank permanentTapes)
open CompactComplexSpectatorTargetBank (oldSlot roleSlot numericSlot)
open CompactComplexScalarCallerEndpoint (storageOutput nativePayload)
open CompactComplexScalarRowBlock (wireCount)
open CompactComplexRolePhaseSite (roleCount)
open CompactComplexScalarRolePorts (roleIndex)
open CompactComplexScalarIntegerRows (RowIndex)
open ButterflyStreamData (Coefficient)
variable {s c : ℕ}

private theorem supported_transport {f g : ℤ → Fin 6} {n : ℕ}
    (he : f=g) (h : RoleArrayStack.Supported g n) : RoleArrayStack.Supported f n := by
  intro z hz
  exact congrFun he z |>.trans (h z hz)

private theorem supported_volume {f : ℤ → Fin 6} {n m : ℕ}
    (he : n=m) (h : RoleArrayStack.Supported f n) : RoleArrayStack.Supported f m :=
  he ▸ h

/-- Native stage rows and child-entry coefficient arrays use literally the
same tape encoding and row-major coefficient order. -/
theorem native_array_word {sh : CompactGadgetReservationShape.Shape} {R w : ℕ}
    (inp : ActivePrefixStageFullData.Inputs sh)
    (xs : Fin (ActivePrefixStageTripleWords.count inp) → Fin R → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
      (ActivePrefixStageNativePolynomial.rows inp xs hw)))=
    NativeZeroPadding.word
      (NativeZeroPaddingArray.word (ActivePrefixStageNativePolynomial.flattenArray xs)) := by
  rw [ActivePrefixStageNativePolynomial.serialized_rows]
  rfl

/-- A completely free suffix above the real stack head, independent of the
next frame's generated runtime volume. Ancestor cells below the head may remain. -/
def BlankAfter {t : ℕ} (v : Tapes t 2) (i : Fin t) : Prop :=
  ∀ z,v.head i ≤ z → v.tape i z=blank

theorem blankAfter_frame {t : ℕ} {v w : Tapes t 2} {i : Fin t}
    (hf : w.head i=v.head i ∧ w.tape i=v.tape i) (h : BlankAfter v i) :
    BlankAfter w i := by
  intro z hz
  rw [hf.2]
  exact h z (hf.1 ▸ hz)

theorem blankAfter_free (selected : Fin c) (masterVolume roleVolume : ℕ)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (h : BlankAfter v CompactComplexNonleafRoleEntry.stack) :
    CompactComplexNonleafRoleReturn.Free selected masterVolume roleVolume v := by
  intro z hz _
  exact h z hz

/-- Retained source65 is payload0, independently of scalar role replacement. -/
theorem source_bank (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes s 2) (payload : Tapes (1+c) 2) :
    (bank control queue scalar stage tail storage payload).head (numericSlot 65)=payload.head 0 ∧
    (bank control queue scalar stage tail storage payload).tape (numericSlot 65)=payload.tape 0 := by
  simp only [bank,CompactComplexNativeRoleBridge.bank,
    CompactComplexControllerNativeFrame.bank,numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Tapes.append,
    Fin.addCases_left,Fin.addCases_right,CompactComplexNativeRoleBridge.native,
    CompactComplexNativeRoleBridge.single]
  exact ⟨rfl,rfl⟩

/-- Every storage port other than live7 retains its literal head and entire
word. This includes target8, count-header0 and all persistent stack ports. -/
theorem next_storage (hs : 7<s) (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes s 2) (payload nextPayload : Tapes (1+c) 2) (d : ℕ)
    (i : Fin s) (hi : i.val≠7) :
    (bank control queue scalar stage tail (storageOutput hs storage d) nextPayload).head (oldSlot i)=
      (bank control queue scalar stage tail storage payload).head (oldSlot i) ∧
    (bank control queue scalar stage tail (storageOutput hs storage d) nextPayload).tape (oldSlot i)=
      (bank control queue scalar stage tail storage payload).tape (oldSlot i) := by
  have hn := CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail
    (storageOutput hs storage d) nextPayload i
  have ho := CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail storage payload i
  have hf := CompactComplexScalarCallerEndpoint.storage_frame hs storage d i hi
  exact ⟨hn.1.trans (hf.1.trans ho.1.symm),hn.2.trans (hf.2.trans ho.2.symm)⟩

section Scalar
variable {sh : CompactGadgetReservationShape.Shape} {R w : ℕ}
variable (inp : ActivePrefixStageFullData.Inputs sh) (hs : 7<s)
variable (control : Tapes 43 2) (queue : Tapes 1 2)
variable (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
variable (storage : Tapes s 2) (payload : Tapes (1+roleCount) 2)
variable (ops : List RowIndex)
variable (xs : Fin wireCount → Fin (ActivePrefixStageTripleWords.count inp) → Fin R → Coefficient)
variable (hw : ∀ a i j,(xs a i j).1.length=w ∧ (xs a i j).2.length=w) (d : ℕ)

/-- The entire immutable original/raw 86-tape metadata bank is retained by
the actual scalar endpoint, including every numeric head. -/
theorem next_metadata :
    SharedBank.payload (bank control queue scalar stage tail (storageOutput hs storage d)
      (nativePayload inp ops xs hw payload)) CompactComplexNativeCodecFrame.slot=
    (ActiveRepairRankHeadersCommands.bank scalar).append (ActiveRepairRankHeadersCommands.bank stage) :=
  CompactComplexNativeCodecFrame.payload_bank _ _ _ _ _ _ _

theorem next_source :
    (bank control queue scalar stage tail (storageOutput hs storage d)
      (nativePayload inp ops xs hw payload)).head (numericSlot 65)=
      (bank control queue scalar stage tail storage payload).head (numericSlot 65) ∧
    (bank control queue scalar stage tail (storageOutput hs storage d)
      (nativePayload inp ops xs hw payload)).tape (numericSlot 65)=
      (bank control queue scalar stage tail storage payload).tape (numericSlot 65) := by
  have hn := source_bank control queue scalar stage tail (storageOutput hs storage d)
    (nativePayload inp ops xs hw payload)
  have ho := source_bank control queue scalar stage tail storage payload
  have hf := CompactComplexScalarCallerEndpoint.native_payload_source inp ops xs hw payload
  exact ⟨hn.1.trans (hf.1.trans ho.1.symm),hn.2.trans (hf.2.trans ho.2.symm)⟩

/-- Genuine named native rows, with widths obtained from executed_width. -/
theorem next_role (a : Fin wireCount) :
    (bank control queue scalar stage tail (storageOutput hs storage d)
      (nativePayload inp ops xs hw payload)).head (roleSlot (roleIndex a))=0 ∧
    (bank control queue scalar stage tail (storageOutput hs storage d)
      (nativePayload inp ops xs hw payload)).tape (roleSlot (roleIndex a))=
      SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
        (ActivePrefixStageNativePolynomial.rows inp
          (CompactComplexScalarNativeEndpoint.executed ops xs a)
          (CompactComplexScalarNativeEndpoint.executed_width ops xs hw a)))) := by
  have hb := CompactComplexSpectatorTargetBank.role_bank control queue scalar stage tail
    (storageOutput hs storage d) (nativePayload inp ops xs hw payload) (roleIndex a)
  have hr := CompactComplexScalarCallerEndpoint.native_payload_role inp ops xs hw payload a
  exact ⟨hb.1.trans hr.1,hb.2.trans hr.2⟩

theorem next_role_supported (a : Fin wireCount) :
    RoleArrayStack.Supported
      ((bank control queue scalar stage tail (storageOutput hs storage d)
        (nativePayload inp ops xs hw payload)).tape (roleSlot (roleIndex a)))
      (ActivePrefixStageTripleWords.count inp*ActivePrefixStageNativePolynomial.symbols R w) := by
  rw [(next_role inp hs control queue scalar stage tail storage payload ops xs hw d a).2]
  apply RoleArrayStack.supported_word
  simp only [List.length_ofFn]
  exact le_rfl

/-- Source head/support assumptions survive scalar execution because the
master stream is literally retained, including possible blank interior cells. -/
theorem next_source_supported (volume : ℕ)
    (h : (bank control queue scalar stage tail storage payload).head (numericSlot 65)=0 ∧
      RoleArrayStack.Supported
        ((bank control queue scalar stage tail storage payload).tape (numericSlot 65)) volume) :
    (bank control queue scalar stage tail (storageOutput hs storage d)
      (nativePayload inp ops xs hw payload)).head (numericSlot 65)=0 ∧
      RoleArrayStack.Supported
        ((bank control queue scalar stage tail (storageOutput hs storage d)
          (nativePayload inp ops xs hw payload)).tape (numericSlot 65)) volume := by
  have hf := next_source inp hs control queue scalar stage tail storage payload ops xs hw d
  exact ⟨hf.1.trans h.1,supported_transport hf.2 h.2⟩

theorem next_header_blank (header : Fin s) (hh : header.val≠7)
    (h : storage.head header=0 ∧ storage.tape header=(fun _ => blank)) :
    (bank control queue scalar stage tail (storageOutput hs storage d)
      (nativePayload inp ops xs hw payload)).head (oldSlot header)=0 ∧
    (bank control queue scalar stage tail (storageOutput hs storage d)
      (nativePayload inp ops xs hw payload)).tape (oldSlot header)=(fun _ => blank) := by
  have hb := CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail
    (storageOutput hs storage d) (nativePayload inp ops xs hw payload) header
  have hf := CompactComplexScalarCallerEndpoint.storage_frame hs storage d header hh
  exact ⟨hb.1.trans (hf.1.trans h.1),hb.2.trans (hf.2.trans h.2)⟩

end Scalar

/-- The native serialization length is precisely the generated stream volume
for the true retained geometry and executed coefficient widths. -/
theorem native_volume {sh : CompactGadgetReservationShape.Shape}
    (inp : ActivePrefixStageFullData.Inputs sh) (ell p c : ℕ) :
    ActivePrefixStageTripleWords.count inp*
      ActivePrefixStageNativePolynomial.symbols (2^ell) (ButterflyGuard.halfWidth p sh.bits+1)=
    CompactComplexSpectatorVolumeHeaders.streamVolume sh c inp.rows ell p false := by
  have hn := CompactComplexScalarCountHeaders.native_count inp ell
  unfold ActivePrefixStageNativePolynomial.symbols
    CompactComplexSpectatorVolumeHeaders.streamVolume CompactComplexSpectatorVolumeHeaders.roleRows
    CompactNativeRoleHeaders.recordWidth ButterflyGuard.width
  simp only [Bool.false_eq_true,ite_false]
  calc
    _=(ActivePrefixStageTripleWords.count inp*2^ell)*
        (2*(ButterflyGuard.halfWidth p sh.bits+1+1)) := by ring
    _=(inp.rows*2^sh.bits*2^ell)*(2*(ButterflyGuard.halfWidth p sh.bits+1+1)) := by rw [←hn]

/-- A child-selected role uses the actual parent quotient rows, so its word
support is exactly the role-volume header used by physical parking. -/
theorem native_role_volume {sh : CompactGadgetReservationShape.Shape}
    (inp : ActivePrefixStageFullData.Inputs sh) (rows ell p c : ℕ)
    (hrows : inp.rows=rows/c) :
    ActivePrefixStageTripleWords.count inp*
      ActivePrefixStageNativePolynomial.symbols (2^ell) (ButterflyGuard.halfWidth p sh.bits+1)=
    CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p true := by
  rw [native_volume inp ell p c]
  simp only [CompactComplexSpectatorVolumeHeaders.streamVolume,
    CompactComplexSpectatorVolumeHeaders.roleRows,Bool.false_eq_true,ite_true,ite_false,hrows]

/-- Literal prefix port inside the scalar-inclusive fixed machine. -/
def fullPort (i : Fin (CompactComplexSourceReadyScalarWorkspace.permanentTapes s c)) :
    Fin (CompactComplexSourceReadyScalarWorkspace.tapes s c) :=
  Fin.castAdd CompactComplexSourceReadyScalarWorkspace.scratch
    (⟨i.val,lt_of_lt_of_le i.isLt CompactComplexSourceReadyScalarWorkspace.public_le⟩ :
      Fin (CompactComplexSourceReadyScalarWorkspace.nodeTapes s c))

theorem full_output_port (v : Tapes (CompactComplexSourceReadyScalarWorkspace.nodeTapes s c) 2)
    (next : Tapes (CompactComplexSourceReadyScalarWorkspace.permanentTapes s c) 2)
    (i : Fin (CompactComplexSourceReadyScalarWorkspace.permanentTapes s c)) :
    (CompactComplexSourceReadyScalarWorkspace.ready
      (CompactComplexSourceReadyScalarWorkspace.output v next)).head (fullPort i)=next.head i ∧
    (CompactComplexSourceReadyScalarWorkspace.ready
      (CompactComplexSourceReadyScalarWorkspace.output v next)).tape (fullPort i)=next.tape i := by
  simp only [fullPort,CompactComplexSourceReadyScalarWorkspace.ready,Tapes.append,Fin.addCases_left]
  exact CompactComplexSourceReadyScalarWorkspace.output_public v next i

theorem full_output_payload {p : ℕ}
    (v : Tapes (CompactComplexSourceReadyScalarWorkspace.nodeTapes s c) 2)
    (next : Tapes (CompactComplexSourceReadyScalarWorkspace.permanentTapes s c) 2)
    (slot : Fin p → Fin (CompactComplexSourceReadyScalarWorkspace.permanentTapes s c)) :
    SharedBank.payload (CompactComplexSourceReadyScalarWorkspace.ready
      (CompactComplexSourceReadyScalarWorkspace.output v next))
      (fun i => fullPort (slot i))=SharedBank.payload next slot := by
  apply congrArg₂ Tapes.mk <;> funext i
  · exact (full_output_port v next (slot i)).1
  · exact (full_output_port v next (slot i)).2

/-- Source-ready workspace suffix ports retain their whole state in the actual
ready(output) endpoint, as opposed to only its abstract permanent projection. -/
theorem full_output_frame (v : Tapes (CompactComplexSourceReadyScalarWorkspace.nodeTapes s c) 2)
    (next : Tapes (CompactComplexSourceReadyScalarWorkspace.permanentTapes s c) 2)
    (i : Fin (CompactComplexSourceReadyScalarWorkspace.nodeTapes s c))
    (hi : CompactComplexSourceReadyScalarWorkspace.permanentTapes s c ≤ i.val) :
    (CompactComplexSourceReadyScalarWorkspace.ready
      (CompactComplexSourceReadyScalarWorkspace.output v next)).head
      (Fin.castAdd CompactComplexSourceReadyScalarWorkspace.scratch i)=v.head i ∧
    (CompactComplexSourceReadyScalarWorkspace.ready
      (CompactComplexSourceReadyScalarWorkspace.output v next)).tape
      (Fin.castAdd CompactComplexSourceReadyScalarWorkspace.scratch i)=v.tape i := by
  simp only [CompactComplexSourceReadyScalarWorkspace.ready,Tapes.append,Fin.addCases_left]
  exact CompactComplexSourceReadyScalarWorkspace.output_frame v next i hi

theorem full_output_blankAfter (v : Tapes (CompactComplexSourceReadyScalarWorkspace.nodeTapes s c) 2)
    (next : Tapes (CompactComplexSourceReadyScalarWorkspace.permanentTapes s c) 2)
    (i : Fin (CompactComplexSourceReadyScalarWorkspace.nodeTapes s c))
    (hi : CompactComplexSourceReadyScalarWorkspace.permanentTapes s c ≤ i.val)
    (h : BlankAfter v i) :
    BlankAfter (CompactComplexSourceReadyScalarWorkspace.ready
      (CompactComplexSourceReadyScalarWorkspace.output v next))
      (Fin.castAdd CompactComplexSourceReadyScalarWorkspace.scratch i) := by
  intro z hz
  have hf := full_output_frame v next i hi
  rw [hf.2]
  exact h z (hf.1 ▸ hz)

section FullScalar
variable {sh : CompactGadgetReservationShape.Shape} {R w : ℕ}
variable (inp : ActivePrefixStageFullData.Inputs sh) (hs : 7<10+s)
variable (control : Tapes 43 2) (queue : Tapes 1 2)
variable (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
variable (storage : Tapes (10+s) 2) (payload : Tapes (1+roleCount) 2)
variable (ops : List RowIndex)
variable (xs : Fin wireCount → Fin (ActivePrefixStageTripleWords.count inp) → Fin R → Coefficient)
variable (hw : ∀ a i j,(xs a i j).1.length=w ∧ (xs a i j).2.length=w) (d : ℕ)
variable (v : Tapes (CompactComplexSourceReadyScalarWorkspace.nodeTapes s roleCount) 2)

/-- Genuine native role words at their actual fixed-machine ports after the
complete scalar event. No next-bank codec or role-word premise is required. -/
theorem full_next_role (a : Fin wireCount) :
    let next := bank control queue scalar stage tail (storageOutput hs storage d)
      (nativePayload inp ops xs hw payload)
    let endpoint := CompactComplexSourceReadyScalarWorkspace.ready
      (CompactComplexSourceReadyScalarWorkspace.output v next)
    endpoint.head (fullPort (roleSlot (roleIndex a)))=0 ∧
    endpoint.tape (fullPort (roleSlot (roleIndex a)))=
      SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
        (ActivePrefixStageNativePolynomial.rows inp
          (CompactComplexScalarNativeEndpoint.executed ops xs a)
          (CompactComplexScalarNativeEndpoint.executed_width ops xs hw a)))) := by
  dsimp only
  have hp := full_output_port v
    (bank control queue scalar stage tail (storageOutput hs storage d)
      (nativePayload inp ops xs hw payload)) (roleSlot (roleIndex a))
  have hr := next_role inp hs control queue scalar stage tail storage payload ops xs hw d a
  exact ⟨hp.1.trans hr.1,hp.2.trans hr.2⟩

/-- The selected role is already the original child-entry array word; no
conversion subroutine or prepared coefficient-word premise is needed. -/
theorem full_next_role_array (a : Fin wireCount) :
    let next := bank control queue scalar stage tail (storageOutput hs storage d)
      (nativePayload inp ops xs hw payload)
    (CompactComplexSourceReadyScalarWorkspace.ready
      (CompactComplexSourceReadyScalarWorkspace.output v next)).tape
      (fullPort (roleSlot (roleIndex a)))=
    NativeZeroPadding.word (NativeZeroPaddingArray.word
      (ActivePrefixStageNativePolynomial.flattenArray
        (CompactComplexScalarNativeEndpoint.executed ops xs a))) := by
  exact (full_next_role inp hs control queue scalar stage tail storage payload ops xs hw d v a).2.trans
    (native_array_word inp _ (CompactComplexScalarNativeEndpoint.executed_width ops xs hw a))

theorem full_next_role_supported (a : Fin wireCount) :
    let next := bank control queue scalar stage tail (storageOutput hs storage d)
      (nativePayload inp ops xs hw payload)
    RoleArrayStack.Supported
      ((CompactComplexSourceReadyScalarWorkspace.ready
        (CompactComplexSourceReadyScalarWorkspace.output v next)).tape
          (fullPort (roleSlot (roleIndex a))))
      (ActivePrefixStageTripleWords.count inp*ActivePrefixStageNativePolynomial.symbols R w) := by
  dsimp only
  have hp := full_output_port v
    (bank control queue scalar stage tail (storageOutput hs storage d)
      (nativePayload inp ops xs hw payload)) (roleSlot (roleIndex a))
  exact supported_transport hp.2
    (next_role_supported inp hs control queue scalar stage tail storage payload ops xs hw d a)

/-- Raw scalar/native metadata on the literal full endpoint is unchanged. -/
theorem full_next_metadata :
    let next := bank control queue scalar stage tail (storageOutput hs storage d)
      (nativePayload inp ops xs hw payload)
    SharedBank.payload
      (CompactComplexSourceReadyScalarWorkspace.permanent
        (CompactComplexSourceReadyScalarWorkspace.output v next))
      CompactComplexNativeCodecFrame.slot=
      (ActiveRepairRankHeadersCommands.bank scalar).append
        (ActiveRepairRankHeadersCommands.bank stage) := by
  dsimp only
  rw [CompactComplexSourceReadyScalarWorkspace.permanent_output]
  exact next_metadata inp hs control queue scalar stage tail storage payload ops xs hw d

/-- Direct physical 86-tape view on the full fixed-machine endpoint, with
all numeric tapes and heads taken at their actual full-bank ports. -/
theorem full_next_raw :
    let next := bank control queue scalar stage tail (storageOutput hs storage d)
      (nativePayload inp ops xs hw payload)
    SharedBank.payload
      (CompactComplexSourceReadyScalarWorkspace.ready
        (CompactComplexSourceReadyScalarWorkspace.output v next))
      (fun i => fullPort (CompactComplexNativeCodecFrame.slot i))=
      (ActiveRepairRankHeadersCommands.bank scalar).append
        (ActiveRepairRankHeadersCommands.bank stage) := by
  dsimp only
  rw [full_output_payload]
  exact next_metadata inp hs control queue scalar stage tail storage payload ops xs hw d

/-- Actual target8, header0 and stack ports retain their full storage states. -/
theorem full_next_storage (i : Fin (10+s)) (hi : i.val≠7) :
    let next := bank control queue scalar stage tail (storageOutput hs storage d)
      (nativePayload inp ops xs hw payload)
    let endpoint := CompactComplexSourceReadyScalarWorkspace.ready
      (CompactComplexSourceReadyScalarWorkspace.output v next)
    endpoint.head (fullPort (oldSlot i))=storage.head i ∧
      endpoint.tape (fullPort (oldSlot i))=storage.tape i := by
  dsimp only
  have hp := full_output_port v
    (bank control queue scalar stage tail (storageOutput hs storage d)
      (nativePayload inp ops xs hw payload)) (oldSlot i)
  have hb := CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail
    (storageOutput hs storage d) (nativePayload inp ops xs hw payload) i
  have hf := CompactComplexScalarCallerEndpoint.storage_frame hs storage d i hi
  exact ⟨hp.1.trans (hb.1.trans hf.1),hp.2.trans (hb.2.trans hf.2)⟩

theorem full_next_source (volume : ℕ)
    (h : payload.head 0=0 ∧ RoleArrayStack.Supported (payload.tape 0) volume) :
    let next := bank control queue scalar stage tail (storageOutput hs storage d)
      (nativePayload inp ops xs hw payload)
    let endpoint := CompactComplexSourceReadyScalarWorkspace.ready
      (CompactComplexSourceReadyScalarWorkspace.output v next)
    endpoint.head (fullPort (numericSlot 65))=0 ∧
      RoleArrayStack.Supported (endpoint.tape (fullPort (numericSlot 65))) volume := by
  dsimp only
  have hp := full_output_port v
    (bank control queue scalar stage tail (storageOutput hs storage d)
      (nativePayload inp ops xs hw payload)) (numericSlot 65)
  have hb := source_bank control queue scalar stage tail (storageOutput hs storage d)
    (nativePayload inp ops xs hw payload)
  have hf := CompactComplexScalarCallerEndpoint.native_payload_source inp ops xs hw payload
  exact ⟨hp.1.trans (hb.1.trans (hf.1.trans h.1)),
    supported_transport (hp.2.trans (hb.2.trans hf.2)) h.2⟩

end FullScalar

/-- Every physical role is ready at the exact generated parent role volume.
The row quotient is geometric data; no serialized-word equality is assumed. -/
theorem full_next_roles {sh : CompactGadgetReservationShape.Shape}
    (inp : ActivePrefixStageFullData.Inputs sh) (hs : 7<10+s)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+roleCount) 2)
    (ops : List RowIndex) (rows ell p d : ℕ) (hrows : inp.rows=rows/roleCount)
    (xs : Fin wireCount → Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=ButterflyGuard.halfWidth p sh.bits+1 ∧
      (xs a i j).2.length=ButterflyGuard.halfWidth p sh.bits+1)
    (v : Tapes (CompactComplexSourceReadyScalarWorkspace.nodeTapes s roleCount) 2) :
    let next := bank control queue scalar stage tail (storageOutput hs storage d)
      (nativePayload inp ops xs hw payload)
    let endpoint := CompactComplexSourceReadyScalarWorkspace.ready
      (CompactComplexSourceReadyScalarWorkspace.output v next)
    ∀ j,endpoint.head (fullPort (roleSlot j))=0 ∧
      RoleArrayStack.Supported (endpoint.tape (fullPort (roleSlot j)))
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh roleCount rows ell p true) := by
  dsimp only
  intro j
  have hh := (full_next_role inp hs control queue scalar stage tail storage payload ops xs hw d v
    (roleIndex.symm j)).1
  have hv := full_next_role_supported inp hs control queue scalar stage tail storage payload ops xs hw d v
    (roleIndex.symm j)
  have hsupp := supported_volume (native_role_volume inp rows ell p roleCount hrows) hv
  simpa only [Equiv.apply_symm_apply] using And.intro hh hsupp

/-- The actual scalar full-bank endpoint preserves every node workspace tape
outside the permanent prefix, including the payload stack's ancestor suffix. -/
theorem output_blankAfter (v : Tapes (CompactComplexSourceReadyScalarWorkspace.nodeTapes s c) 2)
    (next : Tapes (CompactComplexSourceReadyScalarWorkspace.permanentTapes s c) 2)
    (i : Fin (CompactComplexSourceReadyScalarWorkspace.nodeTapes s c))
    (hi : CompactComplexSourceReadyScalarWorkspace.permanentTapes s c ≤ i.val)
    (h : BlankAfter v i) :
    BlankAfter (CompactComplexSourceReadyScalarWorkspace.output v next) i :=
  blankAfter_frame (CompactComplexSourceReadyScalarWorkspace.output_frame v next i hi) h

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyPrefixReadiness
