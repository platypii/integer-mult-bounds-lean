import IntegerMultBounds.Machine.CompactComplexScalarNativeEndpoint
import IntegerMultBounds.Machine.CompactComplexSpectatorTargetBank

/-! Scalar source replacement and count destruction reconstruct the literal
original codec caller. Only true live storage7 and genuine role streams change;
all native metadata, immutable scalar descriptors and stacks remain in place. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarCallerEndpoint
noncomputable section
open CompactComplexNativeCodecFrame (bank permanentTapes)
open CompactComplexSpectatorTargetBank (roleSlot oldSlot)
open CompactComplexControllerNativeFrame (tapes)
open ActiveRepairRankHeadersCommands (State)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}

/-- Source65 is retained; every actual permanent role receives its new word. -/
def emitted (payload : Tapes (1+c) 2) (words : Fin c → ℤ → Fin 6) : Tapes (1+c) 2 :=
  ⟨Fin.addCases (fun i : Fin 1 => payload.head (Fin.castAdd c i)) (fun _ => 0),
    Fin.addCases (fun i : Fin 1 => payload.tape (Fin.castAdd c i)) words⟩

def storageOutput (hs : 7<s) (storage : Tapes s 2) (d : ℕ) :=
  setTape storage ⟨7,hs⟩ (RadixZeroFill.encodedBinary (bits d)) 1

private theorem emitted_source (payload : Tapes (1+c) 2) (words : Fin c → ℤ → Fin 6) :
    CompactComplexNativeRoleBridge.single (emitted payload words)=CompactComplexNativeRoleBridge.single payload := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem prefix_emitted (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : State) (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+c) 2)
    (words : Fin c → ℤ → Fin 6) (i : Fin (tapes (s+43))) :
    (bank control queue scalar stage tail storage (emitted payload words)).head (Fin.castAdd c i)=
      (bank control queue scalar stage tail storage payload).head (Fin.castAdd c i) ∧
    (bank control queue scalar stage tail storage (emitted payload words)).tape (Fin.castAdd c i)=
      (bank control queue scalar stage tail storage payload).tape (Fin.castAdd c i) := by
  simp only [bank,CompactComplexNativeRoleBridge.bank,CompactComplexNativeRoleBridge.native,
    emitted_source,Tapes.append,Fin.addCases_left,and_self]

private theorem bank_storage (hs : 7<s) (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : State) (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+c) 2) (d : ℕ) :
    bank control queue scalar stage tail (storageOutput hs storage d) payload=
      setTape (bank control queue scalar stage tail storage payload) (oldSlot ⟨7,hs⟩)
        (RadixZeroFill.encodedBinary (bits d)) 1 := by
  unfold storageOutput oldSlot bank CompactComplexNativeRoleBridge.bank
    CompactComplexControllerNativeFrame.storageSlot CompactComplexControllerNativeFrame.bank
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_left]

private theorem prefix_ne_role (i : Fin (tapes (s+43))) (j : Fin c) :
    Fin.castAdd c i≠(roleSlot (s:=s) j) := by
  intro h
  have hv := congrArg Fin.val h
  simp only [roleSlot,CompactComplexNativeRoleBridge.roleSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  have := i.isLt
  omega

private theorem slot_injective : Function.Injective (oldSlot (s:=s) (c:=c)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [oldSlot,CompactComplexControllerNativeFrame.storageSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem caller_endpoint (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar stage : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+c) 2)
    (words : Fin c → ℤ → Fin 6) (d : ℕ) (out : Tapes (permanentTapes s c) 2)
    (hblank : storage.head header=0 ∧ storage.tape header=(fun _ => blank))
    (hc : out.head (oldSlot header)=0 ∧ out.tape (oldSlot header)=(fun _ => blank))
    (hl : out.head (oldSlot ⟨7,hs⟩)=1 ∧ out.tape (oldSlot ⟨7,hs⟩)=RadixZeroFill.encodedBinary (bits d))
    (hr : ∀ j,out.head (roleSlot j)=0 ∧ out.tape (roleSlot j)=words j)
    (hf : ∀ i,i≠oldSlot header → i≠oldSlot ⟨7,hs⟩ →
      (∀ j,roleSlot j≠i) → out.head i=(bank control queue scalar stage tail storage payload).head i ∧
        out.tape i=(bank control queue scalar stage tail storage payload).tape i) :
    out=bank control queue scalar stage tail (storageOutput hs storage d) (emitted payload words) := by
  have hne : (⟨7,hs⟩ : Fin s)≠header := by
    intro h
    exact hh (congrArg Fin.val h).symm
  have count_word := CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail
    (storageOutput hs storage d) (emitted payload words) header
  have count_head : (storageOutput hs storage d).head header=0 := by
    simpa only [storageOutput,setTape,Function.update_of_ne hne.symm] using hblank.1
  have count_tape : (storageOutput hs storage d).tape header=(fun _ => blank) := by
    simpa only [storageOutput,setTape,Function.update_of_ne hne.symm] using hblank.2
  have live_word := CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail
    (storageOutput hs storage d) (emitted payload words) ⟨7,hs⟩
  have live_head : (storageOutput hs storage d).head ⟨7,hs⟩=1 := by simp [storageOutput,setTape]
  have live_tape : (storageOutput hs storage d).tape ⟨7,hs⟩=RadixZeroFill.encodedBinary (bits d) := by
    simp [storageOutput,setTape]
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases (m:=tapes (s+43)) (n:=c) with
  | right j =>
    have h := CompactComplexSpectatorTargetBank.role_bank control queue scalar stage tail
      (storageOutput hs storage d) (emitted payload words) j
    simp only [emitted,Fin.addCases_right] at h
    first | exact (hr j).1.trans h.1.symm | exact (hr j).2.trans h.2.symm
  | left i =>
    by_cases hcount : Fin.castAdd c i=oldSlot header
    · rw [hcount]
      first | exact hc.1.trans (count_word.1.trans count_head).symm
            | exact hc.2.trans (count_word.2.trans count_tape).symm
    by_cases hlive : Fin.castAdd c i=oldSlot ⟨7,hs⟩
    · rw [hlive]
      first | exact hl.1.trans (live_word.1.trans live_head).symm
            | exact hl.2.trans (live_word.2.trans live_tape).symm
    have hframe := hf _ hcount hlive (fun j => (prefix_ne_role i j).symm)
    have hp := prefix_emitted control queue scalar stage tail storage payload words i
    have hb := bank_storage hs control queue scalar stage tail storage (emitted payload words) d
    have hbhead := congrArg (fun z => z.head (Fin.castAdd c i)) hb
    have hbtape := congrArg (fun z => z.tape (Fin.castAdd c i)) hb
    simp only [setTape,Function.update_of_ne hlive] at hbhead hbtape
    first | exact hframe.1.trans (hp.1.symm.trans hbhead.symm)
          | exact hframe.2.trans (hp.2.symm.trans hbtape.symm)


open CompactComplexScalarRowBlock (wireCount)
open CompactComplexRolePhaseSite (roleCount)
open CompactComplexScalarRolePorts (roleIndex)
open CompactComplexScalarIntegerRows (RowIndex)
open ButterflyStreamData (Coefficient)
attribute [local irreducible] Networks.ComplexRank25.program CompactComplexScalarIntegerRows.gates

/-- Count lifecycle output is the literal original caller bank. Count was
blank at entry and is blank at return; only storage7 and actual role words
change, so every following event can use its genuine raw-bank contract. -/
theorem output_bank {N : ℕ} (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar stage : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+roleCount) 2)
    (data : Fin wireCount → Fin N → Coefficient) (d : ℕ)
    (hblank : storage.head header=0 ∧ storage.tape header=(fun _ => blank)) :
    CompactComplexScalarCountLifecycle.output hs header
      (bank control queue scalar stage tail storage payload) data d=
    bank control queue scalar stage tail (storageOutput hs storage d)
      (emitted payload (fun j => ButterflyStreamData.full (fun _ => blank) 0 (data (roleIndex.symm j)))) := by
  apply caller_endpoint hs header hh control queue scalar stage tail storage payload _ d _ hblank
    (CompactComplexScalarCountLifecycle.output_count hs header _ data d)
    (CompactComplexScalarCountLifecycle.output_live hs header hh _ data d)
  · intro j
    have h := CompactComplexScalarNativeEndpoint.output_source hs header hh
      (bank control queue scalar stage tail storage payload) data d (roleIndex.symm j)
    simpa only [roleSlot,Equiv.apply_symm_apply] using h
  · intro i hc hl hr
    exact CompactComplexScalarNativeEndpoint.output_frame hs header
      (bank control queue scalar stage tail storage payload) data d i hc hl (fun a => hr (roleIndex a))

/-- Native role payload physically emitted by a complete named scalar block. -/
def nativePayload {sh : CompactGadgetReservationShape.Shape} {R w : ℕ}
    (inp : ActivePrefixStageFullData.Inputs sh) (ops : List RowIndex)
    (xs : Fin wireCount → Fin (ActivePrefixStageTripleWords.count inp) → Fin R → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=w ∧ (xs a i j).2.length=w)
    (payload : Tapes (1+roleCount) 2) :=
  emitted payload (fun j => SymbolTripleClean.word
    (List.ofFn (ActivePrefixStageNativeRows.flat
      (ActivePrefixStageNativePolynomial.rows inp
        (CompactComplexScalarNativeEndpoint.executed ops xs (roleIndex.symm j))
        (CompactComplexScalarNativeEndpoint.executed_width ops xs hw (roleIndex.symm j))))))

/-- The actual executed polynomial arrays occupy the next literal raw caller,
with unchanged native descriptors, original scalar43, controller, queue, tail
and payload0. Only the physically advanced live denominator remains changed. -/
theorem output_executed_bank {sh : CompactGadgetReservationShape.Shape} {R w : ℕ}
    (inp : ActivePrefixStageFullData.Inputs sh) (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar stage : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+roleCount) 2)
    (ops : List RowIndex)
    (xs : Fin wireCount → Fin (ActivePrefixStageTripleWords.count inp) → Fin R → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=w ∧ (xs a i j).2.length=w)
    (d : ℕ) (hblank : storage.head header=0 ∧ storage.tape header=(fun _ => blank)) :
    CompactComplexScalarCountLifecycle.output hs header
      (bank control queue scalar stage tail storage payload)
      (CompactComplexScalarPolynomialSequence.execute ops (fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a)))
      (d+ops.length)=
    bank control queue scalar stage tail (storageOutput hs storage (d+ops.length))
      (nativePayload inp ops xs hw payload) := by
  apply caller_endpoint hs header hh control queue scalar stage tail storage payload _ (d+ops.length) _ hblank
    (CompactComplexScalarCountLifecycle.output_count hs header _ _ _)
    (CompactComplexScalarCountLifecycle.output_live hs header hh _ _ _)
  · intro j
    have h := CompactComplexScalarNativeEndpoint.output_executed_native inp hs header hh
      (bank control queue scalar stage tail storage payload) ops xs hw d (roleIndex.symm j)
    simpa only [roleSlot,Equiv.apply_symm_apply] using h
  · intro i hc hl hr
    exact CompactComplexScalarNativeEndpoint.output_frame hs header
      (bank control queue scalar stage tail storage payload) _ _ i hc hl (fun a => hr (roleIndex a))


private theorem emitted_zero (payload : Tapes (1+c) 2) (words : Fin c → ℤ → Fin 6) :
    (emitted payload words).head 0=payload.head 0 ∧
    (emitted payload words).tape 0=payload.tape 0 := ⟨rfl,rfl⟩

/-- The next event reuses precisely the original source65 word and head. -/
theorem native_payload_source {sh : CompactGadgetReservationShape.Shape} {R w : ℕ}
    (inp : ActivePrefixStageFullData.Inputs sh) (ops : List RowIndex)
    (xs : Fin wireCount → Fin (ActivePrefixStageTripleWords.count inp) → Fin R → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=w ∧ (xs a i j).2.length=w)
    (payload : Tapes (1+roleCount) 2) :
    (nativePayload inp ops xs hw payload).head 0=payload.head 0 ∧
    (nativePayload inp ops xs hw payload).tape 0=payload.tape 0 := emitted_zero _ _

private theorem emitted_equiv {m : ℕ} (e : Fin m ≃ Fin c) (payload : Tapes (1+c) 2)
    (words : Fin m → ℤ → Fin 6) (a : Fin m) :
    (emitted payload (fun j => words (e.symm j))).head (Fin.natAdd 1 (e a))=0 ∧
    (emitted payload (fun j => words (e.symm j))).tape (Fin.natAdd 1 (e a))=words a := by
  simp only [emitted,Fin.addCases_right,Equiv.symm_apply_apply,and_self]

/-- Named role-source premises for the next native event are direct endpoint
facts, with no additional bank or stream equality supplied by the caller. -/
theorem native_payload_role {sh : CompactGadgetReservationShape.Shape} {R w : ℕ}
    (inp : ActivePrefixStageFullData.Inputs sh) (ops : List RowIndex)
    (xs : Fin wireCount → Fin (ActivePrefixStageTripleWords.count inp) → Fin R → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=w ∧ (xs a i j).2.length=w)
    (payload : Tapes (1+roleCount) 2) (a : Fin wireCount) :
    (nativePayload inp ops xs hw payload).head (Fin.natAdd 1 (roleIndex a))=0 ∧
    (nativePayload inp ops xs hw payload).tape (Fin.natAdd 1 (roleIndex a))=
      SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
        (ActivePrefixStageNativePolynomial.rows inp (CompactComplexScalarNativeEndpoint.executed ops xs a)
          (CompactComplexScalarNativeEndpoint.executed_width ops xs hw a)))) :=
  emitted_equiv roleIndex payload (fun j => SymbolTripleClean.word
    (List.ofFn (ActivePrefixStageNativeRows.flat
      (ActivePrefixStageNativePolynomial.rows inp (CompactComplexScalarNativeEndpoint.executed ops xs j)
        (CompactComplexScalarNativeEndpoint.executed_width ops xs hw j))))) a

/-- Existing stack and denominator ports outside live7 remain literal. -/
theorem storage_frame (hs : 7<s) (storage : Tapes s 2) (d : ℕ) (i : Fin s) (hi : i.val≠7) :
    (storageOutput hs storage d).head i=storage.head i ∧
    (storageOutput hs storage d).tape i=storage.tape i := by
  have hne : i≠⟨7,hs⟩ := fun h => hi (congrArg Fin.val h)
  simp only [storageOutput,setTape,Function.update_of_ne hne,and_self]

end
end IntegerMultBounds.Machine.CompactComplexScalarCallerEndpoint
