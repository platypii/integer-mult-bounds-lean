import IntegerMultBounds.Machine.CompactComplexScalarCountBudget
import IntegerMultBounds.Machine.CompactComplexScalarRolePorts
import IntegerMultBounds.Machine.CompactComplexNativeCodecFrame

/-! The genuine controller/native/role bank derives scalar coefficient count
from its retained native original13 and ell/p descriptors. Existing storage
indices remain fixed; immutable scalar43, roles, ledgers and stacks are framed. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarCountRootBank
noncomputable section
open CompactComplexNativeCodecFrame (bank permanentTapes headerSlot originalSlot)
open CompactComplexControllerNativeFrame (storageSlot tapes)
open ActiveRepairRankHeadersCommands (State)
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}

def countSlot (header : Fin s) : Fin (permanentTapes s c) :=
  Fin.castAdd c (storageSlot (Fin.castAdd 43 header))
def common (header : Fin s) (j : Fin 16) : Fin (permanentTapes s c) :=
  if j=15 then countSlot header else headerSlot (CompactComplexScalarCountPlaced.ports j)

theorem common_injective (header : Fin s) : Function.Injective (common (c:=c) header) := by
  intro i j h
  by_cases hi : i=15 <;> by_cases hj : j=15
  · exact hi.trans hj.symm
  · have hv := congrArg Fin.val h
    simp only [common,hi,hj,↓reduceIte,countSlot,headerSlot,storageSlot,
      CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
    have hp := (CompactComplexScalarCountPlaced.ports j).isLt
    omega
  · have hv := congrArg Fin.val h
    simp only [common,hi,hj,↓reduceIte,countSlot,headerSlot,storageSlot,
      CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
    have hp := (CompactComplexScalarCountPlaced.ports i).isLt
    omega
  · apply CompactComplexScalarCountPlaced.ports_injective
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [common,hi,hj,↓reduceIte,headerSlot,
      CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega

def program (header : Fin s) := CompactComplexScalarCountPlaced.program (common (c:=c) header)
  (common_injective header)
def output (header : Fin s) (v : Tapes (permanentTapes s c) 2) (N : ℕ) :=
  CompactComplexScalarCountPlaced.output (common header) v N

theorem header_bank (control : Tapes 43 2) (queue : Tapes 1 2) (scalar stage : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+c) 2) (j : Fin 43) :
    (bank control queue scalar stage tail storage payload).head (headerSlot j)=
      (ActiveRepairRankHeadersCommands.bank (a:=2) stage).head j ∧
    (bank control queue scalar stage tail storage payload).tape (headerSlot j)=
      (ActiveRepairRankHeadersCommands.bank (a:=2) stage).tape j := by
  simp only [headerSlot,CompactComplexNativeCodecFrame.bank,CompactComplexNativeRoleBridge.bank,
    CompactComplexControllerNativeFrame.bank,CompactComplexNativeRoleBridge.native,
    CompactComplexControllerNativeFrame.nativeSlot,Tapes.append,Fin.addCases_left,Fin.addCases_right,and_self]

theorem count_bank (header : Fin s) (control : Tapes 43 2) (queue : Tapes 1 2) (scalar stage : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+c) 2) :
    (bank control queue scalar stage tail storage payload).head (countSlot header)=storage.head header ∧
    (bank control queue scalar stage tail storage payload).tape (countSlot header)=storage.tape header := by
  simp only [countSlot,CompactComplexNativeCodecFrame.bank,CompactComplexNativeRoleBridge.bank,
    CompactComplexControllerNativeFrame.bank,storageSlot,Tapes.append,Fin.addCases_left,Fin.addCases_right,and_self]

private theorem input_payload (header : Fin s) (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar : State) {sh : Shape} (v : Stage sh) (rows ell p : ℕ) (tail : Tapes 22 2)
    (storage : Tapes s 2) (payload : Tapes (1+c) 2)
    (hh : storage.head header=0) (ht : storage.tape header=(fun _ => blank)) :
    SharedBank.payload (ActiveRepairRankHeadersCommands.bank (a:=2) (CompactComplexNativeCodec.raw v rows ell p))
      CompactComplexScalarCountPlaced.ports=
    SharedBank.payload (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell p) tail storage payload)
      (common header) := by
  apply congrArg₂ Tapes.mk
  · funext j
    by_cases hj : j=15
    · subst j
      change 0=(bank control queue scalar (CompactComplexNativeCodec.raw v rows ell p) tail storage payload).head (countSlot header)
      exact ((count_bank header control queue scalar _ tail storage payload).1.trans hh).symm
    · simp only [common,hj,↓reduceIte]
      exact (header_bank control queue scalar _ tail storage payload _).1.symm
  · funext j
    by_cases hj : j=15
    · subst j
      change (fun _ => blank)=(bank control queue scalar (CompactComplexNativeCodec.raw v rows ell p) tail storage payload).tape (countSlot header)
      exact ((count_bank header control queue scalar _ tail storage payload).2.trans ht).symm
    · simp only [common,hj,↓reduceIte]
      exact (header_bank control queue scalar _ tail storage payload _).2.symm

/-- Only a blank count slot is supplied. The number itself is physically
constructed from the genuine stage original descriptors and retained ell. -/
theorem runs (header : Fin s) (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State)
    {sh : Shape} (v : Stage sh) (rows ell p : ℕ) (tail : Tapes 22 2)
    (storage : Tapes s 2) (payload : Tapes (1+c) 2)
    (hr : 0<rows) (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hh : storage.head header=0) (ht : storage.tape header=(fun _ => blank)) :
    let caller := bank control queue scalar (CompactComplexNativeCodec.raw v rows ell p) tail storage payload
    HoareTime (program (c:=c) header) (fun z => z=CleanSubbank.bank (s:=43) caller)
      (fun z => z=CleanSubbank.bank (s:=43) (output header caller (rows*2^sh.bits*2^ell)))
      (CompactComplexScalarCountBudget.constant*(rows*2^sh.bits*2^ell)) := by
  exact CompactComplexScalarCountBudget.placed_runs_linear (common header) (common_injective header) _
    sh rows ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val hr hG hA hK
    (input_payload header control queue scalar v rows ell p tail storage payload hh ht)

/-- On the actual expanded native polynomial geometry, setup is linear in
the original native record volume with all moves and work cleanup paid. -/
theorem runs_native (header : Fin s) (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State)
    {sh : Shape} (v : Stage sh) (rows ell p : ℕ) (tail : Tapes 22 2)
    (storage : Tapes s 2) (payload : Tapes (1+c) 2)
    (hr : 0<rows) (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hh : storage.head header=0) (ht : storage.tape header=(fun _ => blank)) :
    let nativeStage := NativePolynomialStageShape.stage v ell p
    let caller := bank control queue scalar (CompactComplexNativeCodec.raw nativeStage rows ell p) tail storage payload
    HoareTime (program (c:=c) header) (fun z => z=CleanSubbank.bank (s:=43) caller)
      (fun z => z=CleanSubbank.bank (s:=43) (output header caller (rows*2^sh.bits*2^ell)))
      (CompactComplexScalarCountBudget.constant*(rows*(NativePolynomialStageShape.shape sh ell p).recordWidth)) := by
  have h := runs header control queue scalar (NativePolynomialStageShape.stage v ell p) rows ell p
    tail storage payload hr hG hA hK hh ht
  exact h.consequence (fun _ h => h) (fun _ h => h)
    (Nat.mul_le_mul_left _ (CompactComplexScalarCountBudget.count_le_native_volume sh rows ell p))

theorem count_ready (header : Fin s) (v : Tapes (permanentTapes s c) 2) (N : ℕ) :
    (output header v N).head (countSlot header)=1 ∧
    (output header v N).tape (countSlot header)=RadixZeroFill.encodedBinary (bits N) := by
  exact CompactComplexScalarCountPlaced.output_count (common header) v N

/-- Every caller cell outside the one generated count header is preserved. -/
theorem output_frame (header : Fin s) (v : Tapes (permanentTapes s c) 2) (N : ℕ)
    (i : Fin (permanentTapes s c)) (hi : i≠countSlot header) :
    (output header v N).head i=v.head i ∧ (output header v N).tape i=v.tape i :=
  CompactComplexScalarCountPlaced.output_outside (common header) v N i hi

theorem role_ne_count (header : Fin s) (j : Fin c) :
    CompactComplexNativeRoleBridge.roleSlot (s:=s+43) j≠countSlot (c:=c) header := by
  intro h
  have hv := congrArg Fin.val h
  simp only [CompactComplexNativeRoleBridge.roleSlot,countSlot,storageSlot,tapes,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  have := header.isLt
  omega

theorem old_storage_frame (header j : Fin s) (v : Tapes (permanentTapes s c) 2) (N : ℕ)
    (hj : j≠header) :
    (output header v N).head (countSlot j)=v.head (countSlot j) ∧
    (output header v N).tape (countSlot j)=v.tape (countSlot j) := by
  apply output_frame
  intro h
  apply hj
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [countSlot,storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

theorem original_frame (header : Fin s) (v : Tapes (permanentTapes s c) 2) (N : ℕ) (j : Fin 43) :
    (output header v N).head (originalSlot j)=v.head (originalSlot j) ∧
    (output header v N).tape (originalSlot j)=v.tape (originalSlot j) := by
  apply output_frame
  intro h
  have hv := congrArg Fin.val h
  simp only [originalSlot,countSlot,storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  have := header.isLt
  omega

/-- Count storage can be chosen beyond the existing stack ports; the same
pointwise frame theorem retains any stack index distinct from that choice. -/
theorem protected_storage (hs : 9<s) (header : Fin s)
    (h7 : header.val≠7) (h8 : header.val≠8) (h9 : header.val≠9)
    (v : Tapes (permanentTapes s c) 2) (N : ℕ) (j : Fin 3) :
    let ledger : Fin s := ⟨7+j.val,by omega⟩
    (output header v N).head (countSlot ledger)=v.head (countSlot ledger) ∧
    (output header v N).tape (countSlot ledger)=v.tape (countSlot ledger) := by
  apply old_storage_frame
  intro h
  have hv := congrArg Fin.val h
  fin_cases j <;> simp only at hv <;> omega

/-- Genuine role arrays and the physically independent live denominator turn
into scalar Ready after the proved count constructor runs on matching stage
geometry. Existing role streams are stationary throughout count setup. -/
theorem scalar_ready {sh : Shape} (inp : ActivePrefixStageFullData.Inputs sh)
    (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (v : Tapes (permanentTapes s CompactComplexRolePhaseSite.roleCount) 2)
    {ell w : ℕ}
    (xs : Fin CompactComplexScalarRowBlock.wireCount →
      Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → ButterflyStreamData.Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=w ∧ (xs a i j).2.length=w) (d : ℕ)
    (hsource : ∀ a,v.head (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=0 ∧
      v.tape (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=
        SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
          (ActivePrefixStageNativePolynomial.rows inp (xs a) (hw a)))))
    (hlive : v.head (countSlot (c:=CompactComplexRolePhaseSite.roleCount) ⟨7,hs⟩)=1 ∧
      v.tape (countSlot (c:=CompactComplexRolePhaseSite.roleCount) ⟨7,hs⟩)=
        RadixZeroFill.encodedBinary (bits d)) :
    CompactComplexScalarRolePorts.Ready (s:=s+43) (by omega) (Fin.castAdd 43 header)
      (output header v (inp.rows*2^sh.bits*2^ell))
      (fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a)) d := by
  apply CompactComplexScalarRolePorts.ready_native inp (by omega) (Fin.castAdd 43 header)
    (output header v (inp.rows*2^sh.bits*2^ell)) xs hw d
  · intro a
    have hf := output_frame header v (inp.rows*2^sh.bits*2^ell) _
      (role_ne_count header (CompactComplexScalarRolePorts.roleIndex a))
    exact ⟨hf.1.trans (hsource a).1,hf.2.trans (hsource a).2⟩
  · rw [←CompactComplexScalarCountHeaders.native_count inp ell]
    exact count_ready header v _
  · have hj : (⟨7,hs⟩ : Fin s)≠header := by intro h; exact hh (congrArg Fin.val h).symm
    have hf := old_storage_frame header ⟨7,hs⟩ v (inp.rows*2^sh.bits*2^ell) hj
    exact ⟨hf.1.trans hlive.1,hf.2.trans hlive.2⟩

end
end IntegerMultBounds.Machine.CompactComplexScalarCountRootBank
