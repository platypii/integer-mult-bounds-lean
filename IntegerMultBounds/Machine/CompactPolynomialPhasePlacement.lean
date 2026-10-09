import IntegerMultBounds.Machine.CompactPolynomialPhaseDispatch
import IntegerMultBounds.Machine.ActivePrefixStageNativePolynomial
import IntegerMultBounds.Machine.SharedPlacementAlphabet

/-! Place the actual fixed phase-family call on the caller's native source.
The numeric phase bank is outside the entire caller bank; all other caller
cells, including appended native workspace and persistent storage, are framed.
Metadata preparation and all-axis phase aggregation remain separate. -/
namespace IntegerMultBounds.Machine.CompactPolynomialPhasePlacement
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open ButterflyStreamData (Coefficient)
open SharedPlacementAlphabet (setTape sharedPlacement)
open CompactPolynomialPhaseDispatch (count edge)
variable {s : Shape} {a t : ℕ}

def input (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f)
    (ell : ℕ) (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient) :=
  (UnitPhasePolynomialStreamInit.input order v rows axis
    (UnitPhasePolynomialLiteral.tail (fun _ => blank) (fun _ => blank) 0 0 xs) ell).append
    (SharedBank.empty 1 2)

def output (pc : Fin count) (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f)
    (ell : ℕ) (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient) :=
  (UnitPhasePolynomialNative.output order v rows axis (Networks.ComplexPhaseRowSchedule.dimension (edge pc))
    (CompactComplexPhaseControlCodec.weights (edge pc)).reverse ell xs).append (SharedBank.empty 1 2)

def program (ha : 2≤a) (src : Fin t) (pc : Fin count) :=
  Placement.placed (Alphabet.program (SymbolTriplePlaced.encoding ha) (CompactPolynomialPhaseDispatch.call pc))
    (sharedPlacement src (56 : Fin 67))

/-- A genuine phase-family call shares the original source; no execution
callback is assumed. Every caller cell outside that source is retained. -/
theorem runs (ha : 2≤a) (src : Fin t) (caller : Tapes t a) (pc : Fin count)
    (hd : 0<Networks.ComplexPhaseRowSchedule.dimension (edge pc))
    (order : Order) (v : Stage s) (rows : ℕ) (hr : 0<rows) (axis : Fin v.f)
    (hslots : Networks.ComplexPhaseRowSchedule.dimension (edge pc)≤v.slots)
    (hspan : SparsePhaseHeadersData.offset v axis (Networks.ComplexPhaseRowSchedule.dimension (edge pc))+
      (Networks.ComplexPhaseRowSchedule.dimension (edge pc)-1)*(v.f*s.chunk)<s.bits)
    (ell w : ℕ) (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w)
    (hs : caller.tape src=SymbolTriplePlaced.mapTape ha
      (putWord (fun _ => blank) 0 (UnitPhaseFullStreamNormalized.serialized xs)))
    (hp : caller.head src=0) :
    HoareTime (program ha src pc)
      (fun z => z=caller.append
        (setTape (Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) (input order v rows axis ell xs))
          56 (fun _ => blank) 0))
      (fun z => z=(setTape caller src
        ((Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) (output pc order v rows axis ell xs)).tape 56)
        ((Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) (output pc order v rows axis ell xs)).head 56)).append
        (setTape (Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) (output pc order v rows axis ell xs))
          56 (fun _ => blank) 0))
      (2*count+3+UnitPhasePolynomialNative.cost order v rows axis
        (Networks.ComplexPhaseRowSchedule.dimension (edge pc)) ell w) := by
  have h0 := CompactPolynomialPhaseDispatch.call_runs pc hd order v rows hr axis hslots hspan ell w xs hw
  have h1 : HoareTime
      (Alphabet.program (SymbolTriplePlaced.encoding ha) (CompactPolynomialPhaseDispatch.call pc))
      (fun z => z=Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) (input order v rows axis ell xs))
      (fun z => z=Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) (output pc order v rows axis ell xs))
      (2*count+3+UnitPhasePolynomialNative.cost order v rows axis
        (Networks.ComplexPhaseRowSchedule.dimension (edge pc)) ell w) := by
    apply (Alphabet.map_hoare (SymbolTriplePlaced.encoding ha) h0).consequence _ _ le_rfl
    · rintro z rfl; exact ⟨_,rfl,rfl⟩
    · rintro z ⟨b,rfl,rfl⟩; rfl
  exact SharedPlacementAlphabet.shared_hoare h1 caller src (56 : Fin 67) (fun _ => blank) 0 hs hp

/-- Phase work and numeric controls return to their original ready bank;
only the literal native coefficient source changes. -/
theorem output_update (pc : Fin count) (order : Order) (v : Stage s)
    (rows : ℕ) (axis : Fin v.f) (ell : ℕ)
    (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient) :
    output pc order v rows axis ell xs=
      setTape (input order v rows axis ell xs) 56
        (putWord (fun _ => blank) 0 (UnitPhaseFullStreamNormalized.serialized
          (UnitPhasePolynomialLiteralEndpoint.result v axis
            (Networks.ComplexPhaseRowSchedule.dimension (edge pc))
            (CompactComplexPhaseControlCodec.weights (edge pc)).reverse xs))) 0 := by
  unfold output
  rw [UnitPhasePolynomialNative.restored]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- The appended source-sharing slot remains blank; all ready numeric metadata
and every private phase tape are restored literally. -/
theorem cleared_output (pc : Fin count) (order : Order) (v : Stage s)
    (rows : ℕ) (axis : Fin v.f) (ell : ℕ)
    (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient) :
    setTape (output pc order v rows axis ell xs) 56 (fun _ => blank) 0=
      setTape (input order v rows axis ell xs) 56 (fun _ => blank) 0 := by
  rw [output_update,SharedPlacementAlphabet.setTape_setTape]

private theorem map_clear (ha : 2≤a) (b : Tapes 67 2) :
    Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) (setTape b 56 (fun _ => blank) 0)=
      setTape (Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) b) 56 (fun _ => blank) 0 := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i z
    by_cases h : i=56 <;> simp [Alphabet.mapTapes,setTape,h,SymbolTriplePlaced.encoding,blank]

theorem mapped_cleared_output (ha : 2≤a) (pc : Fin count) (order : Order) (v : Stage s)
    (rows : ℕ) (axis : Fin v.f) (ell : ℕ)
    (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient) :
    setTape (Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) (output pc order v rows axis ell xs))
        56 (fun _ => blank) 0=
      setTape (Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) (input order v rows axis ell xs))
        56 (fun _ => blank) 0 := by
  simpa only [map_clear] using congrArg (Alphabet.mapTapes (SymbolTriplePlaced.encoding ha))
    (cleared_output pc order v rows axis ell xs)

/-- The installed caller stream is the literal phase result, with head zero. -/
theorem output_source (ha : 2≤a) (pc : Fin count) (order : Order) (v : Stage s)
    (rows : ℕ) (axis : Fin v.f) (ell : ℕ)
    (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient) :
    (Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) (output pc order v rows axis ell xs)).tape 56=
      SymbolTriplePlaced.mapTape ha (putWord (fun _ => blank) 0
        (UnitPhaseFullStreamNormalized.serialized
          (UnitPhasePolynomialLiteralEndpoint.result v axis
            (Networks.ComplexPhaseRowSchedule.dimension (edge pc))
            (CompactComplexPhaseControlCodec.weights (edge pc)).reverse xs))) ∧
    (Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) (output pc order v rows axis ell xs)).head 56=0 := by
  exact ⟨rfl,rfl⟩

end
end IntegerMultBounds.Machine.CompactPolynomialPhasePlacement
