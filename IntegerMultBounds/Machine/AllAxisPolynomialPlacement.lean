import IntegerMultBounds.Machine.AllAxisPolynomialNative
import IntegerMultBounds.Machine.SharedPlacementAlphabet
import IntegerMultBounds.Machine.SymbolTriplePlaced

/-! The actual aggregate polynomial phase traversal shares the native source
of an arbitrary caller and frames every other complete tape. The appended
phase source slot remains blank; original phase metadata and immutable ell
are retained. Original metadata preparation is a separate physical stage. -/
namespace IntegerMultBounds.Machine.AllAxisPolynomialPlacement
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open ButterflyStreamData (Coefficient)
open SharedPlacementAlphabet (setTape sharedPlacement)
variable {s : Shape} {a t : ℕ}

def input (order : Order) (v : Stage s) (rows ell : ℕ)
    (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient) :=
  (AllAxisPolynomialStreamInit.input order v rows
    (AllAxisPolynomialLiteral.tail (fun _ => blank) (fun _ => blank) 0 0 xs) ell).append
    (SharedBank.empty 1 2)
def output (order : Order) (v : Stage s) (rows m : ℕ) (ws : List (ZMod 4)) (ell : ℕ)
    (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient) :=
  (AllAxisPolynomialNative.output order v rows m ws ell xs).append (SharedBank.empty 1 2)
def program (ha : 2≤a) (src : Fin t) (m : ℕ) (ws : List (ZMod 4)) :=
  Placement.placed (Alphabet.program (SymbolTriplePlaced.encoding ha)
    (extend (AllAxisPolynomialNative.program m ws) 1))
    (sharedPlacement src (56 : Fin 67))

theorem runs (ha : 2≤a) (src : Fin t) (caller : Tapes t a)
    (order : Order) (v : Stage s) (rows : ℕ) (hr : 0<rows) (m : ℕ)
    (ws : List (ZMod 4)) (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (hspan : AllAxisPhaseHeadersData.offset v m+(m*v.f-1)*s.chunk<s.bits)
    (ell w : ℕ) (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w)
    (hs : caller.tape src=SymbolTriplePlaced.mapTape ha
      (putWord (fun _ => blank) 0 (UnitPhaseFullStreamNormalized.serialized xs)))
    (hp : caller.head src=0) :
    HoareTime (program ha src m ws)
      (fun z => z=caller.append
        (setTape (Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) (input order v rows ell xs))
          56 (fun _ => blank) 0))
      (fun z => z=(setTape caller src
        ((Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) (output order v rows m ws ell xs)).tape 56)
        ((Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) (output order v rows m ws ell xs)).head 56)).append
        (setTape (Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) (output order v rows m ws ell xs))
          56 (fun _ => blank) 0))
      (AllAxisPolynomialNative.cost order v rows m ell w) := by
  have h0 := hoare_extend_eq
    (AllAxisPolynomialNative.runs order v rows hr m ws hm hslots hl hspan ell w xs hw)
    (SharedBank.empty 1 2)
  have h1 : HoareTime
      (Alphabet.program (SymbolTriplePlaced.encoding ha) (extend (AllAxisPolynomialNative.program m ws) 1))
      (fun z => z=Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) (input order v rows ell xs))
      (fun z => z=Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) (output order v rows m ws ell xs))
      (AllAxisPolynomialNative.cost order v rows m ell w) := by
    apply (Alphabet.map_hoare (SymbolTriplePlaced.encoding ha) h0).consequence _ _ le_rfl
    · rintro z rfl; exact ⟨_,rfl,rfl⟩
    · rintro z ⟨b,rfl,rfl⟩; rfl
  exact SharedPlacementAlphabet.shared_hoare h1 caller src (56 : Fin 67) (fun _ => blank) 0 hs hp

private theorem input_cleared_eq (order : Order) (v : Stage s) (rows ell : ℕ)
    (xs ys : Fin ((rows*2^s.bits)*2^ell) → Coefficient) :
    setTape (input order v rows ell xs) 56 (fun _ => blank) 0=
      setTape (input order v rows ell ys) 56 (fun _ => blank) 0 := by
  have ht : setTape (AllAxisPolynomialLiteral.tail (fun _ => blank) (fun _ => blank) 0 0 xs)
      (0 : Fin 4) (fun _ => blank) 0 =
      setTape (AllAxisPolynomialLiteral.tail (fun _ => blank) (fun _ => blank) 0 0 ys)
      (0 : Fin 4) (fun _ => blank) 0 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hi : (56 : Fin 67)=Fin.castAdd 1 (Fin.castAdd 6
      (Fin.natAdd 43 (Fin.natAdd 13 (0 : Fin 4)))) := rfl
  simp only [hi,input,AllAxisPolynomialStreamInit.input,AllAxisFullStreamInit.input,
    AllAxisPhaseStreamInit.input,SharedPlacementAlphabet.setTape_append_left,
    SharedPlacementAlphabet.setTape_append_right,ht]

theorem cleared_output (order : Order) (v : Stage s) (rows m : ℕ) (ws : List (ZMod 4)) (ell : ℕ)
    (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient) :
    setTape (output order v rows m ws ell xs) 56 (fun _ => blank) 0=
      setTape (input order v rows ell xs) 56 (fun _ => blank) 0 := by
  unfold output
  rw [AllAxisPolynomialNative.restored]
  exact input_cleared_eq order v rows ell _ xs


private theorem map_clear (ha : 2≤a) (b : Tapes 67 2) :
    Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) (setTape b 56 (fun _ => blank) 0)=
      setTape (Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) b) 56 (fun _ => blank) 0 := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i z
    by_cases h : i=56 <;> simp [Alphabet.mapTapes,setTape,h,SymbolTriplePlaced.encoding,blank]

theorem mapped_cleared_output (ha : 2≤a) (order : Order) (v : Stage s)
    (rows m : ℕ) (ws : List (ZMod 4)) (ell : ℕ)
    (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient) :
    setTape (Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) (output order v rows m ws ell xs))
        56 (fun _ => blank) 0=
      setTape (Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) (input order v rows ell xs))
        56 (fun _ => blank) 0 := by
  simpa only [map_clear] using congrArg (Alphabet.mapTapes (SymbolTriplePlaced.encoding ha))
    (cleared_output order v rows m ws ell xs)

theorem output_source (ha : 2≤a) (order : Order) (v : Stage s)
    (rows m : ℕ) (ws : List (ZMod 4)) (ell : ℕ)
    (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient) :
    (Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) (output order v rows m ws ell xs)).tape 56=
      SymbolTriplePlaced.mapTape ha (putWord (fun _ => blank) 0
        (UnitPhaseFullStreamNormalized.serialized (AllAxisPolynomialLiteralEndpoint.result v m ws xs))) ∧
    (Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) (output order v rows m ws ell xs)).head 56=0 :=
  ⟨rfl,rfl⟩

end
end IntegerMultBounds.Machine.AllAxisPolynomialPlacement
