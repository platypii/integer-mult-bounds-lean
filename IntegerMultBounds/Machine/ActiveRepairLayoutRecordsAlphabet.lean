import IntegerMultBounds.Machine.ActiveTargetHighestLaterBank
import IntegerMultBounds.Machine.FixedHeaderBankCopy
import IntegerMultBounds.Machine.ActiveTargetRotation

/-! Exact Fin-five repair simulation in the fixed prime alphabet. The fifth
repair marker is retained, and literal binary payloads/descriptors have the
same symbol codes as the original payload machines. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAlphabet
noncomputable section
open Networks.Shared50ModularControl (prime)
variable {t u q : ℕ}

theorem prime_ge_one : 1≤prime := by
  have h := Networks.Shared50ModularControl.prime_odd
  omega

def encoding : Alphabet.Encoding 1 prime where
  encode x := ⟨x.val,by have := x.isLt; have := prime_ge_one; omega⟩
  decode x := if h : x.val<5 then ⟨x.val,h⟩ else blank
  decode_encode := by intro x; simp [x.isLt]

@[simp] theorem encode_blank : encoding.encode blank=blank := rfl
@[simp] theorem encode_bit (b : Bool) : encoding.encode (bitSymbol b)=bitSymbol b := rfl
@[simp] theorem encode_separator : encoding.encode separator=separator := rfl

 theorem encode_value (x : Fin 5) : (encoding.encode x).val=x.val := rfl

 theorem map_append (v : Tapes t 1) (w : Tapes u 1) :
    Alphabet.mapTapes encoding (v.append w)=
      (Alphabet.mapTapes encoding v).append (Alphabet.mapTapes encoding w) := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    induction i using Fin.addCases with
    | left i => simp only [Tapes.append,Fin.addCases_left,Alphabet.mapTapes]
    | right i => simp only [Tapes.append,Fin.addCases_right,Alphabet.mapTapes]

 theorem map_empty (t : ℕ) :
    Alphabet.mapTapes encoding (SharedBank.empty t 1)=SharedBank.empty t prime := rfl

 theorem map_payload {k : ℕ} (v : Tapes t 1) (slots : Fin k → Fin t) :
    Alphabet.mapTapes encoding (SharedBank.payload v slots)=
      SharedBank.payload (Alphabet.mapTapes encoding v) slots := rfl

 theorem mapTapes_fixed_empty (t : ℕ) :
    Alphabet.mapTapes encoding (FixedHeaderBankCopy.empty (a:=1) t)=FixedHeaderBankCopy.empty (a:=prime) t := rfl

 theorem map_word (f : ℤ → Fin 5) (p : ℤ) (xs : List (Fin 5)) :
    (fun z => encoding.encode (putWord f p xs z))=
      putWord (fun z => encoding.encode (f z)) p (xs.map encoding.encode) :=
  ActiveTargetHighestLaterBank.map_word encoding f p xs

 theorem map_raw (xs : List Bool) :
    (fun z => encoding.encode (putWord (fun _ => blank) 0 (xs.map bitSymbol) z))=
      putWord (fun _ => blank) 0 (xs.map bitSymbol) := by
  rw [map_word]
  simp only [encode_blank,List.map_map,Function.comp_def,encode_bit]

 theorem map_array_word {m : ℕ} (x : Fin m → Bool) :
    (fun z => encoding.encode (putWord (fun _ => blank) 0 ((List.ofFn x).map bitSymbol) z))=
      ActiveTargetRotation.word (a:=prime) x := by
  rw [map_raw,List.map_ofFn]
  rfl

 theorem map_rotation_word {m : ℕ} (x : Fin m → Bool) :
    (fun z => encoding.encode (ActiveTargetRotation.word (a:=1) x z))=
      ActiveTargetRotation.word (a:=prime) x := by
  rw [ActiveTargetRotation.word,map_word,List.map_ofFn]
  simp only [encode_blank]
  rfl

 theorem map_binary (bs : List Bool) :
    (fun z => encoding.encode (RadixZeroFill.encodedBinary (q:=1) bs z))=
      RadixZeroFill.encodedBinary (q:=prime) bs := by
  funext z
  rfl

 theorem map_headerBank (bs : Fin t → List Bool) :
    Alphabet.mapTapes encoding (FixedHeaderBankCopy.headerBank (a:=1) bs)=
      FixedHeaderBankCopy.headerBank (a:=prime) bs := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    exact map_binary (bs i)

 theorem map_hoare_eq {M : Program t q 1} {v w : Tapes t 1} {cost : ℕ}
    (h : HoareTime M (fun x => x=v) (fun x => x=w) cost) :
    HoareTime (Alphabet.program encoding M)
      (fun x => x=Alphabet.mapTapes encoding v) (fun x => x=Alphabet.mapTapes encoding w) cost := by
  apply (Alphabet.map_hoare encoding h).consequence _ _ le_rfl
  · rintro x rfl
    exact ⟨_,rfl,rfl⟩
  · rintro x ⟨original,rfl,rfl⟩
    rfl

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAlphabet
