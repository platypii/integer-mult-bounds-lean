import IntegerMultBounds.Machine.BinaryParityXorOffsetNegate
import IntegerMultBounds.Machine.RowPaddingConstructedAlphabet
import IntegerMultBounds.Machine.CompactGadgetReservationPlacement

/-! Paid rowwise modular negation on caller-selected tapes. The positive stream
is physically erased and the negative stream rewound; all private cells erase. -/
namespace IntegerMultBounds.Machine.ActivePrefixParityNegativeNegate
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {a t : ℕ}

def word (xs : List Bool) : ℤ → Fin (a+4) := putWord (fun _ => blank) 0 (xs.map bitSymbol)
def ports : Fin 4 → Fin 41 := ![0,1,4,6]
theorem ports_injective : Function.Injective ports := by decide

def localBank (xs ys ws ns : List Bool) : Tapes 41 a :=
  (Alphabet.mapTapes (CountedLoopReuseAlphabet.encoding a)
    (BinaryParityXorOffsetNegate.raw (BinaryParityXorOffsetRow.word xs)
      (BinaryParityXorOffsetRow.word ys) 0 0 ws ns)).append (SharedBank.empty 34 a)

def sources (xs ws ns : List Bool) : Tapes 4 a :=
  SharedBank.payload (localBank xs [] ws ns) ports

def program (focus : Fin 4 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (extend (Alphabet.program (CountedLoopReuseAlphabet.encoding a)
    BinaryParityXorOffsetNegate.program) 34) (CleanSubbank.placement ports focus hf)

def result (caller : Tapes t a) (focus : Fin 4 → Fin t) (ys : List Bool) :=
  setTape (setTape caller (focus 0) (fun _ => blank) 0) (focus 1) (word ys) 0

theorem map_word (xs : List Bool) :
    (fun z => (CountedLoopReuseAlphabet.encoding a).encode (BinaryParityXorOffsetRow.word xs z))=
      word (a := a) xs := by
  have h := RowPaddingConstructedAlphabet.map_putWord (a := a) (fun _ => blank) 0 (xs.map bitSymbol)
  change (fun z => (CountedLoopReuseAlphabet.encoding a).encode (BinaryParityXorOffsetRow.word xs z))=
    putWord (fun _ => blank) 0 ((xs.map bitSymbol).map (CountedLoopReuseAlphabet.encoding a).encode) at h
  rw [List.map_map] at h
  have he : (CountedLoopReuseAlphabet.encoding a).encode ∘ (bitSymbol : Bool → Fin 4)=bitSymbol := by
    funext b; cases b <;> rfl
  simpa only [he,word] using h

theorem local_payload (xs ys ws ns : List Bool) :
    SharedBank.payload (localBank (a := a) xs ys ws ns) ports=
      (⟨![0,0,1,1],![word xs,word ys,RadixZeroFill.encodedBinary ws,RadixZeroFill.encodedBinary ns]⟩ : Tapes 4 a) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact map_word _

 theorem local_clean (xs ys ws ns : List Bool) :
    SharedBank.strip (localBank (a := a) xs ys ws ns) ports=SharedBank.empty 41 a := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [localBank,ports,SharedBank.empty,Alphabet.mapTapes,BinaryParityXorOffsetNegate.raw,
    Tapes.append,Fin.addCases,Fin.exists_fin_succ]
  all_goals rfl

 theorem runs (caller : Tapes t a) (focus : Fin 4 → Fin t) (hf : Function.Injective focus)
    (blocks : List (List Bool)) (width : ℕ) (hu : BlockRotationData.Uniform width blocks)
    (ws ns : List Bool) (hw : Counter.value ws=width) (hn : Counter.value ns=blocks.length)
    (hsrc : SharedBank.payload caller focus=sources blocks.flatten ws ns) :
    HoareTime (program focus hf) (fun x => x=CleanSubbank.bank (s := 41) caller)
      (fun x => x=CleanSubbank.bank (s := 41) (result caller focus (BinaryParityXorOffsetLoop.result blocks)))
      (BinaryParityXorOffsetNegate.cost width blocks.length ws ns) := by
  have h := BinaryParityXorOffsetNegate.runs blocks width hu ws ns hw hn
  have hm := Alphabet.map_hoare (CountedLoopReuseAlphabet.encoding a) h
  have hm' : HoareTime (Alphabet.program (CountedLoopReuseAlphabet.encoding a) BinaryParityXorOffsetNegate.program)
      (fun x => x=Alphabet.mapTapes (CountedLoopReuseAlphabet.encoding a)
        (BinaryParityXorOffsetNegate.raw (BinaryParityXorOffsetRow.word blocks.flatten) (fun _ => blank) 0 0 ws ns))
      (fun x => x=Alphabet.mapTapes (CountedLoopReuseAlphabet.encoding a)
        (BinaryParityXorOffsetNegate.raw (fun _ => blank) (BinaryParityXorOffsetRow.word (BinaryParityXorOffsetLoop.result blocks)) 0 0 ws ns))
      (BinaryParityXorOffsetNegate.cost width blocks.length ws ns) := by
    apply hm.consequence
    · rintro x rfl; exact ⟨_,rfl,rfl⟩
    · rintro x ⟨_,rfl,rfl⟩; rfl
    · rfl
  have hh := hoare_extend_eq hm' (SharedBank.empty 34 a)
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller
    (result caller focus (BinaryParityXorOffsetLoop.result blocks))
    (localBank blocks.flatten [] ws ns) (localBank [] (BinaryParityXorOffsetLoop.result blocks) ws ns) _ hsrc.symm ?_
    (local_clean _ _ _ _) (local_clean _ _ _ _) ?_ hh
  · rw [local_payload]
    simp only [result,CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,sources,local_payload]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

end
end IntegerMultBounds.Machine.ActivePrefixParityNegativeNegate
