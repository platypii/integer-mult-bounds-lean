import IntegerMultBounds.Machine.BinaryPackedOffsetRun
import IntegerMultBounds.Machine.BinaryPackedRowCountBudget

/-! Compute the fiber count from the original four headers, execute the actual
swap/rotation/swap, and physically erase the derived descriptor. -/
namespace IntegerMultBounds.Machine.BinaryPackedOffsetOriginalRun
noncomputable section
open Networks.Shared50ModularControl (prime)
open BinaryPackedFieldSwap (store)
open BinaryPackedRowCountPlaced (output)

private theorem encoded_binary (xs : List Bool) :
    RadixZeroFill.encodedBinary (q := prime) xs = CountedLoopReuseAlphabet.binary xs :=
  CountedLoopReuseAlphabet.encoding_binary xs

 def headers : Fin 4 → Fin 6 := ![0,1,2,3]
 theorem headers_injective : Function.Injective headers := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [headers]
 def actionHeaders : Fin 4 → Fin 15 := ![0,1,2,3]
 def focus : Fin 5 → Fin 15 := ![5,4,2,6,3]
 theorem focus_injective : Function.Injective focus := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [focus]
 abbrev count := BinaryPackedOffsetRun.count
 def prepare := extend (extend (BinaryPackedRowCountPlaced.program headers headers_injective prime) count) 12
 def clean := extend (extend (BinaryPackedRowCountPlaced.cleanup (t := 6) (a := prime)) count) 12
 def program := seq (seq prepare (BinaryPackedOffsetRun.program actionHeaders focus focus_injective)) clean
 def input (caller : Tapes 6 prime) := BinaryPackedOffsetRun.input (BinaryPackedRowCountPlaced.input caller)
 def prepared (caller : Tapes 6 prime) (P w G : ℕ) := BinaryPackedOffsetRun.input (output caller P w G)
 def cost (P w G B : ℕ) (hs : Fin 4 → List Bool) :=
  BinaryPackedRowCountBudget.cost P w G +
  (2*BinaryRadixEqualShared.cost P G B w hs+BinaryPackedOffsetRun.rotationCost P w G B+2)+
  (2*(BinaryPackedRowCount.rowBits P w G).length+4)+2

 theorem output_store (caller : Tapes 6 prime) (P w G B : ℕ)
    (x : Fin (RadixRangePadding.volume P (2^w) G B) → Bool) :
    output (store caller 5 x) P w G = store (output caller P w G) (focus 0) x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [output,BinaryPackedRowCountPlaced.input,BinaryPackedRowCountPlaced.rowSlot,
      store,SharedPlacementAlphabet.setTape,Tapes.append,Fin.addCases,focus]

 /-- No fiber-count word is supplied: the fixed machine produces it from
 P/G/w, retains every original header and packed word, and cleans all banks. -/
 theorem runs (caller : Tapes 6 prime) (V : List Bool) (P w G B : ℕ)
    (hV : V.length=BinaryPackedOffsetData.rows P w G*w)
    (hP : 0<P) (hG : 0<G) (hB : 0<B) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=BinaryRadixRangePrepare.values P G B w i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hsrc : BinaryAdjacentWidthHeadersShared.Sources caller headers hs)
    (g : ℤ → Fin 4) (s : ℤ) (hg : g (s-1)=blank)
    (ht : caller.tape 4=putWord (StreamedFiberTranslationAlphabet.mapTape g) s (V.map bitSymbol))
    (hh : caller.head 4=s)
    (x : Fin (RadixRangePadding.volume P (2^w) G B) → Bool) :
    HoareTime program (fun z => z=input (store caller 5 x))
      (fun z => z=input (store caller 5 (BinaryPackedOffsetData.result V P w G B x)))
      (cost P w G B hs) := by
  have hne : ∀ i, headers i≠(5 : Fin 6) := by intro i; fin_cases i <;> decide
  have src := BinaryPackedFieldSwap.store_sources caller headers 5 hs hne hsrc x
  have h₀ := hoare_extend_eq (hoare_extend_eq
    (BinaryPackedRowCountPlaced.constructs (store caller 5 x) headers headers_injective hs P w G hG
      src.tape src.head (hv 0) (hv 1) (hv 3) (hc 0) (hc 1) (hc 3))
    (FixedHeaderBankCopy.empty count)) (FixedHeaderBankCopy.empty 12)
  have ha : BinaryAdjacentWidthHeadersShared.Sources (output caller P w G) actionHeaders hs := by
    constructor
    · intro i; have hi := hsrc.tape i; fin_cases i <;>
        simpa [output,BinaryPackedRowCountPlaced.input,BinaryPackedRowCountPlaced.rowSlot,
          actionHeaders,SharedPlacementAlphabet.setTape,Tapes.append,Fin.addCases,headers] using hi
    · intro i; have hi := hsrc.head i; fin_cases i <;>
        simpa [output,BinaryPackedRowCountPlaced.input,BinaryPackedRowCountPlaced.rowSlot,
          actionHeaders,SharedPlacementAlphabet.setTape,Tapes.append,Fin.addCases,headers] using hi
  have h₁ := BinaryPackedOffsetRun.runs (output caller P w G) actionHeaders focus focus_injective
    V P w G B hV hP hG hB hs hv hc
    (by intro i; fin_cases i <;> decide) ha g s hg
    (hs 2) (BinaryPackedRowCount.rowBits P w G) (hs 3)
    (hv 2) (BinaryPackedRowCount.row_value P w G) (hv 3)
    (hc 2) (BinaryPackedRowCount.row_canonical P w G) (hc 3)
    (by
      intro i hi; fin_cases i
      · contradiction
      · simpa [output,BinaryPackedRowCountPlaced.input,BinaryPackedRowCountPlaced.rowSlot,
          focus,SharedPlacementAlphabet.setTape,Tapes.append,Fin.addCases,PackedOffsetPayloadPlaced.tapes,encoded_binary] using ht
      · simpa [output,BinaryPackedRowCountPlaced.input,BinaryPackedRowCountPlaced.rowSlot,
          focus,SharedPlacementAlphabet.setTape,Tapes.append,Fin.addCases,PackedOffsetPayloadPlaced.tapes,headers,encoded_binary] using hsrc.tape 2
      · simp [output,BinaryPackedRowCountPlaced.input,BinaryPackedRowCountPlaced.rowSlot,
          focus,SharedPlacementAlphabet.setTape,PackedOffsetPayloadPlaced.tapes,encoded_binary]
      · simpa [output,BinaryPackedRowCountPlaced.input,BinaryPackedRowCountPlaced.rowSlot,
          focus,SharedPlacementAlphabet.setTape,Tapes.append,Fin.addCases,PackedOffsetPayloadPlaced.tapes,headers,encoded_binary] using hsrc.tape 3)
    (by
      intro i hi; fin_cases i
      · contradiction
      · simpa [output,BinaryPackedRowCountPlaced.input,BinaryPackedRowCountPlaced.rowSlot,
          focus,SharedPlacementAlphabet.setTape,Tapes.append,Fin.addCases,PackedOffsetPayloadPlaced.heads] using hh
      · simpa [output,BinaryPackedRowCountPlaced.input,BinaryPackedRowCountPlaced.rowSlot,
          focus,SharedPlacementAlphabet.setTape,Tapes.append,Fin.addCases,PackedOffsetPayloadPlaced.heads,headers] using hsrc.head 2
      · simp [output,BinaryPackedRowCountPlaced.input,BinaryPackedRowCountPlaced.rowSlot,
          focus,SharedPlacementAlphabet.setTape,PackedOffsetPayloadPlaced.heads]
      · simpa [output,BinaryPackedRowCountPlaced.input,BinaryPackedRowCountPlaced.rowSlot,
          focus,SharedPlacementAlphabet.setTape,Tapes.append,Fin.addCases,PackedOffsetPayloadPlaced.heads,headers] using hsrc.head 3) x
  rw [← output_store,← output_store] at h₁
  have h₂ := hoare_extend_eq (hoare_extend_eq
    (BinaryPackedRowCountPlaced.cleans (store caller 5 (BinaryPackedOffsetData.result V P w G B x)) P w G)
    (FixedHeaderBankCopy.empty count)) (FixedHeaderBankCopy.empty 12)
  exact ((h₀.seq h₁).seq h₂).consequence (fun _ h => h) (fun _ h => h) (by
    unfold cost BinaryPackedRowCountBudget.cost
    omega)
end
end IntegerMultBounds.Machine.BinaryPackedOffsetOriginalRun
