import IntegerMultBounds.Machine.CountedGatherMetadata
import IntegerMultBounds.Machine.ArbitraryWidthZeroHeaderShared
import IntegerMultBounds.Machine.BinaryRadixRootHeadersShared

/-! Construct six original parity-gather dimensions from only the retained
runtime b/count headers. Zero and one are
physically written, copied, and erased. All eight private tapes are reusable. -/
namespace IntegerMultBounds.Machine.CountedPackedParityHeaders
noncomputable section
variable {a t : ℕ}
open BinaryRadixRootHeadersShared (oneBits oneBank)

/-- One low bit from every b-bit block; b=1 is allowed. -/
def shape (b : ℕ) (hb : 1 ≤ b) : Gather.Shape := ⟨b,0,1,1,0,by omega,by omega⟩
def originalValues (b n : ℕ) : Fin 2 → ℕ := ![b,n]
def words (hs : Fin 2 → List Bool) : Fin 6 → List Bool :=
  ![hs 0,[],oneBits,oneBits,[],hs 1]

def baseSlot (i : Fin t) : Fin ((t+1)+1) := Fin.castAdd 1 (Fin.castAdd 1 i)
def zeroSlot : Fin ((t+1)+1) := Fin.castAdd 1 (Fin.natAdd t 0)
def oneSlot : Fin ((t+1)+1) := Fin.natAdd (t+1) 0

def focus (source : Fin 2 → Fin t) : Fin 6 → Fin ((t+1)+1) :=
  ![baseSlot (source 0),zeroSlot,oneSlot,oneSlot,zeroSlot,baseSlot (source 1)]

def input (caller : Tapes t a) :=
  ((caller.append (FixedHeaderBankCopy.empty 1)).append (FixedHeaderBankCopy.empty 1)).append
    (FixedHeaderBankCopy.empty 6)
def output (caller : Tapes t a) (hs : Fin 2 → List Bool) :=
  ((caller.append (FixedHeaderBankCopy.empty 1)).append (FixedHeaderBankCopy.empty 1)).append
    (FixedHeaderBankCopy.headerBank (words hs))
def temporary (caller : Tapes t a) :=
  (caller.append ArbitraryWidthZeroHeaderShared.header).append oneBank

def writeZero := extend (extend (ArbitraryWidthZeroHeaderShared.program (a := a) (t := t)) 1) 6
def writeOne := extend (BinaryRadixRootHeadersShared.oneWriter (a := a) (t := t+1)) 6
def copyProgram (source : Fin 2 → Fin t) := FixedHeaderBankCopy.program
  (a := a) (by omega : 0 < ((t+1)+1)+6) (focus source)
def eraseOne := extend (BinaryRadixRootHeadersShared.oneCleanup (a := a) (t := t+1)) 6
def eraseZero := extend (extend (ArbitraryWidthZeroHeaderShared.cleanup (a := a) (t := t)) 1) 6
def program (source : Fin 2 → Fin t) :=
  seq (seq (seq (seq (writeZero (a := a) (t := t)) writeOne) (copyProgram source)) eraseOne) eraseZero

def cleanup := FixedHeaderBankCopy.cleanup (a := a) (n := 6) (by omega : 0 < ((t+1)+1)+6)

theorem words_canonical (hs : Fin 2 → List Bool)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    ∀ i, GrowingCounterData.Canonical (words hs i) := by
  intro i; fin_cases i
  all_goals first | exact hc _ | exact ArbitraryWidthZeroHeaderShared.zero_canonical |
    exact RecursiveChildQuotientsConstant.bits_canonical 1

theorem words_bounded (hs : Fin 2 → List Bool) (V : ℕ) (hV : 0 < V)
    (hv : ∀ i, Counter.value (hs i) ≤ V) : ∀ i, Counter.value (words hs i) ≤ V := by
  intro i; fin_cases i
  all_goals first | exact hv _ | exact Nat.zero_le _ | (change 1 ≤ V; omega)

theorem words_values (b n : ℕ) (hb : 1 ≤ b)
    (hs : Fin 2 → List Bool) (hv : ∀ i, Counter.value (hs i) = originalValues b n i) :
    ∀ i, Counter.value (words hs i) = CountedGatherMetadata.originalValues (shape b hb) n i := by
  intro i; fin_cases i
  all_goals first | exact hv _ | rfl

theorem source_bounds (b n : ℕ) (hs : Fin 2 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = originalValues b n i) :
    ∀ i, Counter.value (hs i) ≤ b+n+1 := by
  intro i; rw [hv]; fin_cases i <;> simp [originalValues] <;> omega

theorem temporary_sources (source : Fin 2 → Fin t)
    (caller : Tapes t a) (hs : Fin 2 → List Bool)
    (ht : ∀ i, caller.tape (source i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (source i) = 1) :
    (∀ i, (temporary caller).tape (focus source i) = RadixZeroFill.encodedBinary (words hs i)) ∧
    (∀ i, (temporary caller).head (focus source i) = 1) := by
  constructor
  · intro i; fin_cases i <;>
      simp [temporary,focus,words,baseSlot,zeroSlot,oneSlot,Tapes.append,ht,
        ArbitraryWidthZeroHeaderShared.header,FiniteReturnStack.bank,ArbitraryWidthZeroHeaderShared.encoded_zero,
        oneBank,FixedHeaderBankCopy.headerBank,FixedHeaderBankCopy.bank,RecursiveDimensionBank.tape]
  · intro i; fin_cases i <;>
      simp [temporary,focus,baseSlot,zeroSlot,oneSlot,Tapes.append,hh,
        ArbitraryWidthZeroHeaderShared.header,FiniteReturnStack.bank,
        oneBank,FixedHeaderBankCopy.headerBank,FixedHeaderBankCopy.bank,RecursiveDimensionBank.head]

/-- The source focus may repeat tapes. Only the private destinations must be
distinct, as enforced by the ordinary six-header copy routine. -/
theorem constructs_bounded (source : Fin 2 → Fin t)
    (caller : Tapes t a) (hs : Fin 2 → List Bool) (V : ℕ) (hV : 0 < V)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hv : ∀ i, Counter.value (hs i) ≤ V)
    (ht : ∀ i, caller.tape (source i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (source i) = 1) :
    HoareTime (program source) (fun v => v = input caller)
      (fun v => v = output caller hs) (92*V) := by
  have h0 := hoare_extend_eq (hoare_extend_eq (ArbitraryWidthZeroHeaderShared.constructs caller)
    (FixedHeaderBankCopy.empty 1)) (FixedHeaderBankCopy.empty 6)
  have h1 := hoare_extend_eq (BinaryRadixRootHeadersShared.writes_one
    (caller.append ArbitraryWidthZeroHeaderShared.header)) (FixedHeaderBankCopy.empty 6)
  have hc6 := words_canonical hs hc
  have hv6 := words_bounded hs V hV hv
  obtain ⟨hsrc,hhead⟩ := temporary_sources source caller hs ht hh
  have h2 := FixedHeaderBankCopy.constructs_linear (a := a) (by omega : 0 < ((t+1)+1)+6)
    (focus source) (words hs) (temporary caller) hsrc hhead V hV hc6 hv6
  have h3 := hoare_extend_eq (FixedHeaderBankCopy.cleans_linear (a := a)
    (by omega : 0 < (t+1)+1) (caller.append ArbitraryWidthZeroHeaderShared.header)
    (fun _ : Fin 1 => oneBits) V hV (fun _ => RecursiveChildQuotientsConstant.bits_canonical 1)
    (by intro i; change 1 ≤ V; omega)) (FixedHeaderBankCopy.headerBank (words hs))
  have h4 := hoare_extend_eq (hoare_extend_eq (ArbitraryWidthZeroHeaderShared.cleans caller)
    (FixedHeaderBankCopy.empty 1)) (FixedHeaderBankCopy.headerBank (words hs))
  apply ((((h0.seq h1).seq h2).seq h3).seq h4).consequence (fun _ h => h) (fun _ h => h)
  omega

theorem constructs (source : Fin 2 → Fin t)
    (caller : Tapes t a) (b n : ℕ) (hs : Fin 2 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = originalValues b n i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (ht : ∀ i, caller.tape (source i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (source i) = 1) :
    HoareTime (program source) (fun v => v = input caller)
      (fun v => v = output caller hs) (92*(b+n+1)) :=
  constructs_bounded source caller hs (b+n+1) (by omega) hc (source_bounds b n hs hv) ht hh

theorem cleans_bounded (caller : Tapes t a) (hs : Fin 2 → List Bool)
    (V : ℕ) (hV : 0 < V) (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hv : ∀ i, Counter.value (hs i) ≤ V) :
    HoareTime (cleanup (a := a) (t := t)) (fun v => v = output caller hs)
      (fun v => v = input caller) (54*V) :=
  FixedHeaderBankCopy.cleans_linear (by omega)
    ((caller.append (FixedHeaderBankCopy.empty 1)).append (FixedHeaderBankCopy.empty 1))
    (words hs) V hV (words_canonical hs hc) (words_bounded hs V hV hv)

theorem cleans (caller : Tapes t a) (b n : ℕ) (hs : Fin 2 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = originalValues b n i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (cleanup (a := a) (t := t)) (fun v => v = output caller hs)
      (fun v => v = input caller) (54*(b+n+1)) :=
  cleans_bounded caller hs (b+n+1) (by omega) hc (source_bounds b n hs hv)

theorem header_cells (caller : Tapes t a) (hs : Fin 2 → List Bool) (i : Fin 6) :
    (output caller hs).head (Fin.natAdd ((t+1)+1) i) = 1 ∧
    (output caller hs).tape (Fin.natAdd ((t+1)+1) i) = RadixZeroFill.encodedBinary (words hs i) := by
  simp only [output,Tapes.append,Fin.addCases_right,FixedHeaderBankCopy.headerBank,
    FixedHeaderBankCopy.bank,RecursiveDimensionBank.head,RecursiveDimensionBank.tape]
  trivial

theorem caller_cells (caller : Tapes t a) (hs : Fin 2 → List Bool) (i : Fin t) :
    (output caller hs).head (Fin.castAdd 6 (baseSlot i)) = caller.head i ∧
    (output caller hs).tape (Fin.castAdd 6 (baseSlot i)) = caller.tape i := by
  simp only [output,baseSlot,Tapes.append,Fin.addCases_left]
  exact ⟨trivial,trivial⟩

theorem zero_blank (caller : Tapes t a) (hs : Fin 2 → List Bool) :
    (output caller hs).head (Fin.castAdd 6 zeroSlot) = 0 ∧
    (output caller hs).tape (Fin.castAdd 6 zeroSlot) = fun _ => blank := by
  simp only [output,zeroSlot,Tapes.append,Fin.addCases_left,Fin.addCases_right,FixedHeaderBankCopy.empty]
  exact ⟨trivial,trivial⟩

theorem one_blank (caller : Tapes t a) (hs : Fin 2 → List Bool) :
    (output caller hs).head (Fin.castAdd 6 oneSlot) = 0 ∧
    (output caller hs).tape (Fin.castAdd 6 oneSlot) = fun _ => blank := by
  simp only [output,oneSlot,Tapes.append,Fin.addCases_left,Fin.addCases_right,FixedHeaderBankCopy.empty]
  exact ⟨trivial,trivial⟩

end
end IntegerMultBounds.Machine.CountedPackedParityHeaders
