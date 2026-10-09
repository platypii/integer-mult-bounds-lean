import IntegerMultBounds.Machine.CountedGatherMetadata
import IntegerMultBounds.Machine.PackedArith
import IntegerMultBounds.Machine.ArbitraryWidthZeroHeaderShared
import IntegerMultBounds.Machine.BinaryRadixRootHeadersShared

/-! Construct six original gather dimensions for one of three static packed
line shapes from only the retained runtime q/b/n headers. Zero and one are
physically written, copied, and erased. All eight private tapes are reusable. -/
namespace IntegerMultBounds.Machine.CountedPackedShapeHeaders
noncomputable section
variable {a t : ℕ}
open BinaryRadixRootHeadersShared (oneBits oneBank)

/-- Static kinds: maskShift, parity, controlsAt. No runtime dimension occurs
in the program or its finite-control size. -/
def shape (kind : Fin 3) (q b : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) : Gather.Shape :=
  ![PackedArith.maskShift q b hb hbq,PackedArith.parity q b hb hbq,PackedArith.controlsAt q b hb hbq] kind

def originalValues (q b n : ℕ) : Fin 3 → ℕ := ![q,b,n]
def words (kind : Fin 3) (hs : Fin 3 → List Bool) : Fin 6 → List Bool :=
  ![![hs 1,[],hs 1,hs 0,oneBits,hs 2],
    ![hs 0,[],oneBits,hs 1,[],hs 2],
    ![oneBits,[],oneBits,hs 0,[],hs 2]] kind

def baseSlot (i : Fin t) : Fin ((t+1)+1) := Fin.castAdd 1 (Fin.castAdd 1 i)
def zeroSlot : Fin ((t+1)+1) := Fin.castAdd 1 (Fin.natAdd t 0)
def oneSlot : Fin ((t+1)+1) := Fin.natAdd (t+1) 0

def focus (kind : Fin 3) (source : Fin 3 → Fin t) : Fin 6 → Fin ((t+1)+1) :=
  ![![baseSlot (source 1),zeroSlot,baseSlot (source 1),baseSlot (source 0),oneSlot,baseSlot (source 2)],
    ![baseSlot (source 0),zeroSlot,oneSlot,baseSlot (source 1),zeroSlot,baseSlot (source 2)],
    ![oneSlot,zeroSlot,oneSlot,baseSlot (source 0),zeroSlot,baseSlot (source 2)]] kind

def input (caller : Tapes t a) :=
  ((caller.append (FixedHeaderBankCopy.empty 1)).append (FixedHeaderBankCopy.empty 1)).append
    (FixedHeaderBankCopy.empty 6)
def output (caller : Tapes t a) (kind : Fin 3) (hs : Fin 3 → List Bool) :=
  ((caller.append (FixedHeaderBankCopy.empty 1)).append (FixedHeaderBankCopy.empty 1)).append
    (FixedHeaderBankCopy.headerBank (words kind hs))
def temporary (caller : Tapes t a) :=
  (caller.append ArbitraryWidthZeroHeaderShared.header).append oneBank

def writeZero := extend (extend (ArbitraryWidthZeroHeaderShared.program (a := a) (t := t)) 1) 6
def writeOne := extend (BinaryRadixRootHeadersShared.oneWriter (a := a) (t := t+1)) 6
def copyProgram (kind : Fin 3) (source : Fin 3 → Fin t) := FixedHeaderBankCopy.program
  (a := a) (by omega : 0 < ((t+1)+1)+6) (focus kind source)
def eraseOne := extend (BinaryRadixRootHeadersShared.oneCleanup (a := a) (t := t+1)) 6
def eraseZero := extend (extend (ArbitraryWidthZeroHeaderShared.cleanup (a := a) (t := t)) 1) 6
def program (kind : Fin 3) (source : Fin 3 → Fin t) :=
  seq (seq (seq (seq (writeZero (a := a) (t := t)) writeOne) (copyProgram kind source)) eraseOne) eraseZero

def cleanup := FixedHeaderBankCopy.cleanup (a := a) (n := 6) (by omega : 0 < ((t+1)+1)+6)

theorem words_canonical (kind : Fin 3) (hs : Fin 3 → List Bool)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    ∀ i, GrowingCounterData.Canonical (words kind hs i) := by
  intro i; fin_cases kind <;> fin_cases i
  all_goals first | exact hc _ | exact ArbitraryWidthZeroHeaderShared.zero_canonical |
    exact RecursiveChildQuotientsConstant.bits_canonical 1

theorem words_bounded (kind : Fin 3) (hs : Fin 3 → List Bool) (V : ℕ) (hV : 0 < V)
    (hv : ∀ i, Counter.value (hs i) ≤ V) : ∀ i, Counter.value (words kind hs i) ≤ V := by
  intro i; fin_cases kind <;> fin_cases i
  all_goals first | exact hv _ | exact Nat.zero_le _ | (change 1 ≤ V; omega)

theorem words_values (kind : Fin 3) (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q)
    (hs : Fin 3 → List Bool) (hv : ∀ i, Counter.value (hs i) = originalValues q b n i) :
    ∀ i, Counter.value (words kind hs i) = CountedGatherMetadata.originalValues (shape kind q b hb hbq) n i := by
  intro i; fin_cases kind <;> fin_cases i
  all_goals first | exact hv _ | rfl

theorem source_bounds (q b n : ℕ) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = originalValues q b n i) :
    ∀ i, Counter.value (hs i) ≤ q+b+n+1 := by
  intro i; rw [hv]; fin_cases i <;> simp [originalValues] <;> omega

theorem temporary_sources (kind : Fin 3) (source : Fin 3 → Fin t)
    (caller : Tapes t a) (hs : Fin 3 → List Bool)
    (ht : ∀ i, caller.tape (source i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (source i) = 1) :
    (∀ i, (temporary caller).tape (focus kind source i) = RadixZeroFill.encodedBinary (words kind hs i)) ∧
    (∀ i, (temporary caller).head (focus kind source i) = 1) := by
  constructor
  · intro i; fin_cases kind <;> fin_cases i <;>
      simp [temporary,focus,words,baseSlot,zeroSlot,oneSlot,Tapes.append,ht,
        ArbitraryWidthZeroHeaderShared.header,FiniteReturnStack.bank,ArbitraryWidthZeroHeaderShared.encoded_zero,
        oneBank,FixedHeaderBankCopy.headerBank,FixedHeaderBankCopy.bank,RecursiveDimensionBank.tape]
  · intro i; fin_cases kind <;> fin_cases i <;>
      simp [temporary,focus,baseSlot,zeroSlot,oneSlot,Tapes.append,hh,
        ArbitraryWidthZeroHeaderShared.header,FiniteReturnStack.bank,
        oneBank,FixedHeaderBankCopy.headerBank,FixedHeaderBankCopy.bank,RecursiveDimensionBank.head]

/-- The source focus may repeat tapes. Only the private destinations must be
distinct, as enforced by the ordinary six-header copy routine. -/
theorem constructs_bounded (kind : Fin 3) (source : Fin 3 → Fin t)
    (caller : Tapes t a) (hs : Fin 3 → List Bool) (V : ℕ) (hV : 0 < V)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hv : ∀ i, Counter.value (hs i) ≤ V)
    (ht : ∀ i, caller.tape (source i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (source i) = 1) :
    HoareTime (program kind source) (fun v => v = input caller)
      (fun v => v = output caller kind hs) (92*V) := by
  have h0 := hoare_extend_eq (hoare_extend_eq (ArbitraryWidthZeroHeaderShared.constructs caller)
    (FixedHeaderBankCopy.empty 1)) (FixedHeaderBankCopy.empty 6)
  have h1 := hoare_extend_eq (BinaryRadixRootHeadersShared.writes_one
    (caller.append ArbitraryWidthZeroHeaderShared.header)) (FixedHeaderBankCopy.empty 6)
  have hc6 := words_canonical kind hs hc
  have hv6 := words_bounded kind hs V hV hv
  obtain ⟨hsrc,hhead⟩ := temporary_sources kind source caller hs ht hh
  have h2 := FixedHeaderBankCopy.constructs_linear (a := a) (by omega : 0 < ((t+1)+1)+6)
    (focus kind source) (words kind hs) (temporary caller) hsrc hhead V hV hc6 hv6
  have h3 := hoare_extend_eq (FixedHeaderBankCopy.cleans_linear (a := a)
    (by omega : 0 < (t+1)+1) (caller.append ArbitraryWidthZeroHeaderShared.header)
    (fun _ : Fin 1 => oneBits) V hV (fun _ => RecursiveChildQuotientsConstant.bits_canonical 1)
    (by intro i; change 1 ≤ V; omega)) (FixedHeaderBankCopy.headerBank (words kind hs))
  have h4 := hoare_extend_eq (hoare_extend_eq (ArbitraryWidthZeroHeaderShared.cleans caller)
    (FixedHeaderBankCopy.empty 1)) (FixedHeaderBankCopy.headerBank (words kind hs))
  apply ((((h0.seq h1).seq h2).seq h3).seq h4).consequence (fun _ h => h) (fun _ h => h)
  omega

theorem constructs (kind : Fin 3) (source : Fin 3 → Fin t)
    (caller : Tapes t a) (q b n : ℕ) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = originalValues q b n i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (ht : ∀ i, caller.tape (source i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (source i) = 1) :
    HoareTime (program kind source) (fun v => v = input caller)
      (fun v => v = output caller kind hs) (92*(q+b+n+1)) :=
  constructs_bounded kind source caller hs (q+b+n+1) (by omega) hc (source_bounds q b n hs hv) ht hh

theorem cleans_bounded (kind : Fin 3) (caller : Tapes t a) (hs : Fin 3 → List Bool)
    (V : ℕ) (hV : 0 < V) (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hv : ∀ i, Counter.value (hs i) ≤ V) :
    HoareTime (cleanup (a := a) (t := t)) (fun v => v = output caller kind hs)
      (fun v => v = input caller) (54*V) :=
  FixedHeaderBankCopy.cleans_linear (by omega)
    ((caller.append (FixedHeaderBankCopy.empty 1)).append (FixedHeaderBankCopy.empty 1))
    (words kind hs) V hV (words_canonical kind hs hc) (words_bounded kind hs V hV hv)

theorem cleans (kind : Fin 3) (caller : Tapes t a) (q b n : ℕ) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = originalValues q b n i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (cleanup (a := a) (t := t)) (fun v => v = output caller kind hs)
      (fun v => v = input caller) (54*(q+b+n+1)) :=
  cleans_bounded kind caller hs (q+b+n+1) (by omega) hc (source_bounds q b n hs hv)

theorem header_cells (kind : Fin 3) (caller : Tapes t a) (hs : Fin 3 → List Bool) (i : Fin 6) :
    (output caller kind hs).head (Fin.natAdd ((t+1)+1) i) = 1 ∧
    (output caller kind hs).tape (Fin.natAdd ((t+1)+1) i) = RadixZeroFill.encodedBinary (words kind hs i) := by
  simp only [output,Tapes.append,Fin.addCases_right,FixedHeaderBankCopy.headerBank,
    FixedHeaderBankCopy.bank,RecursiveDimensionBank.head,RecursiveDimensionBank.tape]
  trivial

theorem caller_cells (kind : Fin 3) (caller : Tapes t a) (hs : Fin 3 → List Bool) (i : Fin t) :
    (output caller kind hs).head (Fin.castAdd 6 (baseSlot i)) = caller.head i ∧
    (output caller kind hs).tape (Fin.castAdd 6 (baseSlot i)) = caller.tape i := by
  simp only [output,baseSlot,Tapes.append,Fin.addCases_left]
  exact ⟨trivial,trivial⟩

theorem zero_blank (kind : Fin 3) (caller : Tapes t a) (hs : Fin 3 → List Bool) :
    (output caller kind hs).head (Fin.castAdd 6 zeroSlot) = 0 ∧
    (output caller kind hs).tape (Fin.castAdd 6 zeroSlot) = fun _ => blank := by
  simp only [output,zeroSlot,Tapes.append,Fin.addCases_left,Fin.addCases_right,FixedHeaderBankCopy.empty]
  exact ⟨trivial,trivial⟩

theorem one_blank (kind : Fin 3) (caller : Tapes t a) (hs : Fin 3 → List Bool) :
    (output caller kind hs).head (Fin.castAdd 6 oneSlot) = 0 ∧
    (output caller kind hs).tape (Fin.castAdd 6 oneSlot) = fun _ => blank := by
  simp only [output,oneSlot,Tapes.append,Fin.addCases_left,Fin.addCases_right,FixedHeaderBankCopy.empty]
  exact ⟨trivial,trivial⟩

end
end IntegerMultBounds.Machine.CountedPackedShapeHeaders
