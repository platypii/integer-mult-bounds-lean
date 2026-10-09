import IntegerMultBounds.Machine.ArbitraryWidthOriginalTotalRun
import IntegerMultBounds.Machine.BinaryRadixRootHeadersShared
import IntegerMultBounds.Machine.BinaryRadixRootEncoding
import IntegerMultBounds.Machine.BinaryRadixRangeRuntimeBudget

/-! Complete equal-width binary H/D interchange through radix padding. Every
conversion, root header, recursive branch, crop and erasure is physically run. -/
namespace IntegerMultBounds.Machine.BinaryRadixEqualRun
noncomputable section
open Networks
open Shared50ModularControl (prime)
open ArbitraryWidthHighLayout (originalDescriptor)
open RadixRangeDescriptors (exponent)
open BinaryRadixRangePrepareAlphabet (word prepared)
open BinaryRadixRootHeadersShared (preparedWords)
open SharedPlacementAlphabet (setTape)
open ArbitraryWidthHighExchangeJoin (exchangeCount movementCount)
open ArbitraryWidthHighRun (paddingCount)

def extendPrivate {states : ℕ} (M : Program 26 states prime) :=
  extend (extend (extend (extend (extend (extend (extend (extend (extend M 16) 19) 17) 12) 1)
    exchangeCount) movementCount) paddingCount) ArbitraryWidthElementary.tapeCount

def input (source : ℤ → Fin (prime+4)) (hs : Fin 4 → List Bool) :=
  ArbitraryWidthOriginalTotalRun.input (BinaryRadixRootHeadersShared.input
    (BinaryRadixRangePrepareAlphabet.input source (fun _ => blank) hs))

def headers : Fin 6 → Fin 26 := Fin.natAdd 20
def source : Fin 26 := 0

def prepareProgram := extendPrivate (extend (extend
  (BinaryRadixRangePrepareAlphabet.program (a := prime) prime) 1) 6)
def rootProgram := extendPrivate (BinaryRadixRootHeadersShared.program (a := prime)
  BinaryRadixRootHeadersShared.preparedSources)
def runProgram := ArbitraryWidthOriginalTotalRun.program headers source
def eraseProgram := extendPrivate (BinaryRadixRootHeadersShared.cleanup (a := prime) (t := 19))
def finishProgram := extendPrivate (extend (extend
  (BinaryRadixRangePrepareAlphabet.finishProgram (a := prime)) 1) 6)
def program := seq (seq (seq (seq prepareProgram rootProgram) (ArbitraryWidthOriginalTotalRun.program headers source)) eraseProgram) finishProgram

def cost (P G B u : ℕ) (hs : Fin 4 → List Bool) :=
  BinaryRadixRangePrepare.prepareConstant prime*RadixRangePadding.volume P (2^u) G B+1+
    80*RadixRangePadding.volume P (2^u) G B+1+
    ArbitraryWidthOriginalTotalRun.cost (originalDescriptor P (exponent prime u) G B)
      (BinaryRadixRootHeadersShared.words (preparedWords prime u hs))+1+
    54*RadixRangePadding.volume P (2^u) G B+1+
    BinaryRadixRangePrepare.finishConstant prime*RadixRangePadding.volume P (2^u) G B

private theorem private_hoare {states budget : ℕ} {M : Program 26 states prime}
    {v w : Tapes 26 prime} (h : HoareTime M (fun z => z = v) (fun z => z = w) budget) :
    HoareTime (extendPrivate M) (fun z => z = ArbitraryWidthOriginalTotalRun.input v)
      (fun z => z = ArbitraryWidthOriginalTotalRun.input w) budget :=
  hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq
    (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq h
    (FixedHeaderBankCopy.empty 16)) ArbitraryWidthHighPrepareShared.privateInput)
    (FixedHeaderBankCopy.empty 17)) (FixedHeaderBankCopy.empty 12)) ArbitraryWidthZeroHeaderShared.empty)
    (SharedBank.empty exchangeCount prime)) (SharedBank.empty movementCount prime))
    (SharedBank.empty paddingCount prime)) (FixedHeaderBankCopy.empty ArbitraryWidthElementary.tapeCount)

private theorem five_hoare {t a s1 s2 s3 s4 s5 b1 b2 b3 b4 b5 : ℕ}
    {M1 : Program t s1 a} {M2 : Program t s2 a} {M3 : Program t s3 a}
    {M4 : Program t s4 a} {M5 : Program t s5 a} {p0 p1 p2 p3 p4 p5 : TapePred t a}
    (h1 : HoareTime M1 p0 p1 b1) (h2 : HoareTime M2 p1 p2 b2)
    (h3 : HoareTime M3 p2 p3 b3) (h4 : HoareTime M4 p3 p4 b4) (h5 : HoareTime M5 p4 p5 b5) :
    HoareTime (seq (seq (seq (seq M1 M2) M3) M4) M5) p0 p5
      (b1+1+b2+1+b3+1+b4+1+b5) := (((h1.seq h2).seq h3).seq h4).seq h5

private theorem changed_root (u : ℕ) (hs : Fin 4 → List Bool) (s s' : ℤ → Fin (prime+4)) :
    setTape (BinaryRadixRootHeadersShared.output (prepared prime u s (fun _ => blank) hs)
      (preparedWords prime u hs)) source s' 0 =
    BinaryRadixRootHeadersShared.output (prepared prime u s' (fun _ => blank) hs)
      (preparedWords prime u hs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (P G B u : ℕ) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (x : Fin (RadixRangePadding.volume P (2^u) G B) → Bool) :
    HoareTime program (fun z => z = input (word (fun i => bitSymbol (x i))) hs)
      (fun z => z = input (word (RadixRangePadding.transpose (fun i => bitSymbol (x i)))) hs)
      (cost P G B u hs) := by
  unfold program input cost
  simp only [BinaryRadixRootHeadersShared.input]
  let M := prime^exponent prime u
  let sx : ℤ → Fin (prime+4) := word (RadixRangePadding.pad M (bitSymbol false) (fun i => bitSymbol (x i)))
  let tx : ℤ → Fin (prime+4) := word (RadixRangePadding.transpose (RadixRangePadding.pad M (bitSymbol false) (fun i => bitSymbol (x i))))
  have h1 := private_hoare (hoare_extend_eq (hoare_extend_eq
    (BinaryRadixRangePrepareAlphabet.prepare_bits_hoare (a := prime) prime P G B u
      Shared50ModularControl.prime_prime.two_le hs hv hc hP hG hB x)
      (FixedHeaderBankCopy.empty 1)) (FixedHeaderBankCopy.empty 6))
  change HoareTime prepareProgram _ _ _ at h1
  have h2 := private_hoare (BinaryRadixRootHeadersShared.prepared_constructs (a := prime)
    prime P G B u Shared50ModularControl.prime_prime.two_le sx (fun _ => blank) hs hv hc hP hG hB)
  change HoareTime rootProgram _ _ _ at h2
  let caller : Tapes 26 prime := BinaryRadixRootHeadersShared.output (prepared prime u sx (fun _ => blank) hs)
    (preparedWords prime u hs)
  let bits := RadixRangePadding.pad M false x
  have hbits : ArbitraryWidthHighExchangeShared.sourceWord
      (BinaryRadixRootEncoding.rootArray (fun i => BinaryRadixRootEncoding.bitValue (bits i))) = sx := by
    rw [BinaryRadixRootEncoding.source_bits]
    dsimp only [sx,bits,M]
    rw [BinaryRadixRootEncoding.pad_bits]
  have hout : ArbitraryWidthHighExchangeShared.sourceWord
      (Shared50RecursiveNodeRows.transpose (one_dvd _)
        (BinaryRadixRootEncoding.rootArray (fun i => BinaryRadixRootEncoding.bitValue (bits i)))) = tx := by
    rw [BinaryRadixRootEncoding.source_transpose_bits]
    dsimp only [tx,bits,M]
    rw [BinaryRadixRootEncoding.pad_bits]
  have hp : (originalDescriptor P (exponent prime u) G B).Positive :=
    ⟨hP,by change 0 < 1; decide,by change 0 < 1; decide,hG,hB⟩
  have h3 := ArbitraryWidthOriginalTotalRun.runs caller headers source
    (originalDescriptor P (exponent prime u) G B) (BinaryRadixRootHeadersShared.words (preparedWords prime u hs))
    hp (BinaryRadixRootHeadersShared.prepared_headers prime P G B u hs hv hc)
    (fun i => (BinaryRadixRootHeadersShared.header_cells _ _ i).2)
    (fun i => (BinaryRadixRootHeadersShared.header_cells _ _ i).1)
    (BinaryRadixRootEncoding.rootArray (fun i => BinaryRadixRootEncoding.bitValue (bits i)))
    (by change sx = _; exact hbits.symm) rfl
  rw [hout] at h3
  dsimp only [caller] at h3
  rw [changed_root] at h3
  have h4 := private_hoare (BinaryRadixRootHeadersShared.prepared_cleans (a := prime)
    prime P G B u Shared50ModularControl.prime_prime.two_le tx (fun _ => blank) hs hv hc hP hG hB)
  change HoareTime eraseProgram _ _ _ at h4
  have h5 := private_hoare (hoare_extend_eq (hoare_extend_eq
    (BinaryRadixRangePrepareAlphabet.finish_transpose_pad_bits_hoare (a := prime) prime P G B u
      Shared50ModularControl.prime_prime.two_le hs hv hc hP hG hB x)
      (FixedHeaderBankCopy.empty 1)) (FixedHeaderBankCopy.empty 6))
  change HoareTime finishProgram _ _ _ at h5
  exact five_hoare h1 h2 h3 h4 h5

theorem cost_eq_combined (P G B u : ℕ) (hs : Fin 4 → List Bool) :
    cost P G B u hs = BinaryRadixRangeRuntimeBudget.combinedCost P G B u
      (BinaryRadixRootHeadersShared.words (preparedWords prime u hs)) := by
  simp only [cost,BinaryRadixRangeRuntimeBudget.combinedCost,
    BinaryRadixRangeRuntimeBudget.overheadCoefficient,BinaryRadixRangeRuntimeBudget.originalVolume,
    BinaryRadixRangeRuntimeBudget.rootCost,BinaryRadixRangeRuntimeBudget.rootDescriptor,Nat.add_mul]
  omega

/-- The complete physical binary wrapper, including radix padding and crop,
retains the certified exponent measured against the original binary width. -/
theorem uniform_bound : ∃ C : ℝ, 0 < C ∧ ∀ (P G B u : ℕ) (hs : Fin 4 → List Bool),
    0 < P → 0 < G → 0 < B →
    (∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values P G B u i) →
    (∀ i, GrowingCounterData.Canonical (hs i)) →
    (cost P G B u hs : ℝ) ≤ C*(RadixRangePadding.volume P (2^u) G B : ℝ)*
      ((max 1 u : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := BinaryRadixRangeRuntimeBudget.uniform_bound
  refine ⟨C,hC,?_⟩
  intro P G B u hs hP hG hB hv hc
  rw [cost_eq_combined]
  exact hbound P G B u _ hP hG hB
    (BinaryRadixRootHeadersShared.prepared_headers prime P G B u hs hv hc)

end
end IntegerMultBounds.Machine.BinaryRadixEqualRun
