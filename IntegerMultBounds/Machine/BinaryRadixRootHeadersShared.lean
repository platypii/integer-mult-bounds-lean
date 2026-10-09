import IntegerMultBounds.Machine.BinaryRadixRangePrepareAlphabet
import IntegerMultBounds.Machine.FixedHeaderBankCopy
import IntegerMultBounds.Machine.ArbitraryWidthHighLayout

/-! Physically synthesize [P,1,1,e,G,B] from retained P/e/G/B. The one
constant is written and erased; all root descriptor copies are charged. -/
namespace IntegerMultBounds.Machine.BinaryRadixRootHeadersShared
noncomputable section
variable {a t : ℕ}

def oneBits := RecursiveChildQuotientsConstant.bits 1
def oneBank : Tapes 1 a := FixedHeaderBankCopy.headerBank (fun _ => oneBits)

def words (hs : Fin 4 → List Bool) : Fin 6 → List Bool := ![hs 0,oneBits,oneBits,hs 1,hs 2,hs 3]
def values (P e G B : ℕ) : Fin 4 → ℕ := ![P,e,G,B]

def focus (source : Fin 4 → Fin t) : Fin 6 → Fin (t+1) :=
  ![Fin.castAdd 1 (source 0),Fin.natAdd t 0,Fin.natAdd t 0,
    Fin.castAdd 1 (source 1),Fin.castAdd 1 (source 2),Fin.castAdd 1 (source 3)]

def oneWriter := Placement.placed (RecursiveChildQuotientsConstant.program (a := a) 1)
  (finAddFlip : Fin (1+t) ≃ Fin (t+1))
def oneCleanup := FixedHeaderBankCopy.cleanup (a := a) (n := 1) (by omega : 0 < t+1)
def copyProgram (source : Fin 4 → Fin t) := FixedHeaderBankCopy.program (a := a)
  (by omega : 0 < (t+1)+6) (focus source)
def program (source : Fin 4 → Fin t) := seq
  (seq (extend (oneWriter (a := a) (t := t)) 6) (copyProgram source))
  (extend (oneCleanup (a := a) (t := t)) 6)
def cleanup := FixedHeaderBankCopy.cleanup (a := a) (n := 6) (by omega : 0 < (t+1)+6)

def input (caller : Tapes t a) := (caller.append (FixedHeaderBankCopy.empty 1)).append (FixedHeaderBankCopy.empty 6)
def output (caller : Tapes t a) (hs : Fin 4 → List Bool) :=
  (caller.append (FixedHeaderBankCopy.empty 1)).append (FixedHeaderBankCopy.headerBank (words hs))

private theorem right_hoare {states budget : ℕ} {M : Program 1 states a}
    {v w : Tapes 1 a} (h : HoareTime M (fun z => z = v) (fun z => z = w) budget)
    (caller : Tapes t a) :
    HoareTime (Placement.placed M (finAddFlip : Fin (1+t) ≃ Fin (t+1)))
      (fun z => z = caller.append v) (fun z => z = caller.append w) budget := by
  have ha : Placement.active (finAddFlip : Fin (1+t) ≃ Fin (t+1)) (caller.append v) = v := by
    apply congrArg₂ Tapes.mk <;> funext i <;> simp [Tapes.append]
  have hw : Placement.active (finAddFlip : Fin (1+t) ≃ Fin (t+1)) (caller.append w) = w := by
    apply congrArg₂ Tapes.mk <;> funext i <;> simp [Tapes.append]
  have hf : Placement.extra (finAddFlip : Fin (1+t) ≃ Fin (t+1)) (caller.append v) =
      Placement.extra (finAddFlip : Fin (1+t) ≃ Fin (t+1)) (caller.append w) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> simp [Tapes.append]
  have hp := Placement.hoare_at h _ (caller.append v) ha
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,hs,rfl⟩
  rw [hs,Placement.replace,hf]
  exact (congrArg (fun z => Placement.combine
    (finAddFlip : Fin (1+t) ≃ Fin (t+1)) z
    (Placement.extra finAddFlip (caller.append w))) hw.symm).trans (Placement.view _ _)

theorem writes_one (caller : Tapes t a) :
    HoareTime (oneWriter (a := a) (t := t))
      (fun w => w = caller.append (FixedHeaderBankCopy.empty 1))
      (fun w => w = caller.append oneBank) 9 := by
  have h := RecursiveChildQuotientsConstant.initialize_hoare (a := a) 1
  have he : FiniteReturnStack.bank (BinaryDescriptorStack.descriptor oneBits) 1 = oneBank (a := a) := by
    apply congrArg₂ Tapes.mk
    · rfl
    · funext i; exact BinaryDescriptorStackRoundtrip.descriptor_encoded _
  change HoareTime _ (fun w => w = FixedHeaderBankCopy.empty 1)
    (fun w => w = FiniteReturnStack.bank (BinaryDescriptorStack.descriptor oneBits) 1) 9 at h
  rw [he] at h
  exact right_hoare h caller

theorem words_canonical (hs : Fin 4 → List Bool) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    ∀ i, GrowingCounterData.Canonical (words hs i) := by
  intro i; fin_cases i <;> first | exact hc _ | exact RecursiveChildQuotientsConstant.bits_canonical 1

theorem words_bounded (hs : Fin 4 → List Bool) (V : ℕ) (hV : 0 < V)
    (hv : ∀ i, Counter.value (hs i) ≤ V) : ∀ i, Counter.value (words hs i) ≤ V := by
  intro i; fin_cases i <;> first | exact hv _ | change 1 ≤ V; omega

theorem constructs (source : Fin 4 → Fin t) (caller : Tapes t a) (hs : Fin 4 → List Bool)
    (V : ℕ) (hV : 0 < V) (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hv : ∀ i, Counter.value (hs i) ≤ V)
    (ht : ∀ i, caller.tape (source i) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (source i) = 1) :
    HoareTime (program source) (fun w => w = input caller)
      (fun w => w = output caller hs) (80*V) := by
  have hw := hoare_extend_eq (writes_one caller) (FixedHeaderBankCopy.empty 6)
  have hc6 := words_canonical hs hc
  have hv6 := words_bounded hs V hV hv
  have hcopy := FixedHeaderBankCopy.constructs_linear (a := a)
    (by omega : 0 < (t+1)+6) (focus source) (words hs) (caller.append oneBank)
    (by intro i; fin_cases i <;> simp [focus,words,Tapes.append,oneBank,
      FixedHeaderBankCopy.headerBank,FixedHeaderBankCopy.bank,RecursiveDimensionBank.tape,ht])
    (by intro i; fin_cases i <;> simp [focus,Tapes.append,oneBank,
      FixedHeaderBankCopy.headerBank,FixedHeaderBankCopy.bank,RecursiveDimensionBank.head,hh])
    V hV hc6 hv6
  have he := hoare_extend_eq (FixedHeaderBankCopy.cleans_linear (a := a)
    (by omega : 0 < t+1) caller (fun _ : Fin 1 => oneBits) V hV
    (fun _ => RecursiveChildQuotientsConstant.bits_canonical 1) (by intro i; change 1 ≤ V; omega))
    (FixedHeaderBankCopy.headerBank (words hs))
  exact ((hw.seq hcopy).seq he).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem cleans (caller : Tapes t a) (hs : Fin 4 → List Bool) (V : ℕ) (hV : 0 < V)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hv : ∀ i, Counter.value (hs i) ≤ V) :
    HoareTime (cleanup (a := a) (t := t)) (fun w => w = output caller hs)
      (fun w => w = input caller) (54*V) :=
  FixedHeaderBankCopy.cleans_linear (by omega) (caller.append (FixedHeaderBankCopy.empty 1))
    (words hs) V hV (words_canonical hs hc) (words_bounded hs V hV hv)

theorem headers (P e G B : ℕ) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = values P e G B i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    RecursiveDimensionBank.Headers (ArbitraryWidthHighLayout.originalDescriptor P e G B) (words hs) := by
  refine ⟨?_,words_canonical hs hc⟩
  intro i; fin_cases i <;> first | rfl | exact hv _

theorem header_cells (caller : Tapes t a) (hs : Fin 4 → List Bool) (i : Fin 6) :
    (output caller hs).head (Fin.natAdd (t+1) i) = 1 ∧
    (output caller hs).tape (Fin.natAdd (t+1) i) = RadixZeroFill.encodedBinary (words hs i) := by
  simp only [output,FixedHeaderBankCopy.headerBank,FixedHeaderBankCopy.bank,Tapes.append,Fin.addCases_right,
    RecursiveDimensionBank.head,RecursiveDimensionBank.tape]
  trivial


def preparedSources : Fin 4 → Fin 19 := ![2,8,3,4]
def preparedWords (radix u : ℕ) (hs : Fin 4 → List Bool) : Fin 4 → List Bool :=
  ![hs 0,RadixRangeDescriptors.exponentBits radix u,hs 1,hs 2]

theorem prepared_canonical (radix u : ℕ) (hs : Fin 4 → List Bool)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    ∀ i, GrowingCounterData.Canonical (preparedWords radix u hs i) := by
  intro i; fin_cases i <;> first | exact hc _ | exact RadixRangeDescriptors.exponent_canonical radix u

theorem prepared_values (radix P G B u : ℕ) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values P G B u i) :
    ∀ i, Counter.value (preparedWords radix u hs i) = values P (RadixRangeDescriptors.exponent radix u) G B i := by
  intro i; fin_cases i <;> first | exact hv _ | exact RadixRangeDescriptors.exponent_value radix u

theorem prepared_bounds (radix P G B u : ℕ) (hr : 2 ≤ radix) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values P G B u i)
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) :
    ∀ i, Counter.value (preparedWords radix u hs i) ≤ RadixRangePadding.volume P (2^u) G B := by
  have hp : (ArbitraryWidthHighLayout.originalDescriptor P u G B).Positive :=
    ⟨hP,by change 0 < 1; decide,by change 0 < 1; decide,hG,hB⟩
  have hb := RecursiveHeaderBounds.values_le_volume (by decide : 2 ≤ 2)
    (ArbitraryWidthHighLayout.originalDescriptor P u G B) hp
  have hvol : RecursiveInterchangeLayout.volume 2 (ArbitraryWidthHighLayout.originalDescriptor P u G B) =
      RadixRangePadding.volume P (2^u) G B := by
    simp [RecursiveInterchangeLayout.volume,ArbitraryWidthHighLayout.originalDescriptor,RadixRangePadding.volume]
  rw [hvol] at hb
  intro i
  rw [prepared_values radix P G B u hs hv i]
  fin_cases i
  · exact hb 0
  · exact (RadixRangeDescriptors.exponent_le radix u hr).trans (hb 3)
  · exact hb 4
  · exact hb 5

theorem prepared_constructs (radix P G B u : ℕ) (hr : 2 ≤ radix)
    (source dest : ℤ → Fin (a+4)) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) :
    HoareTime (program (a := a) preparedSources)
      (fun w => w = input (BinaryRadixRangePrepareAlphabet.prepared radix u source dest hs))
      (fun w => w = output (BinaryRadixRangePrepareAlphabet.prepared radix u source dest hs) (preparedWords radix u hs))
      (80*RadixRangePadding.volume P (2^u) G B) := by
  have hV := lt_of_lt_of_le (Nat.two_pow_pos u) (BinaryRadixRangePrepare.range_le_volume P G B u hP hG hB)
  apply constructs preparedSources _ _ _ hV (prepared_canonical radix u hs hc)
    (prepared_bounds radix P G B u hr hs hv hP hG hB)
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

theorem prepared_cleans (radix P G B u : ℕ) (hr : 2 ≤ radix)
    (source dest : ℤ → Fin (a+4)) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) :
    HoareTime (cleanup (a := a) (t := 19))
      (fun w => w = output (BinaryRadixRangePrepareAlphabet.prepared radix u source dest hs) (preparedWords radix u hs))
      (fun w => w = input (BinaryRadixRangePrepareAlphabet.prepared radix u source dest hs))
      (54*RadixRangePadding.volume P (2^u) G B) :=
  cleans _ _ _ (lt_of_lt_of_le (Nat.two_pow_pos u) (BinaryRadixRangePrepare.range_le_volume P G B u hP hG hB))
    (prepared_canonical radix u hs hc) (prepared_bounds radix P G B u hr hs hv hP hG hB)

theorem prepared_headers (radix P G B u : ℕ) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    RecursiveDimensionBank.Headers
      (ArbitraryWidthHighLayout.originalDescriptor P (RadixRangeDescriptors.exponent radix u) G B)
      (words (preparedWords radix u hs)) :=
  headers P (RadixRangeDescriptors.exponent radix u) G B _
    (prepared_values radix P G B u hs hv) (prepared_canonical radix u hs hc)

end
end IntegerMultBounds.Machine.BinaryRadixRootHeadersShared
