import IntegerMultBounds.Machine.BinaryRadixRangePrepare
import IntegerMultBounds.Machine.RowPaddingConstructedAlphabet

/-! Actual binary-range preparation and cropping embedded into the recursive
alphabet, with literal encoded payload and header endpoints. -/
namespace IntegerMultBounds.Machine.BinaryRadixRangePrepareAlphabet
noncomputable section
variable {a : ℕ}

def encoding := CountedLoopReuseAlphabet.encoding a
def mapTape (source : ℤ → Fin 4) : ℤ → Fin (a+4) := fun z => (encoding (a := a)).encode (source z)
def mapArray {n : ℕ} (x : Fin n → Fin 4) : Fin n → Fin (a+4) := fun z => (encoding (a := a)).encode (x z)
def word {n : ℕ} (x : Fin n → Fin (a+4)) := putWord (fun _ => blank) 0 (List.ofFn x)

private def hd : Option (List Bool) → ℤ | none => 0 | some _ => 1
private def tp : Option (List Bool) → ℤ → Fin (a+4)
  | none => fun _ => blank
  | some bs => RadixZeroFill.encodedBinary bs

def bank (source dest : ℤ → Fin (a+4)) (hs : Fin 4 → List Bool)
    (ns ms es : Option (List Bool)) : Tapes 19 a :=
  ⟨(fun i => match i.val with
    | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 1
    | 6 => hd ns | 7 => hd ms | 8 => hd es | _ => 0),
    (fun i => match i.val with
    | 0 => source | 1 => dest
    | 2 => RadixZeroFill.encodedBinary (hs 0)
    | 3 => RadixZeroFill.encodedBinary (hs 1)
    | 4 => RadixZeroFill.encodedBinary (hs 2)
    | 5 => RadixZeroFill.encodedBinary (hs 3)
    | 6 => tp ns | 7 => tp ms | 8 => tp es | _ => fun _ => blank)⟩

def input (source dest : ℤ → Fin (a+4)) (hs : Fin 4 → List Bool) := bank source dest hs none none none

def prepared (radix u : ℕ) (source dest : ℤ → Fin (a+4)) (hs : Fin 4 → List Bool) :=
  bank source dest hs (some (RadixRangeDescriptors.binaryBits u))
    (some (RadixRangeDescriptors.radixBits radix u)) (some (RadixRangeDescriptors.exponentBits radix u))

def program (radix : ℕ) := Alphabet.program (encoding (a := a)) (BinaryRadixRangePrepare.program radix)
def finishProgram := Alphabet.program (encoding (a := a)) BinaryRadixRangePrepare.finishProgram

theorem map_binary (bs : List Bool) :
    mapTape (a := a) (RadixZeroFill.encodedBinary (q := 0) bs) = RadixZeroFill.encodedBinary bs := by
  change (fun z => (CountedLoopReuseAlphabet.encoding a).encode
    ((RadixToBinary.binaryEncoding (q := 0)).encode (CountedCopyReuse.binary bs z))) =
    (fun z => (RadixToBinary.binaryEncoding (q := a)).encode (CountedCopyReuse.binary bs z))
  funext z
  generalize hx : CountedCopyReuse.binary bs z = x
  fin_cases x <;> rfl

theorem mapped_bank (source dest : ℤ → Fin 4) (hs : Fin 4 → List Bool)
    (ns ms es : Option (List Bool)) :
    Alphabet.mapTapes (encoding (a := a)) (BinaryRadixRangePrepare.bank source dest hs ns ms es) =
      bank (mapTape source) (mapTape dest) hs ns ms es := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    fin_cases i
    all_goals first | rfl | exact map_binary _ | skip
    · cases ns <;> rfl
    · cases ms <;> rfl
    · cases es <;> rfl

theorem mapped_input (source dest : ℤ → Fin 4) (hs : Fin 4 → List Bool) :
    Alphabet.mapTapes (encoding (a := a)) (BinaryRadixRangePrepare.input source dest hs) =
      input (mapTape source) (mapTape dest) hs := mapped_bank _ _ _ _ _ _

theorem mapped_prepared (radix u : ℕ) (source dest : ℤ → Fin 4) (hs : Fin 4 → List Bool) :
    Alphabet.mapTapes (encoding (a := a)) (BinaryRadixRangePrepare.prepared radix u source dest hs) =
      prepared radix u (mapTape source) (mapTape dest) hs := mapped_bank _ _ _ _ _ _

theorem map_word {n : ℕ} (x : Fin n → Fin 4) :
    mapTape (a := a) (RadixRangePaddingExecution.word x) = word (mapArray x) :=
  RowPaddingConstructedAlphabet.map_array_word (fun _ => blank) 0 x

theorem map_empty : mapTape (a := a) RadixRangePaddingExecution.empty = fun _ => blank := rfl

theorem pad_encoding (P N G B M : ℕ) (x : Fin (RadixRangePadding.volume P N G B) → Fin 4) :
    mapArray (a := a) (RadixRangePadding.pad M (bitSymbol false) x) =
      RadixRangePadding.pad M (bitSymbol false) (mapArray x) := by
  funext z
  unfold mapArray RadixRangePadding.pad RecursiveRowPadding.pad
  dsimp only
  split_ifs <;> rfl

theorem transpose_encoding (P N G B : ℕ) (x : Fin (RadixRangePadding.volume P N G B) → Fin 4) :
    mapArray (a := a) (RadixRangePadding.transpose x) = RadixRangePadding.transpose (mapArray x) := rfl

theorem crop_encoding (P N G B M : ℕ) (hNM : N ≤ M)
    (x : Fin (RadixRangePadding.volume P M G B) → Fin 4) :
    mapArray (a := a) (RadixRangePadding.cropStages hNM x) = RadixRangePadding.cropStages hNM (mapArray x) := rfl

theorem map_bits {n : ℕ} (x : Fin n → Bool) :
    mapArray (a := a) (fun z => bitSymbol (x z)) = fun z => bitSymbol (x z) := by
  funext z
  unfold mapArray
  dsimp only
  cases x z <;> rfl

private theorem map_exact {s states cost : ℕ} {M : Program s states 0} {v w : Tapes s 0}
    (h : HoareTime M (fun z => z = v) (fun z => z = w) cost) :
    HoareTime (Alphabet.program (encoding (a := a)) M)
      (fun z => z = Alphabet.mapTapes encoding v) (fun z => z = Alphabet.mapTapes encoding w) cost := by
  apply (Alphabet.map_hoare encoding h).consequence _ _ le_rfl
  · rintro z rfl; exact ⟨_,rfl,rfl⟩
  · rintro z ⟨original,rfl,rfl⟩; rfl

theorem prepare_hoare (radix P G B u : ℕ) (hr : 2 ≤ radix) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (x : Fin (RadixRangePadding.volume P (2^u) G B) → Fin 4) :
    HoareTime (program (a := a) radix)
      (fun v => v = input (word (mapArray x)) (fun _ => blank) hs)
      (fun v => v = prepared radix u (word (RadixRangePadding.pad
        (radix^RadixRangeDescriptors.exponent radix u) (bitSymbol false) (mapArray x))) (fun _ => blank) hs)
      (BinaryRadixRangePrepare.prepareConstant radix*RadixRangePadding.volume P (2^u) G B) := by
  have h := map_exact (a := a) (BinaryRadixRangePrepare.prepare_hoare radix P G B u hr hs hv hc hP hG hB x)
  simp only [mapped_input,mapped_prepared,map_word,map_empty] at h
  rw [pad_encoding P (2^u) G B (radix^RadixRangeDescriptors.exponent radix u) x] at h
  exact h

theorem finish_hoare (radix P G B u : ℕ) (hr : 2 ≤ radix) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (x : Fin (RadixRangePadding.volume P (radix^RadixRangeDescriptors.exponent radix u) G B) → Fin 4) :
    HoareTime (finishProgram (a := a))
      (fun v => v = prepared radix u (word (mapArray x)) (fun _ => blank) hs)
      (fun v => v = input (word (RadixRangePadding.cropStages
        (RadixRangeDescriptors.range_bounds radix u hr).1 (mapArray x))) (fun _ => blank) hs)
      (BinaryRadixRangePrepare.finishConstant radix*RadixRangePadding.volume P (2^u) G B) := by
  have h := map_exact (a := a) (BinaryRadixRangePrepare.finish_hoare radix P G B u hr hs hv hc hP hG hB x)
  simpa only [finishProgram,mapped_input,mapped_prepared,map_word,map_empty,crop_encoding] using h

theorem finish_transpose_pad_hoare (radix P G B u : ℕ) (hr : 2 ≤ radix) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (x : Fin (RadixRangePadding.volume P (2^u) G B) → Fin 4) :
    HoareTime (finishProgram (a := a))
      (fun v => v = prepared radix u (word (RadixRangePadding.transpose (RadixRangePadding.pad
        (radix^RadixRangeDescriptors.exponent radix u) (bitSymbol false) (mapArray x)))) (fun _ => blank) hs)
      (fun v => v = input (word (RadixRangePadding.transpose (mapArray x))) (fun _ => blank) hs)
      (BinaryRadixRangePrepare.finishConstant radix*RadixRangePadding.volume P (2^u) G B) := by
  have h := map_exact (a := a) (BinaryRadixRangePrepare.finish_transpose_pad_hoare radix P G B u hr hs hv hc hP hG hB x)
  simp only [mapped_input,mapped_prepared,map_word,map_empty,transpose_encoding] at h
  rw [pad_encoding P (2^u) G B (radix^RadixRangeDescriptors.exponent radix u) x] at h
  exact h


theorem prepare_bits_hoare (radix P G B u : ℕ) (hr : 2 ≤ radix) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (x : Fin (RadixRangePadding.volume P (2^u) G B) → Bool) :
    HoareTime (program (a := a) radix)
      (fun v => v = input (word (fun z => bitSymbol (x z))) (fun _ => blank) hs)
      (fun v => v = prepared radix u (word (RadixRangePadding.pad
        (radix^RadixRangeDescriptors.exponent radix u) (bitSymbol false) (fun z => bitSymbol (x z)))) (fun _ => blank) hs)
      (BinaryRadixRangePrepare.prepareConstant radix*RadixRangePadding.volume P (2^u) G B) := by
  simpa only [map_bits] using prepare_hoare (a := a) radix P G B u hr hs hv hc hP hG hB (fun z => bitSymbol (x z))

theorem finish_transpose_pad_bits_hoare (radix P G B u : ℕ) (hr : 2 ≤ radix) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (x : Fin (RadixRangePadding.volume P (2^u) G B) → Bool) :
    HoareTime (finishProgram (a := a))
      (fun v => v = prepared radix u (word (RadixRangePadding.transpose (RadixRangePadding.pad
        (radix^RadixRangeDescriptors.exponent radix u) (bitSymbol false) (fun z => bitSymbol (x z))))) (fun _ => blank) hs)
      (fun v => v = input (word (RadixRangePadding.transpose (fun z => bitSymbol (x z)))) (fun _ => blank) hs)
      (BinaryRadixRangePrepare.finishConstant radix*RadixRangePadding.volume P (2^u) G B) := by
  simpa only [map_bits] using finish_transpose_pad_hoare (a := a) radix P G B u hr hs hv hc hP hG hB (fun z => bitSymbol (x z))

def headerWords (radix u : ℕ) (hs : Fin 4 → List Bool) : Fin 7 → List Bool :=
  ![hs 0,hs 1,hs 2,hs 3,RadixRangeDescriptors.binaryBits u,
    RadixRangeDescriptors.radixBits radix u,RadixRangeDescriptors.exponentBits radix u]

def headerSlot (i : Fin 7) : Fin 19 := ⟨2+i.val,by omega⟩

theorem prepared_headers (radix u : ℕ) (source dest : ℤ → Fin (a+4))
    (hs : Fin 4 → List Bool) (i : Fin 7) :
    (prepared radix u source dest hs).head (headerSlot i) = 1 ∧
    (prepared radix u source dest hs).tape (headerSlot i) =
      RadixZeroFill.encodedBinary (headerWords radix u hs i) := by
  fin_cases i <;> exact ⟨rfl,rfl⟩

theorem prepared_work_blank (radix u : ℕ) (source dest : ℤ → Fin (a+4))
    (hs : Fin 4 → List Bool) (i : Fin 19) (hi : 9 ≤ i.val) :
    (prepared radix u source dest hs).head i = 0 ∧
    (prepared radix u source dest hs).tape i = fun _ => blank := by
  fin_cases i <;> first | exact ⟨rfl,rfl⟩ | solve | norm_num at hi

end
end IntegerMultBounds.Machine.BinaryRadixRangePrepareAlphabet
