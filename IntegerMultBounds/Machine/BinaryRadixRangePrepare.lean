import IntegerMultBounds.Machine.RadixRangeDescriptors
import IntegerMultBounds.Machine.RadixRangePaddingExecution

/-! Actual numerical range preparation from only P/G/B/binary-width input
headers. The fixed-radix range, exponent and binary range are generated,
both payload coordinates are padded, and inverse cropping erases metadata. -/
namespace IntegerMultBounds.Machine.BinaryRadixRangePrepare
noncomputable section
open RadixRangePaddingExecution (word empty)

private def hd : Option (List Bool) → ℤ | none => 0 | some _ => 1
private def tp : Option (List Bool) → ℤ → Fin 4
  | none => fun _ => blank
  | some bs => RadixZeroFill.encodedBinary bs

/-- Payload0/1; immutable P/G/B/u2–5; generated N/M/e6–8;
ten work tapes9–18. Payload heads0, present descriptor heads1. -/
def bank (source dest : ℤ → Fin 4) (hs : Fin 4 → List Bool)
    (ns ms es : Option (List Bool)) : Tapes 19 0 :=
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

def input (source dest : ℤ → Fin 4) (hs : Fin 4 → List Bool) :=
  bank source dest hs none none none

def prepared (radix u : ℕ) (source dest : ℤ → Fin 4) (hs : Fin 4 → List Bool) :=
  bank source dest hs (some (RadixRangeDescriptors.binaryBits u))
    (some (RadixRangeDescriptors.radixBits radix u))
    (some (RadixRangeDescriptors.exponentBits radix u))

def headers (radix u : ℕ) (hs : Fin 4 → List Bool) : Fin 5 → List Bool :=
  ![hs 0,RadixRangeDescriptors.binaryBits u,hs 1,hs 2,RadixRangeDescriptors.radixBits radix u]

def values (P G B u : ℕ) : Fin 4 → ℕ := ![P,G,B,u]

def metadataPlacement : Fin (12+7) ≃ Fin 19 where
  toFun := fun i => match i.val with
    | 0 => 9 | 1 => 10 | 2 => 11 | 3 => 12 | 4 => 13 | 5 => 6 | 6 => 14 | 7 => 5 | 8 => 15 | 9 => 16 | 10 => 7 | 11 => 8 | 12 => 0 | 13 => 1 | 14 => 2 | 15 => 3 | 16 => 4 | 17 => 17 | _ => 18
  invFun := fun i => match i.val with
    | 0 => 12 | 1 => 13 | 2 => 14 | 3 => 15 | 4 => 16 | 5 => 7 | 6 => 5 | 7 => 10 | 8 => 11 | 9 => 0 | 10 => 1 | 11 => 2 | 12 => 3 | 13 => 4 | 14 => 6 | 15 => 8 | 16 => 9 | 17 => 17 | _ => 18
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def paddingPlacement : Fin (17+2) ≃ Fin 19 where
  toFun := fun i => match i.val with
    | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 6 | 4 => 3 | 5 => 4 | 6 => 7 | 7 => 9 | 8 => 10 | 9 => 11 | 10 => 12 | 11 => 13 | 12 => 14 | 13 => 15 | 14 => 16 | 15 => 17 | 16 => 18 | 17 => 5 | _ => 8
  invFun := fun i => match i.val with
    | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 17 | 6 => 3 | 7 => 6 | 8 => 18 | 9 => 7 | 10 => 8 | 11 => 9 | 12 => 10 | 13 => 11 | 14 => 12 | 15 => 13 | 16 => 14 | 17 => 15 | _ => 16
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private theorem binary_eq (bs : List Bool) : RadixZeroFill.encodedBinary (q := 0) bs =
    CountedLoopReuseAlphabet.binary bs := by
  change (fun z => (RadixToBinary.binaryEncoding (q := 0)).encode (CountedCopyReuse.binary bs z)) = _
  exact CountedLoopReuseAlphabet.encoding_binary bs

private theorem metadata_input (source dest : ℤ → Fin 4) (hs : Fin 4 → List Bool) :
    Placement.active metadataPlacement (input source dest hs) = RadixRangeDescriptors.input (hs 3) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact binary_eq _

private theorem metadata_prepared (radix u : ℕ) (source dest : ℤ → Fin 4) (hs : Fin 4 → List Bool) :
    Placement.active metadataPlacement (prepared radix u source dest hs) =
      RadixRangeDescriptors.output radix u (hs 3) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm

private theorem metadata_extra (radix u : ℕ) (source dest : ℤ → Fin 4) (hs : Fin 4 → List Bool) :
    Placement.extra metadataPlacement (input source dest hs) =
      Placement.extra metadataPlacement (prepared radix u source dest hs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem padding_active (radix u : ℕ) (source dest : ℤ → Fin 4) (hs : Fin 4 → List Bool) :
    Placement.active paddingPlacement (prepared radix u source dest hs) =
      RangePaddingDimensions.input source dest (headers radix u hs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem padding_extra (radix u : ℕ) (source dest source' dest' : ℤ → Fin 4) (hs : Fin 4 → List Bool) :
    Placement.extra paddingPlacement (prepared radix u source dest hs) =
      Placement.extra paddingPlacement (prepared radix u source' dest' hs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem placed_exact {s u t r cost : ℕ} {M : Program s r 0}
    (e : Fin (s+u) ≃ Fin t) (v w : Tapes t 0) (small small' : Tapes s 0)
    (ha : Placement.active e v = small) (hf : Placement.active e w = small')
    (he : Placement.extra e v = Placement.extra e w)
    (hh : HoareTime M (fun x => x = small) (fun x => x = small') cost) :
    HoareTime (Placement.placed M e) (fun x => x = v) (fun x => x = w) cost := by
  apply (Placement.hoare_at hh e v ha).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨y,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

def descriptorProgram (radix : ℕ) := Placement.placed (RadixRangeDescriptors.program radix) metadataPlacement
def padProgram := Placement.placed RadixRangePaddingExecution.padProgram paddingPlacement
def cropProgram := Placement.placed RadixRangePaddingExecution.cropProgram paddingPlacement
def cleanupProgram := Placement.placed RadixRangeDescriptors.cleanupProgram metadataPlacement

def program (radix : ℕ) := seq (descriptorProgram radix) padProgram
def finishProgram := seq cropProgram cleanupProgram

theorem descriptor_hoare (radix u : ℕ) (hr : 2 ≤ radix) (source dest : ℤ → Fin 4)
    (hs : Fin 4 → List Bool) (hu : Counter.value (hs 3) = u)
    (cu : GrowingCounterData.Canonical (hs 3)) :
    HoareTime (descriptorProgram radix) (fun v => v = input source dest hs)
      (fun v => v = prepared radix u source dest hs) (RadixRangeDescriptors.constant radix*2^u) := by
  exact placed_exact metadataPlacement _ _ _ _ (metadata_input _ _ _) (metadata_prepared _ _ _ _ _)
    (metadata_extra _ _ _ _ _) (RadixRangeDescriptors.construct_hoare radix u hr _ hu cu)

theorem cleanup_hoare (radix u : ℕ) (hr : 2 ≤ radix) (source dest : ℤ → Fin 4)
    (hs : Fin 4 → List Bool) :
    HoareTime cleanupProgram (fun v => v = prepared radix u source dest hs)
      (fun v => v = input source dest hs) ((12*radix+15)*2^u) := by
  exact placed_exact metadataPlacement _ _ _ _ (metadata_prepared _ _ _ _ _) (metadata_input _ _ _)
    (metadata_extra _ _ _ _ _).symm (RadixRangeDescriptors.cleanup_linear radix u hr _)

private theorem headers_value (radix P G B u : ℕ) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i) :
    ∀ i, Counter.value (headers radix u hs i) =
      RangePaddingDimensions.values P (2^u) G B (radix^RadixRangeDescriptors.exponent radix u) i := by
  intro i; fin_cases i
  all_goals first | exact hv _ | exact RadixRangeDescriptors.binary_value _ | exact RadixRangeDescriptors.radix_value _ _

private theorem headers_canonical (radix u : ℕ) (hs : Fin 4 → List Bool)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    ∀ i, GrowingCounterData.Canonical (headers radix u hs i) := by
  intro i; fin_cases i
  all_goals first | exact hc _ | exact RadixRangeDescriptors.binary_canonical _ | exact RadixRangeDescriptors.radix_canonical _ _

theorem pad_hoare (radix P G B u : ℕ) (hr : 2 ≤ radix) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (x : Fin (RadixRangePadding.volume P (2^u) G B) → Fin 4) :
    HoareTime padProgram (fun v => v = prepared radix u (word x) empty hs)
      (fun v => v = prepared radix u
        (word (RadixRangePadding.pad (radix^RadixRangeDescriptors.exponent radix u) (bitSymbol false) x)) empty hs)
      (1200*RadixRangePadding.volume P (radix^RadixRangeDescriptors.exponent radix u) G B) := by
  exact placed_exact paddingPlacement _ _ _ _ (padding_active _ _ _ _ _) (padding_active _ _ _ _ _)
    (padding_extra _ _ _ _ _ _ _)
    (RadixRangePaddingExecution.pad_hoare _ _ _ _ _ _ (headers_value _ _ _ _ _ _ hv)
      (headers_canonical _ _ _ hc) hP (Nat.two_pow_pos _) hG hB (RadixRangeDescriptors.range_bounds radix u hr).1 x)

theorem crop_hoare (radix P G B u : ℕ) (hr : 2 ≤ radix) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (x : Fin (RadixRangePadding.volume P (radix^RadixRangeDescriptors.exponent radix u) G B) → Fin 4) :
    HoareTime cropProgram (fun v => v = prepared radix u (word x) empty hs)
      (fun v => v = prepared radix u (word (RadixRangePadding.cropStages
        (RadixRangeDescriptors.range_bounds radix u hr).1 x)) empty hs)
      (1200*RadixRangePadding.volume P (radix^RadixRangeDescriptors.exponent radix u) G B) := by
  exact placed_exact paddingPlacement _ _ _ _ (padding_active _ _ _ _ _) (padding_active _ _ _ _ _)
    (padding_extra _ _ _ _ _ _ _)
    (RadixRangePaddingExecution.crop_hoare _ _ _ _ _ _ (headers_value _ _ _ _ _ _ hv)
      (headers_canonical _ _ _ hc) hP (Nat.two_pow_pos _) hG hB (RadixRangeDescriptors.range_bounds radix u hr).1 x)

/-- The enclosing numerical range expands each of the two coordinates by
at most the fixed radix. Hence the physical scans remain linear in the
original serialized payload volume. -/
theorem volume_bound (radix P G B u : ℕ) (hr : 2 ≤ radix) :
    RadixRangePadding.volume P (radix^RadixRangeDescriptors.exponent radix u) G B ≤
      (radix*radix)*RadixRangePadding.volume P (2^u) G B := by
  have hm := (RadixRangeDescriptors.range_bounds radix u hr).2.le
  have hh := Nat.mul_le_mul hm hm
  calc
    RadixRangePadding.volume P (radix^RadixRangeDescriptors.exponent radix u) G B =
      (P*G*B)*((radix^RadixRangeDescriptors.exponent radix u)*(radix^RadixRangeDescriptors.exponent radix u)) := by
        unfold RadixRangePadding.volume; ring
    _ ≤ (P*G*B)*((radix*2^u)*(radix*2^u)) := Nat.mul_le_mul_left _ hh
    _ = (radix*radix)*RadixRangePadding.volume P (2^u) G B := by
      unfold RadixRangePadding.volume; ring

theorem range_le_volume (P G B u : ℕ) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) :
    2^u ≤ RadixRangePadding.volume P (2^u) G B := by
  have hn := Nat.two_pow_pos u
  have hPG : 1 ≤ P*G*B := Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos (Nat.mul_pos hP hG) hB).ne'
  have hNN : 2^u ≤ 2^u*2^u := by nlinarith
  calc
    2^u ≤ 2^u*2^u := hNN
    _ ≤ (P*G*B)*(2^u*2^u) := by nlinarith
    _ = RadixRangePadding.volume P (2^u) G B := by unfold RadixRangePadding.volume; ring

def prepareConstant (radix : ℕ) := RadixRangeDescriptors.constant radix+1200*(radix*radix)+1
def finishConstant (radix : ℕ) := 1200*(radix*radix)+(12*radix+15)+1

/-- From only canonical P/G/B/u, construct the exact N=2^u, least enclosing
M=radix^e and e, then physically pad both coordinates with zero symbols.
The input headers survive and all ten work tapes finish wholly blank. -/
theorem prepare_hoare (radix P G B u : ℕ) (hr : 2 ≤ radix) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (x : Fin (RadixRangePadding.volume P (2^u) G B) → Fin 4) :
    HoareTime (program radix) (fun v => v = input (word x) empty hs)
      (fun v => v = prepared radix u
        (word (RadixRangePadding.pad (radix^RadixRangeDescriptors.exponent radix u) (bitSymbol false) x)) empty hs)
      (prepareConstant radix*RadixRangePadding.volume P (2^u) G B) := by
  have h := (descriptor_hoare radix u hr (word x) empty hs (hv 3) (hc 3)).seq
    (pad_hoare radix P G B u hr hs hv hc hP hG hB x)
  apply h.consequence (fun _ hh => hh) (fun _ hh => hh)
  have hN := range_le_volume P G B u hP hG hB
  have hV := volume_bound radix P G B u hr
  have hpos : 0 < RadixRangePadding.volume P (2^u) G B := lt_of_lt_of_le (Nat.two_pow_pos u) hN
  have hcst := Nat.mul_le_mul_left (RadixRangeDescriptors.constant radix) hN
  unfold prepareConstant
  nlinarith

/-- Crop arbitrary padded content, then physically erase all three generated
range descriptors. Only the original four canonical headers remain. -/
theorem finish_hoare (radix P G B u : ℕ) (hr : 2 ≤ radix) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (x : Fin (RadixRangePadding.volume P (radix^RadixRangeDescriptors.exponent radix u) G B) → Fin 4) :
    HoareTime finishProgram (fun v => v = prepared radix u (word x) empty hs)
      (fun v => v = input (word (RadixRangePadding.cropStages
        (RadixRangeDescriptors.range_bounds radix u hr).1 x)) empty hs)
      (finishConstant radix*RadixRangePadding.volume P (2^u) G B) := by
  have h := (crop_hoare radix P G B u hr hs hv hc hP hG hB x).seq
    (cleanup_hoare radix u hr _ empty hs)
  apply h.consequence (fun _ hh => hh) (fun _ hh => hh)
  have hN := range_le_volume P G B u hP hG hB
  have hV := volume_bound radix P G B u hr
  have hpos : 0 < RadixRangePadding.volume P (2^u) G B := lt_of_lt_of_le (Nat.two_pow_pos u) hN
  have hcst := Nat.mul_le_mul_left (12*radix+15) hN
  unfold finishConstant
  nlinarith

/-- Finish after an externally proved padded-range transpose returns exactly
the original binary-range transpose, with all generated metadata erased. -/
theorem finish_transpose_pad_hoare (radix P G B u : ℕ) (hr : 2 ≤ radix) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (x : Fin (RadixRangePadding.volume P (2^u) G B) → Fin 4) :
    HoareTime finishProgram
      (fun v => v = prepared radix u (word (RadixRangePadding.transpose
        (RadixRangePadding.pad (radix^RadixRangeDescriptors.exponent radix u) (bitSymbol false) x))) empty hs)
      (fun v => v = input (word (RadixRangePadding.transpose x)) empty hs)
      (finishConstant radix*RadixRangePadding.volume P (2^u) G B) := by
  have h := finish_hoare radix P G B u hr hs hv hc hP hG hB
    (RadixRangePadding.transpose (RadixRangePadding.pad (radix^RadixRangeDescriptors.exponent radix u) (bitSymbol false) x))
  simpa only [RadixRangePadding.cropStages_transpose_pad] using h

end
end IntegerMultBounds.Machine.BinaryRadixRangePrepare
