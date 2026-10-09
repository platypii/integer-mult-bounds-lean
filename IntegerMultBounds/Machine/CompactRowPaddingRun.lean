import IntegerMultBounds.Machine.CompactRowPaddingRound
import IntegerMultBounds.Machine.RowPaddingConstructedAlphabet

/-! Actual whole-record binary padding from original row/record-width runtime
headers. The fixed role count, enclosing row count, group-one and both span
counts are physically constructed; every generated tape is erased. -/
namespace IntegerMultBounds.Machine.CompactRowPaddingRun
noncomputable section
variable {a : ℕ}
open IntegerMultBounds.Compact.Layout (paddedRows)

private def head : Option (List Bool) → ℤ | none => 0 | some _ => 1
private def tape : Option (List Bool) → ℤ → Fin (a+4)
  | none => fun _ => blank
  | some bs => RadixZeroFill.encodedBinary bs

def oneBits := RecursiveChildQuotientsConstant.bits 1

/-- Original source/destination and row/width descriptors; every private tape
is wholly blank except the explicitly present one/rounded descriptors. -/
def bank (source dest : ℤ → Fin (a+4)) (p q : ℤ) (rs ls : List Bool)
    (one rounded : Option (List Bool)) : Tapes 25 a :=
  ⟨fun i => match i.val with
    | 0 => p | 1 => q | 2 => 1 | 3 => 1 | 4 => head one | 6 => head rounded | _ => 0,
   fun i => match i.val with
    | 0 => source | 1 => dest | 2 => RadixZeroFill.encodedBinary rs
    | 3 => RadixZeroFill.encodedBinary ls | 4 => tape one | 6 => tape rounded
    | _ => fun _ => blank⟩

def roundPlace : Fin (16+9) ≃ Fin 25 where
  toFun := ![2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,0,1,4,19,20,21,22,23,24]
  invFun := ![16,17,0,1,18,2,3,4,5,6,7,8,9,10,11,12,13,14,15,19,20,21,22,23,24]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def padPlace : Fin (12+13) ≃ Fin 25 where
  toFun := ![0,1,4,2,6,3,19,20,21,22,23,24,5,7,8,9,10,11,12,13,14,15,16,17,18]
  invFun := ![0,1,3,5,2,12,4,13,14,15,16,17,18,19,20,21,22,23,24,6,7,8,9,10,11]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def roundProgram (c : ℕ) := Placement.placed (CompactRowPaddingRound.program (a := a) c) roundPlace
def oneProgram := Placement.placed (RecursiveChildQuotientsConstant.program (a := a) 1)
  (FiniteReturnStackAt.placement (4 : Fin 25))
def padProgram := Placement.placed (RowPaddingConstructedAlphabet.program (a := a)) padPlace
def clearOne := BinaryDescriptorCleanupList.oneProgram (a := a) (4 : Fin 25)
def clearRounded := BinaryDescriptorCleanupList.oneProgram (a := a) (6 : Fin 25)
def program (c : ℕ) := seq (seq (seq (seq (roundProgram (a := a) c) oneProgram) padProgram) clearOne) clearRounded

private theorem placed_exact {s u t k cost : ℕ} {M : Program s k a}
    (e : Fin (s+u) ≃ Fin t) (v w : Tapes t a) (small small' : Tapes s a)
    (ha : Placement.active e v = small) (hf : Placement.active e w = small')
    (he : Placement.extra e v = Placement.extra e w)
    (hh : HoareTime M (fun x => x = small) (fun x => x = small') cost) :
    HoareTime (Placement.placed M e) (fun x => x = v) (fun x => x = w) cost := by
  apply (Placement.hoare_at hh e v ha).consequence (fun _ h => h) ?_ le_rfl
  rintro x ⟨y,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

theorem rounds (c : ℕ) (source dest : ℤ → Fin (a+4)) (p q : ℤ)
    (rs ls : List Bool) (r : ℕ) (hr : Counter.value rs = r)
    (cr : GrowingCounterData.Canonical rs) (hR : 0 < r) (hc : 0 < c) :
    HoareTime (roundProgram c) (fun w => w = bank source dest p q rs ls none none)
      (fun w => w = bank source dest p q rs ls none (some (CompactRowPaddingRound.bits r c)))
      (4096*paddedRows r c+5*(RecursiveChildQuotientsConstant.bits c).length+12) := by
  apply placed_exact roundPlace _ _ _ _ _ _ _ (CompactRowPaddingRound.constructs c rs ls r hr cr hR hc)
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem writes_one (source dest : ℤ → Fin (a+4)) (p q : ℤ)
    (rs ls rp : List Bool) :
    HoareTime (oneProgram (a := a)) (fun w => w = bank source dest p q rs ls none (some rp))
      (fun w => w = bank source dest p q rs ls (some oneBits) (some rp)) 9 := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) 1)
    (FiniteReturnStackAt.placement (4 : Fin 25)) (bank source dest p q rs ls none (some rp))
    (by rw [FiniteReturnStackAt.active_bank]; rfl)
  apply h.consequence (fun _ h => h) ?_ (by decide)
  rintro w ⟨z,rfl,rfl⟩
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [bank,head,tape,oneBits,BinaryDescriptorStackRoundtrip.descriptor_encoded]

private theorem encoded_binary (bs : List Bool) : RadixZeroFill.encodedBinary (q := a) bs =
    CountedLoopReuseAlphabet.binary bs := by
  exact CountedLoopReuseAlphabet.encoding_binary bs

theorem pads (c : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (rs ls : List Bool) (r l : ℕ) (x : Fin (1*r*l) → Bool)
    (hr : Counter.value rs = r) (hl : Counter.value ls = l)
    (cr : GrowingCounterData.Canonical rs) (cl : GrowingCounterData.Canonical ls)
    (hR : 0 < r) (hL : 0 < l) (hc : 0 < c) :
    HoareTime (padProgram (a := a))
      (fun w => w = bank (putWord (RowPaddingConstructedAlphabet.mapTape source) p
        (List.ofFn (fun z => bitSymbol (x z)))) (RowPaddingConstructedAlphabet.mapTape dest)
        p q rs ls (some oneBits) (some (CompactRowPaddingRound.bits r c)))
      (fun w => w = bank (RowPaddingConstructedAlphabet.erased
        (putWord (RowPaddingConstructedAlphabet.mapTape source) p (List.ofFn (fun z => bitSymbol (x z)))) p (1*r*l))
        (putWord (RowPaddingConstructedAlphabet.mapTape dest) q
          (List.ofFn (RecursiveRowPadding.pad (paddedRows r c) (bitSymbol false) (fun z => bitSymbol (x z)))))
        p q rs ls (some oneBits) (some (CompactRowPaddingRound.bits r c)))
      (413*(paddedRows r c*l)) := by
  have h := RowPaddingConstructedAlphabet.pad_bits_hoare (a := a) source dest p q
    oneBits rs (CompactRowPaddingRound.bits r c) ls 1 r (paddedRows r c) l x
    (RecursiveChildQuotientsConstant.bits_value 1) hr (CompactRowPaddingRound.bits_value r c hR hc) hl
    (RecursiveChildQuotientsConstant.bits_canonical 1) cr (CompactRowPaddingRound.bits_canonical r c) cl
    (by decide) hR (CompactRowPaddingRound.padded_bounds r c hc).1 hL
  apply placed_exact padPlace _ _ _ _ _ _ _ h
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact encoded_binary _

theorem clears_one (source dest : ℤ → Fin (a+4)) (p q : ℤ)
    (rs ls rp : List Bool) :
    HoareTime (clearOne (a := a))
      (fun w => w = bank source dest p q rs ls (some oneBits) (some rp))
      (fun w => w = bank source dest p q rs ls none (some rp)) 6 := by
  have h := BinaryDescriptorCleanupList.one_hoare (4 : Fin 25)
    (bank source dest p q rs ls (some oneBits) (some rp)) oneBits
    (BinaryDescriptorStackRoundtrip.descriptor_encoded oneBits).symm rfl
  apply h.consequence (fun _ h => h) ?_ (by decide)
  rintro w rfl
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem clears_rounded (source dest : ℤ → Fin (a+4)) (p q : ℤ)
    (rs ls rp : List Bool) :
    HoareTime (clearRounded (a := a))
      (fun w => w = bank source dest p q rs ls none (some rp))
      (fun w => w = bank source dest p q rs ls none none) (2*rp.length+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare (6 : Fin 25)
    (bank source dest p q rs ls none (some rp)) rp
    (BinaryDescriptorStackRoundtrip.descriptor_encoded rp).symm rfl
  apply h.consequence (fun _ h => h) ?_ le_rfl
  rintro w rfl
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- Padding is physically executed, and all twenty-one private tapes return
blank at origin. Original row/width headers and arbitrary exterior backgrounds
are retained. Dirty binary suffix fields are included in the literal records. -/
theorem runs (c : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (rs ls : List Bool) (r l : ℕ) (x : Fin (1*r*l) → Bool)
    (hr : Counter.value rs = r) (hl : Counter.value ls = l)
    (cr : GrowingCounterData.Canonical rs) (cl : GrowingCounterData.Canonical ls)
    (hR : 0 < r) (hL : 0 < l) (hc : 0 < c) :
    HoareTime (program (a := a) c)
      (fun w => w = bank (putWord (RowPaddingConstructedAlphabet.mapTape source) p
        (List.ofFn (fun z => bitSymbol (x z)))) (RowPaddingConstructedAlphabet.mapTape dest) p q rs ls none none)
      (fun w => w = bank (RowPaddingConstructedAlphabet.erased
        (putWord (RowPaddingConstructedAlphabet.mapTape source) p (List.ofFn (fun z => bitSymbol (x z)))) p (1*r*l))
        (putWord (RowPaddingConstructedAlphabet.mapTape dest) q
          (List.ofFn (RecursiveRowPadding.pad (paddedRows r c) (bitSymbol false) (fun z => bitSymbol (x z)))))
        p q rs ls none none)
      (4096*paddedRows r c+413*(paddedRows r c*l)+
        5*(RecursiveChildQuotientsConstant.bits c).length+2*(CompactRowPaddingRound.bits r c).length+35) := by
  let srcin := putWord (RowPaddingConstructedAlphabet.mapTape (a := a) source) p
    (List.ofFn (fun z => bitSymbol (x z)))
  let dstin := RowPaddingConstructedAlphabet.mapTape (a := a) dest
  let srcout := RowPaddingConstructedAlphabet.erased srcin p (1*r*l)
  let dstout := putWord dstin q
    (List.ofFn (RecursiveRowPadding.pad (paddedRows r c) (bitSymbol false) (fun z => bitSymbol (x z))))
  have h0 := rounds c srcin dstin p q rs ls r hr cr hR hc
  have h1 := writes_one srcin dstin p q rs ls (CompactRowPaddingRound.bits r c)
  have h2 := pads (a := a) c source dest p q rs ls r l x hr hl cr cl hR hL hc
  have h3 := clears_one srcout dstout p q rs ls (CompactRowPaddingRound.bits r c)
  have h4 := clears_rounded srcout dstout p q rs ls (CompactRowPaddingRound.bits r c)
  apply ((((h0.seq h1).seq h2).seq h3).seq h4).consequence (fun _ h => h) (fun _ h => h)
  omega

theorem budget_linear (r c l : ℕ) (hr : 0 < r) (hc : 0 < c) (hl : 0 < l) :
    4096*paddedRows r c+413*(paddedRows r c*l)+
      5*(RecursiveChildQuotientsConstant.bits c).length+2*(CompactRowPaddingRound.bits r c).length+35 ≤
      4600*(paddedRows r c*l) := by
  have hP : 0 < paddedRows r c := lt_of_lt_of_le hr (CompactRowPaddingRound.padded_bounds r c hc).1
  have hcP : c ≤ paddedRows r c := by
    rw [← CompactRowPaddingRound.rounded_eq r c hr hc]
    exact RoundedRowDescriptor.divisor_le r c
  have hcwidth := GrowingCounterData.canonical_width (RecursiveChildQuotientsConstant.bits c)
    (RecursiveChildQuotientsConstant.bits_canonical c)
  have hpwidth := GrowingCounterData.canonical_width (CompactRowPaddingRound.bits r c)
    (CompactRowPaddingRound.bits_canonical r c)
  rw [RecursiveChildQuotientsConstant.bits_value] at hcwidth
  rw [CompactRowPaddingRound.bits_value r c hr hc] at hpwidth
  have hcLog := Nat.log2_le_self c
  have hpLog := Nat.log2_le_self (paddedRows r c)
  have hPV := Nat.le_mul_of_pos_right (paddedRows r c) hl
  nlinarith

/-- The paid runtime is linear in padded literal record volume. -/
theorem runs_linear (c : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (rs ls : List Bool) (r l : ℕ) (x : Fin (1*r*l) → Bool)
    (hr : Counter.value rs = r) (hl : Counter.value ls = l)
    (cr : GrowingCounterData.Canonical rs) (cl : GrowingCounterData.Canonical ls)
    (hR : 0 < r) (hL : 0 < l) (hc : 0 < c) :
    HoareTime (program (a := a) c)
      (fun w => w = bank (putWord (RowPaddingConstructedAlphabet.mapTape source) p
        (List.ofFn (fun z => bitSymbol (x z)))) (RowPaddingConstructedAlphabet.mapTape dest) p q rs ls none none)
      (fun w => w = bank (RowPaddingConstructedAlphabet.erased
        (putWord (RowPaddingConstructedAlphabet.mapTape source) p (List.ofFn (fun z => bitSymbol (x z)))) p (1*r*l))
        (putWord (RowPaddingConstructedAlphabet.mapTape dest) q
          (List.ofFn (RecursiveRowPadding.pad (paddedRows r c) (bitSymbol false) (fun z => bitSymbol (x z)))))
        p q rs ls none none) (4600*(paddedRows r c*l)) :=
  (runs (a := a) c source dest p q rs ls r l x hr hl cr cl hR hL hc).consequence
    (fun _ h => h) (fun _ h => h) (budget_linear r c l hR hc hL)

/-- In the usual reservation range, rounding costs less than twice the
original complete-row volume. -/
theorem volume_le_twice (r c l : ℕ) (hc : 0 < c) (hcr : c ≤ r) :
    paddedRows r c*l ≤ 2*(r*l) := by
  have h := (IntegerMultBounds.Compact.Layout.padding_bounds r c hc hcr).2.2.1
  nlinarith [Nat.mul_le_mul_right l h]

/-- A fixed role count gives a uniform bound against original record volume,
even when there are fewer original rows than physical roles. -/
theorem volume_le_original (r c l : ℕ) (hr : 0 < r) (hc : 0 < c) :
    paddedRows r c*l ≤ (c+1)*(r*l) := by
  have h := (CompactRowPaddingRound.padded_bounds r c hc).2.1
  have hcr := Nat.le_mul_of_pos_right c hr
  have hp : paddedRows r c ≤ (c+1)*r := by nlinarith
  nlinarith [Nat.mul_le_mul_right l hp]

/-- Complete retained records crop back to the exact original binary array. -/
theorem crop_pad (r c l : ℕ) (hc : 0 < c) (x : Fin (1*r*l) → Bool) :
    RecursiveRowPadding.crop (CompactRowPaddingRound.padded_bounds r c hc).1
      (RecursiveRowPadding.pad (paddedRows r c) (bitSymbol (a := a) false)
        (fun z => bitSymbol (x z))) = fun z => bitSymbol (x z) :=
  RecursiveRowPadding.crop_pad _ _ _


end
end IntegerMultBounds.Machine.CompactRowPaddingRun
