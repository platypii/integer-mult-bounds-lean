import IntegerMultBounds.Machine.RationalOffsetPrepare
import IntegerMultBounds.Machine.TranslationExecutionReuse

/-! A concrete rational-controlled translation of one physical fiber. Fixed
rational arithmetic reads a marked radix prefix coordinate, converts its residue
to canonical binary, installs the translation descriptor, then executes actual
metadata synthesis, payload rotation and cleanup. Radix workspace is framed
outside the alphabet-lifted translation machine. -/
namespace IntegerMultBounds.Machine.RationalTranslationExecution

variable {radix : ℕ}

/-- Twelve encoded translation tapes and four actual radix preparation tapes. -/
def bank (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs supplied offset : List Bool)
    (xs : List (Fin radix)) : Tapes 16 radix :=
  (Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix))
    (TranslationExecutionReuse.bank source dest p q bs qs offset)).append
    (RadixRationalBinaryReuse.input supplied xs)

private def prepPlacement : Fin (5+11) ≃ Fin 16 where
  toFun := ![12,13,14,15,8,5,6,7,4,9,10,11,0,1,2,3]
  invFun := ![12,13,14,15,8,5,6,7,4,9,10,11,0,1,2,3]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private theorem active_bank (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs supplied offset : List Bool)
    (xs : List (Fin radix)) :
    Placement.active prepPlacement (bank source dest p q bs qs supplied offset xs) =
      RationalOffsetPrepare.bank supplied offset xs := by
  unfold Placement.active prepPlacement bank RationalOffsetPrepare.bank RationalOffsetPrepare.descriptor
    Tapes.append Alphabet.mapTapes
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem extra_bank (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs supplied offset new : List Bool)
    (xs : List (Fin radix)) :
    Placement.extra prepPlacement (bank source dest p q bs qs supplied offset xs) =
      Placement.extra prepPlacement (bank source dest p q bs qs new new xs) := by
  unfold Placement.extra prepPlacement bank Tapes.append Alphabet.mapTapes
    TranslationExecutionReuse.bank TranslationPreparedExecution.bank TranslationDescriptors.bank
  congr 1
  funext i
  fin_cases i <;> rfl

variable [Fact radix.Prime]

/-- Preparation shares the physical offset descriptor with the rotation machine. -/
def prepProgram (r : ℚ) : Program 16 ((4+((2+(2*r.num.natAbs+r.den+1)+2)+18+6))+7) radix :=
  Placement.placed (RationalOffsetPrepare.program r) prepPlacement

theorem prepare_hoare (r : ℚ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs supplied offset : List Bool) (xs : List (Fin radix)) (B : ℕ) (hB : 0 < B)
    (cs : GrowingCounterData.Canonical supplied) (co : GrowingCounterData.Canonical offset)
    (hs : Counter.value supplied < radix^xs.length) (ho : Counter.value offset < radix^xs.length) :
    HoareTime (prepProgram r)
      (fun v => v = bank source dest p q bs qs supplied offset xs)
      (fun v => v = bank source dest p q bs qs (RationalOffsetPrepare.result r xs) (RationalOffsetPrepare.result r xs) xs)
      (67*(radix^xs.length*B)) := by
  have hh := Placement.hoare_at (RationalOffsetPrepare.prepare_hoare_fiber r supplied offset xs B hB cs co hs ho)
    prepPlacement (bank source dest p q bs qs supplied offset xs) (active_bank source dest p q bs qs supplied offset xs)
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  rw [Placement.replace,extra_bank,← active_bank source dest p q bs qs (RationalOffsetPrepare.result r xs) (RationalOffsetPrepare.result r xs) xs]
  exact Placement.view _ _

/-- Lift only the twelve active four-symbol tapes, preserving arbitrary radix digits. -/
def translationProgram : Program 16 217 radix :=
  extend (Alphabet.program (RadixToBinary.binaryEncoding (q := radix)) TranslationExecutionReuse.program) 4

omit [Fact radix.Prime] in
private theorem translation_hoare (Q a B : ℕ) (ha : a ≤ Q) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (hlen : blocks.length = Q) (hwidth : BlockRotationData.Uniform B blocks)
    (bs qs supplied offset : List Bool) (xs : List (Fin radix))
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (ha' : Counter.value offset = a)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (ca : GrowingCounterData.Canonical offset) :
    HoareTime translationProgram
      (fun v => v = bank (putWord source p blocks.flatten) dest p q bs qs supplied offset xs)
      (fun v => v = bank (putWord source p blocks.flatten)
        (putWord dest q (BlockRotationData.rotate a blocks).flatten) (p+Q*B) (q+Q*B) bs qs supplied offset xs)
      (207*(Q*B)+241) := by
  have hh := Alphabet.map_hoare (RadixToBinary.binaryEncoding (q := radix))
    (TranslationExecutionReuse.translate_hoare Q a B ha hB source dest p q blocks hlen hwidth bs qs offset hb hq ha' cb cq ca)
  have hh' : HoareTime (Alphabet.program (RadixToBinary.binaryEncoding (q := radix)) TranslationExecutionReuse.program)
      (fun v => v = Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix))
        (TranslationExecutionReuse.input source dest p q blocks bs qs offset))
      (fun v => v = Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix))
        (TranslationExecutionReuse.output Q a B source dest p q blocks bs qs offset))
      (207*(Q*B)+241) := by
    apply hh.consequence _ _ le_rfl
    · intro v hv; exact ⟨_,rfl,hv⟩
    · rintro v ⟨w,rfl,hv⟩; exact hv
  have he := hh'.extend (RadixRationalBinaryReuse.input supplied xs)
  apply he.consequence _ _ le_rfl
  · intro v hv; exact ⟨_,rfl,hv⟩
  · rintro v ⟨w,rfl,hv⟩; exact hv

/-- Fixed machine: concrete rational offset preparation then literal translation. -/
def program (r : ℚ) : Program 16 (((4+((2+(2*r.num.natAbs+r.den+1)+2)+18+6))+7)+217) radix :=
  seq (prepProgram r) translationProgram

def input (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs supplied offset : List Bool) (xs : List (Fin radix)) : Tapes 16 radix :=
  bank (putWord source p blocks.flatten) dest p q bs qs supplied offset xs

def output (r : ℚ) (B : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs : List Bool) (xs : List (Fin radix)) : Tapes 16 radix :=
  bank (putWord source p blocks.flatten)
    (putWord dest q (BlockRotationData.rotate (Counter.value (RationalOffsetPrepare.result r xs)) blocks).flatten)
    (p+radix^xs.length*B) (q+radix^xs.length*B) bs qs
    (RationalOffsetPrepare.result r xs) (RationalOffsetPrepare.result r xs) xs

/-- End-to-end one-fiber execution from only input counts and a physical prefix
coordinate. Old binary offsets are erased; generated split descriptors never
appear in the input or survive in the recurring output metadata. -/
theorem translate_hoare (r : ℚ) (B : ℕ) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs supplied offset : List Bool) (xs : List (Fin radix))
    (hlen : blocks.length = radix^xs.length) (hwidth : BlockRotationData.Uniform B blocks)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^xs.length)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cs : GrowingCounterData.Canonical supplied) (co : GrowingCounterData.Canonical offset)
    (hs : Counter.value supplied < radix^xs.length) (ho : Counter.value offset < radix^xs.length) :
    HoareTime (program r) (fun v => v = input source dest p q blocks bs qs supplied offset xs)
      (fun v => v = output r B source dest p q blocks bs qs xs) (274*(radix^xs.length*B)+242) := by
  have hp := prepare_hoare r (putWord source p blocks.flatten) dest p q bs qs supplied offset xs B hB cs co hs ho
  have ht := translation_hoare (radix^xs.length) (Counter.value (RationalOffsetPrepare.result r xs)) B
    (RationalOffsetPrepare.result_lt r xs).le hB source dest p q blocks hlen hwidth
    bs qs (RationalOffsetPrepare.result r xs) (RationalOffsetPrepare.result r xs) xs hb hq rfl cb cq
    (RationalOffsetPrepare.result_canonical r xs)
  exact (hp.seq ht).consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- Full physical destination tape, with encoded payload and unchanged background. -/
theorem output_destination (r : ℚ) (B : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (blocks : List (List (Fin 4))) (bs qs : List Bool) (xs : List (Fin radix)) :
    (output r B source dest p q blocks bs qs xs).tape 11 = fun z =>
      (RadixToBinary.binaryEncoding (q := radix)).encode
        (putWord dest q (BlockRotationData.rotate (Counter.value (RationalOffsetPrepare.result r xs)) blocks).flatten z) := rfl

/-- The marked prefix-control word is not changed by preparation or translation. -/
theorem output_control (r : ℚ) (B : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (blocks : List (List (Fin 4))) (bs qs : List Bool) (xs : List (Fin radix)) :
    (output r B source dest p q blocks bs qs xs).tape 15 = RadixRationalBinary.source xs ∧
    (output r B source dest p q blocks bs qs xs).head 15 = 1 := ⟨rfl,rfl⟩

/-- The additive control cost is absorbed by every nonempty physical fiber. -/
theorem translate_hoare_fiber (r : ℚ) (B : ℕ) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs supplied offset : List Bool) (xs : List (Fin radix))
    (hlen : blocks.length = radix^xs.length) (hwidth : BlockRotationData.Uniform B blocks)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^xs.length)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cs : GrowingCounterData.Canonical supplied) (co : GrowingCounterData.Canonical offset)
    (hs : Counter.value supplied < radix^xs.length) (ho : Counter.value offset < radix^xs.length) :
    HoareTime (program r) (fun v => v = input source dest p q blocks bs qs supplied offset xs)
      (fun v => v = output r B source dest p q blocks bs qs xs) (516*(radix^xs.length*B)) := by
  apply (translate_hoare r B hB source dest p q blocks bs qs supplied offset xs hlen hwidth hb hq cb cq cs co hs ho).consequence
    (fun _ h => h) (fun _ h => h) _
  have hp : 1 ≤ radix^xs.length := Nat.one_le_pow _ _ (by have := (Fact.out : radix.Prime).two_le; omega)
  have hm : 1 ≤ radix^xs.length*B := by nlinarith
  omega

/-- The computed physical offset is the manuscript's rational coefficient action. -/
theorem offset_value (r : ℚ) (hden : r.den < radix) (xs : List (Fin radix)) :
    (Counter.value (RationalOffsetPrepare.result r xs) : ZMod (radix^xs.length)) =
      Swap.Modular.ratMod (radix^xs.length) r * (RadixDigits.value xs : ZMod (radix^xs.length)) :=
  RationalOffsetPrepare.result_value r hden xs

end IntegerMultBounds.Machine.RationalTranslationExecution
