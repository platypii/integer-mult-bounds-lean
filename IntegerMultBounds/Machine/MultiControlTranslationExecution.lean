import IntegerMultBounds.Machine.RadixLinearCombinationReuse
import IntegerMultBounds.Machine.TranslationExecutionReuse

/-! Recurring translation controlled by an actual bounded expression over a
shared physical radix bank. The computed binary tape is statically shared with
the translation offset input. The original translation offset slot is a blank
spectator; no fresh leaf copies or independently supplied offsets are assumed. -/
namespace IntegerMultBounds.Machine.MultiControlTranslationExecution

open RadixLinearCombinationRefresh (Expr controls leaves)
open SharedPlacementAlphabet (setTape sharedPlacement)
variable {c radix : ℕ}

abbrev ArithmeticTapes (e : Expr c) := RadixLinearCombinationShared.TapeCount e
abbrev TapeCount (e : Expr c) := ArithmeticTapes e+12

/-- The compiler's physical binary output, after its finite shared control bank. -/
def offsetSlot (e : Expr c) : Fin (ArithmeticTapes e) :=
  Fin.natAdd c (Fin.castAdd (RadixLinearCombination.AuxTapes e.erase) (0 : Fin 3))

private def liftedBank (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs offset : List Bool) : Tapes 12 radix :=
  Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix))
    (TranslationExecutionReuse.bank source dest p q bs qs offset)

/-- Twelve payload/translation tapes, with slot8 genuinely blank at origin.
The actual offset is read from the separately shared arithmetic output tape. -/
def translationBank (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs : List Bool) : Tapes 12 radix :=
  setTape (liftedBank source dest p q bs qs []) 8 (fun _ => blank) 0

private theorem no_offset (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs offset : List Bool) :
    setTape (liftedBank (radix := radix) source dest p q bs qs offset) 8 (fun _ => blank) 0 =
      translationBank source dest p q bs qs := by
  unfold translationBank setTape liftedBank Alphabet.mapTapes
  congr 1
  funext i
  fin_cases i <;> simp <;> rfl

/-- Current controls, old internal copies and binary output, then the reusable
translation workspace and payload. Every represented tape is an actual tape. -/
def bank (e : Expr c) (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs supplied : List Bool)
    (xs old : ℕ → List (Fin radix)) : Tapes (TapeCount e) radix :=
  (RadixLinearCombinationReuse.state e xs old supplied).append (translationBank source dest p q bs qs)

variable [Fact radix.Prime]

def bits (e : Expr c) (xs : ℕ → List (Fin radix)) : List Bool :=
  RadixLinearCombinationBinary.bits e.erase xs

def offset (e : Expr c) (xs : ℕ → List (Fin radix)) : ℕ := Counter.value (bits e xs)

/-- The translation machine sees only the twelve encoded four-symbol tapes.
All arbitrary radix symbols stay in the literal stationary frame. -/
def translationProgram (e : Expr c) : Program (TapeCount e) 217 radix :=
  Placement.placed (Alphabet.program (RadixToBinary.binaryEncoding (q := radix)) TranslationExecutionReuse.program)
    (sharedPlacement (offsetSlot e) (8 : Fin 12))

private theorem shared_output (e : Expr c) (xs : ℕ → List (Fin radix)) :
    (RadixLinearCombinationShared.output e xs).tape (offsetSlot e) =
      (fun z => (RadixToBinary.binaryEncoding (q := radix)).encode (CountedCopyReuse.binary (bits e xs) z)) ∧
    (RadixLinearCombinationShared.output e xs).head (offsetSlot e) = 1 := by
  exact ⟨(RadixLinearCombinationShared.output_binary e xs).2,(RadixLinearCombinationShared.output_binary e xs).1⟩

/-- Literal fiber translation using the actual compiler output as its input
without copying, replacing, or assuming a second offset descriptor. -/
theorem translation_hoare (e : Expr c) (xs : ℕ → List (Fin radix)) (Q B : ℕ)
    (ha : offset e xs ≤ Q) (hB : 0 < B) (source dest : ℤ → Fin 4) (p q : ℤ)
    (blocks : List (List (Fin 4))) (hlen : blocks.length = Q) (hwidth : BlockRotationData.Uniform B blocks)
    (bs qs : List Bool) (hb : Counter.value bs = B) (hq : Counter.value qs = Q)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs) :
    HoareTime (translationProgram e)
      (fun v => v = bank e (putWord source p blocks.flatten) dest p q bs qs (bits e xs) xs xs)
      (fun v => v = bank e (putWord source p blocks.flatten)
        (putWord dest q (BlockRotationData.rotate (offset e xs) blocks).flatten)
        (p+Q*B) (q+Q*B) bs qs (bits e xs) xs xs)
      (207*(Q*B)+241) := by
  let before := TranslationExecutionReuse.input source dest p q blocks bs qs (bits e xs)
  let after := TranslationExecutionReuse.output Q (offset e xs) B source dest p q blocks bs qs (bits e xs)
  have hm := Alphabet.map_hoare (RadixToBinary.binaryEncoding (q := radix))
    (TranslationExecutionReuse.translate_hoare Q (offset e xs) B ha hB source dest p q blocks hlen hwidth
      bs qs (bits e xs) hb hq rfl cb cq (RadixLinearCombinationBinary.bits_canonical e.erase xs))
  have h : HoareTime (Alphabet.program (RadixToBinary.binaryEncoding (q := radix)) TranslationExecutionReuse.program)
      (fun v => v = Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix)) before)
      (fun v => v = Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix)) after)
      (207*(Q*B)+241) := by
    apply hm.consequence _ _ le_rfl
    · rintro v rfl; exact ⟨_,rfl,rfl⟩
    · rintro v ⟨w,rfl,rfl⟩; rfl
  have hf : (RadixLinearCombinationShared.output e xs).tape (offsetSlot e) =
      (Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix)) before).tape 8 := (shared_output e xs).1
  have hp : (RadixLinearCombinationShared.output e xs).head (offsetSlot e) =
      (Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix)) before).head 8 := (shared_output e xs).2
  have hs := SharedPlacementAlphabet.shared_hoare h (RadixLinearCombinationShared.output e xs)
    (offsetSlot e) (8 : Fin 12) (fun _ => blank) 0 hf hp
  have hr : setTape (RadixLinearCombinationShared.output e xs) (offsetSlot e)
      ((Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix)) after).tape 8)
      ((Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix)) after).head 8) =
        RadixLinearCombinationShared.output e xs := by
    change setTape (RadixLinearCombinationShared.output e xs) (offsetSlot e)
      (fun z => (RadixToBinary.binaryEncoding (q := radix)).encode (CountedCopyReuse.binary (bits e xs) z)) 1 = _
    rw [← (shared_output e xs).1,← (shared_output e xs).2]
    exact SharedPlacementAlphabet.setTape_self _ _
  rw [hr] at hs
  change HoareTime _
    (fun v => v = (RadixLinearCombinationShared.output e xs).append
      (setTape (liftedBank (putWord source p blocks.flatten) dest p q bs qs (bits e xs)) 8 (fun _ => blank) 0))
    (fun v => v = (RadixLinearCombinationShared.output e xs).append
      (setTape (liftedBank (putWord source p blocks.flatten)
        (putWord dest q (BlockRotationData.rotate (offset e xs) blocks).flatten)
        (p+Q*B) (q+Q*B) bs qs (bits e xs)) 8 (fun _ => blank) 0)) _ at hs
  rw [no_offset,no_offset] at hs
  exact hs

abbrev States (e : Expr c) := RadixLinearCombinationReuse.States e+217

/-- Fixed bounded-expression evaluator, followed by the actual shared-offset rotation. -/
def program (e : Expr c) : Program (TapeCount e) (States e) radix :=
  seq (extend (RadixLinearCombinationReuse.program e) 12) (translationProgram e)

def input (e : Expr c) (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs supplied : List Bool) (xs old : ℕ → List (Fin radix)) : Tapes (TapeCount e) radix :=
  bank e (putWord source p blocks.flatten) dest p q bs qs supplied xs old

def output (e : Expr c) (b B : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (blocks : List (List (Fin 4))) (bs qs : List Bool) (xs : ℕ → List (Fin radix)) : Tapes (TapeCount e) radix :=
  bank e (putWord source p blocks.flatten)
    (putWord dest q (BlockRotationData.rotate (offset e xs) blocks).flatten)
    (p+radix^b*B) (q+radix^b*B) bs qs (bits e xs) xs xs

/-- No fresh leaves or precomputed offsets: old binary output and all stale
leaf sources are erased/refreshed before using the new physically computed offset. -/
theorem translate_hoare (e : Expr c) (b B : ℕ) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs supplied : List Bool) (xs old : ℕ → List (Fin radix))
    (hw : ∀ i, (xs i).length = b) (ho : ∀ i : Fin c, (old i.val).length ≤ b)
    (hs : supplied.length ≤ radix^b) (hlen : blocks.length = radix^b) (hwidth : BlockRotationData.Uniform B blocks)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^b)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs) :
    HoareTime (program e) (fun v => v = input e source dest p q blocks bs qs supplied xs old)
      (fun v => v = output e b B source dest p q blocks bs qs xs)
      ((13*leaves e+RadixLinearCombination.linearConstant e.erase+254)*(radix^b*B)+242) := by
  have hp := FamilyPlacementAlphabet.extend_hoare
    (RadixLinearCombinationReuse.compute_hoare_linear e xs old supplied b hw ho hs)
    (translationBank (putWord source p blocks.flatten) dest p q bs qs)
  have ht := translation_hoare e xs (radix^b) B
    (RadixLinearCombinationBinary.bits_lt e.erase xs b hw).le hB source dest p q blocks hlen hwidth bs qs hb hq cb cq
  apply (hp.seq ht).consequence (fun _ h => h) (fun _ h => h)
  have hm : radix^b ≤ radix^b*B := Nat.le_mul_of_pos_right _ hB
  have hmul := Nat.mul_le_mul_left (13*leaves e+RadixLinearCombination.linearConstant e.erase+47) hm
  nlinarith

/-- All overhead is absorbed in the nonempty physical fiber volume. -/
theorem translate_hoare_fiber (e : Expr c) (b B : ℕ) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs supplied : List Bool) (xs old : ℕ → List (Fin radix))
    (hw : ∀ i, (xs i).length = b) (ho : ∀ i : Fin c, (old i.val).length ≤ b)
    (hs : supplied.length ≤ radix^b) (hlen : blocks.length = radix^b) (hwidth : BlockRotationData.Uniform B blocks)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^b)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs) :
    HoareTime (program e) (fun v => v = input e source dest p q blocks bs qs supplied xs old)
      (fun v => v = output e b B source dest p q blocks bs qs xs)
      ((13*leaves e+RadixLinearCombination.linearConstant e.erase+496)*(radix^b*B)) := by
  apply (translate_hoare e b B hB source dest p q blocks bs qs supplied xs old hw ho hs hlen hwidth hb hq cb cq).consequence
    (fun _ h => h) (fun _ h => h)
  have hqpos : 1 ≤ radix^b := Nat.one_le_pow _ _ (by have := (Fact.out : radix.Prime).two_le; omega)
  have hv : 1 ≤ radix^b*B := by nlinarith
  nlinarith

/-- Recurring form: current controls may have advanced, while the actual old
compiler output and leaf bank remain as produced by the previous call. -/
theorem translate_after_advance (e : Expr c) (b B : ℕ) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs : List Bool) (xs old : ℕ → List (Fin radix))
    (hw : ∀ i, (xs i).length = b) (ho : ∀ i, (old i).length = b)
    (hlen : blocks.length = radix^b) (hwidth : BlockRotationData.Uniform B blocks)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^b)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs) :
    HoareTime (program e) (fun v => v = input e source dest p q blocks bs qs (bits e old) xs old)
      (fun v => v = output e b B source dest p q blocks bs qs xs)
      ((13*leaves e+RadixLinearCombination.linearConstant e.erase+496)*(radix^b*B)) :=
  translate_hoare_fiber e b B hB source dest p q blocks bs qs (bits e old) xs old hw (fun i => (ho i.val).le)
    (RadixLinearCombinationReuse.bits_length_le e old b ho) hlen hwidth hb hq cb cq

/-- All data parameters are finite physical control banks. The explicit seed
only defines the mathematical lookup outside that bank; the machine cannot use
an out-of-bounds reference because expression leaves contain `Fin c`. -/
theorem translate_finite_after_advance (e : Expr c) (seed : Fin c) (b B : ℕ) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs : List Bool) (xs old : Fin c → List (Fin radix))
    (hw : ∀ i, (xs i).length = b) (ho : ∀ i, (old i).length = b)
    (hlen : blocks.length = radix^b) (hwidth : BlockRotationData.Uniform B blocks)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^b)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs) :
    HoareTime (program e)
      (fun v => v = input e source dest p q blocks bs qs (bits e (RadixLinearCombinationShared.read seed old))
        (RadixLinearCombinationShared.read seed xs) (RadixLinearCombinationShared.read seed old))
      (fun v => v = output e b B source dest p q blocks bs qs (RadixLinearCombinationShared.read seed xs))
      ((13*leaves e+RadixLinearCombination.linearConstant e.erase+496)*(radix^b*B)) :=
  translate_after_advance e b B hB source dest p q blocks bs qs _ _
    (RadixLinearCombinationShared.read_width seed xs b hw) (RadixLinearCombinationShared.read_width seed old b ho)
    hlen hwidth hb hq cb cq

/-- The physically used translation amount is the actual fixed rational expression. -/
theorem offset_value (e : Expr c) (he : RadixLinearCombination.Valid (q := radix) e.erase)
    (xs : ℕ → List (Fin radix)) (b : ℕ) (hw : ∀ i, (xs i).length = b) :
    (offset e xs : ZMod (radix^b)) = RadixLinearCombination.valueMod b e.erase xs :=
  RadixLinearCombinationBinary.bits_value e.erase he xs b hw

/-- Exact full destination tape, including the unchanged encoded background. -/
theorem output_destination (e : Expr c) (b B : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (blocks : List (List (Fin 4))) (bs qs : List Bool) (xs : ℕ → List (Fin radix)) :
    (output e b B source dest p q blocks bs qs xs).tape (Fin.natAdd (ArithmeticTapes e) (11 : Fin 12)) =
      fun z => (RadixToBinary.binaryEncoding (q := radix)).encode
        (putWord dest q (BlockRotationData.rotate (offset e xs) blocks).flatten z) := by
  simp only [output,bank,Tapes.append,Fin.addCases_right]
  rfl

/-- Whole shared radix controls are preserved by computation and translation. -/
theorem output_controls (e : Expr c) (b B : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (blocks : List (List (Fin 4))) (bs qs : List Bool) (xs : ℕ → List (Fin radix)) (i : Fin c) :
    let slot := Fin.castAdd 12 (Fin.castAdd (RadixLinearCombinationBinary.TapeCount e.erase) i)
    (output e b B source dest p q blocks bs qs xs).head slot = 1 ∧
    (output e b B source dest p q blocks bs qs xs).tape slot = MarkedRadixRefresh.source (xs i.val) := by
  simp [output,bank,RadixLinearCombinationReuse.state,Tapes.append,controls]

/-- Both physical payload heads advance exactly one whole fiber. -/
theorem output_heads (e : Expr c) (b B : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (blocks : List (List (Fin 4))) (bs qs : List Bool) (xs : ℕ → List (Fin radix)) :
    (output e b B source dest p q blocks bs qs xs).head (Fin.natAdd (ArithmeticTapes e) (10 : Fin 12)) = p+radix^b*B ∧
    (output e b B source dest p q blocks bs qs xs).head (Fin.natAdd (ArithmeticTapes e) (11 : Fin 12)) = q+radix^b*B := by
  simp only [output,bank,Tapes.append,Fin.addCases_right]
  exact ⟨rfl,rfl⟩

/-- The unused duplicate offset slot stays genuinely blank, with its head at zero. -/
theorem output_offset_spare (e : Expr c) (b B : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (blocks : List (List (Fin 4))) (bs qs : List Bool) (xs : ℕ → List (Fin radix)) :
    (output e b B source dest p q blocks bs qs xs).head (Fin.natAdd (ArithmeticTapes e) (8 : Fin 12)) = 0 ∧
    (output e b B source dest p q blocks bs qs xs).tape (Fin.natAdd (ArithmeticTapes e) (8 : Fin 12)) = (fun _ => blank) := by
  simp [output,bank,Tapes.append,translationBank,setTape]

end IntegerMultBounds.Machine.MultiControlTranslationExecution
