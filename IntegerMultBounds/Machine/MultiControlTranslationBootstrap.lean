import IntegerMultBounds.Machine.MultiControlTranslationExecution
import IntegerMultBounds.Machine.RadixLinearCombinationBootstrap

/-! First actual multi-control translation from blank arithmetic scratch and
unprepared writable translation metadata. The computed binary tape is physically
shared with the initial translation program. Canonical B/Q inputs and marked
shared radix controls are explicit premises; no old result or leaf copy exists. -/
namespace IntegerMultBounds.Machine.MultiControlTranslationBootstrap

open RadixLinearCombinationRefresh (Expr leaves)
open SharedPlacementAlphabet (setTape sharedPlacement)
open MultiControlTranslationExecution (ArithmeticTapes TapeCount offsetSlot bits offset)
variable {c radix : ℕ}

private def liftedInitial (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs as : List Bool) : Tapes 12 radix :=
  Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix))
    ((TranslationDescriptors.initial bs qs as).append (TranslationPreparedExecution.payload source dest p q))

/-- Writable metadata is blank, with only B/Q descriptors supplied at head1.
The inherited blank spare has head1; the unused offset slot is blank/head0. -/
def preparedTranslationInitial (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs : List Bool) : Tapes 12 radix :=
  setTape (liftedInitial source dest p q bs qs []) 8 (fun _ => blank) 0

private theorem no_initial_offset (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs as : List Bool) :
    setTape (liftedInitial (radix := radix) source dest p q bs qs as) 8 (fun _ => blank) 0 =
      preparedTranslationInitial source dest p q bs qs := by
  unfold preparedTranslationInitial liftedInitial setTape Alphabet.mapTapes
  congr 1
  funext i
  fin_cases i <;> simp <;> rfl

private theorem no_final_offset (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs as : List Bool) :
    setTape (Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix))
      (TranslationExecutionReuse.bank source dest p q bs qs as)) 8 (fun _ => blank) 0 =
      MultiControlTranslationExecution.translationBank source dest p q bs qs := by
  change setTape (Alphabet.mapTapes _ _) 8 (fun _ => blank) 0 =
    setTape (Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix))
      (TranslationExecutionReuse.bank source dest p q bs qs [])) 8 (fun _ => blank) 0
  unfold setTape Alphabet.mapTapes
  congr 1
  funext i
  fin_cases i <;> simp <;> rfl

/-- The arithmetic suffix contains no supplied sentinels, stale sources, binary
result, or conversion workspace: it is entirely blank with every head zero. -/
def preparedBank (e : Expr c) (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs : List Bool)
    (xs : ℕ → List (Fin radix)) : Tapes (TapeCount e) radix :=
  (RadixLinearCombinationBootstrap.input e xs).append (preparedTranslationInitial source dest p q bs qs)

def preparedInput (e : Expr c) (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs : List Bool) (xs : ℕ → List (Fin radix)) : Tapes (TapeCount e) radix :=
  preparedBank e (putWord source p blocks.flatten) dest p q bs qs xs

variable [Fact radix.Prime]

/-- All translation marker installation, descriptor synthesis, payload rotation
and metadata cleanup are performed by the existing initial machine. -/
def translationProgram (e : Expr c) : Program (TapeCount e) 219 radix :=
  Placement.placed (Alphabet.program (RadixToBinary.binaryEncoding (q := radix)) TranslationExecutionReuse.initialProgram)
    (sharedPlacement (offsetSlot e) (8 : Fin 12))

private theorem translation_hoare (e : Expr c) (xs : ℕ → List (Fin radix)) (Q B : ℕ)
    (ha : offset e xs ≤ Q) (hB : 0 < B) (source dest : ℤ → Fin 4) (p q : ℤ)
    (blocks : List (List (Fin 4))) (hlen : blocks.length = Q) (hwidth : BlockRotationData.Uniform B blocks)
    (bs qs : List Bool) (hb : Counter.value bs = B) (hq : Counter.value qs = Q)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs) :
    HoareTime (translationProgram e)
      (fun v => v = (RadixLinearCombinationShared.output e xs).append
        (preparedTranslationInitial (putWord source p blocks.flatten) dest p q bs qs))
      (fun v => v = MultiControlTranslationExecution.bank e (putWord source p blocks.flatten)
        (putWord dest q (BlockRotationData.rotate (offset e xs) blocks).flatten)
        (p+Q*B) (q+Q*B) bs qs (bits e xs) xs xs)
      (207*(Q*B)+243) := by
  let before := TranslationPreparedExecution.input source dest p q blocks bs qs (bits e xs)
  let after := TranslationExecutionReuse.output Q (offset e xs) B source dest p q blocks bs qs (bits e xs)
  have hm := Alphabet.map_hoare (RadixToBinary.binaryEncoding (q := radix))
    (TranslationExecutionReuse.initial_translate_hoare Q (offset e xs) B ha hB source dest p q blocks hlen hwidth
      bs qs (bits e xs) hb hq rfl cb cq (RadixLinearCombinationBinary.bits_canonical e.erase xs))
  have h : HoareTime (Alphabet.program (RadixToBinary.binaryEncoding (q := radix)) TranslationExecutionReuse.initialProgram)
      (fun v => v = Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix)) before)
      (fun v => v = Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix)) after)
      (207*(Q*B)+243) := by
    apply hm.consequence _ _ le_rfl
    · rintro v rfl; exact ⟨_,rfl,rfl⟩
    · rintro v ⟨w,rfl,rfl⟩; rfl
  have hf : (RadixLinearCombinationShared.output e xs).tape (offsetSlot e) =
      (Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix)) before).tape 8 :=
    (RadixLinearCombinationShared.output_binary e xs).2
  have hp : (RadixLinearCombinationShared.output e xs).head (offsetSlot e) =
      (Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix)) before).head 8 :=
    (RadixLinearCombinationShared.output_binary e xs).1
  have hs := SharedPlacementAlphabet.shared_hoare h (RadixLinearCombinationShared.output e xs)
    (offsetSlot e) (8 : Fin 12) (fun _ => blank) 0 hf hp
  have hr : setTape (RadixLinearCombinationShared.output e xs) (offsetSlot e)
      ((Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix)) after).tape 8)
      ((Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix)) after).head 8) =
        RadixLinearCombinationShared.output e xs := by
    change setTape (RadixLinearCombinationShared.output e xs) (offsetSlot e)
      (fun z => (RadixToBinary.binaryEncoding (q := radix)).encode (CountedCopyReuse.binary (bits e xs) z)) 1 = _
    dsimp only [bits,offsetSlot]
    rw [← (RadixLinearCombinationShared.output_binary e xs).2,← (RadixLinearCombinationShared.output_binary e xs).1]
    exact SharedPlacementAlphabet.setTape_self _ _
  rw [hr] at hs
  change HoareTime _
    (fun v => v = (RadixLinearCombinationShared.output e xs).append
      (setTape (liftedInitial (putWord source p blocks.flatten) dest p q bs qs (bits e xs)) 8 (fun _ => blank) 0))
    (fun v => v = (RadixLinearCombinationShared.output e xs).append
      (setTape (Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix))
        (TranslationExecutionReuse.bank (putWord source p blocks.flatten)
          (putWord dest q (BlockRotationData.rotate (offset e xs) blocks).flatten)
          (p+Q*B) (q+Q*B) bs qs (bits e xs))) 8 (fun _ => blank) 0)) _ at hs
  rw [no_initial_offset,no_final_offset] at hs
  exact hs

abbrev PreparedStates (e : Expr c) := RadixLinearCombinationBootstrap.States e+219

/-- No runtime width or supplied offset is embedded in this finite control. -/
def preparedProgram (e : Expr c) : Program (TapeCount e) (PreparedStates e) radix :=
  seq (extend (RadixLinearCombinationBootstrap.program e) 12) (translationProgram e)

/-- Complete first fiber: create leaves, read actual shared controls, compute
and share the canonical offset, synthesize translation metadata and rotate. -/
theorem prepared_translate_hoare (e : Expr c) (b B : ℕ) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs : List Bool) (xs : ℕ → List (Fin radix)) (hw : ∀ i, (xs i).length = b)
    (hlen : blocks.length = radix^b) (hwidth : BlockRotationData.Uniform B blocks)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^b)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs) :
    HoareTime (preparedProgram e) (fun v => v = preparedInput e source dest p q blocks bs qs xs)
      (fun v => v = MultiControlTranslationExecution.output e b B source dest p q blocks bs qs xs)
      ((15*leaves e+RadixLinearCombination.linearConstant e.erase+247)*(radix^b*B)+244) := by
  have hp := FamilyPlacementAlphabet.extend_hoare (RadixLinearCombinationBootstrap.compute_hoare e xs b hw)
    (preparedTranslationInitial (putWord source p blocks.flatten) dest p q bs qs)
  have ht := translation_hoare e xs (radix^b) B
    (RadixLinearCombinationBinary.bits_lt e.erase xs b hw).le hB source dest p q blocks hlen hwidth bs qs hb hq cb cq
  apply (hp.seq ht).consequence (fun _ h => h) (fun _ h => h)
  have hm : radix^b ≤ radix^b*B := Nat.le_mul_of_pos_right _ hB
  have hmul := Nat.mul_le_mul_left (15*leaves e+RadixLinearCombination.linearConstant e.erase+40) hm
  nlinarith

/-- Bootstrap is linear in physical fiber size with a coefficient fixed by the
compiled expression. No stale-leaf or stale-result data appears in its input. -/
theorem prepared_translate_hoare_fiber (e : Expr c) (b B : ℕ) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs : List Bool) (xs : ℕ → List (Fin radix)) (hw : ∀ i, (xs i).length = b)
    (hlen : blocks.length = radix^b) (hwidth : BlockRotationData.Uniform B blocks)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^b)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs) :
    HoareTime (preparedProgram e) (fun v => v = preparedInput e source dest p q blocks bs qs xs)
      (fun v => v = MultiControlTranslationExecution.output e b B source dest p q blocks bs qs xs)
      ((15*leaves e+RadixLinearCombination.linearConstant e.erase+491)*(radix^b*B)) := by
  apply (prepared_translate_hoare e b B hB source dest p q blocks bs qs xs hw hlen hwidth hb hq cb cq).consequence
    (fun _ h => h) (fun _ h => h)
  have hqpos : 1 ≤ radix^b := Nat.one_le_pow _ _ (by have := (Fact.out : radix.Prime).two_le; omega)
  have hv : 1 ≤ radix^b*B := by nlinarith
  nlinarith

/-- Finite physical-bank API, directly producing the frozen recurring bank. -/
theorem prepared_translate_finite_hoare (e : Expr c) (seed : Fin c) (b B : ℕ) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs : List Bool) (xs : Fin c → List (Fin radix)) (hw : ∀ i, (xs i).length = b)
    (hlen : blocks.length = radix^b) (hwidth : BlockRotationData.Uniform B blocks)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^b)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs) :
    HoareTime (preparedProgram e)
      (fun v => v = preparedInput e source dest p q blocks bs qs (RadixLinearCombinationShared.read seed xs))
      (fun v => v = MultiControlTranslationExecution.output e b B source dest p q blocks bs qs
        (RadixLinearCombinationShared.read seed xs))
      ((15*leaves e+RadixLinearCombination.linearConstant e.erase+491)*(radix^b*B)) :=
  prepared_translate_hoare_fiber e b B hB source dest p q blocks bs qs _
    (RadixLinearCombinationShared.read_width seed xs b hw) hlen hwidth hb hq cb cq

omit [Fact radix.Prime] in
/-- Of the ten metadata tapes, only the supplied B/Q descriptors contain data. -/
theorem prepared_workspace_blank (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs : List Bool)
    (i : Fin 10) (hi : i ≠ 5 ∧ i ≠ 7) :
    (preparedTranslationInitial (radix := radix) source dest p q bs qs).tape (Fin.castAdd 2 i) = (fun _ => blank) := by
  unfold preparedTranslationInitial setTape liftedInitial Alphabet.mapTapes
  fin_cases i <;> simp_all <;> rfl

omit [Fact radix.Prime] in
/-- The explicit initial head convention retains the inherited blank spare at
one. B/Q descriptors also start at one; every other metadata head is at zero. -/
theorem prepared_metadata_heads (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs : List Bool) (i : Fin 10) :
    (preparedTranslationInitial (radix := radix) source dest p q bs qs).head (Fin.castAdd 2 i) =
      if i = 0 ∨ i = 5 ∨ i = 7 then 1 else 0 := by
  unfold preparedTranslationInitial setTape liftedInitial Alphabet.mapTapes
  fin_cases i <;> simp <;> rfl

omit [Fact radix.Prime] in
/-- Every actual expression and conversion scratch tape starts entirely blank,
including all future leaf-source sentinels and the shared binary output tape. -/
theorem prepared_arithmetic_blank (e : Expr c) (source dest : ℤ → Fin 4) (p q : ℤ)
    (blocks : List (List (Fin 4))) (bs qs : List Bool) (xs : ℕ → List (Fin radix))
    (i : Fin (RadixLinearCombinationBinary.TapeCount e.erase)) :
    let slot := Fin.castAdd 12 (Fin.natAdd c i)
    (preparedInput e source dest p q blocks bs qs xs).head slot = 0 ∧
    (preparedInput e source dest p q blocks bs qs xs).tape slot = (fun _ => blank) := by
  simp [preparedInput,preparedBank,RadixLinearCombinationBootstrap.input,RadixLinearCombinationBootstrap.empty,Tapes.append]

omit [Fact radix.Prime] in
/-- The only supplied binary metadata consists of B and Q. -/
theorem prepared_descriptors (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs : List Bool) :
    (preparedTranslationInitial (radix := radix) source dest p q bs qs).tape 5 =
      (fun z => (RadixToBinary.binaryEncoding (q := radix)).encode (CountedCopyReuse.binary bs z)) ∧
    (preparedTranslationInitial (radix := radix) source dest p q bs qs).tape 7 =
      (fun z => (RadixToBinary.binaryEncoding (q := radix)).encode (CountedCopyReuse.binary qs z)) := by
  exact ⟨rfl,rfl⟩


omit [Fact radix.Prime] in
/-- Every writable translation metadata head is zero; only supplied B/Q remain
at head1. The blank spare is positioned by an actual transition below. -/
def translationInitial (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs : List Bool) : Tapes 12 radix :=
  setTape (preparedTranslationInitial source dest p q bs qs) 0 (fun _ => blank) 0

omit [Fact radix.Prime] in
private theorem initial_tapes (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs : List Bool) :
    (translationInitial (radix := radix) source dest p q bs qs).tape =
      (preparedTranslationInitial source dest p q bs qs).tape := by
  change Function.update (preparedTranslationInitial (radix := radix) source dest p q bs qs).tape 0 (fun _ => blank) = _
  apply Function.update_eq_self_iff.mpr
  rfl

omit [Fact radix.Prime] in
private def spareProgram : Program 12 2 radix where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols => if s = 0 then
    some (1,fun i => (symbols i,if i = 0 then Move.right else Move.stay)) else none

omit [Fact radix.Prime] in
private theorem spare_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs : List Bool) :
    HoareTime (spareProgram (radix := radix))
      (fun v => v = translationInitial source dest p q bs qs)
      (fun v => v = preparedTranslationInitial source dest p q bs qs) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,(preparedTranslationInitial source dest p q bs qs).head,
    (preparedTranslationInitial source dest p q bs qs).tape⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,spareProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i
      fin_cases i <;> simp [translationInitial,setTape,Move.offset]
      rfl
    · rw [initial_tapes]
      funext i z
      by_cases hz : z = (translationInitial (radix := radix) source dest p q bs qs).head i <;> simp [hz]
  · simp [step,spareProgram]

omit [Fact radix.Prime] in
/-- Shared marked inputs plus completely blank arithmetic scratch and writable
translation metadata, all writable heads at origin. -/
def bank (e : Expr c) (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs : List Bool)
    (xs : ℕ → List (Fin radix)) : Tapes (TapeCount e) radix :=
  (RadixLinearCombinationBootstrap.input e xs).append (translationInitial source dest p q bs qs)

omit [Fact radix.Prime] in
def input (e : Expr c) (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs : List Bool) (xs : ℕ → List (Fin radix)) : Tapes (TapeCount e) radix :=
  bank e (putWord source p blocks.flatten) dest p q bs qs xs

omit [Fact radix.Prime] in
private def setupProgram (e : Expr c) : Program (TapeCount e) 2 radix :=
  Placement.placed spareProgram (finAddFlip : Fin (12+ArithmeticTapes e) ≃ Fin (TapeCount e))

omit [Fact radix.Prime] in
private theorem setup_hoare (e : Expr c) (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs : List Bool)
    (xs : ℕ → List (Fin radix)) :
    HoareTime (setupProgram e) (fun v => v = bank e source dest p q bs qs xs)
      (fun v => v = preparedBank e source dest p q bs qs xs) 1 := by
  let wire : Fin (12+ArithmeticTapes e) ≃ Fin (TapeCount e) := finAddFlip
  have hb : Placement.active wire (bank e source dest p q bs qs xs) = translationInitial source dest p q bs qs := by
    unfold Placement.active wire bank
    congr 1 <;> funext i <;> simp [Tapes.append] <;> rfl
  have ha : Placement.active wire (preparedBank e source dest p q bs qs xs) = preparedTranslationInitial source dest p q bs qs := by
    unfold Placement.active wire preparedBank
    congr 1 <;> funext i <;> simp [Tapes.append] <;> rfl
  have hf : Placement.extra wire (bank e source dest p q bs qs xs) =
      Placement.extra wire (preparedBank e source dest p q bs qs xs) := by
    unfold Placement.extra wire bank preparedBank
    congr 1 <;> funext i <;> simp [Tapes.append]
  apply (Placement.hoare_at (spare_hoare source dest p q bs qs) wire _ hb).consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  rw [Placement.replace,hf,← ha]
  exact Placement.view _ _

abbrev States (e : Expr c) := 2+PreparedStates e

/-- The actual first-use machine includes the spare-head move and its join. -/
def program (e : Expr c) : Program (TapeCount e) (States e) radix :=
  seq (setupProgram e) (preparedProgram e)

theorem translate_hoare (e : Expr c) (b B : ℕ) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs : List Bool) (xs : ℕ → List (Fin radix)) (hw : ∀ i, (xs i).length = b)
    (hlen : blocks.length = radix^b) (hwidth : BlockRotationData.Uniform B blocks)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^b)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs) :
    HoareTime (program e) (fun v => v = input e source dest p q blocks bs qs xs)
      (fun v => v = MultiControlTranslationExecution.output e b B source dest p q blocks bs qs xs)
      ((15*leaves e+RadixLinearCombination.linearConstant e.erase+493)*(radix^b*B)) := by
  have hh := (setup_hoare e (putWord source p blocks.flatten) dest p q bs qs xs).seq
    (prepared_translate_hoare_fiber e b B hB source dest p q blocks bs qs xs hw hlen hwidth hb hq cb cq)
  apply hh.consequence (fun _ h => h) (fun _ h => h)
  have hqpos : 1 ≤ radix^b := Nat.one_le_pow _ _ (by have := (Fact.out : radix.Prime).two_le; omega)
  have hv : 1 ≤ radix^b*B := by nlinarith
  nlinarith

/-- First call of the finite shared-control scheduler, with no inherited
writable head positions and no prepared arithmetic or derived translation data. -/
theorem translate_finite_hoare (e : Expr c) (seed : Fin c) (b B : ℕ) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs : List Bool) (xs : Fin c → List (Fin radix)) (hw : ∀ i, (xs i).length = b)
    (hlen : blocks.length = radix^b) (hwidth : BlockRotationData.Uniform B blocks)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^b)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs) :
    HoareTime (program e)
      (fun v => v = input e source dest p q blocks bs qs (RadixLinearCombinationShared.read seed xs))
      (fun v => v = MultiControlTranslationExecution.output e b B source dest p q blocks bs qs
        (RadixLinearCombinationShared.read seed xs))
      ((15*leaves e+RadixLinearCombination.linearConstant e.erase+493)*(radix^b*B)) :=
  translate_hoare e b B hB source dest p q blocks bs qs _
    (RadixLinearCombinationShared.read_width seed xs b hw) hlen hwidth hb hq cb cq

omit [Fact radix.Prime] in
/-- Every non-input metadata tape is entirely blank with its head at origin. -/
theorem initial_workspace (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs : List Bool)
    (i : Fin 10) (hi : i ≠ 5 ∧ i ≠ 7) :
    (translationInitial (radix := radix) source dest p q bs qs).head (Fin.castAdd 2 i) = 0 ∧
    (translationInitial (radix := radix) source dest p q bs qs).tape (Fin.castAdd 2 i) = (fun _ => blank) := by
  constructor
  · unfold translationInitial setTape
    have hh := prepared_metadata_heads (radix := radix) source dest p q bs qs i
    fin_cases i <;> simp_all
  · rw [initial_tapes]
    exact prepared_workspace_blank source dest p q bs qs i hi

omit [Fact radix.Prime] in
theorem input_arithmetic_blank (e : Expr c) (source dest : ℤ → Fin 4) (p q : ℤ)
    (blocks : List (List (Fin 4))) (bs qs : List Bool) (xs : ℕ → List (Fin radix))
    (i : Fin (RadixLinearCombinationBinary.TapeCount e.erase)) :
    let slot := Fin.castAdd 12 (Fin.natAdd c i)
    (input e source dest p q blocks bs qs xs).head slot = 0 ∧
    (input e source dest p q blocks bs qs xs).tape slot = (fun _ => blank) := by
  simp [input,bank,RadixLinearCombinationBootstrap.input,RadixLinearCombinationBootstrap.empty,Tapes.append]

omit [Fact radix.Prime] in
/-- The two supplied size descriptors survive the raw initial layout exactly. -/
theorem initial_descriptors (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs : List Bool) :
    (translationInitial (radix := radix) source dest p q bs qs).tape 5 =
      (fun z => (RadixToBinary.binaryEncoding (q := radix)).encode (CountedCopyReuse.binary bs z)) ∧
    (translationInitial (radix := radix) source dest p q bs qs).tape 7 =
      (fun z => (RadixToBinary.binaryEncoding (q := radix)).encode (CountedCopyReuse.binary qs z)) := by
  rw [initial_tapes]
  exact prepared_descriptors source dest p q bs qs

end IntegerMultBounds.Machine.MultiControlTranslationBootstrap
