import IntegerMultBounds.Machine.RepeatedControlTranslationStream
import IntegerMultBounds.Machine.FlatFixedControlShift

/-! Literal flat-array boundary for repeated controlled shifts with arbitrary
outer prefix and middle spectator cardinalities. Canonical runtime dimensions
and the initial control word are explicit prepared inputs. -/
namespace IntegerMultBounds.Machine.FlatRepeatedControlShift
variable {radix N C Q B : ℕ} [Fact radix.Prime]

def slice (a : Fin (N*(C*(Q*B))) → Fin 4) (i : Fin N) : Fin (C*(Q*B)) → Fin 4 :=
  fun j => a (finProdFinEquiv (i,j))

def payload (a : Fin (N*(C*(Q*B))) → Fin 4) (i c y : ℕ) : List (Fin 4) :=
  if hi : i < N then FlatControlledShift.payload (slice a ⟨i,hi⟩) c y else List.replicate B 0

@[simp] theorem payload_length (a : Fin (N*(C*(Q*B))) → Fin 4) (i c y : ℕ) :
    (payload a i c y).length = B := by
  unfold payload
  split <;> simp

theorem source_eq (a : Fin (N*(C*(Q*B))) → Fin 4) :
    (RepeatedControlTranslationStream.groups Q C N (payload a)).flatten = List.ofFn a := by
  rw [List.ofFn_mul a]
  congr 1
  apply List.ext_getElem
  · simp [RepeatedControlTranslationStream.groups]
  · intro i hi hi'
    have hiN : i < N := by simpa [RepeatedControlTranslationStream.groups] using hi
    simp only [RepeatedControlTranslationStream.groups,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    have hp : payload a i = FlatControlledShift.payload (slice a ⟨i,hiN⟩) := by
      funext c y
      simp [payload,hiN]
    rw [hp]
    rw [FlatControlledShift.source_eq]
    apply congrArg List.ofFn
    funext j
    change a (finProdFinEquiv (⟨i,hiN⟩,j)) = a _
    congr 1
    apply Fin.ext
    simp [finProdFinEquiv]
    ring

def translated (r : ℚ) (xs : List (Fin radix))
    (a : Fin (N*(C*(radix^xs.length*B))) → Fin 4) : List (Fin 4) :=
  (List.ofFn (fun i : Fin N => FiberLayoutData.translated (slice a i)
    (fun _ => FlatFixedControlShift.offset r (RationalTranslationStream.control xs i.val)))).flatten

theorem output_eq (r : ℚ) (xs : List (Fin radix))
    (a : Fin (N*(C*(radix^xs.length*B))) → Fin 4) :
    RepeatedControlTranslationStream.outputPrefix r xs C N (payload a) = translated r xs a := by
  unfold RepeatedControlTranslationStream.outputPrefix translated
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    have hiN : i < N := by simpa using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    unfold FixedControlTranslationStream.outputPrefix
    simp only [RationalTranslationStream.control_length]
    have hp : payload a i = FlatControlledShift.payload (slice a ⟨i,hiN⟩) := by
      funext c y
      simp [payload,hiN]
    rw [hp]
    rw [FlatControlledShift.output_eq]
    rfl

def state (r : ℚ) (xs : List (Fin radix))
    (a : Fin (N*(C*(radix^xs.length*B))) → Fin 4) (bs qs cs ns old : List Bool) (i : ℕ) :=
  CountedLoopReuseAlphabet.bank
    (RepeatedControlTranslationStream.state r B C N (fun _ => blank) (fun _ => blank) 0 0
      bs qs cs old xs (payload a) i)
    CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1

theorem source_tape (r : ℚ) (xs : List (Fin radix))
    (a : Fin (N*(C*(radix^xs.length*B))) → Fin 4) (bs qs cs ns old : List Bool) (i : ℕ) :
    (state r xs a bs qs cs ns old i).tape 10 = fun z =>
      (RadixToBinary.binaryEncoding (q := radix)).encode (putWord (fun _ => blank) 0 (List.ofFn a) z) := by
  change (fun z => (RadixToBinary.binaryEncoding (q := radix)).encode
    (putWord (fun _ => blank) 0 (RepeatedControlTranslationStream.groups (radix^xs.length) C N (payload a)).flatten z)) = _
  rw [source_eq]

theorem destination_tape (r : ℚ) (xs : List (Fin radix))
    (a : Fin (N*(C*(radix^xs.length*B))) → Fin 4) (bs qs cs ns old : List Bool) :
    (state r xs a bs qs cs ns old N).tape 11 = fun z =>
      (RadixToBinary.binaryEncoding (q := radix)).encode (putWord (fun _ => blank) 0 (translated r xs a) z) := by
  change (fun z => (RadixToBinary.binaryEncoding (q := radix)).encode
    (putWord (fun _ => blank) 0 (RepeatedControlTranslationStream.outputPrefix r xs C N (payload a)) z)) = _
  rw [output_eq]

theorem realizes_hoare (r : ℚ) (hB : 0 < B) (hC : 0 < C) (xs : List (Fin radix))
    (a : Fin (N*(C*(radix^xs.length*B))) → Fin 4) (bs qs cs ns old : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^xs.length)
    (hc : Counter.value cs = C) (hn : Counter.value ns = N)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cc : GrowingCounterData.Canonical cs) (cn : GrowingCounterData.Canonical ns)
    (cold : GrowingCounterData.Canonical old) (hold : Counter.value old < radix^xs.length) :
    HoareTime (RepeatedControlTranslationStream.program r)
      (fun v => v = state r xs a bs qs cs ns old 0)
      (fun v => v = state r xs a bs qs cs ns old N)
      (570*(N*(C*(radix^xs.length*B)))+23) :=
  RepeatedControlTranslationStream.stream_hoare r hB hC (fun _ => blank) (fun _ => blank)
    0 0 bs qs cs ns old xs hb hq hc hn cb cq cc cn cold hold (payload a) (payload_length a)

/-- Every middle spectator and suffix position survives the physical shift. -/
theorem translated_entry (r : ℚ) (xs : List (Fin radix))
    (a : Fin (N*(C*(radix^xs.length*B))) → Fin 4)
    (i : Fin N) (c : Fin C) (y : Fin (radix^xs.length)) (j : Fin B) :
    (translated r xs a)[i.val*(C*(radix^xs.length*B))+c.val*(radix^xs.length*B)+
      ((y.val+FlatFixedControlShift.offset r (RationalTranslationStream.control xs i.val))%radix^xs.length)*B+j.val]? =
      some (a (finProdFinEquiv (i,FiberLayoutData.index c y j))) := by
  have hu : BlockRotationData.Uniform (C*(radix^xs.length*B))
      (List.ofFn (fun i : Fin N => FiberLayoutData.translated (slice a i)
        (fun _ => FlatFixedControlShift.offset r (RationalTranslationStream.control xs i.val)))) := by
    intro word hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact FiberLayoutData.translated_length _ _
  have hentry := FiberLayoutData.translated_entry (slice a i)
    (fun _ => FlatFixedControlShift.offset r (RationalTranslationStream.control xs i.val)) c y j
  have hbound := (List.getElem?_eq_some_iff.mp hentry).1
  rw [FiberLayoutData.translated_length] at hbound
  unfold translated
  rw [show i.val*(C*(radix^xs.length*B))+c.val*(radix^xs.length*B)+
      ((y.val+FlatFixedControlShift.offset r (RationalTranslationStream.control xs i.val))%radix^xs.length)*B+j.val =
      i.val*(C*(radix^xs.length*B))+(c.val*(radix^xs.length*B)+
      ((y.val+FlatFixedControlShift.offset r (RationalTranslationStream.control xs i.val))%radix^xs.length)*B+j.val) by omega]
  rw [BlockRotationData.flatten_index _ _ hu i.val _ (by simp) hbound]
  simpa only [List.getElem_ofFn,Fin.eta,slice] using hentry

theorem destination_entry (r : ℚ) (xs : List (Fin radix))
    (a : Fin (N*(C*(radix^xs.length*B))) → Fin 4) (bs qs cs ns old : List Bool)
    (i : Fin N) (c : Fin C) (y : Fin (radix^xs.length)) (j : Fin B) :
    (state r xs a bs qs cs ns old N).tape 11
      ((i.val*(C*(radix^xs.length*B))+c.val*(radix^xs.length*B)+
      ((y.val+FlatFixedControlShift.offset r (RationalTranslationStream.control xs i.val))%radix^xs.length)*B+j.val : ℕ) : ℤ) =
      (RadixToBinary.binaryEncoding (q := radix)).encode
        (a (finProdFinEquiv (i,FiberLayoutData.index c y j))) := by
  rw [destination_tape]
  obtain ⟨hb,hv⟩ := List.getElem?_eq_some_iff.mp (translated_entry r xs a i c y j)
  rw [show ((i.val*(C*(radix^xs.length*B))+c.val*(radix^xs.length*B)+
      ((y.val+FlatFixedControlShift.offset r (RationalTranslationStream.control xs i.val))%radix^xs.length)*B+j.val : ℕ) : ℤ) =
      0+((i.val*(C*(radix^xs.length*B))+c.val*(radix^xs.length*B)+
      ((y.val+FlatFixedControlShift.offset r (RationalTranslationStream.control xs i.val))%radix^xs.length)*B+j.val : ℕ) : ℤ) by omega]
  dsimp only
  rw [WordSegments.get _ _ _ _ hb,hv]

/-- The executing cyclic H counter supplies the rational multiple of H,
even when the outer prefix has completed arbitrarily many cycles. -/
theorem offset_value (r : ℚ) (hden : r.den < radix) (b i : ℕ) :
    FlatFixedControlShift.offset r (RationalTranslationStream.control
      (RadixCounterData.zeros (Fact.out : radix.Prime).two_le b) i) =
      (Swap.Modular.ratMod (radix^b) r * (i : ZMod (radix^b))).val := by
  have hv := RationalTranslationStream.offset_value r hden
    (RadixCounterData.zeros (Fact.out : radix.Prime).two_le b) i
  have hb := RationalOffsetPrepare.result_lt r (RationalTranslationStream.control
    (RadixCounterData.zeros (Fact.out : radix.Prime).two_le b) i)
  simp only [RationalTranslationStream.control_length,RadixCounterData.zeros_length] at hb
  have hpos : 0 < radix^b := pow_pos (Fact.out : radix.Prime).pos _
  let : NeZero (radix^b) := ⟨by omega⟩
  simp only [RadixCounterData.zeros_value,Nat.zero_add] at hv
  generalize hlen : (RadixCounterData.zeros (Fact.out : radix.Prime).two_le b).length = w at hv
  have hw : w = b := hlen.symm.trans (RadixCounterData.zeros_length _ _)
  rw [hw] at hv
  have hh := congrArg ZMod.val hv
  simpa only [RationalTranslationStream.offset,RadixCounterData.zeros_length,ZMod.val_natCast,
    Nat.mod_eq_of_lt hb] using hh

/-- At L complete H cycles the physical control tape is restored to zero. -/
theorem control_restored (r : ℚ) (b L : ℕ)
    (a : Fin ((L*radix^b)*(C*(radix^(RadixCounterData.zeros (Fact.out : radix.Prime).two_le b).length*B))) → Fin 4)
    (bs qs cs ns old : List Bool) :
    (state r (RadixCounterData.zeros (Fact.out : radix.Prime).two_le b) a bs qs cs ns old (L*radix^b)).head 15 = 1 ∧
    (state r (RadixCounterData.zeros (Fact.out : radix.Prime).two_le b) a bs qs cs ns old (L*radix^b)).tape 15 =
      RadixRationalBinary.source (RadixCounterData.zeros (Fact.out : radix.Prime).two_le b) := by
  constructor
  · rfl
  · change RadixRationalBinary.source (RationalTranslationStream.control
      (RadixCounterData.zeros (Fact.out : radix.Prime).two_le b) (L*radix^b)) = _
    rw [RepeatedControlTranslationStream.control_prefix_cycles]

end IntegerMultBounds.Machine.FlatRepeatedControlShift
