import IntegerMultBounds.Machine.RationalPrefixTranslationStream
import IntegerMultBounds.Machine.FiberLayoutData

/-! A concrete flat-array controlled shift. The fibers are extracted from the
actual input array; the selected control is extracted from the physical prefix
index and computed by the executing mixed-prefix counter. -/
namespace IntegerMultBounds.Machine.FlatControlledShift

variable {P Q B radix c : ℕ}

/-- Total extension used by the streaming machine specification. -/
def payload (a : Fin (P*(Q*B)) → Fin 4) (i y : ℕ) : List (Fin 4) :=
  if hi : i < P then
    if hy : y < Q then
      List.ofFn (fun j : Fin B => a (FiberLayoutData.index ⟨i,hi⟩ ⟨y,hy⟩ j))
    else List.replicate B 0
  else List.replicate B 0

@[simp] theorem payload_length (a : Fin (P*(Q*B)) → Fin 4) (i y : ℕ) :
    (payload a i y).length = B := by
  unfold payload
  split
  · split <;> simp
  · simp

theorem blocks_eq (a : Fin (P*(Q*B)) → Fin 4) (i : Fin P) :
    TranslationStream.blocks Q (payload a i.val) = FiberLayoutData.fiber a i := by
  apply List.ext_getElem
  · simp [TranslationStream.blocks,FiberLayoutData.fiber]
  · intro j hj hj'
    have hjQ : j < Q := by simpa [TranslationStream.blocks] using hj
    simp [TranslationStream.blocks,FiberLayoutData.fiber,payload,i.isLt,hjQ]

theorem fibers_eq (a : Fin (P*(Q*B)) → Fin 4) :
    TranslationStream.fibers Q P (payload a) = (FiberLayoutData.fibers a).map List.flatten := by
  apply List.ext_getElem
  · simp [TranslationStream.fibers,FiberLayoutData.fibers]
  · intro i hi hi'
    have hiP : i < P := by simpa [TranslationStream.fibers] using hi
    simpa [TranslationStream.fibers,FiberLayoutData.fibers] using
      congrArg List.flatten (blocks_eq a ⟨i,hiP⟩)

theorem source_eq (a : Fin (P*(Q*B)) → Fin 4) :
    (TranslationStream.fibers Q P (payload a)).flatten = List.ofFn a := by
  rw [fibers_eq,FiberLayoutData.flatten_fibers]

theorem output_eq (a : Fin (P*(Q*B)) → Fin 4) (offset : ℕ → ℕ) :
    TranslationPreparedFamily.outputPrefix offset Q P (payload a) =
      FiberLayoutData.translated a (fun p => offset p.val) := by
  unfold TranslationPreparedFamily.outputPrefix FiberLayoutData.translated
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    have hiP : i < P := by simpa using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    rw [blocks_eq a ⟨i,hiP⟩]

variable [Fact radix.Prime]

def initial (width : Fin (c+1) → ℕ) (j : Fin (c+1)) : List (Fin radix) :=
  RadixCounterData.zeros (Fact.out : radix.Prime).two_le (width j)

@[simp] theorem initial_length (width : Fin (c+1) → ℕ) (j : Fin (c+1)) :
    (initial (radix := radix) width j).length = width j := by simp [initial]

/-- Actual control coordinate of a row-major prefix index. -/
def control (low : List (Fin (c+1))) (width : Fin (c+1) → ℕ) (i : ℕ) : ℕ :=
  (i/radix^PrefixAddressData.widthSum low width)%radix^(width 0)

/-- The rational shift computed from the selected physical prefix coordinate. -/
def physicalOffset (r : ℚ) (low : List (Fin (c+1))) (width : Fin (c+1) → ℕ) (i : ℕ) : ℕ :=
  (Swap.Modular.ratMod (radix^(width 0)) r *
    (control (radix := radix) low width i : ZMod (radix^(width 0)))).val

theorem offset_eq (r : ℚ) (hden : r.den < radix)
    (low high : List (Fin (c+1))) (hnodup : (low++0::high).Nodup)
    (width : Fin (c+1) → ℕ) (i : ℕ)
    (hi : i < radix^PrefixAddressData.widthSum (low++0::high) width) :
    RationalPrefixTranslationStream.offset r (low++0::high) (initial (radix := radix) width) i =
      physicalOffset (radix := radix) r low width i := by
  have hv := RationalPrefixTranslationStream.offset_value r hden (low++0::high) (initial (radix := radix) width) i
  have he := PrefixAddressData.enumeration_selected (Fact.out : radix.Prime).two_le
    low high 0 hnodup width i hi
  have hb := RationalOffsetPrepare.result_lt r
    (RationalPrefixTranslationStream.fields (low++0::high) (initial (radix := radix) width) i 0)
  simp only [RationalPrefixTranslationStream.fields_length,initial_length] at hb
  change RationalPrefixTranslationStream.offset r (low++0::high) (initial (radix := radix) width) i < radix^(width 0) at hb
  generalize hlen : (initial (radix := radix) width 0).length = w at hv
  have hw : w = width 0 := hlen.symm.trans (initial_length width 0)
  rw [hw] at hv
  change RadixDigits.value (RationalPrefixTranslationStream.fields (low++0::high)
    (initial (radix := radix) width) i 0) = control (radix := radix) low width i at he
  have hv' : (RationalPrefixTranslationStream.offset r (low++0::high) (initial (radix := radix) width) i :
      ZMod (radix^(width 0))) = Swap.Modular.ratMod (radix^(width 0)) r *
        (control (radix := radix) low width i : ZMod (radix^(width 0))) := by
    simpa only [he] using hv
  have hpos : 0 < radix^(width 0) := pow_pos (Fact.out : radix.Prime).pos _
  let : NeZero (radix^(width 0)) := ⟨by omega⟩
  have hh := congrArg ZMod.val hv'
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hb,physicalOffset] using hh

/-- Concrete whole bank at a stream boundary, including the two loop tapes. -/
def bank (r : ℚ) (order : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (a : Fin (P*(radix^(width 0)*B)) → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs ns : List Bool) (i : ℕ) : Tapes ((16+c)+2) radix :=
  CountedLoopReuseAlphabet.bank
    (RationalPrefixTranslationStream.state r order B P source dest p q bs qs []
      (initial (radix := radix) width) (payload a) i)
    CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1

/-- The source is literally the flat input, independently of all boundary states. -/
theorem source_tape (r : ℚ) (order : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (a : Fin (P*(radix^(width 0)*B)) → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ)
    (bs qs ns : List Bool) (i : ℕ) :
    (bank r order width a source dest p q bs qs ns i).tape 10 =
      fun z => (RadixToBinary.binaryEncoding (q := radix)).encode (putWord source p (List.ofFn a) z) := by
  rw [show (10 : Fin ((16+c)+2)) = Fin.castAdd 2 (Fin.castAdd c (10 : Fin 16)) by
    apply Fin.ext
    simp
    omega]
  simp only [bank,CountedLoopReuseAlphabet.bank,RationalPrefixTranslationStream.state,
    RationalPrefixTranslationExecution.bank,Tapes.append,Fin.addCases_left]
  change (fun z => (RadixToBinary.binaryEncoding (q := radix)).encode
    (putWord source p (TranslationStream.fibers (radix^(initial (radix := radix) width 0).length) P (payload a)).flatten z)) = _
  rw [initial_length,source_eq]

theorem destination_tape (r : ℚ) (hden : r.den < radix)
    (low high : List (Fin (c+1))) (hnodup : (low++0::high).Nodup) (width : Fin (c+1) → ℕ)
    (a : Fin (radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) :
    (bank r (low++0::high) width a source dest p q bs qs ns
      (radix^PrefixAddressData.widthSum (low++0::high) width)).tape 11 =
      fun z => (RadixToBinary.binaryEncoding (q := radix)).encode
        (putWord dest q (FiberLayoutData.translated a (fun i => physicalOffset (radix := radix) r low width i.val)) z) := by
  rw [show (11 : Fin ((16+c)+2)) = Fin.castAdd 2 (Fin.castAdd c (11 : Fin 16)) by
    apply Fin.ext
    simp
    omega]
  simp only [bank,CountedLoopReuseAlphabet.bank,RationalPrefixTranslationStream.state,
    RationalPrefixTranslationExecution.bank,Tapes.append,Fin.addCases_left]
  change (fun z => (RadixToBinary.binaryEncoding (q := radix)).encode
    (putWord dest q (RationalPrefixTranslationStream.outputPrefix r (low++0::high)
      (initial (radix := radix) width) (radix^PrefixAddressData.widthSum (low++0::high) width) (payload a)) z)) = _
  unfold RationalPrefixTranslationStream.outputPrefix
  rw [initial_length,output_eq]
  have hoff : (fun i : Fin (radix^PrefixAddressData.widthSum (low++0::high) width) =>
      RationalPrefixTranslationStream.offset r (low++0::high) (initial (radix := radix) width) i.val) =
      (fun i => physicalOffset (radix := radix) r low width i.val) := by
    funext i
    exact offset_eq r hden low high hnodup width i.val i.isLt
  rw [hoff]

/-- Every actual input symbol reaches its rational-controlled physical address. -/
theorem output_symbol (r : ℚ) (hden : r.den < radix)
    (low high : List (Fin (c+1))) (hnodup : (low++0::high).Nodup) (width : Fin (c+1) → ℕ)
    (a : Fin (radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool)
    (i : Fin (radix^PrefixAddressData.widthSum (low++0::high) width)) (y : Fin (radix^(width 0))) (j : Fin B) :
    (bank r (low++0::high) width a source dest p q bs qs ns
      (radix^PrefixAddressData.widthSum (low++0::high) width)).tape 11
      (q+((i.val*(radix^(width 0)*B)+((y.val+physicalOffset (radix := radix) r low width i.val)%radix^(width 0))*B+j.val : ℕ) : ℤ)) =
      (RadixToBinary.binaryEncoding (q := radix)).encode (a (FiberLayoutData.index i y j)) := by
  rw [destination_tape r hden low high hnodup]
  have hs := FiberLayoutData.translated_entry a (fun i => physicalOffset (radix := radix) r low width i.val) i y j
  obtain ⟨hj,hvalue⟩ := List.getElem?_eq_some_iff.mp hs
  dsimp only
  rw [WordSegments.get _ _ _ _ hj,hvalue]

/-- A full physical prefix traversal, with actual selected-field arithmetic,
carry scheduling and payload transport, has a uniform volume-linear runtime.
Canonical size descriptors and the marked zero prefix bank are explicit inputs. -/
theorem realizes_hoare (r : ℚ) (hden : r.den < radix)
    (low high : List (Fin (c+1))) (hfull : (low++0::high).Perm (List.finRange (c+1)))
    (width : Fin (c+1) → ℕ) (hB : 0 < B)
    (a : Fin (radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^(width 0))
    (hn : Counter.value ns = radix^PrefixAddressData.widthSum (low++0::high) width)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns) :
    HoareTime (RationalPrefixTranslationStream.program (radix := radix) r (low++0::high) (by simp))
      (fun v => v = bank r (low++0::high) width a source dest p q bs qs ns 0)
      (fun v => v = bank r (low++0::high) width a source dest p q bs qs ns
          (radix^PrefixAddressData.widthSum (low++0::high) width) ∧
        ∀ (i : Fin (radix^PrefixAddressData.widthSum (low++0::high) width))
          (y : Fin (radix^(width 0))) (j : Fin B),
        v.tape 11
          (q+((i.val*(radix^(width 0)*B)+((y.val+physicalOffset (radix := radix) r low width i.val)%radix^(width 0))*B+j.val : ℕ) : ℤ)) =
          (RadixToBinary.binaryEncoding (q := radix)).encode (a (FiberLayoutData.index i y j)))
      ((536+4*c)*(radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B))+23) := by
  have hnodup := hfull.nodup_iff.mpr (List.nodup_finRange (c+1))
  have hp : 0 < radix^(width 0) := pow_pos (Fact.out : radix.Prime).pos _
  have hh := RationalPrefixTranslationStream.translate_hoare_linear r (low++0::high) (by simp) hnodup
    hB source dest p q bs qs ns [] (initial (radix := radix) width) hb
    (by simpa using hq) hn cb cq cn (by simp [GrowingCounterData.Canonical])
    (by simpa [Counter.value] using hp) (payload a) (payload_length a)
  apply hh.consequence (fun _ h => h) ?_ ?_
  · rintro v rfl
    exact ⟨rfl,fun i y j => output_symbol r hden low high hnodup width a source dest p q bs qs ns i y j⟩
  · rw [initial_length,source_eq,List.length_ofFn]
    simp only [initial_length]
    have hlength : (low++0::high).length = c+1 := by simpa using hfull.length_eq
    rw [hlength]
    have hw := RadixToBinaryData.width_le_power (Fact.out : radix.Prime).two_le (∑ j, width j)
    rw [← PrefixAddressData.full_widthSum _ _ hfull] at hw
    have hvol : radix^PrefixAddressData.widthSum (low++0::high) width ≤
        radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B) := by
      exact Nat.le_mul_of_pos_right _ (Nat.mul_pos hp hB)
    rw [PrefixAddressData.full_widthSum _ _ hfull] at hw hvol ⊢
    nlinarith

end IntegerMultBounds.Machine.FlatControlledShift
