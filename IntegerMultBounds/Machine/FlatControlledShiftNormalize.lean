import IntegerMultBounds.Machine.FlatControlledShift
import IntegerMultBounds.Machine.FlatArrayNormalize
import IntegerMultBounds.Machine.FamilyPlacementAlphabet

/-! Static wiring of actual payload normalization directly into a controlled
shift bank. Existing B/Q/P descriptors and clocks are shared physically. There
are no extra payload copies, sentinels or free head resets in the handoff. -/
namespace IntegerMultBounds.Machine.FlatControlledShiftNormalize
variable {radix c : ℕ}
open CountedLoopReuseAlphabet (empty binary)

private def basePlacement : Fin (6+10) ≃ Fin 16 where
  toFun := ![11,10,4,5,6,7,0,1,2,3,8,9,12,13,14,15]
  invFun := ![6,7,8,9,2,3,4,5,10,11,1,0,12,13,14,15]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private def bodyPlacement (c : ℕ) : Fin (6+(10+c)) ≃ Fin (16+c) :=
  FamilyPlacement.pair basePlacement (finCongr (by omega) : Fin (0+c) ≃ Fin c)

/-- Source/destination, B clock/count, Q clock/count, and P clock/count. -/
def placement (c : ℕ) : Fin (8+(10+c)) ≃ Fin ((16+c)+2) :=
  FamilyPlacement.withFrame (r := 2) (bodyPlacement c)

private def encoded (f : ℤ → Fin 4) : ℤ → Fin (radix+4) :=
  fun z => (RadixToBinary.binaryEncoding (q := radix)).encode (f z)

def bank (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ps old : List Bool)
    (fields : Fin (c+1) → List (Fin radix)) : Tapes ((16+c)+2) radix :=
  CountedLoopReuseAlphabet.bank
    (RationalPrefixTranslationExecution.bank source dest p q bs qs old old fields) empty (binary ps) 1 1

private theorem base_active (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs old : List Bool)
    (xs : List (Fin radix)) :
    Placement.active basePlacement (RationalTranslationExecution.bank source dest p q bs qs old old xs) =
      CountedLoopReuseAlphabet.bank
        (CountedLoopReuseAlphabet.bank (FlatArrayNormalize.pair (encoded dest) (encoded source) q p)
          empty (binary bs) 1 1) empty (binary qs) 1 1 := by
  unfold Placement.active basePlacement
  congr 1 <;> funext i <;> fin_cases i <;> first
    | rfl
    | exact CountedLoopReuseAlphabet.encoding_empty
    | exact CountedLoopReuseAlphabet.encoding_binary _

/-- Projection is an equality of actual heads and tapes, not a copied bank. -/
theorem active_bank (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ps old : List Bool)
    (fields : Fin (c+1) → List (Fin radix)) :
    Placement.active (placement c) (bank source dest p q bs qs ps old fields) =
      FlatArrayNormalize.bank (encoded dest) (encoded source) q p bs qs ps := by
  unfold placement bank CountedLoopReuseAlphabet.bank RationalPrefixTranslationExecution.bank
  rw [FamilyPlacementAlphabet.active_withFrame]
  change (Placement.active (bodyPlacement c) _).append _ = _
  unfold bodyPlacement
  rw [FamilyPlacementAlphabet.active_pair,base_active]
  unfold Placement.active
  simp only [FlatArrayNormalize.bank,CountedVolumeLoop.bank,CountedLoopReuseAlphabet.bank,Tapes.append]
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem extra_bank (source dest source' dest' : ℤ → Fin 4) (p q p' q' : ℤ)
    (bs qs ps old : List Bool) (fields : Fin (c+1) → List (Fin radix)) :
    Placement.extra (placement c) (bank source dest p q bs qs ps old fields) =
      Placement.extra (placement c) (bank source' dest' p' q' bs qs ps old fields) := by
  unfold placement bank CountedLoopReuseAlphabet.bank RationalPrefixTranslationExecution.bank
  rw [FamilyPlacementAlphabet.extra_withFrame,FamilyPlacementAlphabet.extra_withFrame]
  unfold bodyPlacement
  rw [FamilyPlacementAlphabet.extra_pair,FamilyPlacementAlphabet.extra_pair]
  congr 1
  unfold Placement.extra basePlacement
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def normalizeProgram : Program ((16+c)+2) 150 radix :=
  Placement.placed FlatArrayNormalize.program (placement c)

private theorem encoded_word (f : ℤ → Fin 4) (z : ℤ) (xs : List (Fin 4)) : encoded (radix := radix) (putWord f z xs) =
    putWord (encoded f) z (xs.map (RadixToBinary.binaryEncoding (q := radix)).encode) := by
  induction xs generalizing f z with
  | nil => rfl
  | cons x xs ih =>
    funext k
    by_cases hk : k = z
    · subst k; simp [encoded,putWord,List.map_cons]
    · simp only [List.map_cons,putWord,encoded,Function.update_of_ne hk]
      exact congrFun (ih f (z+1)) k

/-- The shifted array is physically transferred to the common source, the old
output is cleared, and both payload heads are physically restored. -/
theorem normalize_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (xs : List (Fin 4))
    (P Q B : ℕ) (bs qs ps old : List Bool) (fields : Fin (c+1) → List (Fin radix))
    (hlen : xs.length = P*(Q*B)) (hb : Counter.value bs = B) (hq : Counter.value qs = Q)
    (hp : Counter.value ps = P) (hP : 0 < P) (hQ : 0 < Q) (hB : 0 < B)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cp : GrowingCounterData.Canonical ps)
    (hblank : ∀ z, q ≤ z → z < q+xs.length → dest z = blank) :
    HoareTime normalizeProgram
      (fun v => v = bank source (putWord dest q xs) (p+xs.length) (q+xs.length) bs qs ps old fields)
      (fun v => v = bank (putWord source p xs) dest p q bs qs ps old fields)
      (327*xs.length+2) := by
  have hh := FlatArrayNormalize.normalize_hoare (encoded (radix := radix) dest) (encoded source) q p
    (xs.map (RadixToBinary.binaryEncoding (q := radix)).encode) P Q B bs qs ps
    (by simpa using hlen) hb hq hp hP hQ hB cb cq cp
    (by intro z hz hz'; change (RadixToBinary.binaryEncoding (q := radix)).encode (dest z) = blank
        rw [hblank z hz (by simpa using hz')]; rfl)
  simp only [List.length_map,← encoded_word] at hh
  have hp' := Placement.hoare_at hh (placement c)
    (bank source (putWord dest q xs) (p+xs.length) (q+xs.length) bs qs ps old fields)
    (active_bank _ _ _ _ _ _ _ _ _)
  apply hp'.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [Placement.replace,extra_bank source (putWord dest q xs) (putWord source p xs) dest
    (p+xs.length) (q+xs.length) p q bs qs ps old fields,← active_bank]
  exact Placement.view _ _

variable [Fact radix.Prime]

/-- Actual shift followed by the physically wired normalizer. -/
def program (r : ℚ) (order : List (Fin (c+1))) (hne : order ≠ []) :=
  seq (RationalPrefixTranslationStream.program (radix := radix) r order hne) normalizeProgram

def word {B : ℕ} (r : ℚ) (low high : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (a : Fin (radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B)) → Fin 4) : List (Fin 4) :=
  FiberLayoutData.translated a (fun i => FlatControlledShift.physicalOffset (radix := radix) r low width i.val)

omit [Fact radix.Prime] in
@[simp] theorem word_length {B : ℕ} (r : ℚ) (low high : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (a : Fin (radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B)) → Fin 4) :
    (word r low high width a).length = radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B) :=
  FiberLayoutData.translated_length _ _

/-- Exact retained final arithmetic metadata; only payload normalization changes
these endpoints relative to the stream's bank. -/
def output {B : ℕ} (r : ℚ) (low high : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (a : Fin (radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ps : List Bool) :=
  bank (putWord (putWord source p (List.ofFn a)) p (word r low high width a)) dest p q bs qs ps
    (RationalPrefixTranslationStream.descriptor r (low++0::high) [] (FlatControlledShift.initial (radix := radix) width)
      (radix^PrefixAddressData.widthSum (low++0::high) width))
    (RationalPrefixTranslationStream.fields (low++0::high) (FlatControlledShift.initial (radix := radix) width)
      (radix^PrefixAddressData.widthSum (low++0::high) width))

/-- Both physical payload heads are back at their common origins, and scratch
is exactly restored while the source contains the transformed flat word. -/
theorem output_payload {B : ℕ} (r : ℚ) (low high : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (a : Fin (radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ps : List Bool) :
    let v := output r low high width a source dest p q bs qs ps
    v.tape 10 = (fun z => (RadixToBinary.binaryEncoding (q := radix)).encode
      (putWord (putWord source p (List.ofFn a)) p (word r low high width a) z)) ∧
    v.tape 11 = (fun z => (RadixToBinary.binaryEncoding (q := radix)).encode (dest z)) ∧
    v.head 10 = p ∧ v.head 11 = q := by
  dsimp only
  rw [show (10 : Fin ((16+c)+2)) = Fin.castAdd 2 (Fin.castAdd c (10 : Fin 16)) by
        apply Fin.ext; simp; omega,
      show (11 : Fin ((16+c)+2)) = Fin.castAdd 2 (Fin.castAdd c (11 : Fin 16)) by
        apply Fin.ext; simp; omega]
  simp only [output,bank,CountedLoopReuseAlphabet.bank,RationalPrefixTranslationExecution.bank,
    Tapes.append,Fin.addCases_left]
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- Exact shifted symbols are now on the common input tape for the next stage. -/
theorem output_symbol {B : ℕ} (r : ℚ) (low high : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (a : Fin (radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ps : List Bool)
    (i : Fin (radix^PrefixAddressData.widthSum (low++0::high) width)) (y : Fin (radix^(width 0))) (j : Fin B) :
    (output r low high width a source dest p q bs qs ps).tape 10
      (p+((i.val*(radix^(width 0)*B)+
        ((y.val+FlatControlledShift.physicalOffset (radix := radix) r low width i.val)%radix^(width 0))*B+j.val : ℕ) : ℤ)) =
      (RadixToBinary.binaryEncoding (q := radix)).encode (a (FiberLayoutData.index i y j)) := by
  rw [(output_payload r low high width a source dest p q bs qs ps).1]
  have hh := FiberLayoutData.translated_entry a
    (fun i => FlatControlledShift.physicalOffset (radix := radix) r low width i.val) i y j
  obtain ⟨hi,hvalue⟩ := List.getElem?_eq_some_iff.mp hh
  dsimp only
  change (RadixToBinary.binaryEncoding (q := radix)).encode
    (putWord (putWord source p (List.ofFn a)) p (word r low high width a) _) = _
  unfold word
  rw [WordSegments.get _ _ _ _ hi,hvalue]

private theorem stream_final {B : ℕ} (r : ℚ) (hden : r.den < radix)
    (low high : List (Fin (c+1))) (hnodup : (low++0::high).Nodup) (width : Fin (c+1) → ℕ)
    (a : Fin (radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ps : List Bool) :
    FlatControlledShift.bank r (low++0::high) width a source dest p q bs qs ps
      (radix^PrefixAddressData.widthSum (low++0::high) width) =
    bank (putWord source p (List.ofFn a)) (putWord dest q (word r low high width a))
      (p+(word r low high width a).length) (q+(word r low high width a).length) bs qs ps
      (RationalPrefixTranslationStream.descriptor r (low++0::high) [] (FlatControlledShift.initial (radix := radix) width)
        (radix^PrefixAddressData.widthSum (low++0::high) width))
      (RationalPrefixTranslationStream.fields (low++0::high) (FlatControlledShift.initial (radix := radix) width)
        (radix^PrefixAddressData.widthSum (low++0::high) width)) := by
  have hoff : (fun i : Fin (radix^PrefixAddressData.widthSum (low++0::high) width) =>
      RationalPrefixTranslationStream.offset r (low++0::high) (FlatControlledShift.initial (radix := radix) width) i.val) =
      (fun i => FlatControlledShift.physicalOffset (radix := radix) r low width i.val) := by
    funext i
    exact FlatControlledShift.offset_eq r hden low high hnodup width i.val i.isLt
  unfold FlatControlledShift.bank RationalPrefixTranslationStream.state
  simp only [FlatControlledShift.initial_length,FlatControlledShift.source_eq,
    RationalPrefixTranslationStream.outputPrefix,FlatControlledShift.output_eq,hoff,word_length]
  rfl

/-- A complete concrete shift plus normalization. The result is back on the
common source tape, the output scratch is restored, both heads are rewound,
and the exact computed offset/prefix metadata remains explicitly retained. -/
theorem realizes_hoare {B : ℕ} (r : ℚ) (hden : r.den < radix)
    (low high : List (Fin (c+1))) (hfull : (low++0::high).Perm (List.finRange (c+1)))
    (width : Fin (c+1) → ℕ) (hB : 0 < B)
    (a : Fin (radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B)) → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ps : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^(width 0))
    (hp : Counter.value ps = radix^PrefixAddressData.widthSum (low++0::high) width)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cp : GrowingCounterData.Canonical ps)
    (hblank : ∀ z, q ≤ z → z < q+(word r low high width a).length → dest z = blank) :
    HoareTime (program r (low++0::high) (by simp))
      (fun v => v = FlatControlledShift.bank r (low++0::high) width a source dest p q bs qs ps 0)
      (fun v => v = output r low high width a source dest p q bs qs ps)
      ((863+4*c)*(radix^PrefixAddressData.widthSum (low++0::high) width*(radix^(width 0)*B))+26) := by
  have hs := (FlatControlledShift.realizes_hoare r hden low high hfull width hB a source dest p q bs qs ps
    hb hq hp cb cq cp).consequence (fun _ h => h) (fun _ h => h.1) le_rfl
  rw [stream_final r hden low high (hfull.nodup_iff.mpr (List.nodup_finRange _))] at hs
  have hn := normalize_hoare (putWord source p (List.ofFn a)) dest p q (word r low high width a)
    _ _ B bs qs ps
    (RationalPrefixTranslationStream.descriptor r (low++0::high) [] (FlatControlledShift.initial (radix := radix) width)
      (radix^PrefixAddressData.widthSum (low++0::high) width))
    (RationalPrefixTranslationStream.fields (low++0::high) (FlatControlledShift.initial (radix := radix) width)
      (radix^PrefixAddressData.widthSum (low++0::high) width))
    (word_length r low high width a) hb hq hp
    (pow_pos (Fact.out : radix.Prime).pos _) (pow_pos (Fact.out : radix.Prime).pos _) hB cb cq cp hblank
  apply (hs.seq hn).consequence (fun _ h => h) (fun _ h => h) _
  rw [word_length]
  ring_nf
  rfl

end IntegerMultBounds.Machine.FlatControlledShiftNormalize
