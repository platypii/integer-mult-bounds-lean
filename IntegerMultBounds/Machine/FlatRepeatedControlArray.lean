import IntegerMultBounds.Machine.FlatRepeatedControlNormalize
import IntegerMultBounds.Machine.SharedPayload

/-! Canonical payload pair after heterogeneous repeated shift and normalization.
The complete prepared arithmetic/control bank remains explicit at both ends. -/
namespace IntegerMultBounds.Machine.FlatRepeatedControlArray
open FlatRepeatedControlShift
variable {radix N C B : ℕ} [Fact radix.Prime]

theorem translated_length (r : ℚ) (xs : List (Fin radix))
    (a : Fin (N*(C*(radix^xs.length*B))) → Fin 4) :
    (translated r xs a).length = N*(C*(radix^xs.length*B)) := by
  rw [← output_eq]
  exact RepeatedControlTranslationStream.output_length _ _ _ _ _ _ (payload_length a)

def array (r : ℚ) (xs : List (Fin radix))
    (a : Fin (N*(C*(radix^xs.length*B))) → Fin 4) : Fin (N*(C*(radix^xs.length*B))) → Fin 4 :=
  fun i => (translated r xs a)[i.val]'(by rw [translated_length]; exact i.isLt)

theorem array_word (r : ℚ) (xs : List (Fin radix))
    (a : Fin (N*(C*(radix^xs.length*B))) → Fin 4) : List.ofFn (array r xs a) = translated r xs a := by
  apply List.ext_getElem
  · simp [translated_length]
  · intro i hi hj; simp [array]

theorem array_entry (r : ℚ) (xs : List (Fin radix))
    (a : Fin (N*(C*(radix^xs.length*B))) → Fin 4)
    (i : Fin N) (c : Fin C) (y : Fin (radix^xs.length)) (j : Fin B) :
    array r xs a (finProdFinEquiv (i,FiberLayoutData.index c
      ⟨(y.val+FlatFixedControlShift.offset r (RationalTranslationStream.control xs i.val))%radix^xs.length,
        Nat.mod_lt _ (Nat.zero_lt_of_lt y.isLt)⟩ j)) =
      a (finProdFinEquiv (i,FiberLayoutData.index c y j)) := by
  have hh := FlatRepeatedControlShift.translated_entry r xs a i c y j
  obtain ⟨hi,hv⟩ := List.getElem?_eq_some_iff.mp hh
  have he : (finProdFinEquiv (i,FiberLayoutData.index c
      ⟨(y.val+FlatFixedControlShift.offset r (RationalTranslationStream.control xs i.val))%radix^xs.length,
        Nat.mod_lt _ (Nat.zero_lt_of_lt y.isLt)⟩ j)).val =
      i.val*(C*(radix^xs.length*B))+c.val*(radix^xs.length*B)+
        ((y.val+FlatFixedControlShift.offset r (RationalTranslationStream.control xs i.val))%radix^xs.length)*B+j.val := by
    simp [finProdFinEquiv,FiberLayoutData.index]
    ring
  simpa only [array,he] using hv

private theorem overwrite (f : ℤ → Fin 4) (p : ℤ) (xs ys : List (Fin 4)) (hlen : xs.length = ys.length) :
    putWord (putWord f p xs) p ys = putWord f p ys := by
  funext z
  by_cases hi : p ≤ z ∧ z < p+ys.length
  · let i := (z-p).toNat
    have he : p+(i : ℤ) = z := by dsimp [i]; omega
    have hb : i < ys.length := by dsimp [i]; omega
    rw [← he,WordSegments.get _ _ _ i hb,WordSegments.get _ _ _ i hb]
  · rw [putWord_outside _ p z ys (by omega),putWord_outside _ p z ys (by omega)]
    exact putWord_outside f p z xs (by omega)

def program (r : ℚ) := seq (RepeatedControlTranslationStream.program (radix := radix) r)
  FlatRepeatedControlNormalize.normalizeProgram

def output (r : ℚ) (xs : List (Fin radix))
    (a : Fin (N*(C*(radix^xs.length*B))) → Fin 4) (bs qs cs ns old : List Bool) :=
  FlatRepeatedControlNormalize.bank (putWord (fun _ => blank) 0 (List.ofFn (array r xs a)))
    (fun _ => blank) 0 0 bs qs cs ns (RationalTranslationStream.descriptor r old xs N)
    (RationalTranslationStream.control xs N)

private theorem stream_final (r : ℚ) (xs : List (Fin radix))
    (a : Fin (N*(C*(radix^xs.length*B))) → Fin 4) (bs qs cs ns old : List Bool) :
state r xs a bs qs cs ns old N =
      FlatRepeatedControlNormalize.bank (putWord (fun _ => blank) 0 (List.ofFn a))
        (putWord (fun _ => blank) 0 (translated r xs a))
        (0+(translated r xs a).length) (0+(translated r xs a).length) bs qs cs ns
        (RationalTranslationStream.descriptor r old xs N) (RationalTranslationStream.control xs N) := by
    unfold state RepeatedControlTranslationStream.state
    rw [source_eq,output_eq,translated_length]
    rfl

private theorem normalize_final (r : ℚ) (hN : 0 < N) (hB : 0 < B) (hC : 0 < C) (xs : List (Fin radix))
    (a : Fin (N*(C*(radix^xs.length*B))) → Fin 4) (bs qs cs ns old : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^xs.length)
    (hc : Counter.value cs = C) (hn : Counter.value ns = N)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cc : GrowingCounterData.Canonical cs) (cn : GrowingCounterData.Canonical ns)
    :
    HoareTime FlatRepeatedControlNormalize.normalizeProgram (fun v => v = state r xs a bs qs cs ns old N)
      (fun v => v = output r xs a bs qs cs ns old)
      (435*(N*(C*(radix^xs.length*B)))+2) := by
  have hh := FlatRepeatedControlNormalize.normalize_hoare (putWord (fun _ => blank) 0 (List.ofFn a))
    (fun _ => blank) 0 0 (translated r xs a) N C (radix^xs.length) B bs qs cs ns
    (RationalTranslationStream.descriptor r old xs N) (RationalTranslationStream.control xs N)
    (translated_length r xs a) hb hq hc hn hN hC (pow_pos (Fact.out : radix.Prime).pos _) hB
    cb cq cc cn (by intros; rfl)
  change HoareTime FlatRepeatedControlNormalize.normalizeProgram _ _ _ at hh
  rw [overwrite _ _ _ _ (by simp [translated_length]),← array_word] at hh
  rw [stream_final]
  unfold output
  rw [array_word]
  simpa only [array_word,translated_length] using hh

theorem realizes_hoare (r : ℚ) (hN : 0 < N) (hB : 0 < B) (hC : 0 < C) (xs : List (Fin radix))
    (a : Fin (N*(C*(radix^xs.length*B))) → Fin 4) (bs qs cs ns old : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = radix^xs.length)
    (hc : Counter.value cs = C) (hn : Counter.value ns = N)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cc : GrowingCounterData.Canonical cs) (cn : GrowingCounterData.Canonical ns)
    (cold : GrowingCounterData.Canonical old) (hold : Counter.value old < radix^xs.length) :
    HoareTime (program r) (fun v => v = state r xs a bs qs cs ns old 0)
      (fun v => v = output r xs a bs qs cs ns old)
      (1005*(N*(C*(radix^xs.length*B)))+26) := by
  have hs := FlatRepeatedControlShift.realizes_hoare r hB hC xs a bs qs cs ns old hb hq hc hn cb cq cc cn cold hold
  have hn := normalize_final r hN hB hC xs a bs qs cs ns old hb hq hc hn cb cq cc cn
  apply (hs.seq hn).consequence (fun _ h => h) (fun _ h => h) ?_
  omega

def pair (a : Fin N → Fin 4) : Tapes 2 radix := FlatArrayNormalize.pair
  (FlatRepeatedControlNormalize.encoded (putWord (fun _ => blank) 0 (List.ofFn a)))
  (FlatRepeatedControlNormalize.encoded (fun _ => blank)) 0 0

theorem input_payload (r : ℚ) (xs : List (Fin radix))
    (a : Fin (N*(C*(radix^xs.length*B))) → Fin 4) (bs qs cs ns old : List Bool) :
    SharedPayload.payload (state r xs a bs qs cs ns old 0) 10 11 = pair a := by
  unfold SharedPayload.payload
  rw [FlatRepeatedControlShift.source_tape]
  simp only [state,RepeatedControlTranslationStream.state,Nat.zero_mul,Nat.cast_zero,add_zero,
    RepeatedControlTranslationStream.outputPrefix,List.range_zero,List.map_nil,List.flatten_nil]
  rfl

theorem output_payload (r : ℚ) (xs : List (Fin radix))
    (a : Fin (N*(C*(radix^xs.length*B))) → Fin 4) (bs qs cs ns old : List Bool) :
    SharedPayload.payload (output r xs a bs qs cs ns old) 10 11 = pair (array r xs a) := rfl

end IntegerMultBounds.Machine.FlatRepeatedControlArray
