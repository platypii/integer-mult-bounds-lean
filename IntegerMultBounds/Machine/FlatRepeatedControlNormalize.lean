import IntegerMultBounds.Machine.FlatRepeatedControlShift
import IntegerMultBounds.Machine.FlatHyperArrayNormalize

/-! Physical normalization of the recurring heterogeneous shift on its existing
20 tapes, with all four independent runtime dimensions retained. -/
namespace IntegerMultBounds.Machine.FlatRepeatedControlNormalize
variable {radix : ℕ}
open CountedLoopReuseAlphabet (empty binary)

def placement : Fin (10+10) ≃ Fin 20 where
  toFun := ![11,10,4,5,6,7,16,17,18,19,0,1,2,3,8,9,12,13,14,15]
  invFun := ![10,11,12,13,2,3,4,5,14,15,1,0,16,17,18,19,6,7,8,9]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def encoded (f : ℤ → Fin 4) : ℤ → Fin (radix+4) :=
  fun z => (RadixToBinary.binaryEncoding (q := radix)).encode (f z)

def bank (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs cs ns old : List Bool)
    (xs : List (Fin radix)) : Tapes 20 radix :=
  CountedLoopReuseAlphabet.bank
    (RepeatedControlTranslationExecution.bank source dest p q bs qs cs old xs) empty (binary ns) 1 1

theorem active_bank (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs cs ns old : List Bool)
    (xs : List (Fin radix)) :
    Placement.active placement (bank source dest p q bs qs cs ns old xs) =
      FlatHyperArrayNormalize.bank (encoded dest) (encoded source) q p bs qs cs ns := by
  unfold Placement.active placement
  congr 1 <;> funext i <;> fin_cases i <;> first
    | rfl
    | exact CountedLoopReuseAlphabet.encoding_empty
    | exact CountedLoopReuseAlphabet.encoding_binary _

private theorem extra_payload (u : Tapes 10 0) (v : Tapes 4 radix) (c n : Tapes 2 radix)
    (s d s' d' : ℤ → Fin 4) (p q p' q' : ℤ) :
    Placement.extra placement ((((Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix))
      (u.append (TranslationPreparedExecution.payload s d p q))).append v).append c).append n) =
    Placement.extra placement ((((Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix))
      (u.append (TranslationPreparedExecution.payload s' d' p' q'))).append v).append c).append n) := by
  unfold Placement.extra placement Tapes.append Alphabet.mapTapes
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem extra_bank (source dest source' dest' : ℤ → Fin 4) (p q p' q' : ℤ)
    (bs qs cs ns old : List Bool) (xs : List (Fin radix)) :
    Placement.extra placement (bank source dest p q bs qs cs ns old xs) =
      Placement.extra placement (bank source' dest' p' q' bs qs cs ns old xs) :=
  extra_payload _ _ _ _ _ _ _ _ _ _ _ _

def normalizeProgram : Program 20 198 radix := Placement.placed FlatHyperArrayNormalize.program placement

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

theorem normalize_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (word : List (Fin 4))
    (N C Q B : ℕ) (bs qs cs ns old : List Bool) (xs : List (Fin radix))
    (hlen : word.length = N*(C*(Q*B))) (hb : Counter.value bs = B) (hq : Counter.value qs = Q)
    (hc : Counter.value cs = C) (hn : Counter.value ns = N)
    (hN : 0 < N) (hC : 0 < C) (hQ : 0 < Q) (hB : 0 < B)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cc : GrowingCounterData.Canonical cs) (cn : GrowingCounterData.Canonical ns)
    (hblank : ∀ z, q ≤ z → z < q+word.length → dest z = blank) :
    HoareTime normalizeProgram
      (fun v => v = bank source (putWord dest q word) (p+word.length) (q+word.length) bs qs cs ns old xs)
      (fun v => v = bank (putWord source p word) dest p q bs qs cs ns old xs)
      (435*word.length+2) := by
  have hh := FlatHyperArrayNormalize.normalize_hoare (encoded (radix := radix) dest) (encoded source) q p
    (word.map (RadixToBinary.binaryEncoding (q := radix)).encode) N C Q B bs qs cs ns
    (by simpa using hlen) hb hq hc hn hN hC hQ hB cb cq cc cn
    (by intro z hz hz'; change (RadixToBinary.binaryEncoding (q := radix)).encode (dest z) = blank
        rw [hblank z hz (by simpa using hz')]; rfl)
  simp only [List.length_map,← encoded_word] at hh
  have hp := Placement.hoare_at hh placement
    (bank source (putWord dest q word) (p+word.length) (q+word.length) bs qs cs ns old xs)
    (active_bank _ _ _ _ _ _ _ _ _ _)
  apply hp.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [Placement.replace,extra_bank source (putWord dest q word) (putWord source p word) dest
    (p+word.length) (q+word.length) p q bs qs cs ns old xs,← active_bank]
  exact Placement.view _ _

end IntegerMultBounds.Machine.FlatRepeatedControlNormalize
