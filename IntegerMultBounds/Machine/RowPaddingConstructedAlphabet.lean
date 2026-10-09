import IntegerMultBounds.Machine.RowCropAny
import IntegerMultBounds.Machine.CountedLoopReuseAlphabet

/-! Concrete alphabet lift of the actual twelve-tape row pad/crop machine.
Encoded binary payload and backgrounds have literal target-cell endpoints;
every generated span is still physically constructed and erased. -/
namespace IntegerMultBounds.Machine.RowPaddingConstructedAlphabet
noncomputable section
variable {a : ℕ}

def encoding := CountedLoopReuseAlphabet.encoding a
def mapTape (f : ℤ → Fin 4) : ℤ → Fin (a+4) := fun z => (encoding (a := a)).encode (f z)
def mapArray {n : ℕ} (x : Fin n → Fin 4) : Fin n → Fin (a+4) := fun z => (encoding (a := a)).encode (x z)
def erased (f : ℤ → Fin (a+4)) (p : ℤ) (n : ℕ) : ℤ → Fin (a+4) :=
  fun z => if p ≤ z ∧ z < p+n then blank else f z

/-- Literal target bank: payload heads p/q; original P,R,R',L descriptors
at head one; all six work tapes wholly blank at head zero. -/
def bank (source dest : ℤ → Fin (a+4)) (p q : ℤ) (ps rs rps ls : List Bool) : Tapes 12 a :=
  ⟨(fun i => match i.val with
    | 0 => p | 1 => q | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 1 | _ => 0),
    (fun i => match i.val with
    | 0 => source | 1 => dest
    | 2 => CountedLoopReuseAlphabet.binary ps
    | 3 => CountedLoopReuseAlphabet.binary rs
    | 4 => CountedLoopReuseAlphabet.binary rps
    | 5 => CountedLoopReuseAlphabet.binary ls
    | _ => fun _ => blank)⟩

def program : Program 12 215 a := Alphabet.program encoding RowPaddingConstructed.program
def cropProgram : Program 12 215 a := Alphabet.program encoding RowPaddingConstructed.cropProgram

theorem mapped_bank (source dest : ℤ → Fin 4) (p q : ℤ) (ps rs rps ls : List Bool) :
    Alphabet.mapTapes (encoding (a := a)) (RowPaddingConstructed.bank source dest p q ps rs rps ls none none) =
      bank (mapTape source) (mapTape dest) p q ps rs rps ls := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact CountedLoopReuseAlphabet.encoding_binary _

theorem map_putWord (source : ℤ → Fin 4) (p : ℤ) (xs : List (Fin 4)) :
    mapTape (a := a) (putWord source p xs) =
      putWord (mapTape source) p (xs.map (encoding (a := a)).encode) := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    funext z
    by_cases hz : z=p
    · subst z
      simp only [mapTape,putWord,List.map_cons,Function.update_self]
    · simp only [mapTape,putWord,List.map_cons,Function.update_of_ne hz]
      exact congrFun (ih (p+1)) z

theorem map_array_word {n : ℕ} (source : ℤ → Fin 4) (p : ℤ) (x : Fin n → Fin 4) :
    mapTape (a := a) (putWord source p (List.ofFn x)) =
      putWord (mapTape source) p (List.ofFn (mapArray x)) := by
  rw [map_putWord,List.map_ofFn]
  rfl

theorem map_filled (source : ℤ → Fin 4) (p : ℤ) (n : ℕ) :
    mapTape (a := a) (CountedRawFill.filled source p n blank) = erased (mapTape source) p n := by
  funext z
  unfold mapTape CountedRawFill.filled erased
  split_ifs <;> rfl

/-- Padding commutes with the concrete four-symbol embedding, including
its inserted binary zero cells. -/
theorem pad_encoding (P R R' L : ℕ) (x : Fin (P*R*L) → Fin 4) :
    mapArray (a := a) (RecursiveRowPadding.pad R' (bitSymbol false) x) =
      RecursiveRowPadding.pad R' (bitSymbol false) (mapArray x) := by
  funext z
  unfold mapArray RecursiveRowPadding.pad
  dsimp only
  split_ifs <;> rfl

theorem crop_encoding (P R R' L : ℕ) (hR : R ≤ R') (x : Fin (P*R'*L) → Fin 4) :
    mapArray (a := a) (RecursiveRowPadding.crop hR x) = RecursiveRowPadding.crop hR (mapArray x) := rfl

private theorem map_exact {s k cost : ℕ} {M : Program s k 0} {v w : Tapes s 0}
    (h : HoareTime M (fun x => x = v) (fun x => x = w) cost) :
    HoareTime (Alphabet.program (encoding (a := a)) M)
      (fun x => x = Alphabet.mapTapes encoding v) (fun x => x = Alphabet.mapTapes encoding w) cost := by
  apply (Alphabet.map_hoare encoding h).consequence _ _ le_rfl
  · rintro x rfl; exact ⟨_,rfl,rfl⟩
  · rintro x ⟨original,rfl,rfl⟩; rfl

/-- The original machine really pads the encoded array on the larger
alphabet, erasing its source interval and retaining the four input headers. -/
theorem pad_array_hoare (source dest : ℤ → Fin 4) (p q : ℤ)
    (ps rs rps ls : List Bool) (P R R' L : ℕ) (x : Fin (P*R*L) → Fin 4)
    (hp : Counter.value ps = P) (hr : Counter.value rs = R) (hrp : Counter.value rps = R')
    (hl : Counter.value ls = L) (cp : GrowingCounterData.Canonical ps)
    (cr : GrowingCounterData.Canonical rs) (crp : GrowingCounterData.Canonical rps)
    (cl : GrowingCounterData.Canonical ls) (hP : 0 < P) (hRpos : 0 < R)
    (hR : R ≤ R') (hL : 0 < L) :
    HoareTime (program (a := a))
      (fun v => v = bank (putWord (mapTape source) p (List.ofFn (mapArray x))) (mapTape dest) p q ps rs rps ls)
      (fun v => v = bank (erased (putWord (mapTape source) p (List.ofFn (mapArray x))) p (P*R*L))
        (putWord (mapTape dest) q (List.ofFn (RecursiveRowPadding.pad R' (bitSymbol false) (mapArray x))))
        p q ps rs rps ls) (413*P*(R'*L)) := by
  have h := map_exact (a := a) (RowPaddingConstructed.pad_array_hoare source dest p q ps rs rps ls P R R' L x
    hp hr hrp hl cp cr crp cl hP hRpos hR hL)
  simp only [mapped_bank,map_filled,map_array_word] at h
  rw [pad_encoding P R R' L x] at h
  exact h

/-- Cropping accepts arbitrary encoded contents in the discarded rows; the
same real inverse machine erases every consumed cell and writes exact crop. -/
theorem crop_array_hoare (source dest : ℤ → Fin 4) (p q : ℤ)
    (ps rs rps ls : List Bool) (P R R' L : ℕ) (x : Fin (P*R'*L) → Fin 4)
    (hp : Counter.value ps = P) (hr : Counter.value rs = R) (hrp : Counter.value rps = R')
    (hl : Counter.value ls = L) (cp : GrowingCounterData.Canonical ps)
    (cr : GrowingCounterData.Canonical rs) (crp : GrowingCounterData.Canonical rps)
    (cl : GrowingCounterData.Canonical ls) (hP : 0 < P) (hRpos : 0 < R)
    (hR : R ≤ R') (hL : 0 < L) :
    HoareTime (cropProgram (a := a))
      (fun v => v = bank (putWord (mapTape source) p (List.ofFn (mapArray x))) (mapTape dest) p q ps rs rps ls)
      (fun v => v = bank (erased (putWord (mapTape source) p (List.ofFn (mapArray x))) p (P*R'*L))
        (putWord (mapTape dest) q (List.ofFn (RecursiveRowPadding.crop hR (mapArray x))))
        p q ps rs rps ls) (413*P*(R'*L)) := by
  have h := map_exact (a := a) (RowCropAny.constructed_array_hoare source dest p q ps rs rps ls P R R' L x
    hp hr hrp hl cp cr crp cl hP hRpos hR hL)
  simp only [mapped_bank,map_filled,map_array_word] at h
  rw [crop_encoding P R R' L hR x] at h
  exact h

/-- Encoding a bit-array yields literal binary cells in the target alphabet. -/
theorem map_bits {n : ℕ} (x : Fin n → Bool) :
    mapArray (a := a) (fun z => bitSymbol (x z)) = fun z => bitSymbol (x z) := by
  funext z
  unfold mapArray
  dsimp only
  cases x z <;> rfl

/-- If the source interval had a blank background, complete physical erasure
recovers that exact background, including all symbols outside the interval. -/
theorem erased_array_word {n : ℕ} (source : ℤ → Fin 4) (p : ℤ) (x : Fin n → Fin 4)
    (hb : ∀ z, p ≤ z → z < p+n → source z = blank) :
    erased (putWord (mapTape (a := a) source) p (List.ofFn (mapArray x))) p n = mapTape source := by
  have h := CountedRawFill.erased_word source p (List.ofFn x) (by simpa only [List.length_ofFn] using hb)
  have hh := congrArg (mapTape (a := a)) h
  simpa only [map_filled,map_array_word,List.length_ofFn] using hh

/-- Literal binary-cell specialization for direct composition on the target alphabet. -/
theorem pad_bits_hoare (source dest : ℤ → Fin 4) (p q : ℤ)
    (ps rs rps ls : List Bool) (P R R' L : ℕ) (x : Fin (P*R*L) → Bool)
    (hp : Counter.value ps = P) (hr : Counter.value rs = R) (hrp : Counter.value rps = R')
    (hl : Counter.value ls = L) (cp : GrowingCounterData.Canonical ps)
    (cr : GrowingCounterData.Canonical rs) (crp : GrowingCounterData.Canonical rps)
    (cl : GrowingCounterData.Canonical ls) (hP : 0 < P) (hRpos : 0 < R)
    (hR : R ≤ R') (hL : 0 < L) :
    HoareTime (program (a := a))
      (fun v => v = bank (putWord (mapTape source) p (List.ofFn (fun z => bitSymbol (x z)))) (mapTape dest) p q ps rs rps ls)
      (fun v => v = bank (erased (putWord (mapTape source) p (List.ofFn (fun z => bitSymbol (x z)))) p (P*R*L))
        (putWord (mapTape dest) q (List.ofFn (RecursiveRowPadding.pad R' (bitSymbol false) (fun z => bitSymbol (x z)))))
        p q ps rs rps ls) (413*P*(R'*L)) := by
  have h := pad_array_hoare (a := a) source dest p q ps rs rps ls P R R' L (fun z => bitSymbol (x z))
    hp hr hrp hl cp cr crp cl hP hRpos hR hL
  simpa only [map_bits] using h

/-- Literal binary-cell specialization for direct composition on the target alphabet. -/
theorem crop_bits_hoare (source dest : ℤ → Fin 4) (p q : ℤ)
    (ps rs rps ls : List Bool) (P R R' L : ℕ) (x : Fin (P*R'*L) → Bool)
    (hp : Counter.value ps = P) (hr : Counter.value rs = R) (hrp : Counter.value rps = R')
    (hl : Counter.value ls = L) (cp : GrowingCounterData.Canonical ps)
    (cr : GrowingCounterData.Canonical rs) (crp : GrowingCounterData.Canonical rps)
    (cl : GrowingCounterData.Canonical ls) (hP : 0 < P) (hRpos : 0 < R)
    (hR : R ≤ R') (hL : 0 < L) :
    HoareTime (cropProgram (a := a))
      (fun v => v = bank (putWord (mapTape source) p (List.ofFn (fun z => bitSymbol (x z)))) (mapTape dest) p q ps rs rps ls)
      (fun v => v = bank (erased (putWord (mapTape source) p (List.ofFn (fun z => bitSymbol (x z)))) p (P*R'*L))
        (putWord (mapTape dest) q (List.ofFn (RecursiveRowPadding.crop hR (fun z => bitSymbol (x z)))))
        p q ps rs rps ls) (413*P*(R'*L)) := by
  have h := crop_array_hoare (a := a) source dest p q ps rs rps ls P R R' L (fun z => bitSymbol (x z))
    hp hr hrp hl cp cr crp cl hP hRpos hR hL
  simpa only [map_bits] using h

end
end IntegerMultBounds.Machine.RowPaddingConstructedAlphabet
