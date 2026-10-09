import IntegerMultBounds.Machine.StreamedFiberTranslationArray
import IntegerMultBounds.Machine.CountedLoopReuseAlphabet
import IntegerMultBounds.Machine.RowPaddingConstructedAlphabet

/-! Literal binary payload rotations on any larger finite alphabet. This
embeds the actual four-symbol streamed reader/rotation machine, preserving its
runtime and exact cell semantics. Marked-workspace inputs and the retained final
offset remain explicit; this lift does not assume free initialization or reset.
-/
namespace IntegerMultBounds.Machine.StreamedFiberTranslationAlphabet
noncomputable section
variable {a : ℕ}

def encoding := CountedLoopReuseAlphabet.encoding a
def mapTape (f : ℤ → Fin 4) : ℤ → Fin (a+4) := fun z => (encoding (a := a)).encode (f z)
def program (a : ℕ) : Program 15 243 a :=
  Alphabet.program (encoding (a := a)) StreamedFiberTranslation.program

def bank (ws : List (List Bool)) (Q B : ℕ) (source dest control : ℤ → Fin 4)
    (p q r : ℤ) (bs qs ns : List Bool) (x : Fin (ws.length*(Q*B)) → Fin 4) (i : ℕ) : Tapes 15 a :=
  Alphabet.mapTapes encoding
    (StreamedFiberTranslationArray.bank ws Q B source dest control p q r bs qs ns x i)

private theorem map_exact {t s cost : ℕ} {M : Program t s 0} {v w : Tapes t 0}
    (h : HoareTime M (fun x => x = v) (fun x => x = w) cost) :
    HoareTime (Alphabet.program (encoding (a := a)) M)
      (fun x => x = Alphabet.mapTapes encoding v) (fun x => x = Alphabet.mapTapes encoding w) cost := by
  apply (Alphabet.map_hoare encoding h).consequence _ _ le_rfl
  · rintro x rfl; exact ⟨_,rfl,rfl⟩
  · rintro x ⟨original,rfl,rfl⟩; rfl

/-- The lifted finite-control program still reads every literal offset and
executes every physical payload movement, with the same charged runtime. -/
theorem runs (ws : List (List Bool)) (Q B : ℕ) (hQ : 0 < Q) (hB : 0 < B)
    (source dest control : ℤ → Fin 4) (p q r : ℤ) (bs qs ns : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (hn : Counter.value ns = ws.length)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns)
    (hc : ∀ xs ∈ ws, GrowingCounterData.Canonical xs) (hv : ∀ xs ∈ ws, Counter.value xs ≤ Q)
    (x : Fin (ws.length*(Q*B)) → Fin 4) :
    HoareTime (program a)
      (fun v => v = bank ws Q B source dest control p q r bs qs ns x 0)
      (fun v => v = bank ws Q B source dest control p q r bs qs ns x ws.length)
      (481*(ws.length*(Q*B))+23) :=
  map_exact (StreamedFiberTranslationArray.runs ws Q B hQ hB source dest control
    p q r bs qs ns hb hq hn cb cq cn hc hv x)

theorem source_tape (ws : List (List Bool)) (Q B : ℕ) (source dest control : ℤ → Fin 4)
    (p q r : ℤ) (bs qs ns : List Bool) (x : Fin (ws.length*(Q*B)) → Fin 4) (i : ℕ) :
    (bank (a := a) ws Q B source dest control p q r bs qs ns x i).tape 10 =
      putWord (mapTape source) p (List.ofFn fun j => (encoding (a := a)).encode (x j)) := by
  change (fun z => (encoding (a := a)).encode
    ((StreamedFiberTranslationArray.bank ws Q B source dest control p q r bs qs ns x i).tape 10 z)) = _
  rw [StreamedFiberTranslationArray.source_tape]
  exact RowPaddingConstructedAlphabet.map_array_word source p x

/-- A literal bit survives the lifted physical permutation unchanged. -/
theorem destination_bit (ws : List (List Bool)) (Q B : ℕ) (source dest control : ℤ → Fin 4)
    (p q r : ℤ) (bs qs ns : List Bool) (x : Fin (ws.length*(Q*B)) → Bool)
    (i : Fin ws.length) (y : Fin Q) (j : Fin B) :
    (bank (a := a) ws Q B source dest control p q r bs qs ns (fun k => bitSymbol (x k)) ws.length).tape 11
      (q+((i.val*(Q*B)+((y.val+StreamedFiberTranslation.offset ws i.val)%Q)*B+j.val : ℕ) : ℤ)) =
      bitSymbol (x (FiberLayoutData.index i y j)) := by
  change (encoding (a := a)).encode (_ : Fin 4) = _
  rw [StreamedFiberTranslationArray.destination_entry]
  cases x (FiberLayoutData.index i y j) <;> rfl

/-- The complete original offset stream is retained, including delimiters. -/
theorem control_tape (ws : List (List Bool)) (Q B : ℕ) (source dest control : ℤ → Fin 4)
    (p q r : ℤ) (bs qs ns : List Bool) (x : Fin (ws.length*(Q*B)) → Fin 4) (i : ℕ) :
    (bank (a := a) ws Q B source dest control p q r bs qs ns x i).tape 12 =
      putWord (mapTape control) r ((StreamedFiberTranslation.encoded ws).map (encoding (a := a)).encode) := by
  change mapTape ((StreamedFiberTranslationArray.bank ws Q B source dest control p q r bs qs ns x i).tape 12) = _
  rw [StreamedFiberTranslationArray.control_tape]
  exact RowPaddingConstructedAlphabet.map_putWord control r (StreamedFiberTranslation.encoded ws)

/-- The three supplied numeric descriptors remain literal binary words. -/
theorem original_headers (ws : List (List Bool)) (Q B : ℕ) (source dest control : ℤ → Fin 4)
    (p q r : ℤ) (bs qs ns : List Bool) (x : Fin (ws.length*(Q*B)) → Fin 4) (i : ℕ) :
    (bank (a := a) ws Q B source dest control p q r bs qs ns x i).tape 5 = CountedLoopReuseAlphabet.binary bs ∧
    (bank (a := a) ws Q B source dest control p q r bs qs ns x i).tape 7 = CountedLoopReuseAlphabet.binary qs ∧
    (bank (a := a) ws Q B source dest control p q r bs qs ns x i).tape 14 = CountedLoopReuseAlphabet.binary ns := by
  exact ⟨CountedLoopReuseAlphabet.encoding_binary bs,
    CountedLoopReuseAlphabet.encoding_binary qs, CountedLoopReuseAlphabet.encoding_binary ns⟩

end
end IntegerMultBounds.Machine.StreamedFiberTranslationAlphabet
