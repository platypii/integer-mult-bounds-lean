import IntegerMultBounds.Machine.StreamedFiberTranslation
import IntegerMultBounds.Machine.FlatControlledShift

/-! Exact flat-array destinations for the actual literal-control-stream
machine. Every suffix bit is carried intact to its offset back coordinate. -/
namespace IntegerMultBounds.Machine.StreamedFiberTranslationArray
open StreamedFiberTranslation (offset)

def bank (ws : List (List Bool)) (Q B : ℕ) (source dest control : ℤ → Fin 4)
    (p q r : ℤ) (bs qs ns : List Bool) (a : Fin (ws.length*(Q*B)) → Fin 4) (i : ℕ) : Tapes 15 0 :=
  CountedLoopReuse.bank
    (StreamedFiberTranslation.state ws Q B source dest control p q r bs qs (FlatControlledShift.payload a) i)
    CountedCopyReuse.empty (CountedCopyReuse.binary ns) 1 1

/-- One fixed machine moves an arbitrary array using the supplied literal
offset words in prefix order. Zero offsets and an empty prefix family work. -/
theorem runs (ws : List (List Bool)) (Q B : ℕ) (hQ : 0 < Q) (hB : 0 < B)
    (source dest control : ℤ → Fin 4) (p q r : ℤ) (bs qs ns : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (hn : Counter.value ns = ws.length)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns)
    (hc : ∀ xs ∈ ws, GrowingCounterData.Canonical xs) (hv : ∀ xs ∈ ws, Counter.value xs ≤ Q)
    (a : Fin (ws.length*(Q*B)) → Fin 4) :
    HoareTime StreamedFiberTranslation.program
      (fun v => v = bank ws Q B source dest control p q r bs qs ns a 0)
      (fun v => v = bank ws Q B source dest control p q r bs qs ns a ws.length)
      (481*(ws.length*(Q*B))+23) :=
  StreamedFiberTranslation.runs ws Q B hQ hB source dest control p q r bs qs ns hb hq hn cb cq cn hc hv
    (FlatControlledShift.payload a) (FlatControlledShift.payload_length a)

theorem source_tape (ws : List (List Bool)) (Q B : ℕ) (source dest control : ℤ → Fin 4)
    (p q r : ℤ) (bs qs ns : List Bool) (a : Fin (ws.length*(Q*B)) → Fin 4) (i : ℕ) :
    (bank ws Q B source dest control p q r bs qs ns a i).tape 10 = putWord source p (List.ofFn a) := by
  change putWord source p (TranslationStream.fibers Q ws.length (FlatControlledShift.payload a)).flatten = _
  rw [FlatControlledShift.source_eq]

theorem destination_tape (ws : List (List Bool)) (Q B : ℕ) (source dest control : ℤ → Fin 4)
    (p q r : ℤ) (bs qs ns : List Bool) (a : Fin (ws.length*(Q*B)) → Fin 4) :
    (bank ws Q B source dest control p q r bs qs ns a ws.length).tape 11 =
      putWord dest q (FiberLayoutData.translated a (fun i => offset ws i.val)) := by
  change putWord dest q (TranslationPreparedFamily.outputPrefix (offset ws) Q ws.length
    (FlatControlledShift.payload a)) = _
  rw [FlatControlledShift.output_eq]

/-- The symbol at prefix i, back address y, suffix j reaches back address
y+offset(i) modulo Q. Dirty prefix and complete suffix coordinates survive. -/
theorem destination_entry (ws : List (List Bool)) (Q B : ℕ) (source dest control : ℤ → Fin 4)
    (p q r : ℤ) (bs qs ns : List Bool) (a : Fin (ws.length*(Q*B)) → Fin 4)
    (i : Fin ws.length) (y : Fin Q) (j : Fin B) :
    (bank ws Q B source dest control p q r bs qs ns a ws.length).tape 11
      (q+((i.val*(Q*B)+((y.val+offset ws i.val)%Q)*B+j.val : ℕ) : ℤ)) =
      a (FiberLayoutData.index i y j) := by
  rw [destination_tape]
  have he := FiberLayoutData.translated_entry a (fun i => offset ws i.val) i y j
  obtain ⟨hi,hv⟩ := List.getElem?_eq_some_iff.mp he
  rw [WordSegments.get _ _ _ _ hi,hv]

theorem control_tape (ws : List (List Bool)) (Q B : ℕ) (source dest control : ℤ → Fin 4)
    (p q r : ℤ) (bs qs ns : List Bool) (a : Fin (ws.length*(Q*B)) → Fin 4) (i : ℕ) :
    (bank ws Q B source dest control p q r bs qs ns a i).tape 12 =
      putWord control r (StreamedFiberTranslation.encoded ws) := rfl

theorem output_heads (ws : List (List Bool)) (Q B : ℕ) (source dest control : ℤ → Fin 4)
    (p q r : ℤ) (bs qs ns : List Bool) (a : Fin (ws.length*(Q*B)) → Fin 4) :
    (bank ws Q B source dest control p q r bs qs ns a ws.length).head 10 = p+((ws.length*(Q*B) : ℕ) : ℤ) ∧
    (bank ws Q B source dest control p q r bs qs ns a ws.length).head 11 = q+((ws.length*(Q*B) : ℕ) : ℤ) ∧
    (bank ws Q B source dest control p q r bs qs ns a ws.length).head 12 =
      r+(StreamedFiberTranslation.encoded ws).length := by
  refine ⟨rfl,rfl,?_⟩
  change StreamedFiberTranslation.cursor ws r ws.length = _
  simp [StreamedFiberTranslation.cursor]

end IntegerMultBounds.Machine.StreamedFiberTranslationArray
