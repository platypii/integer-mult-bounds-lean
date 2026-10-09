import IntegerMultBounds.Machine.PackedOffsetPayload

/-! Address semantics of the complete packed-offset payload machine. The
offset of each prefix is the value of its actual w-bit packed input block. -/
namespace IntegerMultBounds.Machine.PackedOffsetPayloadValue
open PackedOffsetPayload

def offset (V : List Bool) (w i : ℕ) : ℕ := Counter.value (Gather.field V (i*w) w)

theorem offset_eq (V : List Bool) (w n i : ℕ) (hV : V.length=n*w) (hi : i<n) :
    StreamedFiberTranslation.offset (PackedOffsetStreamRaw.words V w n) i = offset V w i := by
  have hiw : i < (PackedOffsetStreamRaw.words V w n).length := by
    rw [PackedOffsetStreamRaw.words_length]; exact hi
  have hh := PackedOffsetStreamRaw.words_values V w n hV
  rw [Compact.PowerTwo.digits_blocks V w n hV] at hh
  have hg := congrArg (fun xs : List ℤ => xs[i]?) hh
  simp [List.getElem?_map,List.getElem?_eq_getElem hiw,Compact.PowerTwo.blockValues,hi] at hg
  dsimp only [StreamedFiberTranslation.offset,offset]
  rw [List.getElem?_eq_getElem hiw,Option.getD_some]
  exact_mod_cast hg

theorem result_length (V : List Bool) (w n B : ℕ) (a : Fin (n*(2^w*B)) → Bool) :
    (result V w n B a).length = n*(2^w*B) := by
  rw [result,FiberLayoutData.translated_length,PackedOffsetStreamRaw.words_length]

/-- Complete suffix records retain every bit, and each prefix fiber translates
by the corresponding packed control block modulo its back-field range. -/
theorem result_entry (V : List Bool) (w n B : ℕ) (hV : V.length=n*w)
    (a : Fin (n*(2^w*B)) → Bool) (i : Fin n) (y : Fin (2^w)) (j : Fin B) :
    (result V w n B a)[i.val*(2^w*B)+((y.val+offset V w i.val)%2^w)*B+j.val]? =
      some (bitSymbol (a (FiberLayoutData.index i y j))) := by
  let i' : Fin (PackedOffsetStreamRaw.words V w n).length :=
    Fin.cast (PackedOffsetStreamRaw.words_length V w n).symm i
  have hh := FiberLayoutData.translated_entry (fun z => (bitSymbol (view V w n B a z) : Fin 4))
    (fun k => StreamedFiberTranslation.offset (PackedOffsetStreamRaw.words V w n) k.val) i' y j
  have he : view V w n B a (FiberLayoutData.index i' y j) = a (FiberLayoutData.index i y j) := by
    unfold view
    congr 1
  rw [he] at hh
  simpa only [i',Fin.val_cast,offset_eq V w n i.val hV i.isLt,result] using hh

/-- Actual returned tape cell, after stream erasure and restoration of both
caller heads. The offset source and every private tape are already covered
by PackedOffsetPayload.runs' exact whole-bank postcondition. -/
theorem returned_cell (V : List Bool) (w n B : ℕ) (hV : V.length=n*w)
    (f g : ℤ → Fin 4) (p s : ℤ) (bs qs ns ws : List Bool)
    (a : Fin (n*(2^w*B)) → Bool) (i : Fin n) (y : Fin (2^w)) (j : Fin B) :
    (bank (putWord f p (result V w n B a)) (fun _ => blank) (putWord g s (V.map bitSymbol))
      p 0 s bs qs ns ws).tape 10
      (p+((i.val*(2^w*B)+((y.val+offset V w i.val)%2^w)*B+j.val : ℕ) : ℤ)) =
      bitSymbol (a (FiberLayoutData.index i y j)) := by
  change putWord f p (result V w n B a) _ = _
  obtain ⟨hi,hv⟩ := List.getElem?_eq_some_iff.mp (result_entry V w n B hV a i y j)
  rw [WordSegments.get _ _ _ _ hi,hv]

end IntegerMultBounds.Machine.PackedOffsetPayloadValue
