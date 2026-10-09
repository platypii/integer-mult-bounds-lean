import IntegerMultBounds.Machine.PackedOffsetPayloadValue

/-! Canonical Boolean-array handoff after the complete physical packed-offset
rotation. It can feed a subsequent binary field interchange without copying. -/
namespace IntegerMultBounds.Machine.PackedOffsetPayloadArray

theorem translated_map {α β : Type*} {P Q B : ℕ} (f : α → β)
    (a : Fin (P*(Q*B)) → α) (off : Fin P → ℕ) :
    (FiberLayoutData.translated a off).map f = FiberLayoutData.translated (fun i => f (a i)) off := by
  simp only [FiberLayoutData.translated,List.map_flatten,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext p
  simp [BlockRotationData.rotate,FiberLayoutData.fiber,List.map_flatten,List.map_append,
    List.map_drop,List.map_take,List.map_ofFn,Function.comp_def]

noncomputable def word (V : List Bool) (w n B : ℕ) (a : Fin (n*(2^w*B)) → Bool) : List Bool :=
  FiberLayoutData.translated (PackedOffsetPayload.view V w n B a)
    (fun i => StreamedFiberTranslation.offset (PackedOffsetStreamRaw.words V w n) i.val)

theorem word_length (V : List Bool) (w n B : ℕ) (a : Fin (n*(2^w*B)) → Bool) :
    (word V w n B a).length = n*(2^w*B) := by
  rw [word,FiberLayoutData.translated_length,PackedOffsetStreamRaw.words_length]

noncomputable def array (V : List Bool) (w n B : ℕ) (a : Fin (n*(2^w*B)) → Bool) :
    Fin (n*(2^w*B)) → Bool := fun i => (word V w n B a)[i.val]'(by rw [word_length]; exact i.isLt)

theorem array_word (V : List Bool) (w n B : ℕ) (a : Fin (n*(2^w*B)) → Bool) :
    List.ofFn (array V w n B a) = word V w n B a := by
  apply List.ext_getElem
  · simp [word_length]
  · intro i hi hj
    simp [array]

theorem result_word (V : List Bool) (w n B : ℕ) (a : Fin (n*(2^w*B)) → Bool) :
    PackedOffsetPayload.result V w n B a = List.ofFn (fun i => bitSymbol (array V w n B a i)) := by
  change _ = List.ofFn (bitSymbol ∘ array V w n B a)
  rw [← List.map_ofFn, array_word]
  exact (translated_map bitSymbol _ _).symm

/-- The returned canonical array has the actual machine's forward destination
semantics, retaining every suffix bit and allowing arbitrary dirty prefixes. -/
theorem array_entry (V : List Bool) (w n B : ℕ) (hV : V.length=n*w)
    (a : Fin (n*(2^w*B)) → Bool) (i : Fin n) (y : Fin (2^w)) (j : Fin B) :
    array V w n B a (FiberLayoutData.index i
      ⟨(y.val+PackedOffsetPayloadValue.offset V w i.val)%2^w,Nat.mod_lt _ (by positivity)⟩ j) =
      a (FiberLayoutData.index i y j) := by
  have hh := PackedOffsetPayloadValue.result_entry V w n B hV a i y j
  rw [result_word] at hh
  have hi : i.val*(2^w*B)+((y.val+PackedOffsetPayloadValue.offset V w i.val)%2^w)*B+j.val < n*(2^w*B) := by
    have h := (FiberLayoutData.index i
      (⟨(y.val+PackedOffsetPayloadValue.offset V w i.val)%2^w,Nat.mod_lt _ (by positivity)⟩ : Fin (2^w)) j).isLt
    simpa only [FiberLayoutData.index_val] using h
  simp only [List.getElem?_ofFn,hi,↓reduceDIte,Option.some.injEq] at hh
  have he : (⟨i.val*(2^w*B)+((y.val+PackedOffsetPayloadValue.offset V w i.val)%2^w)*B+j.val,hi⟩ : Fin (n*(2^w*B))) =
      FiberLayoutData.index i ⟨(y.val+PackedOffsetPayloadValue.offset V w i.val)%2^w,Nat.mod_lt _ (by positivity)⟩ j := by
    apply Fin.ext
    simp [FiberLayoutData.index_val]
  rw [he] at hh
  cases hl : array V w n B a _ <;> cases hr : a (FiberLayoutData.index i y j) <;>
    simp_all [bitSymbol,Fin.ext_iff]

end IntegerMultBounds.Machine.PackedOffsetPayloadArray
