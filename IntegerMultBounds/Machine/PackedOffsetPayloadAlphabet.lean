import IntegerMultBounds.Machine.PackedOffsetPayloadArray
import IntegerMultBounds.Machine.PackedOffsetPayloadOriginal
import IntegerMultBounds.Machine.StreamedFiberTranslationAlphabet

/-! The original-header packed payload action on any larger fixed alphabet.
The output is the literal canonical Boolean array needed by binary swaps. -/
namespace IntegerMultBounds.Machine.PackedOffsetPayloadAlphabet
noncomputable section
open StreamedFiberTranslationAlphabet (encoding mapTape)
variable {a : ℕ}

def bank (payload offsets : ℤ → Fin (a+4)) (p s : ℤ) (bs ns ws : List Bool) : Tapes 17 a :=
  ⟨![0,0,0,0,0,1,0,0,0,0,p,0,0,0,1,1,s],
    ![(fun _ => blank),(fun _ => blank),(fun _ => blank),(fun _ => blank),(fun _ => blank),
      CountedLoopReuseAlphabet.binary bs,(fun _ => blank),(fun _ => blank),(fun _ => blank),(fun _ => blank),
      payload,(fun _ => blank),(fun _ => blank),(fun _ => blank),CountedLoopReuseAlphabet.binary ns,
      CountedLoopReuseAlphabet.binary ws,offsets]⟩

def program (a : ℕ) := Alphabet.program (encoding (a := a)) PackedOffsetPayloadOriginal.program

theorem mapped_bank (payload offsets : ℤ → Fin 4) (p s : ℤ) (bs ns ws : List Bool) :
    Alphabet.mapTapes (encoding (a := a)) (PackedOffsetPayloadOriginal.bank payload offsets p s bs ns ws) =
      bank (mapTape payload) (mapTape offsets) p s bs ns ws := by
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i <;> first | rfl | exact CountedLoopReuseAlphabet.encoding_binary _

theorem map_bits (f : ℤ → Fin 4) (p : ℤ) (xs : List Bool) :
    mapTape (a := a) (putWord f p (xs.map bitSymbol)) = putWord (mapTape f) p (xs.map bitSymbol) := by
  change RowPaddingConstructedAlphabet.mapTape (putWord f p (xs.map bitSymbol)) =
    putWord (RowPaddingConstructedAlphabet.mapTape f) p (xs.map bitSymbol)
  rw [RowPaddingConstructedAlphabet.map_putWord,List.map_map]
  congr 1

theorem map_array {n : ℕ} (f : ℤ → Fin 4) (p : ℤ) (x : Fin n → Bool) :
    mapTape (a := a) (putWord f p (List.ofFn (fun i => bitSymbol (x i)))) =
      putWord (mapTape f) p (List.ofFn (fun i => bitSymbol (x i))) := by
  change RowPaddingConstructedAlphabet.mapTape (putWord f p (List.ofFn (fun i => bitSymbol (x i)))) =
    putWord (RowPaddingConstructedAlphabet.mapTape f) p (List.ofFn (fun i => bitSymbol (x i)))
  rw [RowPaddingConstructedAlphabet.map_array_word]
  congr 1

/-- All generated controls, Q and work storage are blank on return; both
original heads survive. The larger alphabet adds no simulation overhead. -/
theorem runs (V : List Bool) (w n B : ℕ) (hV : V.length=n*w) (hB : 0 < B)
    (f g : ℤ → Fin 4) (p s : ℤ) (hf : f (p-1)=blank) (hg : g (s-1)=blank)
    (bs ns ws : List Bool) (hb : Counter.value bs=B) (hn : Counter.value ns=n) (hw : Counter.value ws=w)
    (cb : GrowingCounterData.Canonical bs) (cn : GrowingCounterData.Canonical ns)
    (cw : GrowingCounterData.Canonical ws) (x : Fin (n*(2^w*B)) → Bool) :
    HoareTime (program a)
      (fun z => z=bank (putWord (mapTape f) p (List.ofFn (fun i => bitSymbol (x i))))
        (putWord (mapTape g) s (V.map bitSymbol)) p s bs ns ws)
      (fun z => z=bank
        (putWord (mapTape f) p (List.ofFn (fun i => bitSymbol (PackedOffsetPayloadArray.array V w n B x i))))
        (putWord (mapTape g) s (V.map bitSymbol)) p s bs ns ws)
      ((FixedBasePowerDescriptor.constant 2+8)*2^w+600*(n*(2^w*B))+152) := by
  have hh := PackedOffsetPayloadOriginal.runs V w n B hV hB f g p s hf hg bs ns ws hb hn hw cb cn cw x
  rw [PackedOffsetPayloadArray.result_word] at hh
  have hm := Alphabet.map_hoare (encoding (a := a)) hh
  apply hm.consequence ?_ ?_ le_rfl
  · rintro z rfl
    refine ⟨_,rfl,?_⟩
    rw [mapped_bank,map_array,map_bits]
  · rintro z ⟨v,rfl,rfl⟩
    rw [mapped_bank,map_array,map_bits]

end
end IntegerMultBounds.Machine.PackedOffsetPayloadAlphabet
