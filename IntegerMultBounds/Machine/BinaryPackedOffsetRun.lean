import IntegerMultBounds.Machine.BinaryPackedOffsetData
import IntegerMultBounds.Machine.PackedOffsetPayloadPlaced

/-! A real swap/packed back rotation/swap on shared caller tapes. Both private
banks are physically cleaned between uses and every sequencing step is paid. -/
namespace IntegerMultBounds.Machine.BinaryPackedOffsetRun
noncomputable section
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
open BinaryAdjacentWidthHeadersShared (Sources)
open BinaryPackedFieldSwap (store)
open BinaryPackedOffsetData (rows asFiber fromFiber back result)
variable {t : ℕ}

abbrev count := BinaryRadixEqualShared.count

def liftFocus (focus : Fin 5 → Fin t) : Fin 5 → Fin (t+count) := fun i => Fin.castAdd count (focus i)

theorem lift_injective (focus : Fin 5 → Fin t) (hf : Function.Injective focus) :
    Function.Injective (liftFocus focus) := by
  intro i j he
  exact hf (Fin.castAdd_injective _ _ he)

def input (caller : Tapes t prime) :=
  (BinaryRadixEqualShared.input caller).append (FixedHeaderBankCopy.empty 12)

def swap (headers : Fin 4 → Fin t) (payload : Fin t) :=
  extend (BinaryPackedFieldSwap.program headers payload) 12

def rotate (focus : Fin 5 → Fin t) (hf : Function.Injective focus) :=
  PackedOffsetPayloadPlaced.program prime (liftFocus focus) (lift_injective focus hf)

def program (headers : Fin 4 → Fin t) (focus : Fin 5 → Fin t) (hf : Function.Injective focus) :=
  seq (seq (swap headers (focus 0)) (rotate focus hf)) (swap headers (focus 0))

def rotationCost (P w G B : ℕ) :=
  (FixedBasePowerDescriptor.constant 2+8)*2^w+600*(rows P w G*(2^w*B))+152

theorem asFiber_word (P w G B : ℕ) (x : Fin (RadixRangePadding.volume P (2^w) G B) → Bool) :
    putWord (StreamedFiberTranslationAlphabet.mapTape (fun _ => blank)) 0
      (List.ofFn (fun i => bitSymbol (asFiber x i))) =
      BinaryRadixRangePrepareAlphabet.word (fun i => (bitSymbol (x i) : Fin (prime+4))) := by
  unfold asFiber
  rw [BinaryPackedOffsetData.word_cast (BinaryPackedOffsetData.size P w G B)]
  rfl

theorem array_word (P w G B : ℕ) (V : List Bool)
    (x : Fin (RadixRangePadding.volume P (2^w) G B) → Bool) :
    putWord (StreamedFiberTranslationAlphabet.mapTape (fun _ => blank)) 0
      (List.ofFn (fun i => bitSymbol (PackedOffsetPayloadArray.array V w (rows P w G) B (asFiber x) i))) =
      BinaryRadixRangePrepareAlphabet.word (fun i => (bitSymbol (back V P w G B x i) : Fin (prime+4))) := by
  have hh := asFiber_word P w G B (back V P w G B x)
  rw [back,BinaryPackedOffsetData.asFiber_fromFiber] at hh
  exact hh

/-- The actual placed rotation sees the same caller tapes, while the cleaned
interchange bank is retained as a full complementary frame. -/
theorem rotates (caller : Tapes t prime) (focus : Fin 5 → Fin t) (hfocus : Function.Injective focus)
    (V : List Bool) (P w G B : ℕ) (hV : V.length=rows P w G*w) (hB : 0 < B)
    (g : ℤ → Fin 4) (s : ℤ) (hg : g (s-1)=blank) (bs ns ws : List Bool)
    (hb : Counter.value bs=B) (hn : Counter.value ns=rows P w G) (hw : Counter.value ws=w)
    (cb : GrowingCounterData.Canonical bs) (cn : GrowingCounterData.Canonical ns)
    (cw : GrowingCounterData.Canonical ws)
    (x : Fin (RadixRangePadding.volume P (2^w) G B) → Bool)
    (ht : ∀ i, i≠0 → caller.tape (focus i)=PackedOffsetPayloadPlaced.tapes
      (fun _ => blank) (putWord (StreamedFiberTranslationAlphabet.mapTape g) s (V.map bitSymbol)) bs ns ws i)
    (hh : ∀ i, i≠0 → caller.head (focus i)=PackedOffsetPayloadPlaced.heads 0 s i) :
    HoareTime (rotate focus hfocus)
      (fun z => z=input (store caller (focus 0) x))
      (fun z => z=input (store caller (focus 0) (back V P w G B x)))
      (rotationCost P w G B) := by
  have hp := PackedOffsetPayloadPlaced.runs
    (BinaryRadixEqualShared.input (store caller (focus 0) x)) (liftFocus focus) (lift_injective focus hfocus)
    V w (rows P w G) B hV hB (fun _ => blank) g 0 s rfl hg bs ns ws hb hn hw cb cn cw (asFiber x)
    (by
      intro i
      simp only [BinaryRadixEqualShared.input,liftFocus,Tapes.append,Fin.addCases_left]
      by_cases hi : i=0
      · subst i
        simpa only [store,setTape,Function.update_self,PackedOffsetPayloadPlaced.tapes,
          Matrix.cons_val_zero] using (asFiber_word P w G B x).symm
      · have he : focus i≠focus 0 := fun he => hi (hfocus he)
        simp only [store,setTape,Function.update_of_ne he]
        have hi' := ht i hi
        fin_cases i <;> first | contradiction | exact hi')
    (by
      intro i
      simp only [BinaryRadixEqualShared.input,liftFocus,Tapes.append,Fin.addCases_left]
      by_cases hi : i=0
      · subst i
        simp only [store,setTape,Function.update_self,PackedOffsetPayloadPlaced.heads,
          Matrix.cons_val_zero]
      · have he : focus i≠focus 0 := fun he => hi (hfocus he)
        simp only [store,setTape,Function.update_of_ne he]
        exact hh i hi)
  refine hp.consequence (fun _ h => h) ?_ le_rfl
  intro z hz
  rw [hz,array_word]
  change (setTape ((store caller (focus 0) x).append _) (Fin.castAdd count (focus 0)) _ 0).append _ = _
  rw [SharedPlacementAlphabet.setTape_append_left,store,SharedPlacementAlphabet.setTape_setTape]
  rfl

/-- Three real machine calls, with all caller headers and packed source retained.
This theorem has no preparation callback or free payload permutation. -/
theorem runs (caller : Tapes t prime) (headers : Fin 4 → Fin t)
    (focus : Fin 5 → Fin t) (hfocus : Function.Injective focus)
    (V : List Bool) (P w G B : ℕ) (hV : V.length=rows P w G*w)
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=BinaryRadixRangePrepare.values P G B w i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hne : ∀ i, headers i≠focus 0) (hsrc : Sources caller headers hs)
    (g : ℤ → Fin 4) (s : ℤ) (hg : g (s-1)=blank) (bs ns ws : List Bool)
    (hb : Counter.value bs=B) (hn : Counter.value ns=rows P w G) (hw : Counter.value ws=w)
    (cb : GrowingCounterData.Canonical bs) (cn : GrowingCounterData.Canonical ns)
    (cw : GrowingCounterData.Canonical ws)
    (ht : ∀ i, i≠0 → caller.tape (focus i)=PackedOffsetPayloadPlaced.tapes
      (fun _ => blank) (putWord (StreamedFiberTranslationAlphabet.mapTape g) s (V.map bitSymbol)) bs ns ws i)
    (hh : ∀ i, i≠0 → caller.head (focus i)=PackedOffsetPayloadPlaced.heads 0 s i)
    (x : Fin (RadixRangePadding.volume P (2^w) G B) → Bool) :
    HoareTime (program headers focus hfocus)
      (fun z => z=input (store caller (focus 0) x))
      (fun z => z=input (store caller (focus 0) (result V P w G B x)))
      (2*BinaryRadixEqualShared.cost P G B w hs+rotationCost P w G B+2) := by
  have h₀ := hoare_extend_eq
    (BinaryPackedFieldSwap.swaps caller headers (focus 0) P G B w hs hv hc hP hG hB hne hsrc x)
    (FixedHeaderBankCopy.empty 12)
  have h₁ := rotates caller focus hfocus V P w G B hV hB g s hg bs ns ws hb hn hw cb cn cw
    (RadixRangePadding.transpose x) ht hh
  have h₂ := hoare_extend_eq
    (BinaryPackedFieldSwap.swaps caller headers (focus 0) P G B w hs hv hc hP hG hB hne hsrc
      (back V P w G B (RadixRangePadding.transpose x))) (FixedHeaderBankCopy.empty 12)
  exact ((h₀.seq h₁).seq h₂).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.BinaryPackedOffsetRun
