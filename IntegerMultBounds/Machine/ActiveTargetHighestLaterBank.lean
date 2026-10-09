import IntegerMultBounds.Machine.ActiveTargetHighestLaterAlphabet

/-! Literal payload replacement interface, leaving all stage descriptors and
blank work cells unchanged, for physically composing the later-source gadget. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestLaterBank
noncomputable section
open ActiveTargetHighestRun
open SharedPlacementAlphabet (setTape)

def sourceTape (G L : ℕ) {B : ℕ} (a : Array G L B) : ℤ → Fin 6 :=
  fun z => RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0 (List.ofFn a) z)

theorem replace (G L : ℕ) {B : ℕ} (ws : Fin 3 → List Bool)
    (a b : Array G L B) (bs qs ns : List Bool) :
    ActiveTargetHighestRun.input G L ws a bs qs ns=
      setTape (ActiveTargetHighestRun.input G L ws b bs qs ns) 20 (sourceTape G L a) 0 := by
  unfold ActiveTargetHighestRun.input initial
  rw [FlatControlledShiftLayout.input_layout,FlatControlledShiftLayout.input_layout]
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.addCases (m := 27) (n := 27) with
    | left i =>
      induction i using Fin.addCases (m := 10) (n := 17) with
      | left i =>
        have hn : Fin.castAdd 27 (Fin.castAdd 17 i) ≠ (20 : Fin 54) := by
          intro h; have hv := congrArg Fin.val h; change i.val=20 at hv; have hi := i.isLt; omega
        simp only [PrefixCounterInit.tapeCount,Nat.reduceAdd,Tapes.append,Fin.addCases_left,Function.update_of_ne hn]
      | right i =>
        simp only [PrefixCounterInit.tapeCount,Nat.reduceAdd,Tapes.append,Function.update_apply,Fin.addCases_left,Fin.addCases_right]
        fin_cases i <;> simp [Nat.reduceAdd,FlatControlledShiftLayout.suffix,
          FlatControlledShiftLayout.descriptorHead,Matrix.cons_val]
    | right i =>
      have hn : Fin.natAdd 27 i ≠ (20 : Fin 54) := by
        intro h; have hv := congrArg Fin.val h; change 27+i.val=20 at hv; omega
      simp only [PrefixCounterInit.tapeCount,Nat.reduceAdd,Tapes.append,Fin.addCases_right,Function.update_of_ne hn]
  · funext i
    induction i using Fin.addCases (m := 27) (n := 27) with
    | left i =>
      induction i using Fin.addCases (m := 10) (n := 17) with
      | left i =>
        have hn : Fin.castAdd 27 (Fin.castAdd 17 i) ≠ (20 : Fin 54) := by
          intro h; have hv := congrArg Fin.val h; change i.val=20 at hv; have hi := i.isLt; omega
        simp only [PrefixCounterInit.tapeCount,Nat.reduceAdd,Tapes.append,Fin.addCases_left,Function.update_of_ne hn]
      | right i =>
        simp only [PrefixCounterInit.tapeCount,Nat.reduceAdd,Tapes.append,Function.update_apply,Fin.addCases_left,Fin.addCases_right]
        fin_cases i <;> simp [Nat.reduceAdd,FlatControlledShiftLayout.suffix,
          FlatControlledShiftLayout.descriptorTape,Matrix.cons_val]
        all_goals rfl
    | right i =>
      have hn : Fin.natAdd 27 i ≠ (20 : Fin 54) := by
        intro h; have hv := congrArg Fin.val h; change 27+i.val=20 at hv; omega
      simp only [PrefixCounterInit.tapeCount,Nat.reduceAdd,Tapes.append,Fin.addCases_right,Function.update_of_ne hn]

theorem map_word {r s : ℕ} (e : Alphabet.Encoding r s) (f : ℤ → Fin (r+4))
    (p : ℤ) (xs : List (Fin (r+4))) :
    (fun z => e.encode (putWord f p xs z))=
      putWord (fun z => e.encode (f z)) p (xs.map e.encode) := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    funext z
    by_cases hz : z=p
    · subst z
      simp only [putWord,List.map_cons,Function.update_self]
    · simp only [putWord,List.map_cons,Function.update_of_ne hz]
      exact congrFun (ih (p+1)) z

theorem cast_list {n m : ℕ} {α : Type*} (h : n=m) (x : Fin m → α) :
    List.ofFn (fun i : Fin n => x (Fin.cast h i))=List.ofFn x := by
  subst m
  rfl

theorem mapped_source (G L B : ℕ) (x : Fin (RadixRangePadding.volume (2^L) 2 (2^G) B) → Bool) :
    (fun z => ActiveTargetHighestLaterAlphabet.encoding.encode
      (sourceTape G L (ActiveTargetHighestLaterValue.nativeArray G L B x) z))=
      BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)) := by
  have hm : ∀ (z : Fin 4), ActiveTargetHighestLaterAlphabet.encoding.encode
      ((RadixToBinary.binaryEncoding (q := 2)).encode z)=
      (RadixToBinary.binaryEncoding (q := Networks.Shared50ModularControl.prime)).encode z := by
    intro z
    rfl
  simp only [sourceTape,hm]
  rw [map_word,List.map_ofFn]
  have ha : (RadixToBinary.binaryEncoding (q := Networks.Shared50ModularControl.prime)).encode ∘
      ActiveTargetHighestLaterValue.nativeArray G L B x =
      fun i => bitSymbol (x (Fin.cast (ActiveTargetHighestLaterValue.size_eq G L B) i)) := rfl
  have hc := cast_list (ActiveTargetHighestLaterValue.size_eq G L B) (fun i => (bitSymbol (x i) : Fin (Networks.Shared50ModularControl.prime+4)))
  rw [ha,hc]
  rfl

theorem map_setTape {t r s : ℕ} (e : Alphabet.Encoding r s) (v : Tapes t r)
    (i : Fin t) (f : ℤ → Fin (r+4)) (p : ℤ) :
    Alphabet.mapTapes e (setTape v i f p)=
      setTape (Alphabet.mapTapes e v) i (fun z => e.encode (f z)) p := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext j z
    by_cases hj : j=i
    · subst j
      simp only [Alphabet.mapTapes,setTape,Function.update_self]
    · simp only [Alphabet.mapTapes,setTape,Function.update_of_ne hj]

theorem store_input (G L B : ℕ) (ws : Fin 3 → List Bool) (bs qs ns : List Bool)
    (x y : Fin (RadixRangePadding.volume (2^L) 2 (2^G) B) → Bool) :
    BinaryPackedFieldSwap.store
      (ActiveTargetHighestLaterAlphabet.input G L ws (ActiveTargetHighestLaterValue.nativeArray G L B y) bs qs ns)
      20 x =
    ActiveTargetHighestLaterAlphabet.input G L ws (ActiveTargetHighestLaterValue.nativeArray G L B x) bs qs ns := by
  have h := congrArg (Alphabet.mapTapes ActiveTargetHighestLaterAlphabet.encoding)
    (replace G L ws (ActiveTargetHighestLaterValue.nativeArray G L B x)
      (ActiveTargetHighestLaterValue.nativeArray G L B y) bs qs ns)
  rw [map_setTape,mapped_source] at h
  exact h.symm

end
end IntegerMultBounds.Machine.ActiveTargetHighestLaterBank
