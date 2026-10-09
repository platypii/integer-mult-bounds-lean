import IntegerMultBounds.Machine.BinaryDescriptorQueueRead
import IntegerMultBounds.Machine.CompactComplexRootDigits
import IntegerMultBounds.Machine.CompactComplexRootPieceNumbers

/-! Paid reading of the generated root-digit queue into the numeric piece
clock. The source delimiter is tested by the actual fixed reader; no digit
value or field length is supplied to its finite control. -/
namespace IntegerMultBounds.Machine.CompactComplexRootPieceQueue
noncomputable section
open ActiveRepairRankHeadersCommands (State bank put)
open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)
variable {a : ℕ}

def input (st : State) (f : ℤ → Fin (a+4)) (p : ℤ) : Tapes 44 a :=
  (bank st).append (FiniteReturnStack.bank f p)
def focus : Fin 2 → Fin 44 := ![43,4]
theorem focus_injective : Function.Injective focus := by decide
def placement := InjectivePlacement.placement focus focus_injective (by decide : 2+(44-2)=44)
def program := Placement.placed (BinaryDescriptorQueueRead.program (a := a)) placement

private theorem active_input (st : State) (h4 : st 4=none) (f : ℤ → Fin (a+4)) (p : ℤ) :
    Placement.active placement (input (a := a) st f p)=Copy.tapes f (fun _ => blank) p 0 := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [placement,InjectivePlacement.active_slot]
  all_goals fin_cases i
  · rfl
  · change (if (st (4 : Fin 28)).isSome then (1 : ℤ) else 0)=0
    rw [h4]; rfl
  · rfl
  · change (match st (4 : Fin 28) with | none => fun _ => blank | some n => RadixZeroFill.encodedBinary (bits n))=fun _ => blank
    rw [h4]

private theorem replace_write {s u t : ℕ} (e : Fin (s+u) ≃ Fin t) (v : Tapes t a)
    (small : Tapes s a) (i : Fin s) (f : ℤ → Fin (a+4)) (p : ℤ) :
    Placement.replace e v (setTape small i f p)=
      setTape (Placement.replace e v small) (e (Fin.castAdd u i)) f p := by
  have h : Placement.replace e v (setTape small i f p)=
      Placement.replace e (Placement.replace e v small)
        (setTape (Placement.active e (Placement.replace e v small)) i f p) := by
    simp only [Placement.active_replace]
    unfold Placement.replace
    rw [Placement.extra_combine]
  rw [h,PlacedDescriptorConstruction.replace_setTape]

private theorem setTape_append_right {l r : ℕ} (v : Tapes l a) (w : Tapes r a) (i : Fin r)
    (f : ℤ → Fin (a+4)) (p : ℤ) :
    setTape (v.append w) (Fin.natAdd l i) f p=v.append (setTape w i f p) := by
  unfold setTape Tapes.append
  congr 1 <;> funext j <;> induction j using Fin.addCases <;> simp [Function.update_apply,Fin.ext_iff]
  all_goals intro h; omega

private theorem replace_output (st : State) (h4 : st 4=none)
    (f : ℤ → Fin (a+4)) (p p' : ℤ) (n : ℕ) :
    Placement.replace placement (input st f p)
      (Copy.tapes f (BinaryDescriptorStack.descriptor (bits n)) p' 1)=
        input (put st 4 n) f p' := by
  have hs : Copy.tapes f (BinaryDescriptorStack.descriptor (bits n)) p' 1=
      setTape (setTape (Copy.tapes f (fun _ => blank) p 0) 0 f p')
        1 (BinaryDescriptorStack.descriptor (bits n)) 1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [hs,← active_input st h4 f p,replace_write,PlacedDescriptorConstruction.replace_setTape]
  simp only [placement,InjectivePlacement.active_slot,focus]
  change setTape (setTape _ (Fin.natAdd 43 (0 : Fin 1)) f p')
    (Fin.castAdd 1 (Fin.castAdd 15 (4 : Fin 28))) _ 1 = _
  unfold input
  rw [setTape_append_right,SharedPlacementAlphabet.setTape_append_left]
  unfold bank CleanSubbank.bank
  rw [SharedPlacementAlphabet.setTape_append_left,BinaryDescriptorStackRoundtrip.descriptor_encoded,
    ← ActiveRepairRankHeadersCommands.put_caller]
  apply congrArg (fun tail => ((ActiveRepairRankHeadersCommands.caller (a := a) (put st 4 n)).append
    (SharedBank.empty 15 a)).append tail)
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- Read a physically present field, retaining every other numeric descriptor
and all fifteen arithmetic-workspace tapes exactly. -/
theorem runs (st : State) (h4 : st 4=none) (f : ℤ → Fin (a+4)) (p : ℤ) (n : ℕ)
    (he : f (p+(bits n).length)=separator) :
    HoareTime program
      (fun v => v=input st (putWord f p ((bits n).map bitSymbol)) p)
      (fun v => v=input (put st 4 n) (putWord f p ((bits n).map bitSymbol))
        (p+(bits n).length+1)) (2*(bits n).length+6) := by
  have h := Placement.hoare_at (BinaryDescriptorQueueRead.runs (a := a) f p (bits n) he)
    placement _ (active_input st h4 _ p)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact replace_output st h4 _ p _ n

/-- The field is exactly the head of the generated low-to-high queue. -/
theorem fields_runs (st : State) (h4 : st 4=none) (f : ℤ → Fin (a+4))
    (p : ℤ) (n : ℕ) (ds : List ℕ) :
    HoareTime program
      (fun v => v=input st (putWord f p (CompactComplexRootDigits.fields (n::ds))) p)
      (fun v => v=input (put st 4 n) (putWord f p (CompactComplexRootDigits.fields (n::ds)))
        (p+(bits n).length+1)) (2*(bits n).length+6) := by
  let tail := putWord f (p+(bits n).length) (separator::CompactComplexRootDigits.fields (a := a) ds)
  have he : tail (p+(bits n).length)=separator := by exact putWord_head _ _ _ _
  have hw : putWord tail p ((bits n).map bitSymbol)=
      putWord f p (CompactComplexRootDigits.fields (n::ds)) := by
    rw [CompactComplexRootDigits.fields,List.flatMap_cons]
    simp only [List.append_assoc,List.singleton_append]
    rw [putWord_append]
    simp only [List.length_map]
    rfl
  simpa only [hw] using runs (a := a) st h4 tail p n he

/-- Appended native/controller storage is stationary during the field read. -/
theorem fields_runs_framed {t : ℕ} (st : State) (h4 : st 4=none)
    (f : ℤ → Fin (a+4)) (p : ℤ) (n : ℕ) (ds : List ℕ) (tail : Tapes t a) :
    HoareTime (extend program t)
      (fun v => v=(input st (putWord f p (CompactComplexRootDigits.fields (n::ds))) p).append tail)
      (fun v => v=(input (put st 4 n) (putWord f p (CompactComplexRootDigits.fields (n::ds)))
        (p+(bits n).length+1)).append tail) (2*(bits n).length+6) :=
  hoare_extend_eq (fields_runs st h4 f p n ds) tail

end
end IntegerMultBounds.Machine.CompactComplexRootPieceQueue
