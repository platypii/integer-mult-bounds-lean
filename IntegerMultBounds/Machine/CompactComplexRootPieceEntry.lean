import IntegerMultBounds.Machine.CompactComplexRootPieceController
import IntegerMultBounds.Machine.CompactComplexRootDigitsFromHeader

/-! Original native-header entry into the fixed canonical root-piece loop.
The fresh queue cursor, digit queue, exponent/left/width seed and all later
root descriptors are physically generated; only the native callback's proof
is abstracted for the still-unassembled recursive machine. -/
namespace IntegerMultBounds.Machine.CompactComplexRootPieceEntry
noncomputable section
open ActiveRepairRankHeadersCommands (State bank)
open CompactComplexRecursiveGeometry (arity)
open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)
variable {a q t : ℕ}

def control (st : State) (f : ℤ → Fin (a+4)) (p : ℤ) : Tapes 44 a :=
  (bank st).append (FiniteReturnStack.bank f p)
def queuePlacement := FiniteReturnStackAt.placement (43 : Fin 44)
def queueProgram {k : ℕ} (M : Program 1 k a) := Placement.placed M queuePlacement

private theorem setTape_append_right (st : State) (f : ℤ → Fin (a+4)) (p p' : ℤ) :
    setTape (control st f p) 43 f p'=control st f p' := by
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.addCases (m := 43) (n := 1)
    · rename_i i
      have hi : i.val≠43 := by omega
      simp [control,Tapes.append,Fin.ext_iff,hi]
    · rename_i i; fin_cases i; rfl
  · funext i z
    induction i using Fin.addCases (m := 43) (n := 1)
    · rename_i i
      have hi : i.val≠43 := by omega
      simp [control,Tapes.append,Fin.ext_iff,hi]
    · rename_i i; fin_cases i; rfl

private theorem queue_runs {k B : ℕ} (M : Program 1 k a) (st : State)
    (f : ℤ → Fin (a+4)) (p p' : ℤ)
    (h : HoareTime M (fun v => v=FiniteReturnStack.bank f p)
      (fun v => v=FiniteReturnStack.bank f p') B) :
    HoareTime (queueProgram M) (fun v => v=control st f p)
      (fun v => v=control st f p') B := by
  have hp := Placement.hoare_at h queuePlacement (control st f p) (by
    rw [queuePlacement,FiniteReturnStackAt.active_bank]
    rfl)
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  rw [queuePlacement,FiniteReturnStackAt.replace_bank,setTape_append_right]

def startProgram := queueProgram (BinaryDescriptorQueueRewind.moveProgram (a := a) .right)
def rewindProgram := queueProgram (BinaryDescriptorQueueRewind.program (a := a))

private theorem start_runs (st : State) (f : ℤ → Fin (a+4)) (p : ℤ) :
    HoareTime startProgram (fun v => v=control st f p) (fun v => v=control st f (p+1)) 1 := by
  apply queue_runs _ st f p (p+1)
  apply (DescriptorStackControl.once_hoare (by decide) _ (FiniteReturnStack.bank f p)).consequence
    (fun _ h => h) _ le_rfl
  rintro v rfl
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i z
    by_cases hz : z=p <;> simp [FiniteReturnStack.bank,hz]

private theorem rewind_runs (st : State) (ds : List ℕ) :
    HoareTime (rewindProgram (a := a))
      (fun v => v=control st (CompactComplexRootPieceController.queue ds)
        (1+(CompactComplexRootDigits.fields (a := a) ds).length))
      (fun v => v=control st (CompactComplexRootPieceController.queue ds) 1)
      ((CompactComplexRootDigits.fields (a := a) ds).length+4) :=
  queue_runs _ st _ _ _ (BinaryDescriptorQueueRewind.fields_runs ds)

def prefixProgram (src : Fin t) : Σ k, Program (44+t) k a :=
  ⟨_,seq (seq (extend startProgram t)
    (CompactComplexRootDigitsFromHeader.program arity src).2) (extend rewindProgram t)⟩

def program (src : Fin t) (callback : Program (43+(1+t)) q a) : Σ k, Program (43+(1+t)) k a :=
  ⟨_,seq (seq (CompactComplexControllerTapeAssoc.program (prefixProgram src).2)
      (extend (CompactChildHeadersArithmetic.compile CompactComplexRootPieceNumbers.seed).2 (1+t)))
        (CompactComplexRootPieceController.program callback)⟩

/-- The finite entry machine receives only the original retained active
header and fresh controller tapes. All root descriptor generation is paid;
the native callback contract names exactly the generated canonical Visits. -/
theorem runs (src : Fin t) (callback : Program (43+(1+t)) q a) (active : ℕ)
    (native : ℕ → Tapes t a) (callCost : ℕ → ℕ → ℕ)
    (ht : (native 0).tape src=RadixZeroFill.encodedBinary (bits active))
    (hh : (native 0).head src=1)
    (hc : ∀ k (hk : k<(Nat.digits arity active).length), ∀ j<(Nat.digits arity active)[k],
      HoareTime callback
      (fun v => v=CompactComplexRootPieceClock.input
        (CompactComplexRootPieceController.state (CompactComplexRootDigits.state 0) (Nat.digits arity active) k)
        (CompactComplexRootPieceVisits.preceding ((Nat.digits arity active).take k)+j*arity^k)
        ((Nat.digits arity active)[k]-j)
        (FiniteReturnStack.bank (CompactComplexRootPieceController.queue (Nat.digits arity active))
          (CompactComplexRootPieceController.cursor (Nat.digits arity active) (k+1)))
        (native (CompactComplexRootPiecePrefixes.count ((Nat.digits arity active).take k)+j)))
      (fun v => v=CompactComplexRootPieceClock.input
        (CompactComplexRootPieceController.state (CompactComplexRootDigits.state 0) (Nat.digits arity active) k)
        (CompactComplexRootPieceVisits.preceding ((Nat.digits arity active).take k)+j*arity^k)
        ((Nat.digits arity active)[k]-j)
        (FiniteReturnStack.bank (CompactComplexRootPieceController.queue (Nat.digits arity active))
          (CompactComplexRootPieceController.cursor (Nat.digits arity active) (k+1)))
        (native (CompactComplexRootPiecePrefixes.count ((Nat.digits arity active).take k)+j+1)))
      (callCost k j)) :
    HoareTime (program src callback).2
      (fun v => v=CompactComplexRootPieceDigit.input CompactComplexRootDigitsFromHeader.emptyState
        (fun _ => blank) 0 (native 0))
      (fun v => v=CompactComplexRootPieceController.input (CompactComplexRootDigits.state 0)
        (Nat.digits arity active) (Nat.digits arity active).length
        (native (CompactComplexRootPiecePrefixes.count (Nat.digits arity active))))
      (2*active+48+101000*(active+arity+1)^2*(Nat.digits arity active).length+
        (CompactComplexRootDigits.fields (a := a) (Nat.digits arity active)).length+
        ∑ k : Fin (Nat.digits arity active).length,
          (CompactComplexRootPieceController.bodyCost (CompactComplexRootDigits.state 0)
            (Nat.digits arity active) k callCost+2)) := by
  have hs := hoare_extend_eq (start_runs (a := a) CompactComplexRootDigitsFromHeader.emptyState
    (fun _ => blank) 0) (native 0)
  have hg := CompactComplexRootDigitsFromHeader.runs arity (by decide) (native 0) src active ht hh
    (fun _ => blank) 1
  have hr := hoare_extend_eq (rewind_runs (a := a) (CompactComplexRootDigits.state 0)
    (Nat.digits arity active)) (native 0)
  have hn := hoare_extend_eq (CompactComplexRootPieceNumbers.seed_runs (a := a)
    (CompactComplexRootDigits.state 0) (by simp [CompactComplexRootDigits.state])
    (by simp [CompactComplexRootDigits.state]) (by simp [CompactComplexRootDigits.state]))
    ((FiniteReturnStack.bank (CompactComplexRootPieceController.queue (Nat.digits arity active)) 1).append (native 0))
  have ho := CompactComplexRootPieceController.runs callback (CompactComplexRootDigits.state 0)
    (Nat.digits arity active) (by simp [CompactComplexRootDigits.state])
    (by simp [CompactComplexRootDigits.state]) (by simp [CompactComplexRootDigits.state])
    (by simp [CompactComplexRootDigits.state]) native callCost hc
  have hp := CompactComplexControllerTapeAssoc.hoare ((hs.seq hg).seq hr)
  simp only [CompactComplexRootPieceController.input,CompactComplexRootPieceController.state_zero,
    CompactComplexRootPieceController.cursor,List.take_zero,List.map_nil,List.sum_nil,Nat.cast_zero,add_zero,
    CompactComplexRootPieceDigit.input] at ho
  have hseed := CompactComplexRootPieceNumbers.seed_cost_le (CompactComplexRootDigits.state 0)
  have hall := (hp.seq hn).seq ho
  apply hall.consequence (fun _ h => h) (fun _ h => h)
  omega

end
end IntegerMultBounds.Machine.CompactComplexRootPieceEntry
