import IntegerMultBounds.Machine.CompactComplexRootDigits

/-! Enter root enumeration by physically copying the original active-prefix
header into appended controller tapes. No root exponent, piece boundary,
base-digit list or path descriptor is an input to this entry routine. -/
namespace IntegerMultBounds.Machine.CompactComplexRootDigitsFromHeader
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {a t : ℕ}

def emptyState : ActiveRepairRankHeadersCommands.State := fun _ => none

def controller (f : ℤ → Fin (a+4)) (p : ℤ) : Tapes 44 a :=
  (ActiveRepairRankHeadersCommands.bank emptyState).append (FiniteReturnStack.bank f p)

def focus (src : Fin t) : Fin 2 → Fin (44+t) := ![Fin.natAdd 44 src,Fin.castAdd t (0 : Fin 44)]
theorem focus_injective (src : Fin t) : Function.Injective (focus src) := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · have hv := congrArg Fin.val h
    simp [focus] at hv
  · have hv := congrArg Fin.val h
    simp [focus] at hv
    omega
  · rfl

def initializeProgram (src : Fin t) := BinaryDescriptorCopyPlaced.program (a := a) (focus src) (focus_injective src)

private theorem installed (remaining : ℕ) :
    ActiveRepairRankHeadersCommands.put emptyState 0 remaining=CompactComplexRootDigits.state remaining := by
  funext i
  by_cases h : i=0 <;> simp [ActiveRepairRankHeadersCommands.put,emptyState,CompactComplexRootDigits.state,
    Function.update,h]

theorem initialize_runs (native : Tapes t a) (src : Fin t) (remaining : ℕ)
    (ht : native.tape src=RadixZeroFill.encodedBinary (bits remaining)) (hh : native.head src=1)
    (f : ℤ → Fin (a+4)) (p : ℤ) : HoareTime (initializeProgram (a := a) src)
      (fun v => v=(controller f p).append native)
      (fun v => v=(CompactComplexRootDigits.input remaining f p).append native) (2*remaining+7) := by
  have h := BinaryDescriptorCopyPlaced.copies ((controller (a := a) f p).append native)
    (focus src) (focus_injective src) (bits remaining) (by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
      all_goals first | rfl | simpa [SharedBank.payload,focus,Tapes.append,Copy.tapes,Copy.cfg,Config.tapes] using hh |
        simpa [SharedBank.payload,focus,Tapes.append,Copy.tapes,Copy.cfg,Config.tapes] using ht)
  have hl := ActiveRepairRankHeadersCommands.bits_length remaining
  apply h.consequence (fun _ h => h) _ (by omega)
  intro v hv
  rw [hv]
  change setTape ((controller (a := a) f p).append native)
    (Fin.castAdd t (0 : Fin 44)) (RadixZeroFill.encodedBinary (bits remaining)) 1 = _
  rw [SharedPlacementAlphabet.setTape_append_left]
  apply congrArg (fun (control : Tapes 44 a) => control.append native)
  change setTape ((ActiveRepairRankHeadersCommands.bank (a := a) emptyState).append
    (FiniteReturnStack.bank f p)) (Fin.castAdd 1 (Fin.castAdd 15 (0 : Fin 28)))
    (RadixZeroFill.encodedBinary (bits remaining)) 1 = _
  rw [SharedPlacementAlphabet.setTape_append_left]
  unfold ActiveRepairRankHeadersCommands.bank CleanSubbank.bank
  rw [SharedPlacementAlphabet.setTape_append_left,← ActiveRepairRankHeadersCommands.put_caller,installed]
  rfl

def program (base : ℕ) (src : Fin t) : Σ q, Program (44+t) q a :=
  ⟨_,seq (initializeProgram (a := a) src) (extend (CompactComplexRootDigits.program (a := a) base) t)⟩

/-- The generated digit queue has the original header's value, and every
complete native tape and head is retained throughout enumeration. -/
theorem runs (base : ℕ) (hb : 1 < base) (native : Tapes t a) (src : Fin t) (remaining : ℕ)
    (ht : native.tape src=RadixZeroFill.encodedBinary (bits remaining)) (hh : native.head src=1)
    (f : ℤ → Fin (a+4)) (p : ℤ) :
    HoareTime (program (a := a) base src).2 (fun v => v=(controller f p).append native)
      (fun v => v=(CompactComplexRootDigits.input 0
        (putWord f p (CompactComplexRootDigits.fields (Nat.digits base remaining)))
        (p+(CompactComplexRootDigits.fields (a := a) (Nat.digits base remaining)).length)).append native)
      (2*remaining+8+101000*(remaining+base+1)^2*(Nat.digits base remaining).length) := by
  have hi := initialize_runs native src remaining ht hh f p
  have hg := CompactComplexRootDigits.runs_framed base remaining hb f p native
  exact (hi.seq hg).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.CompactComplexRootDigitsFromHeader
