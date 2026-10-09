import IntegerMultBounds.Machine.ButterflyRecordRead

/-! The physical output workspace and paid erasure of the four extracted input
components, ready for serial emission and reuse by the next coefficient pair. -/
namespace IntegerMultBounds.Machine.ButterflyRecordOutputData
noncomputable section
open RadixDigits
open MarkedWordCleanup (one word marked)
open RadixLinearCombinationRefresh (controls)
open RadixLinearCombinationBootstrap (empty)

def block (zs : List (Fin 2)) : Tapes 11 2 := (one (word (zs.map digitSymbol)) 0).append (empty 10)
def work (zs : Fin 4 → List (Fin 2)) : Tapes 44 2 :=
  ((block (zs 0)).append (block (zs 1))).append ((block (zs 2)).append (block (zs 3)))

def input (v : Tapes 4 2) (xs : ℕ → List (Fin 2)) (zs : Fin 4 → List (Fin 2)) : Tapes 52 2 :=
  v.append ((controls (c:=4) xs).append (work zs))
def output (v : Tapes 4 2) (zs : Fin 4 → List (Fin 2)) : Tapes 52 2 :=
  v.append ((empty 4).append (work zs))

theorem arithmetic_bank (v : Tapes 4 2) (xs : ℕ → List (Fin 2)) :
    v.append (ButterflyNumerator.output xs)=input v xs (fun i => ButterflyNumerator.words i xs) := rfl

def controlsProgram : Program 4 16 2 := FamilyPlacementAlphabet.sequence
  (FamilyPlacementAlphabet.sequence MarkedBinaryCleanup.program MarkedBinaryCleanup.program)
  (FamilyPlacementAlphabet.sequence MarkedBinaryCleanup.program MarkedBinaryCleanup.program)

def program := RawLinearCombinationCleanup.prepend (extend controlsProgram 44) 4

theorem controls_runs (xs : ℕ → List (Fin 2)) (w : ℕ) (hw : ∀ i,(xs i).length=w) :
    HoareTime controlsProgram (fun v => v=controls xs) (fun v => v=empty 4) (8*w+19) := by
  have h (i : ℕ) := RawLinearCombinationCleanup.marked_radix (xs i)
  have hh := FamilyPlacementAlphabet.sequence_hoare
    (FamilyPlacementAlphabet.sequence_hoare (h 0) (h 1))
    (FamilyPlacementAlphabet.sequence_hoare (h 2) (h 3))
  have hi : ((one (marked ((xs 0).map digitSymbol)) 1).append (one (marked ((xs 1).map digitSymbol)) 1)).append
      ((one (marked ((xs 2).map digitSymbol)) 1).append (one (marked ((xs 3).map digitSymbol)) 1))=controls xs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have ho : ((one (fun _ => (blank:Fin 6)) 0).append (one (fun _ => blank) 0)).append
      ((one (fun _ => blank) 0).append (one (fun _ => blank) 0))=empty 4 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [hi,ho] at hh
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by simp only [hw]; omega)

/-- Every source copy is really erased; output words are framed in place. -/
theorem runs (v : Tapes 4 2) (xs : ℕ → List (Fin 2)) (zs : Fin 4 → List (Fin 2))
    (w : ℕ) (hw : ∀ i,(xs i).length=w) :
    HoareTime program (fun z => z=input v xs zs) (fun z => z=output v zs) (8*w+19) :=
  RawLinearCombinationCleanup.prepend_runs _ _ _ v
    (FamilyPlacementAlphabet.extend_hoare (controls_runs xs w hw) (work zs))

end
end IntegerMultBounds.Machine.ButterflyRecordOutputData
