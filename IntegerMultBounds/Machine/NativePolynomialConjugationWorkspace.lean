import IntegerMultBounds.Machine.NativePolynomialConjugationRows
import IntegerMultBounds.Machine.CompactComplexSourceReadyWorkspace

/-! The native row conjugation scan on the genuine source65 caller port,
including its Entry7, leaf and work10 suffix. Every other physical port is
retained automatically by one-tape placement. -/
namespace IntegerMultBounds.Machine.NativePolynomialConjugationWorkspace
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexSourceReadyWorkspace (tapes publicTapes leafTapes bank)
open NativePolynomialConjugationData (array)
open SharedPlacementAlphabet (setTape)
variable {s c : ℕ}

def source : Fin (tapes s c) :=
  Fin.castAdd 10 (Fin.castAdd leafTapes
    (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+s) (c:=c))))

def program (s c : ℕ) := NativePolynomialConjugationRows.program (source (s:=s) (c:=c))

theorem runs_linear (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (entryFrame : Tapes 7 2) (leaf : Tapes leafTapes 2) (work : Tapes 10 2)
    (sh : Shape) (rows ell p : ℕ) (hr : 0<rows) (f : Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hs : caller.tape CompactComplexNonleafRoleEntry.source=
      NativeZeroPadding.word (NativeZeroPaddingArray.word f))
    (hh : caller.head CompactComplexNonleafRoleEntry.source=0) :
    HoareTime (program s c) (fun w => w=bank (caller.append entryFrame) leaf work)
      (fun w => w=bank ((setTape caller CompactComplexNonleafRoleEntry.source
        (NativeZeroPadding.word (NativeZeroPaddingArray.word (array f))) 0).append entryFrame) leaf work)
      (5*CompactNativeRoleTransferBudget.volume rows sh ell p) := by
  have h := NativePolynomialConjugationRows.runs_linear source
    (bank (caller.append entryFrame) leaf work) sh rows ell p hr f hw
    (by simpa only [source,bank,Tapes.append,Fin.addCases_left] using hs)
    (by simpa only [source,bank,Tapes.append,Fin.addCases_left] using hh)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w rfl
  simp only [source,bank]
  rw [←SharedPlacementAlphabet.setTape_append_left,
    ←SharedPlacementAlphabet.setTape_append_left,←SharedPlacementAlphabet.setTape_append_left]

end
end IntegerMultBounds.Machine.NativePolynomialConjugationWorkspace
