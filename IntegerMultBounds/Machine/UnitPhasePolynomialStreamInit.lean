import IntegerMultBounds.Machine.UnitPhasePolynomialMultiplicity
import IntegerMultBounds.Machine.UnitPhaseFullStreamInit
import IntegerMultBounds.Machine.UnitPhasePolynomialStreamClean

/-! Initialize all polynomial traversal controls from physical immutable
headers. The external ell scalar65 yields2^ell on60; original row/header
arithmetic yields rows*2^bits on59 and initializes the live address counter.
All six temporary numeric tapes are restored before traversal. -/
namespace IntegerMultBounds.Machine.UnitPhasePolynomialStreamInit
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open DelimitedRadixRecord (Context)
open MarkedWordCleanup (one)
variable {s : Shape}

def scalar (ell : ℕ) : Tapes 1 2 :=
  one (RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits ell)) 1
def input (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (z : Tapes 4 2) (ell : ℕ) :=
  (UnitPhaseFullStreamInit.input order v rows axis z).append ((SharedBank.empty 5 2).append (scalar ell))
def multiplicity (ell : ℕ) :=
  (UnitPhasePolynomialRecord.multiplicity (2^ell)).append ((SharedBank.empty 4 2).append (scalar ell))
def program := seq UnitPhasePolynomialMultiplicity.program (extend UnitPhaseFullStreamInit.program 6)
def output (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (z : Tapes 4 2) (ell : ℕ) :=
  (UnitPhaseFullStreamInit.output order v rows axis (UnitPhaseStreamData.contexts (fun _ => blank) 0 (fun i : Fin 0 => Fin.elim0 i) 0) z).append (multiplicity ell)

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (z : Tapes 4 2) (ell : ℕ)
    (hc : z.tape 1=(fun _ => blank) ∧ z.head 1=0)
    (hn : z.tape 3=(fun _ => blank) ∧ z.head 3=0) :
    HoareTime program (fun t => t=input order v rows axis z ell)
      (fun t => t=output order v rows axis z ell)
      (FixedBasePowerDescriptor.constant 2*2^ell+UnitPhaseFullStreamInit.cost order v rows axis+1) := by
  have h0 := UnitPhasePolynomialMultiplicity.runs (input order v rows axis z ell) ell ⟨rfl,rfl⟩
    (by intro i; fin_cases i <;> exact ⟨rfl,rfl⟩)
  have hm : UnitPhasePolynomialMultiplicity.output (input order v rows axis z ell) ell=
      (UnitPhaseFullStreamInit.input order v rows axis z).append (multiplicity ell) := by
    apply congrArg₂ Tapes.mk <;> funext j <;> fin_cases j <;> rfl
  rw [hm] at h0
  have h1 := hoare_extend_eq (UnitPhaseFullStreamInit.runs order v rows axis
    (UnitPhaseStreamData.contexts (fun _ => blank) 0 (fun i : Fin 0 => Fin.elim0 i) 0) z hc hn) (multiplicity ell)
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.UnitPhasePolynomialStreamInit
