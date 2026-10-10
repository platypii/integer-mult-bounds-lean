import IntegerMultBounds.Machine.CompactComplexScalarPolynomialRows
import IntegerMultBounds.Machine.RawLinearCombinationComplexArrayReusable

/-! Complete actual scalar polynomial row execution, including physical
copy-back, head normalization and erasure of every generated stream. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarPolynomialReusable
noncomputable section
open CompactComplexScalarIntegerRows (RowIndex)
open CompactComplexScalarRowBlock (wireCount wires_pos expressions scratch_fits)
open ButterflyStreamData (Coefficient)
open RecursiveChildQuotientsConstant (bits)
attribute [local irreducible] Networks.ComplexRank25.program

abbrev program (r : RowIndex) :=
  RawLinearCombinationComplexArrayReusable.program wires_pos (expressions r) (scratch_fits r)
abbrev bank {n : ℕ} (r : RowIndex) (data : Fin wireCount → Fin n → Coefficient) :=
  RawLinearCombinationComplexArrayReusable.bank
    (S:=CompactComplexScalarRowBlock.scratch r) data (bits n)

private opaque budgetWires : {c : ℕ // c=wireCount} := ⟨wireCount,rfl⟩
@[irreducible] def timeConstant :=
  CompactComplexScalarPolynomialRows.timeConstant+31*budgetWires.val+47

private theorem allowance (T c n w A : ℕ) (hA : A≤T*n*(w+1)+46) :
    A+c*(7*(n*(2*(w+1)))+17)+1≤(T+31*c+47)*(n+1)*(w+1) := by
  have hn : n≤n*(w+1) := by nlinarith
  have hw : 1≤w+1 := by omega
  have hc : c≤c*(w+1) := by nlinarith
  nlinarith

private theorem transport (T c d n w A : ℕ) (hc : c=d)
    (h : A≤(T+31*c+47)*(n+1)*(w+1)) :
    A≤(T+31*d+47)*(n+1)*(w+1) :=
  h.trans_eq (congrArg (fun x => (T+31*x+47)*(n+1)*(w+1)) hc)

theorem cost_bound (r : RowIndex) (n w : ℕ) :
    n*(RawLinearCombinationComplexArray.bodyCost (expressions r) w+6)+11*(bits n).length+35+
      wireCount*(7*(n*(2*(w+1)))+17)+1≤timeConstant*(n+1)*(w+1) := by
  have h := allowance CompactComplexScalarPolynomialRows.timeConstant wireCount n w _
    (CompactComplexScalarPolynomialRows.cost_bound r n w)
  delta timeConstant
  exact transport _ wireCount budgetWires.val n w _ budgetWires.property.symm h

/-- Every actual scalar row has a reusable exact whole-bank endpoint.
One retained runtime count controls the full array, including empty arrays. -/
theorem runs {n : ℕ} (r : RowIndex) (data : Fin wireCount → Fin n → Coefficient)
    (w : ℕ) (hw : ∀ j i,(data j i).1.length=w ∧ (data j i).2.length=w) :
    HoareTime (program r) (fun v => v=bank r data)
      (fun v => v=bank r (CompactComplexScalarPolynomialRows.result r data))
      (timeConstant*(n+1)*(w+1)) :=
  (RawLinearCombinationComplexArrayReusable.runs wires_pos (expressions r) (scratch_fits r)
    data w hw (bits n) (RecursiveChildQuotientsConstant.bits_value n)).consequence
    (fun _ h => h) (fun _ h => h) (cost_bound r n w)

end
end IntegerMultBounds.Machine.CompactComplexScalarPolynomialReusable
