import IntegerMultBounds.Machine.CompactComplexScalarPolynomialReusable
import IntegerMultBounds.Machine.RawLinearCombinationComplexRowSequence

/-! Actual named scalar rows share one fixed scratch bank and compose on
literal polynomial arrays without assumed numerical stream callbacks. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarPolynomialSequence
noncomputable section
open CompactComplexScalarIntegerRows (RowIndex)
open CompactComplexScalarRowBlock (wireCount wires_pos expressions)
open ButterflyStreamData (Coefficient)
open RecursiveChildQuotientsConstant (bits)
attribute [local irreducible] Networks.ComplexRank25.program CompactComplexScalarIntegerRows.gates

private opaque commonScratch : {S : ℕ // ∀ r j,
    RadixLinearCombinationRefresh.Size (expressions r j)≤S} :=
  ⟨Finset.univ.sup CompactComplexScalarRowBlock.scratch,fun r j =>
    (CompactComplexScalarRowBlock.scratch_fits r j).trans
      (Finset.le_sup (f:=CompactComplexScalarRowBlock.scratch) (Finset.mem_univ _))⟩

@[irreducible] def scratch := commonScratch.val

abbrev rows := expressions

theorem scratch_fits (r : RowIndex) (j : Fin wireCount) :
    RadixLinearCombinationRefresh.Size (rows r j)≤scratch := by
  unfold scratch
  exact commonScratch.property r j

def compile (ops : List RowIndex) :=
  RawLinearCombinationComplexRowSequence.compile wires_pos rows scratch_fits ops

def execute {n : ℕ} (ops : List RowIndex) (data : Fin wireCount → Fin n → Coefficient) :=
  RawLinearCombinationComplexRowSequence.execute wires_pos rows ops data

private def normalizedBank {c S n : ℕ} (data : Fin c → Fin n → Coefficient)
    (bs : List Bool) : Tapes (RawLinearCombinationComplexRowSequence.count c S) 2 :=
  RawLinearCombinationComplexArrayReusable.bank (S:=S) data bs

abbrev bank {n : ℕ} (data : Fin wireCount → Fin n → Coefficient) :=
  normalizedBank (S:=scratch) data (bits n)

@[irreducible] def timeConstant := CompactComplexScalarPolynomialReusable.timeConstant+1

private theorem join_allowance (T n w A : ℕ) (h : A≤T*(n+1)*(w+1)) :
    A+1≤(T+1)*(n+1)*(w+1) := by nlinarith

private theorem row_bound (r : RowIndex) (n w : ℕ) :
    RawLinearCombinationComplexRowSequence.rowCost (rows r) n w (bits n)+1≤
      timeConstant*(n+1)*(w+1) := by
  have hr : RawLinearCombinationComplexRowSequence.rowCost (rows r) n w (bits n)≤
      CompactComplexScalarPolynomialReusable.timeConstant*(n+1)*(w+1) := by
    simpa only [RawLinearCombinationComplexRowSequence.rowCost,rows] using
      CompactComplexScalarPolynomialReusable.cost_bound r n w
  delta timeConstant
  exact join_allowance _ n w _ hr

theorem cost_bound (ops : List RowIndex) (n w : ℕ) :
    RawLinearCombinationComplexRowSequence.cost rows ops n w (bits n)≤
      ops.length*(timeConstant*(n+1)*(w+1)) := by
  have h := @RawLinearCombinationComplexRowSequence.cost_le wireCount RowIndex rows ops n w
    (bits n) (timeConstant*(n+1)*(w+1)) (fun r _ => row_bound r n w)
  exact h

attribute [local irreducible] RawLinearCombinationComplexRowSequence.compile
  RawLinearCombinationComplexRowSequence.execute RawLinearCombinationComplexArrayReusable.bank

private theorem normalized_runs {c S n : ℕ} {ι : Type*} (hc : 0<c)
    (es : ι → Fin c → RadixLinearCombinationRefresh.Expr c)
    (hs : ∀ r j,RadixLinearCombinationRefresh.Size (es r j)≤S)
    (ops : List ι) (data : Fin c → Fin n → Coefficient) (w : ℕ)
    (hw : ∀ j i,(data j i).1.length=w ∧ (data j i).2.length=w)
    (bs : List Bool) (hn : Counter.value bs=n) :
    HoareTime (RawLinearCombinationComplexRowSequence.compile hc es hs ops).2
      (fun v => v=normalizedBank (S:=S) data bs)
      (fun v => v=normalizedBank (S:=S)
        (RawLinearCombinationComplexRowSequence.execute hc es ops data) bs)
      (RawLinearCombinationComplexRowSequence.cost es ops n w bs) :=
  RawLinearCombinationComplexRowSequence.runs hc es hs ops data w hw bs hn

/-- A fixed actual finite scalar row sequence executes every original
polynomial coefficient and returns normalized streams and blank workspace. -/
theorem runs {n : ℕ} (ops : List RowIndex) (data : Fin wireCount → Fin n → Coefficient)
    (w : ℕ) (hw : ∀ j i,(data j i).1.length=w ∧ (data j i).2.length=w) :
    HoareTime (compile ops).2 (fun v => v=bank data)
      (fun v => v=bank (execute ops data))
      (ops.length*(timeConstant*(n+1)*(w+1))) := by
  have h := @normalized_runs wireCount scratch n RowIndex
    wires_pos rows scratch_fits ops data w hw (bits n)
    (RecursiveChildQuotientsConstant.bits_value n)
  exact h.consequence (fun _ h => h) (fun _ h => h) (cost_bound ops n w)

theorem execute_append {n : ℕ} (first second : List RowIndex)
    (data : Fin wireCount → Fin n → Coefficient) :
    execute (first++second) data=execute second (execute first data) := by
  unfold execute
  exact RawLinearCombinationComplexRowSequence.execute_append wires_pos rows _ _ data

end
end IntegerMultBounds.Machine.CompactComplexScalarPolynomialSequence
