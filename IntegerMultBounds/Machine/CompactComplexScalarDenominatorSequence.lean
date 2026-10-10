import IntegerMultBounds.Machine.CompactComplexScalarPolynomialSequence
import IntegerMultBounds.Machine.RawLinearCombinationComplexDenominatorSequence

/-! Actual complex25 polynomial scalar rows update their true live denominator
only after complete source replacement and cleanup. The original coefficient
count survives; one common physical denominator serves the whole array. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarDenominatorSequence
noncomputable section
open CompactComplexScalarIntegerRows (RowIndex)
open CompactComplexScalarRowBlock (wireCount wires_pos)
open CompactComplexScalarPolynomialSequence (rows scratch scratch_fits execute)
open ButterflyStreamData (Coefficient)
open RecursiveChildQuotientsConstant (bits)
attribute [local irreducible] Networks.ComplexRank25.program CompactComplexScalarIntegerRows.gates

private def normalizedBank {c S n : ℕ} (data : Fin c → Fin n → Coefficient)
    (bs : List Bool) (d : ℕ) :
    Tapes (RawLinearCombinationComplexDenominatorSequence.count c S) 2 :=
  RawLinearCombinationComplexDenominatorSequence.bank (S:=S) data bs d

abbrev bank {n : ℕ} (data : Fin wireCount → Fin n → Coefficient) (d : ℕ) :=
  normalizedBank (S:=scratch) data (bits n) d

def compile (ops : List RowIndex) :=
  RawLinearCombinationComplexDenominatorSequence.compile wires_pos rows scratch_fits ops

def cost (ops : List RowIndex) (n w d : ℕ) :=
  ops.length*(CompactComplexScalarPolynomialReusable.timeConstant*(n+1)*(w+1)+
    2*(d+ops.length+1)+2)

theorem cost_bound (ops : List RowIndex) (n w d : ℕ) :
    RawLinearCombinationComplexDenominatorSequence.cost rows n w (bits n) ops d≤cost ops n w d := by
  apply RawLinearCombinationComplexDenominatorSequence.cost_le
  intro r _
  simpa only [RawLinearCombinationComplexRowSequence.rowCost,rows] using
    CompactComplexScalarPolynomialReusable.cost_bound r n w

private theorem descriptor_allowance (d len M n w : ℕ) (hd : d≤w) (hl : len≤M) :
    2*(d+len+1)+2≤(2*M+6)*(n+1)*(w+1) := by
  have hp : w+1≤(n+1)*(w+1) := by nlinarith
  have hbase : 2*(d+len+1)+2≤(2*M+6)*(w+1) := by nlinarith
  simpa only [Nat.mul_assoc] using hbase.trans (Nat.mul_le_mul_left (2*M+6) hp)

/-- A stored-denominator capacity bound absorbs every real descriptor scan
into the same stream-volume scale as actual scalar arithmetic. -/
theorem cost_linear (ops : List RowIndex) (n w d M : ℕ) (hd : d≤w) (hl : ops.length≤M) :
    cost ops n w d≤ops.length*((CompactComplexScalarPolynomialReusable.timeConstant+2*M+6)*
      (n+1)*(w+1)) := by
  unfold cost
  apply Nat.mul_le_mul_left
  have h := descriptor_allowance d ops.length M n w hd hl
  nlinarith

attribute [local irreducible] RawLinearCombinationComplexDenominatorSequence.compile
  RawLinearCombinationComplexDenominatorSequence.bank RawLinearCombinationComplexRowSequence.execute

private theorem normalized_runs {c S n : ℕ} {ι : Type*} (hc : 0<c)
    (es : ι → Fin c → RadixLinearCombinationRefresh.Expr c)
    (hs : ∀ r j,RadixLinearCombinationRefresh.Size (es r j)≤S)
    (ops : List ι) (data : Fin c → Fin n → Coefficient) (w : ℕ)
    (hw : ∀ j i,(data j i).1.length=w ∧ (data j i).2.length=w)
    (bs : List Bool) (hn : Counter.value bs=n) (d : ℕ) :
    HoareTime (RawLinearCombinationComplexDenominatorSequence.compile hc es hs ops).2
      (fun v => v=normalizedBank (S:=S) data bs d)
      (fun v => v=normalizedBank (S:=S)
        (RawLinearCombinationComplexRowSequence.execute hc es ops data) bs (d+ops.length))
      (RawLinearCombinationComplexDenominatorSequence.cost es n w bs ops d) :=
  RawLinearCombinationComplexDenominatorSequence.runs hc es hs ops data w hw bs hn d

/-- Actual completed scalar rows advance the physical common denominator once,
with every coefficient loop, copy-back, increment and join charged. -/
theorem runs {n : ℕ} (ops : List RowIndex) (data : Fin wireCount → Fin n → Coefficient)
    (w d : ℕ) (hw : ∀ j i,(data j i).1.length=w ∧ (data j i).2.length=w) :
    HoareTime (compile ops).2 (fun v => v=bank data d)
      (fun v => v=bank (execute ops data) (d+ops.length)) (cost ops n w d) := by
  have h := @normalized_runs wireCount scratch n RowIndex wires_pos rows scratch_fits ops
    data w hw (bits n) (RecursiveChildQuotientsConstant.bits_value n) d
  exact h.consequence (fun _ h => h) (fun _ h => h) (cost_bound ops n w d)

private theorem normalized_live {c S n : ℕ} (data : Fin c → Fin n → Coefficient)
    (bs : List Bool) (d : ℕ) :
    (normalizedBank (S:=S) data bs d).tape RawLinearCombinationComplexDenominatorSequence.live=
      RadixZeroFill.encodedBinary (bits d) ∧
    (normalizedBank (S:=S) data bs d).head RawLinearCombinationComplexDenominatorSequence.live=1 :=
  RawLinearCombinationComplexDenominatorSequence.bank_live data bs d

/-- The actual stream header is the true marked binary denominator, distinct
from the geometric recursion exponent and stored-width descriptors. -/
theorem live_header {n : ℕ} (data : Fin wireCount → Fin n → Coefficient) (d : ℕ) :
    (bank data d).tape RawLinearCombinationComplexDenominatorSequence.live=
      RadixZeroFill.encodedBinary (bits d) ∧
    (bank data d).head RawLinearCombinationComplexDenominatorSequence.live=1 :=
  @normalized_live wireCount scratch n data (bits n) d

end
end IntegerMultBounds.Machine.CompactComplexScalarDenominatorSequence
