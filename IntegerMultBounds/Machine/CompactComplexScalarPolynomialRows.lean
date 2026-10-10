import IntegerMultBounds.Machine.RawLinearCombinationComplexArray
import IntegerMultBounds.Machine.CompactComplexScalarPathGuard

/-! Actual complex25 scalar rows execute on every literal polynomial
coefficient, with one unchanged denominator for the whole input array and
one common next denominator for the whole output. The actual expression
family and every read, loop, cleanup and join cost are included. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarPolynomialRows
noncomputable section
open CompactComplexScalarIntegerRows (RowIndex Wire wireIndex signedRows gate)
open CompactComplexScalarRowBlock (wireCount wires_pos expressions scratch_fits)
open ButterflyStreamData (Coefficient)
open ButterflySigned Networks.GaussianPrecision
open RecursiveChildQuotientsConstant (bits)
attribute [local irreducible] Networks.ComplexRank25.program wireIndex

abbrev program (r : RowIndex) := RawLinearCombinationComplexArray.program wires_pos (expressions r) (scratch_fits r)
def result {n : ℕ} (r : RowIndex) (data : Fin wireCount → Fin n → Coefficient) :=
  RawLinearCombinationComplexArray.result wires_pos (expressions r) data

private opaque budgetWires : {c : ℕ // c=wireCount} := ⟨wireCount,rfl⟩
@[irreducible] def timeConstant := CompactComplexScalarRowBlock.timeConstant+24*budgetWires.val+21

private theorem body_allowance (c R F w : ℕ) (h : 2*F+1≤R*(w+1)) :
    2*c*(2*w+7)+2*F+2*c*(2*w+5)+11≤(R+24*c+10)*(w+1) := by nlinarith

private theorem transport_body (c d R F w : ℕ) (hc : c=d)
    (h : 2*c*(2*w+7)+2*F+2*c*(2*w+5)+11≤(R+24*c+10)*(w+1)) :
    2*c*(2*w+7)+2*F+2*c*(2*w+5)+11≤(R+24*d+10)*(w+1) := by
  exact h.trans_eq (congrArg (fun x => (R+24*x+10)*(w+1)) hc)

theorem body_bound (r : RowIndex) (w : ℕ) :
    RawLinearCombinationComplexArray.bodyCost (expressions r) w+6≤
      (timeConstant-11)*(w+1) := by
  have h := body_allowance wireCount CompactComplexScalarRowBlock.timeConstant
    (RawLinearCombinationFieldFamily.cost (expressions r) (List.finRange wireCount) w) w
    (CompactComplexScalarRowBlock.time_bound r w)
  unfold RawLinearCombinationComplexArray.bodyCost
  have ht : timeConstant-11=CompactComplexScalarRowBlock.timeConstant+24*budgetWires.val+10 := by
    delta timeConstant
    omega
  rw [ht]
  exact transport_body _ budgetWires.val _ _ w budgetWires.property.symm h

private theorem loop_allowance (T B n w len : ℕ)
    (hT : 11≤T) (hB : B≤(T-11)*(w+1)) (hlen : len≤n+1) :
    n*B+11*len+35≤T*n*(w+1)+46 := by
  have hm := Nat.mul_le_mul_left n hB
  have he : T-11+11=T := Nat.sub_add_cancel hT
  have hn : n≤n*(w+1) := by nlinarith
  calc
    n*B+11*len+35 ≤ n*((T-11)*(w+1))+11*(n+1)+35 := by omega
    _ ≤ n*((T-11)*(w+1))+11*(n*(w+1))+46 := by omega
    _ = (T-11+11)*n*(w+1)+46 := by ring
    _ = T*n*(w+1)+46 := by rw [he]

theorem cost_bound (r : RowIndex) (n w : ℕ) :
    n*(RawLinearCombinationComplexArray.bodyCost (expressions r) w+6)+11*(bits n).length+35≤
      timeConstant*n*(w+1)+46 := by
  have hT : 11≤timeConstant := by delta timeConstant; omega
  exact loop_allowance timeConstant _ n w _ hT (body_bound r w)
    (ActiveRepairRankHeadersCommands.bits_length n)

/-- A fixed actual row machine reads the retained canonical coefficient-count
header at runtime; its control table depends only on the finite actual row. -/
theorem runs {n : ℕ} (r : RowIndex)
    (f g : Fin wireCount → ℤ → Fin 6) (p z : Fin wireCount → ℤ)
    (data : Fin wireCount → Fin n → Coefficient) (w : ℕ)
    (hw : ∀ j i,(data j i).1.length=w ∧ (data j i).2.length=w) :
    HoareTime (program r)
      (fun v => v=CountedLoopHeaderClean.bank
        (RawLinearCombinationComplexArray.counted (S:=CompactComplexScalarRowBlock.scratch r)
          wires_pos (expressions r) f g p z data (bits n) 0))
      (fun v => v=CountedLoopHeaderClean.bank
        (RawLinearCombinationComplexArray.counted (S:=CompactComplexScalarRowBlock.scratch r)
          wires_pos (expressions r) f g p z data (bits n) n))
      (timeConstant*n*(w+1)+46) :=
  (RawLinearCombinationComplexArray.runs wires_pos (expressions r) (scratch_fits r)
    f g p z data w hw (bits n) (RecursiveChildQuotientsConstant.bits_value n)).consequence
      (fun _ hv => hv) (fun _ hv => hv) (cost_bound r n w)

theorem result_width {n : ℕ} (r : RowIndex) (data : Fin wireCount → Fin n → Coefficient)
    (w : ℕ) (hw : ∀ j i,(data j i).1.length=w ∧ (data j i).2.length=w)
    (j : Fin wireCount) (i : Fin n) :
    (result r data j i).1.length=w ∧ (result r data j i).2.length=w :=
  RawLinearCombinationComplexArray.result_width wires_pos (expressions r) data w hw j i

/-- Actual target and spectator expressions share one next denominator across
all coefficients. The result has the original named-wire scalar semantics. -/
theorem result_semantics {N : ℕ} (r : RowIndex) (data : Fin wireCount → Fin N → Coefficient)
    (b p n : ℕ) (hw : ∀ j i,(data j i).1.length=b+1 ∧ (data j i).2.length=b+1)
    (ha : ∀ j i,|signedValue b (data j i).1|≤((2^p:ℕ):ℤ))
    (hb : ∀ j i,|signedValue b (data j i).2|≤((2^p:ℕ):ℤ))
    (hguard : p+CompactComplexScalarIntegerRows.guardBits≤b) (j : Fin wireCount) (i : Fin N) :
    complexValue (signedValue b (result r data j i).1) (signedValue b (result r data j i).2) (n+1)=
      (Networks.RationalScalarGrid.castGate (gate r)).run
        (fun wire => complexValue (signedValue b (data (wireIndex wire) i).1)
          (signedValue b (data (wireIndex wire) i).2) n) (wireIndex.symm j) := by
  let xs := RawLinearCombinationComplexArray.real wires_pos data i
  let ys := RawLinearCombinationComplexArray.imag wires_pos data i
  have hx := RawLinearCombinationComplexArray.real_width wires_pos data (b+1) hw i
  have hy := RawLinearCombinationComplexArray.imag_width wires_pos data (b+1) hw i
  have hre : ∀ wire,signedRows b xs wire=signedValue b (data (wireIndex wire) i).1 := by
    intro wire
    simp only [signedRows,xs,RawLinearCombinationComplexArray.real,RawLinearCombinationComplexArray.index_val]
  have him : ∀ wire,signedRows b ys wire=signedValue b (data (wireIndex wire) i).2 := by
    intro wire
    simp only [signedRows,ys,RawLinearCombinationComplexArray.imag,RawLinearCombinationComplexArray.index_val]
  have h := CompactComplexScalarWireEmit.complex_word r (wireIndex.symm j) b p n xs ys hx hy
    (fun wire => by rw [hre]; exact ha _ i) (fun wire => by rw [him]; exact hb _ i) hguard
  simpa only [result,RawLinearCombinationComplexArray.result,expressions,
    CompactComplexScalarWireEmit.word,hre,him] using h

end
end IntegerMultBounds.Machine.CompactComplexScalarPolynomialRows
