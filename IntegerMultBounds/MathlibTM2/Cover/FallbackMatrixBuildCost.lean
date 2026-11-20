module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackConjugationQueue
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPrefixVolume

/-! Cost of generating a conjugate from a physical label record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open RingFormula
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem liveRecordCost_le_width_budget (r d w H numTime detTime : ℕ) :
    liveRecordCost r d w H 0 (numTime*(H+1)^2) (detTime*(H+1)^2) ≤
      liveRecordCost r d 1 1 0 numTime detTime * (w+1)*(H+1)^2 := by
  unfold liveRecordCost
  ring_nf
  omega

noncomputable def matrixBuildCost (r d w H : ℕ) := liveRecordCost r d w H 0
  (Finset.univ.sup fun ij : Fin r × Fin r => RingFormula.time H (readTime H)
    (numerator (matrixInput false) (matrixInput true) ij.1 ij.2))
  (RingFormula.time H (readTime H) (determinant (matrixInput (m := r) false)))

theorem matrixBuildCost_le (r d w H : ℕ) :
    matrixBuildCost r d w H ≤ matrixBuildCost r d 1 1 * (w+1)*(H+1)^2 := by
  let num := fun h (ij : Fin r × Fin r) => RingFormula.time h (readTime h)
    (numerator (matrixInput false) (matrixInput true) ij.1 ij.2)
  have entries : Finset.univ.sup (num H) ≤ Finset.univ.sup (num 1)*(H+1)^2 := by
    apply Finset.sup_le
    intro ij hi
    exact (time_readTime_le _ H).trans (Nat.mul_le_mul_right _ (Finset.le_sup (f := num 1) hi))
  apply le_trans _ (liveRecordCost_le_width_budget r d w H _ _)
  simp only [matrixBuildCost, liveRecordCost]
  gcongr
  all_goals first | exact entries | exact time_readTime_le _ H

noncomputable def recordConjugationTime (m w H prefixWidth : ℕ) : ℕ :=
  let formula := fun i j : Fin m => numerator (matrixInput false) (matrixInput true) i j
  let formulaCost := Finset.univ.sup fun ij : Fin m × Fin m => time H (readTime H) (formula ij.1 ij.2)
  let detFormula := determinant (matrixInput (m := m) false)
  let C := 48*H*H+152*H+66
  let readCost := m*(m*(12*prefixWidth+8*((w+1)*(m*m))+(w+1)*(7*H+prime+31)+10*H+42)+1)+1
  ((1+(readCost+1)) + (time H (readTime H) detFormula + (6*w+6+(14*H+16+(prime-2)*C+C+w*(12*H+15+prime*C))) +
       ((m*(m*(formulaCost+4*H+4)+1)+1) + (m*(m*(8*(m*m*H)+48*H*H+166*H+88)+1)+1) + (2*(m*m*H)+2)) + 4*H+4) + (2*(m*m*H)+2))

/-- Reading the prefix adds a linear charge; the remaining computation fits
one radix factor of the payload at binary field width. -/
theorem recordConjugationTime_binary_le (m w prefixWidth : ℕ) :
    let M := prime^(w+1)
    recordConjugationTime m w M.size prefixWidth ≤
      12*m*m*prefixWidth + (matrixBuildCost m 0 1 1 * (2*(prime.size+1)^2))*M := by
  intro M
  have conjugate : recordConjugationTime m w M.size prefixWidth ≤
      12*m*m*prefixWidth + matrixBuildCost m 0 w M.size := by
    unfold recordConjugationTime matrixBuildCost liveRecordCost
    ring_nf
    omega
  apply conjugate.trans
  apply Nat.add_le_add_left
  refine (matrixBuildCost_le m 0 w M.size).trans ?_
  rw [Nat.mul_assoc,Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  have bits := prefixSetup_volume_le w 0
  simp only [Nat.zero_add,pow_one,pow_zero] at bits
  exact (Nat.mul_le_mul_right _ (Nat.le_add_right (w+1) 1)).trans bits

end IntegerMultBounds.MathlibTM2.Cover.Fallback
