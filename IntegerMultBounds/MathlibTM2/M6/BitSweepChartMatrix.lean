module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepQuarterProduct
public import IntegerMultBounds.MathlibTM2.M6.BitSweepRankEvaluation
public import IntegerMultBounds.MathlibTM2.M6.BitSweepQuarterInverse

/-! Write the selected chart in the physical rank evaluator's axis order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589 Certificates.PR589.Nine
open Shared50ModularControl Cover.Fallback RingFormula Host Stack Node Cover.LabelTraversal
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def sweepChart (n : Fin 9) (r : Role) : Matrix (Fin 64) (Fin 64) ℚ :=
  let c := port r.port.val
  if r.bank.val / 2 = BitHosting.activePair n.val then (c.stageRoute n).submatrix stageAxis.symm stageAxis.symm
  else c.fullChart.submatrix stageAxis.symm remainderAxis

private theorem chartEntry (w : ℕ) (n : Fin 9) (r : Role) (i j : Fin 64) :
    let q := sweepChart n r i j
    q.den.Coprime (prime^w) ∧ ∃ z : ℤ, q = (z : ℚ)/4 := by
  have checked := port_checked _ r.port.isLt
  dsimp only [sweepChart]
  split
  · exact ⟨stageRoute_admissible _ checked n w _ _,stageRoute_quarter _ checked n _ _⟩
  · refine ⟨Nat.Coprime.pow_right w ((Nat.coprime_of_lt_prime (Rat.den_pos _).ne' ?_ prime_prime).symm),
      fullChart_quarter _ checked _ _⟩
    exact (fullChart_entry _ checked _ _).2.trans_lt prime_odd

theorem sweepChartMatrix_writes {P U : Type} {T Q D : ℕ} (body : P → Pr P T Q prime U)
    (pool : Fin ((D+1)*13) ↪ Fin T) (c : Fin 6 ↪ Fin T) (g : Fin 13 ↪ Fin T)
    (outside : ∀ i j, c i ≠ pool j) (tmpOff : ∀ i, c i ≠ g 0)
    (outOff : ∀ i, c i ≠ g 3) (poolOff : ∀ j, pool j ≠ g 3)
    (n : Fin 9) (r : Role) (depth : ∀ i j, (sweepIntFormula (4*sweepChart n r i j).num).depth ≤ D) :
    ∃ program : Pr P T Q prime U, ∀ w H (parent : Fin 64 → ZMod (prime^w)) (dest : Fin ((prime^w)^128)),
    let M := prime^w
    let cost := fun i j => time H (fun _ => 6*H+6) (sweepIntFormula (4*sweepChart n r i j).num)
    let bound := Finset.univ.sup fun i => Finset.univ.sup (cost i)
    let entry := (D+1)*(6*H+6)+1+(bound+((D+1)*(2*H+2)+1))+(4*H+4)+Gate.mul.time H+(2*H+2)
    M < 2^H →
    Writes body (fun R => (R (c 0) = binSyms H 0 ∧ R (c 1) = binSyms H (1 : ZMod M).val ∧
      R (c 2) = binSyms H M ∧ (∀ i : Fin 6, 3 ≤ i → R (c i) = []) ∧ ∀ j, R (pool j) = []) ∧
      R (g 0) = [] ∧ R (g 1) = binSyms H (Ring.inverse (4 : ZMod M)).val ∧
      R (g 2) = binSyms H M ∧ ∀ i : Fin 13, 4 ≤ i → i < 12 → R (g i) = [])
      (g 3) program (matrixWords prime H (sweepRankMatrices w parent n r dest false)) (64*(64*entry+1)+1) := by
  let leaf : Leaf Empty → Fin T → Pr P T Q prime U := fun a dst => bcopy (literalSource c a) dst (c 4) (c 5)
  let emit (z : ℤ) : Pr P T Q prime U := .seq ((initFrames pool (c 2) (D+1)).seq
    ((compile leaf (registerBank pool) (sweepIntFormula z) 0 (c 3)).seq (clearFrames pool (D+1))))
    (moveRightOrdered (c 3) (c 4) (g 0))
  let cell (i j : Fin 64) : Pr P T Q prime U := .seq (emit (4*sweepChart n r i j).num) (.seq (Gate.mul.program g) (bclear (g 0)))
  refine ⟨sequence (fun i => sequence (cell i) (List.finRange 64)) (List.finRange 64),?_⟩
  intro w H parent dest M cost bound entry fits
  have unit : IsUnit (4 : ZMod M) := by simpa [M] using prefix_denominator_unit 4 (by decide) (by decide) w
  have chart : sweepRankMatrices w parent n r dest false = Swap.Modular.reduce M (sweepChart n r) := by
    by_cases h : r.bank.val / 2 = BitHosting.activePair n.val <;> simp [sweepRankMatrices,sweepChart,h,Swap.Modular.reduce] <;> rfl
  rw [chart]
  apply matrixWords_writes
  · intro R xs ready
    obtain ⟨constants,zero,inv,modulus,free⟩ := ready
    refine ⟨?_,?_,?_,?_,?_⟩
    · simpa only [Function.update_of_ne (outOff _),Function.update_of_ne (poolOff _)] using constants
    · simpa using zero
    · simpa using inv
    · simpa using modulus
    · intro i lo hi
      exact (Function.update_of_ne (g.injective.ne (by omega : i ≠ 3)) _ _).trans (free i lo hi)
  · intro i j v S ready
    have h := chartEntry w n r i j
    have numerator := sweepIntEntry_writes body pool c outside (g 0) tmpOff _ (depth i j) H fits
    obtain ⟨u,t,hu,ht,run⟩ := sweepQuarterProduct_writes body g _ h.1 h.2 _ (Ring.inverse_mul_cancel _ unit)
      H fits _ _ _ numerator v S ready
    have cap : cost i j ≤ bound := (Finset.le_sup (f := cost i) (Finset.mem_univ j)).trans
      (Finset.le_sup (f := fun k => Finset.univ.sup (cost k)) (Finset.mem_univ i))
    change t ≤ (D+1)*(6*H+6)+1+(cost i j+((D+1)*(2*H+2)+1))+(4*H+4)+Gate.mul.time H+(2*H+2) at ht
    exact ⟨u,t,hu,by dsimp only [entry]; omega,run⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
