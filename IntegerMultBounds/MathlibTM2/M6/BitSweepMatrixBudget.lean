module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepChartMatrix
public import IntegerMultBounds.MathlibTM2.M6.BitSweepTranslationRows

/-! Uniform frame depth and time for both initial sweep matrices and their reciprocal. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Networks Shared50ModularControl Cover.Fallback RingFormula

private abbrev SetupIndex := (Fin 9 × Role × Fin 64 × Fin 64) ⊕ (Fin 61 × Fin 64) ⊕ Bool

private noncomputable def setupInteger : SetupIndex → ℤ
  | .inl (n,r,i,j) => (4*sweepChart n r i j).num
  | .inr (.inl (i,j)) => translationRows i j
  | .inr (.inr b) => if b then 4 else -1

/-- One fixed pool and one quadratic time coefficient suffice for all signed
entries, at every role, stage and live tape width. -/
private theorem setupIntegers_bounded {ι : Type} [Fintype ι] (z : ι → ℤ) :
    ∃ D K : ℕ, ∀ i : ι, (sweepIntFormula (z i)).depth ≤ D ∧ ∀ H,
      time H (fun _ => 6*H+6) (sweepIntFormula (z i)) ≤ K*(H+1)^2 := by
  choose k bound using fun i : ι => quadraticFormulaTime 6 (sweepIntFormula (z i))
  refine ⟨Finset.univ.sup (fun i => (sweepIntFormula (z i)).depth),Finset.univ.sup k,?_⟩
  intro i
  refine ⟨Finset.le_sup (f := fun j => (sweepIntFormula (z j)).depth) (Finset.mem_univ i),fun H => ?_⟩
  have read : 6*H+6 ≤ 6*(H+1)^2 := by ring_nf; omega
  have hi : k i ≤ Finset.univ.sup k := Finset.le_sup (f := k) (Finset.mem_univ i)
  exact (bound i H (fun _ => 6*H+6) (fun _ => read)).trans (Nat.mul_le_mul_right _ hi)

/-- The sum of the three physical writer budgets is cubic in field width,
uniformly in the choice of chart and in the archived parent weights. -/
theorem sweepMatrixSetup_budget :
    ∃ D C : ℕ, (∀ n r i j, (sweepIntFormula (4*sweepChart n r i j).num).depth ≤ D) ∧
      (∀ i j, (sweepIntFormula (translationRows i j)).depth ≤ D) ∧
      (sweepIntFormula 4).depth ≤ D ∧ (sweepIntFormula (-1)).depth ≤ D ∧
      ∀ (n : Fin 9) (r : Role) (w H : ℕ), (prime^(w+1))^128 < 2^H → H ≤ (prime^(w+1))^128+1 →
      let L := (prime^(w+1)).size
      let cost := fun z => time H (fun _ => 6*H+6) (sweepIntFormula z)
      let entry := fun k => (D+1)*(6*H+6)+1+(k+((D+1)*(2*H+2)+1))+(4*H+4)
      let chart := Finset.univ.sup fun i => Finset.univ.sup fun j => cost (4*sweepChart n r i j).num
      let trans := Finset.univ.sup fun i => Finset.univ.sup fun j => cost (translationRows i j)
      let mul := 48*H*H+152*H+66
      let inv := entry (cost 4)+(6*w+6+(14*H+16+(prime-2)*mul+mul+w*(12*H+15+prime*mul)))+(2*H+2)
      let input := 61*(64*entry trans+1)+1+(64*(8*(64*L)+14*L+16*H+44)+1+(128*entry (cost (-1))+1))
      inv+input+(64*(64*(entry chart+Gate.mul.time H+(2*H+2))+1)+1) ≤ C*((prime^(w+1))^128)^3 := by
  obtain ⟨D,K,bound⟩ := setupIntegers_bounded setupInteger
  refine ⟨D,27*(10000000*(D+K+prime+1)),fun n r i j => (bound (.inl (n,r,i,j))).1,
    fun i j => (bound (.inr (.inl (i,j)))).1,(bound (.inr (.inr true))).1,(bound (.inr (.inr false))).1,?_⟩
  intro n r w H fits field L cost entry chart trans mul inv input
  let records := (prime^(w+1))^128
  have positive : 0 < records := pow_pos (pow_pos prime_prime.pos _) _
  have width : L ≤ H := Nat.size_le.mpr ((Nat.le_self_pow (by decide : 128 ≠ 0) _).trans_lt fits)
  have ticks : w ≤ H := by
    have small := Nat.size_le_size (Nat.pow_le_pow_left prime_prime.two_le (w+1))
    rw [Nat.size_pow] at small
    change (prime^(w+1)).size ≤ H at width
    omega
  have bits : H+1 ≤ 3*records := by change H ≤ records+1 at field; omega
  let cap := K*(H+1)^2
  have hc : chart ≤ cap := Finset.sup_le fun i _ => Finset.sup_le fun j _ => (bound (.inl (n,r,i,j))).2 H
  have ht : trans ≤ cap := Finset.sup_le fun i _ => Finset.sup_le fun j _ => (bound (.inr (.inl (i,j)))).2 H
  have hf : cost 4 ≤ cap := (bound (.inr (.inr true))).2 H
  have hn : cost (-1) ≤ cap := (bound (.inr (.inr false))).2 H
  let reciprocal := entry cap+(6*H+6+(14*H+16+prime*mul+mul+H*(12*H+15+prime*mul)))+(2*H+2)
  let rows := 61*(64*entry cap+1)+1+(64*(8*(64*H)+14*H+16*H+44)+1+(128*entry cap+1))
  have hi : inv ≤ reciprocal := by dsimp only [inv,reciprocal,entry]; gcongr <;> omega
  have hr : input ≤ rows := by dsimp only [input,rows,entry]; gcongr
  calc
    _ ≤ reciprocal+rows+(64*(64*(entry cap+Gate.mul.time H+(2*H+2))+1)+1) := by
      dsimp only [entry]; gcongr
    _ ≤ (10000000*(D+K+prime+1))*(H+1)^3 := by
      dsimp only [reciprocal,rows,entry,cap,mul,Gate.time]; ring_nf; omega
    _ ≤ (10000000*(D+K+prime+1))*(3*records)^3 := by gcongr
    _ = _ := by change _ = 27*(10000000*(D+K+prime+1))*records^3; ring


/-- Frame depth shared by the physical chart and translation writers. -/
noncomputable def sweepMatrixDepth : ℕ := sweepMatrixSetup_budget.choose

end IntegerMultBounds.MathlibTM2.M6.BitNode
