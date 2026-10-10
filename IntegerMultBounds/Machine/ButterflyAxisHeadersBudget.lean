import IntegerMultBounds.Machine.ButterflyAxisHeadersData

/-! Every physically synthesized descriptor is charged to the actual full
coefficient stream. The budget is uniform in selected bit t and initial p. -/
namespace IntegerMultBounds.Machine.ButterflyAxisHeadersBudget
noncomputable section
open ButterflyAxisHeadersData ButterflyAxisHeadersArithmetic

def logicalVolume (D R p : ℕ) := 2^D*R*recordLength D p

theorem volume_eq (D t R p : ℕ) (ht : t<D) :
    logicalVolume D R p=2*streamLength D t R p := by
  have he : D=(D-t-1)+t+1 := by omega
  unfold logicalVolume streamLength higher rowLength lower
  nth_rw 1 [he]
  rw [pow_add,pow_add,pow_one]
  ring

private def first : List Op :=
  [.base (.constant 4 1),.base (.constant 5 2),.base (.constant 6 0),.base (.constant 20 4),
   cmd (.copy 0 19 (by decide)),cmd (.add 19 0 (by decide)),cmd (.add 19 3 (by decide)),cmd (.add 19 20 (by decide)),
   cmd (.difference 0 1 7 (by decide)),cmd (.difference 7 4 8 (by decide))]
private def second : List Op :=
  [.power ![1,9] (by decide),.power ![8,10] (by decide),
   product ![2,9,11] (by decide),cmd (.copy 19 16 (by decide)),cmd (.add 16 4 (by decide)),
   product ![5,16,17] (by decide),product ![17,11,12] (by decide),
   product ![5,10,13] (by decide),product ![11,10,14] (by decide),product ![12,10,15] (by decide)]
private def middle (D t R p : ℕ) (i : Fin 28) : Option ℕ :=
  match i.val with
  | 0 => some D | 1 => some t | 2 => some R | 3 => some p
  | 4 => some 1 | 5 => some 2 | 6 => some 0 | 7 => some (D-t) | 8 => some (D-t-1)
  | 19 => some (width D p) | 20 => some 4 | _ => none

private theorem execute_first (D t R p : ℕ) : execute first (initial D t R p)=middle D t R p := by
  funext i
  fin_cases i
  all_goals simp [first,execute,eval,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,initial,middle,width,Function.update]

private theorem cost_first (D t R p : ℕ) : scheduleCost first (initial D t R p)=
    100*(6*D+p+t+(D-t)+width D p+7)+52 := by
  dsimp [first,scheduleCost,cost,eval,CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,initial,Function.update,
    RecursiveChildQuotientsConstant.cost]
  simp only [Option.getD_some,width]
  norm_num [RecursiveChildQuotientsConstant.bits_eq_advance,GrowingCounterData.advance,GrowingCounterData.increment]
  ring

private theorem cost_second (D t R p : ℕ) : scheduleCost second (middle D t R p)=
    100*(2*width D p+3)+FixedBasePowerDescriptor.constant 2*(2^t+higher D t)+
    53*(lower t R+recordLength D p+rowLength D t R p+2*higher D t+pairCount D t R+streamLength D t R p)+178 := by
  dsimp [second,scheduleCost,cost,eval,CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,middle,Function.update]
  simp only [higher,lower,recordLength,rowLength,pairCount,streamLength,Option.getD_some]
  ring

private theorem cost_append (xs ys : List Op) (st : ActiveRepairRankHeadersCommands.State) :
    scheduleCost (xs++ys) st=scheduleCost xs st+scheduleCost ys (execute xs st) := by
  induction xs generalizing st with
  | nil => simp [scheduleCost,execute]
  | cons x xs ih => simp only [List.cons_append,scheduleCost,execute,ih]; omega

theorem cost_eq (D t R p : ℕ) : scheduleCost schedule (initial D t R p)=
    100*(6*D+p+t+(D-t)+3*width D p+10)+
    FixedBasePowerDescriptor.constant 2*(2^t+higher D t)+
    53*(lower t R+recordLength D p+rowLength D t R p+2*higher D t+pairCount D t R+streamLength D t R p)+230 := by
  rw [show schedule=first++second from rfl,cost_append,execute_first,cost_first,cost_second]
  ring

/-- The constructor's output headers are all bounded by the literal full stream. -/
theorem values_le (D t R p : ℕ) (ht : t<D) (hR : 0<R) :
    D≤logicalVolume D R p ∧ p≤logicalVolume D R p ∧ t≤logicalVolume D R p ∧
    D-t≤logicalVolume D R p ∧ width D p≤logicalVolume D R p ∧
    2^t≤logicalVolume D R p ∧ higher D t≤logicalVolume D R p ∧
    lower t R≤logicalVolume D R p ∧ recordLength D p≤logicalVolume D R p ∧
    rowLength D t R p≤logicalVolume D R p ∧ 2*higher D t≤logicalVolume D R p ∧
    pairCount D t R≤logicalVolume D R p ∧ streamLength D t R p≤logicalVolume D R p := by
  have hH : 0<higher D t := pow_pos (by decide) _
  have hN : 0<lower t R := Nat.mul_pos (pow_pos (by decide) _) hR
  have hL : 0<recordLength D p := by unfold recordLength; omega
  have hNB : lower t R≤rowLength D t R p := Nat.le_mul_of_pos_right _ hL
  have hLB : recordLength D p≤rowLength D t R p := Nat.le_mul_of_pos_left _ hN
  have hB : 0<rowLength D t R p := Nat.mul_pos hN hL
  have hBS : rowLength D t R p≤streamLength D t R p := Nat.le_mul_of_pos_left _ hH
  have hHS : higher D t≤streamLength D t R p := Nat.le_mul_of_pos_right _ hB
  have hPS : pairCount D t R≤streamLength D t R p := Nat.mul_le_mul_left _ hNB
  have hSV : streamLength D t R p≤logicalVolume D R p := by rw [volume_eq D t R p ht]; omega
  have h2H : 2*higher D t≤logicalVolume D R p := by rw [volume_eq D t R p ht]; omega
  have hW : width D p≤recordLength D p := by unfold recordLength; omega
  have hD : D≤width D p := by unfold width; omega
  have hp : p≤width D p := by unfold width; omega
  have hlow : 2^t≤lower t R := Nat.le_mul_of_pos_right _ hR
  exact ⟨hD.trans (hW.trans (hLB.trans (hBS.trans hSV))),
    hp.trans (hW.trans (hLB.trans (hBS.trans hSV))),
    (Nat.le_of_lt ht).trans (hD.trans (hW.trans (hLB.trans (hBS.trans hSV)))),
    (Nat.sub_le D t).trans (hD.trans (hW.trans (hLB.trans (hBS.trans hSV)))),
    hW.trans (hLB.trans (hBS.trans hSV)),hlow.trans (hNB.trans (hBS.trans hSV)),hHS.trans hSV,
    hNB.trans (hBS.trans hSV),hLB.trans (hBS.trans hSV),hBS.trans hSV,h2H,hPS.trans hSV,hSV⟩

def constant := 5000+2*FixedBasePowerDescriptor.constant 2

theorem cost_linear (D t R p : ℕ) (ht : t<D) (hR : 0<R) :
    scheduleCost schedule (initial D t R p)≤constant*logicalVolume D R p := by
  obtain ⟨hD,hp,ht',hd,hW,hlo,hH,hN,hL,hB,h2H,hP,hS⟩ := values_le D t R p ht hR
  have hV : 0<logicalVolume D R p := by unfold logicalVolume recordLength; positivity
  have hpow := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) (show 2^t+higher D t≤2*logicalVolume D R p by omega)
  rw [cost_eq]
  unfold constant
  nlinarith

end
end IntegerMultBounds.Machine.ButterflyAxisHeadersBudget
