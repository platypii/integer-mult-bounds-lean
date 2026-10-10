import IntegerMultBounds.Machine.ButterflyInverseSpectatorOriginal
import IntegerMultBounds.Machine.ButterflyAxisHeadersBudget

/-! The actual spectator machine is linear in its entire serialized native
word, uniformly in the selected original coordinate. All synthesized headers,
physical copies, arithmetic, routing and erasure are included. -/
namespace IntegerMultBounds.Machine.ButterflySpectatorBudget
noncomputable section
open ButterflyAxisHeadersData
open ButterflyAxisHeadersArithmetic
open ButterflySpectatorGeometry

def volume (rows D R p : ℕ) := rows*ButterflyAxisHeadersBudget.logicalVolume D R p

theorem positive (rows D R p : ℕ) (hr : 0<rows) (hR : 0<R) : 0<volume rows D R p := by
  unfold volume ButterflyAxisHeadersBudget.logicalVolume recordLength
  positivity

theorem row_volume (rows D t R p : ℕ) (ht : t<D) :
    RecursiveInterchangeLayout.volume 2 (descriptor rows D t R p)=volume rows D R p := by
  rw [volume,ButterflyAxisHeadersBudget.volume_eq D t R p ht]
  simp only [RecursiveInterchangeLayout.volume,descriptor,CompactRowHeaders.descriptor,
    streamLength,pow_zero,mul_one,one_mul]
  ring

private def first : List Op :=
  [.base (.constant 4 1),.base (.constant 5 2),.base (.constant 6 0),.base (.constant 20 4),
   cmd (.copy 0 19 (by decide)),cmd (.add 19 0 (by decide)),cmd (.add 19 3 (by decide)),cmd (.add 19 20 (by decide)),
   cmd (.difference 0 1 7 (by decide)),cmd (.difference 7 4 8 (by decide))]
private def powersRows : List Op := [.power ![1,9] (by decide),.power ![8,10] (by decide),
  product ![18,10,21] (by decide),cmd (.erase 10),cmd (.copy 21 10 (by decide)),cmd (.erase 21)]
private def last : List Op := [product ![2,9,11] (by decide),cmd (.copy 19 16 (by decide)),cmd (.add 16 4 (by decide)),
  product ![5,16,17] (by decide),product ![17,11,12] (by decide),product ![5,10,13] (by decide),
  product ![11,10,14] (by decide),product ![12,10,15] (by decide)]
private def middle (phase rows D t R p : ℕ) (i : Fin 28) : Option ℕ :=
  match i.val with
  | 0 => some D | 1 => some t | 2 => some R | 3 => some p
  | 4 => some 1 | 5 => some 2 | 6 => some 0 | 7 => some (D-t) | 8 => some (D-t-1)
  | 9 => if phase=0 then none else some (2^t)
  | 10 => if phase=0 then none else some (rows*higher D t)
  | 18 => some rows | 19 => some (width D p) | 20 => some 4 | _ => none

private theorem first_eval (rows D t R p : ℕ) : execute first (ButterflySpectatorHeaders.initial rows D t R p)=middle 0 rows D t R p := by
  funext i
  fin_cases i <;> simp [first,execute,eval,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,ButterflySpectatorHeaders.initial,middle,width,Function.update]
private theorem rows_eval (rows D t R p : ℕ) : execute powersRows (middle 0 rows D t R p)=middle 1 rows D t R p := by
  funext i
  fin_cases i <;> simp [powersRows,execute,eval,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,middle,Function.update,higher]
  all_goals ring
private theorem first_cost (rows D t R p : ℕ) : scheduleCost first (ButterflySpectatorHeaders.initial rows D t R p)=
    100*(6*D+p+t+(D-t)+width D p+7)+52 := by
  dsimp [first,scheduleCost,cost,eval,CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,ButterflySpectatorHeaders.initial,Function.update,
    RecursiveChildQuotientsConstant.cost]
  simp only [Option.getD_some,width]
  norm_num [RecursiveChildQuotientsConstant.bits_eq_advance,GrowingCounterData.advance,GrowingCounterData.increment]
  ring
private theorem rows_cost (rows D t R p : ℕ) : scheduleCost powersRows (middle 0 rows D t R p)=
    FixedBasePowerDescriptor.constant 2*(2^t+higher D t)+53*(rows*higher D t)+
      100*(higher D t+2*(rows*higher D t)+3)+34 := by
  dsimp [powersRows,scheduleCost,cost,eval,CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,middle,Function.update]
  simp only [Option.getD_some,higher]
  ring
private theorem last_cost (rows D t R p : ℕ) : scheduleCost last (middle 1 rows D t R p)=
    100*(2*width D p+3)+53*(lower t R+recordLength D p+rowLength D t R p+
      rows*(2*higher D t+pairCount D t R+streamLength D t R p))+176 := by
  dsimp [last,scheduleCost,cost,eval,CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,middle,Function.update]
  simp only [Option.getD_some,lower,recordLength,rowLength,pairCount,streamLength]
  ring
private theorem cost_append (xs ys : List Op) (st : ActiveRepairRankHeadersCommands.State) :
    scheduleCost (xs++ys) st=scheduleCost xs st+scheduleCost ys (execute xs st) := by
  induction xs generalizing st with
  | nil => simp [scheduleCost,execute]
  | cons x xs ih => simp only [List.cons_append,scheduleCost,execute,ih]; omega
private theorem execute_append (xs ys : List Op) (st : ActiveRepairRankHeadersCommands.State) :
    execute (xs++ys) st=execute ys (execute xs st) := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => exact ih (eval x st)

theorem header_cost_eq (rows D t R p : ℕ) :
    scheduleCost ButterflySpectatorHeaders.schedule (ButterflySpectatorHeaders.initial rows D t R p)=
      100*(6*D+p+t+(D-t)+3*width D p+10)+
      FixedBasePowerDescriptor.constant 2*(2^t+higher D t)+
      53*(lower t R+recordLength D p+rowLength D t R p+
        rows*(2*higher D t+pairCount D t R+streamLength D t R p)+rows*higher D t)+
      100*(higher D t+2*(rows*higher D t)+3)+262 := by
  rw [show ButterflySpectatorHeaders.schedule=(first++powersRows)++last from rfl,
    cost_append,cost_append,execute_append,first_eval,rows_eval,first_cost,rows_cost,last_cost]
  ring

theorem cleanup_cost_eq (rows D t R p : ℕ) :
    scheduleCost ButterflySpectatorHeaders.cleanup (ButterflySpectatorHeaders.output rows D t R p)=
      100*(t+(D-t)+(D-t-1)+2^t+3*(rows*higher D t)+lower t R+rowLength D t R p+
        rows*pairCount D t R+rows*streamLength D t R p+2*width D p+recordLength D p+26)+17 := by
  dsimp [ButterflySpectatorHeaders.cleanup,List.map,scheduleCost,cost,eval,CompactChildHeadersArithmetic.cost,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    ButterflySpectatorHeaders.output,Function.update]
  simp only [Option.getD_some]
  ring

theorem row_values (rows D t R p : ℕ) (hr : 0<rows) (ht : t<D) (hR : 0<R) :
    ButterflyAxisHeadersBudget.logicalVolume D R p≤volume rows D R p ∧
    rows*higher D t≤volume rows D R p ∧ rows*(2*higher D t)≤volume rows D R p ∧
    rows*pairCount D t R≤volume rows D R p ∧ rows*streamLength D t R p≤volume rows D R p ∧
    rows≤volume rows D R p ∧ R≤volume rows D R p := by
  have hv := ButterflyAxisHeadersBudget.values_le D t R p ht hR
  have hV : 0<ButterflyAxisHeadersBudget.logicalVolume D R p := by
    unfold ButterflyAxisHeadersBudget.logicalVolume recordLength
    positivity
  have hv0 := Nat.le_mul_of_pos_left (ButterflyAxisHeadersBudget.logicalVolume D R p) hr
  have hv1 := Nat.mul_le_mul_left rows hv.2.2.2.2.2.2.1
  have hv2 := Nat.mul_le_mul_left rows hv.2.2.2.2.2.2.2.2.2.2.1
  have hv3 := Nat.mul_le_mul_left rows hv.2.2.2.2.2.2.2.2.2.2.2.1
  have hv4 := Nat.mul_le_mul_left rows hv.2.2.2.2.2.2.2.2.2.2.2.2
  have hrV := Nat.le_mul_of_pos_right rows hV
  have hRp : R≤ButterflyAxisHeadersBudget.logicalVolume D R p := by
    have hp : 0<2^D := pow_pos (by decide) _
    have hl : 0<recordLength D p := by unfold recordLength; omega
    have h0 := Nat.le_mul_of_pos_left R hp
    have h1 := Nat.le_mul_of_pos_right (2^D*R) hl
    exact h0.trans h1
  exact ⟨hv0,hv1,hv2,hv3,hv4,hrV,hRp.trans hv0⟩

def headerConstant := 10000+2*FixedBasePowerDescriptor.constant 2

theorem headers_linear (rows D t R p : ℕ) (hr : 0<rows) (ht : t<D) (hR : 0<R) :
    scheduleCost ButterflySpectatorHeaders.schedule (ButterflySpectatorHeaders.initial rows D t R p)+
    scheduleCost ButterflySpectatorHeaders.cleanup (ButterflySpectatorHeaders.output rows D t R p)≤
      headerConstant*volume rows D R p := by
  obtain ⟨hD,hp,ht',hd,hW,hlo,hH,hN,hL,hB,h2H,hP,hS⟩ := ButterflyAxisHeadersBudget.values_le D t R p ht hR
  obtain ⟨hv,hrH,hr2H,hrP,hrS,hr',hR'⟩ := row_values rows D t R p hr ht hR
  have hV := positive rows D R p hr hR
  have hpow := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2)
    (show 2^t+higher D t≤2*volume rows D R p by omega)
  have hpw : FixedBasePowerDescriptor.constant 2*(2^t+higher D t)≤
      2*(FixedBasePowerDescriptor.constant 2*volume rows D R p) := by nlinarith only [hpow]
  have hD' := hD.trans hv
  have hp' := hp.trans hv
  have ht'' := ht'.trans hv
  have hd' := hd.trans hv
  have hW' := hW.trans hv
  have hlo' := hlo.trans hv
  have hH' := hH.trans hv
  have hN' := hN.trans hv
  have hL' := hL.trans hv
  have hB' := hB.trans hv
  have hds : D-t-1≤volume rows D R p := by omega
  simp only [header_cost_eq,cleanup_cost_eq]
  unfold headerConstant
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc] at *
  omega


theorem words_le (rows D t R p : ℕ) (hr : 0<rows) (ht : t<D) (hR : 0<R) :
    ∀ i,Counter.value (words rows D t R p i)≤volume rows D R p := by
  obtain ⟨_,_,hr2H,hrP,hrS,_,_⟩ := row_values rows D t R p hr ht hR
  have h2 : 2*(rows*higher D t)≤volume rows D R p := by nlinarith only [hr2H]
  have hV := positive rows D R p hr hR
  have hv := ButterflyAxisHeadersBudget.values_le D t R p ht hR
  have hbound := (row_values rows D t R p hr ht hR).1
  intro i
  induction i using Fin.addCases (m:=2) (n:=6) with
  | left i =>
    simp only [words,Fin.addCases_left]
    fin_cases i
    · change Counter.value (RecursiveChildQuotientsConstant.bits (rows*pairCount D t R))≤volume rows D R p
      simpa only [RecursiveChildQuotientsConstant.bits_value] using hrP
    · change Counter.value (RecursiveChildQuotientsConstant.bits (rows*streamLength D t R p))≤volume rows D R p
      simpa only [RecursiveChildQuotientsConstant.bits_value] using hrS
  | right i =>
    simp only [words,Fin.addCases_right,headers]
    fin_cases i <;> simp [values,RecursiveChildQuotientsConstant.bits_value]
    all_goals omega

def constant := headerConstant+ButterflyAxisRun.constant+156

theorem cost_linear (rows D t R p : ℕ) (hr : 0<rows) (ht : t<D) (hR : 0<R) :
    ButterflySpectatorOriginal.cost rows D t R p≤constant*volume rows D R p := by
  have hV := positive rows D R p hr hR
  have hh := headers_linear rows D t R p hr ht hR
  have hc := FixedHeaderBankCopy.cost_linear (words rows D t R p) (volume rows D R p) hV
    (canonical rows D t R p) (words_le rows D t R p hr ht hR)
  have he := FixedHeaderBankCopy.cleanup_cost_linear (t:=44) (words rows D t R p) (volume rows D R p) hV
    (canonical rows D t R p) (words_le rows D t R p hr ht hR)
  unfold ButterflySpectatorOriginal.cost ButterflySpectatorOriginal.axisCost
  rw [row_volume rows D t R p ht]
  unfold constant
  nlinarith only [hh,hc,he,hV]

theorem inverse_cost_linear (rows D t R p : ℕ) (hr : 0<rows) (ht : t<D) (hR : 0<R) :
    ButterflyInverseSpectatorOriginal.cost rows D t R p≤constant*volume rows D R p := by
  exact cost_linear rows D t R p hr ht hR

end
end IntegerMultBounds.Machine.ButterflySpectatorBudget
