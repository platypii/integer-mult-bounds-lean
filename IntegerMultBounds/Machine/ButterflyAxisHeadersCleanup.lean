import IntegerMultBounds.Machine.ButterflyAxisHeadersBudget

/-! After an axis finishes, increment the actual selected-position header and
physically erase every generated power, product, guard-width and constant word.
The four original shape headers and the clean shared scratch bank remain. -/
namespace IntegerMultBounds.Machine.ButterflyAxisHeadersCleanup
noncomputable section
open ButterflyAxisHeadersData ButterflyAxisHeadersArithmetic ButterflyAxisHeadersBudget
open ActiveRepairRankHeadersCommands (State)
variable {a : ℕ}

def generated : List (Fin 28) := [4,5,6,7,8,9,10,11,12,13,14,15,16,17,19,20]
def erases (slots : List (Fin 28)) : List Op := slots.map (fun i => cmd (.erase i))
def schedule := cmd (.add 1 4 (by decide))::erases generated

theorem execute_eq (D t R p : ℕ) : execute schedule (output D t R p)=initial D (t+1) R p := by
  funext i
  fin_cases i
  all_goals simp [schedule,generated,erases,execute,eval,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    output,initial,Function.update]

theorem valid (D t R p : ℕ) : validSchedule schedule (output D t R p) := by
  simp [schedule,generated,erases,validSchedule,ButterflyAxisHeadersArithmetic.valid,eval,
    CompactChildHeadersArithmetic.valid,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    output,Function.update]

private theorem erased_cost (slots : List (Fin 28)) (st : State) (V : ℕ)
    (hs : ∀ i,(st i).getD 0≤V) :
    scheduleCost (erases slots) st≤slots.length*(100*(V+1)+1) := by
  induction slots generalizing st with
  | nil => simp [erases,scheduleCost]
  | cons i slots ih =>
    have hb : ∀ j,((Function.update st i none) j).getD 0≤V := by
      intro j
      by_cases hj : j=i
      · simp [Function.update,hj]
      · simpa [Function.update,hj] using hs j
    have hh := ih (Function.update st i none) hb
    simp only [erases,List.map_cons,scheduleCost,List.length_cons,eval,cmd,
      CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.eval,cost,CompactChildHeadersArithmetic.cost,
      ActivePrefixStageHeadersOps.cost,ActiveRepairRankHeadersCommands.cost]
    have hi := hs i
    change 100*((st i).getD 0+1)+1+scheduleCost (erases slots) (Function.update st i none)≤_
    nlinarith

private theorem output_bounded (D t R p : ℕ) (ht : t<D) (hR : 0<R) (i : Fin 28) :
    ((output D t R p) i).getD 0≤logicalVolume D R p := by
  obtain ⟨hD,hp,ht',hd,hW,hlo,hH,hN,hL,hB,h2H,hP,hS⟩ := values_le D t R p ht hR
  have hR' : R≤lower t R := Nat.le_mul_of_pos_left _ (pow_pos (by decide) _)
  have hW1 : width D p+1≤recordLength D p := by unfold recordLength; omega
  have hW4 : 4≤width D p := by unfold width; omega
  fin_cases i <;> simp only [output,Option.getD_some,Option.getD_none]
  all_goals omega

theorem cost_linear (D t R p : ℕ) (ht : t<D) (hR : 0<R) :
    scheduleCost schedule (output D t R p)≤3500*logicalVolume D R p := by
  have hV : 0<logicalVolume D R p := by unfold logicalVolume recordLength; positivity
  have hD := (values_le D t R p ht hR).1
  have hb : ∀ i,((ActiveRepairRankHeadersCommands.put (output D t R p) 1 (t+1)) i).getD 0≤logicalVolume D R p := by
    intro i
    by_cases hi : i=1
    · simp only [ActiveRepairRankHeadersCommands.put,hi,Function.update_self,Option.getD_some]
      omega
    · simpa only [ActiveRepairRankHeadersCommands.put,Function.update_of_ne hi] using output_bounded D t R p ht hR i
  have hh := erased_cost generated _ (logicalVolume D R p) hb
  change scheduleCost (erases generated) (ActiveRepairRankHeadersCommands.put (output D t R p) 1 (t+1))≤
    16*(100*(logicalVolume D R p+1)+1) at hh
  dsimp [schedule,scheduleCost,cost,eval,cmd,CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval]
  change 100*(t+1+1)+1+scheduleCost (erases generated)
    (ActiveRepairRankHeadersCommands.put (output D t R p) 1 (t+1))≤3500*logicalVolume D R p
  nlinarith

theorem runs (D t R p : ℕ) (ht : t<D) (hR : 0<R) :
    HoareTime (compile (a:=a) schedule).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (output D t R p))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (initial D (t+1) R p))
      (3500*logicalVolume D R p) := by
  have hh := schedule_runs (a:=a) schedule (output D t R p) (valid D t R p)
  rw [execute_eq] at hh
  exact hh.consequence (fun _ h => h) (fun _ h => h) (cost_linear D t R p ht hR)

end
end IntegerMultBounds.Machine.ButterflyAxisHeadersCleanup
