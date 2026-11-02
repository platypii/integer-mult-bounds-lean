module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStreamedChunkBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBalancedChunkInterchangeLoop

/-! Binary schedule rows, exact worker frames and paid stage ledgers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace StreamedChunkBank
variable {t₀ T Q K : ℕ}

noncomputable def scheduleStream (bank : StreamedChunkBank t₀ T Q) (V : ℕ) :
    List (BalancedChunkInterchangeStage T) → List (Fin (prime+K+4))
  | [] => []
  | r::rs => ((interchangeDimensionRow bank.dims r.outerCount r.blockWidth r.leftBits r.rightBits).flatMap
      fun p => binSyms V p.1)++bank.scheduleStream V rs

noncomputable def scheduleState (bank : StreamedChunkBank t₀ T Q) (V : ℕ)
    (rs : List (BalancedChunkInterchangeStage T)) (xs : List Bool)
    (tail : List (Fin (prime+K+4))) (S : Stacks T (prime+K)) : Stacks T (prime+K) :=
  {S with L := fun _ => [], R := (Function.update (Function.update S.R bank.queue
    (bank.scheduleStream V rs++tail)) (bank.ι (reg bank.pay)) (xs.map bitSymbol))}

noncomputable def stageTimeCost (bank : StreamedChunkBank t₀ T Q) (V stock : ℕ)
    (r : BalancedChunkInterchangeStage T) : ℕ :=
  let row := interchangeDimensionRow bank.dims r.outerCount r.blockWidth r.leftBits r.rightBits
  readDimensionRowCost V row+
    generatedBalancedChunkInterchangeCost T t₀ r.outerCount r.blockWidth r.leftBits r.rightBits stock+
    (2*(row.map Prod.fst).sum+2*row.length+1)

noncomputable def stageStockAllowance (bank : StreamedChunkBank t₀ T Q) (V : ℕ)
    (r : BalancedChunkInterchangeStage T) : ℕ :=
  3*readDimensionRowCost V (interchangeDimensionRow bank.dims r.outerCount r.blockWidth r.leftBits r.rightBits)+
    generatedChunkStockAllowance T r.outerCount r.blockWidth r.leftBits r.rightBits

noncomputable def scheduleStockAllowance (bank : StreamedChunkBank t₀ T Q) (V : ℕ) :
    List (BalancedChunkInterchangeStage T) → ℕ
  | [] => 0
  | r::rs => max (bank.stageStockAllowance V r) (bank.scheduleStockAllowance V rs)

theorem stageStockAllowance_le (bank : StreamedChunkBank t₀ T Q) (V : ℕ)
    (rs : List (BalancedChunkInterchangeStage T)) :
    ∀ r ∈ rs, bank.stageStockAllowance V r ≤ bank.scheduleStockAllowance V rs := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    intro s hs
    rcases List.mem_cons.mp hs with he | hs
    · subst s; exact Nat.le_max_left _ _
    · exact (ih s hs).trans (Nat.le_max_right _ _)

theorem scheduleState_ready (bank : StreamedChunkBank t₀ T Q) (V : ℕ)
    (rs : List (BalancedChunkInterchangeStage T)) (xs : List Bool)
    (tail : List (Fin (prime+K+4))) (S : Stacks T (prime+K)) (hready : bank.Ready V S) :
    bank.Ready V (bank.scheduleState V rs xs tail S) := by
  apply Ready.of_frame bank V S _ hready (by intro i; rfl)
  intro i hq hp
  simp only [scheduleState,Function.update_of_ne hp,Function.update_of_ne hq]

theorem scheduleState_bankStock (bank : StreamedChunkBank t₀ T Q) (V : ℕ)
    (rs : List (BalancedChunkInterchangeStage T)) (xs : List Bool)
    (tail : List (Fin (prime+K+4))) (S : Stacks T (prime+K))
    (hlen : xs.length = (S.R (bank.ι (reg bank.pay))).length) :
    (∑ j, ((bank.scheduleState V rs xs tail S).R (bank.ι j)).length) =
      ∑ j, (S.R (bank.ι j)).length := by
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hp : bank.ι j = bank.ι (reg bank.pay)
  · simp only [scheduleState,hp,Function.update_self,List.length_map,hlen]
  · simp only [scheduleState,Function.update_of_ne hp,Function.update_of_ne (bank.hqueueOff j).symm]

theorem scheduleState_step (bank : StreamedChunkBank t₀ T Q) (V : ℕ)
    (rs ss : List (BalancedChunkInterchangeStage T)) (xs ys : List Bool)
    (tail : List (Fin (prime+K+4))) (S : Stacks T (prime+K)) :
    {(bank.scheduleState V rs xs tail S) with L := (fun _ => []), R := (Function.update
      (Function.update (bank.scheduleState V rs xs tail S).R bank.queue (bank.scheduleStream V ss++tail))
      (bank.ι (reg bank.pay)) (ys.map bitSymbol))} = bank.scheduleState V ss ys tail S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hp : i = bank.ι (reg bank.pay)
  · subst i; simp only [scheduleState,Function.update_self]
  · by_cases hq : i = bank.queue
    · subst i
      simp only [scheduleState,Function.update_of_ne (bank.hqueueOff (reg bank.pay)),Function.update_self]
    · simp only [scheduleState,Function.update_of_ne hp,Function.update_of_ne hq]

end StreamedChunkBank

theorem balancedChunkStageBits_append {T : ℕ} (rs ss : List (BalancedChunkInterchangeStage T)) (xs : List Bool) :
    balancedChunkStageBits (rs++ss) xs = balancedChunkStageBits ss (balancedChunkStageBits rs xs) := by
  induction rs generalizing xs with
  | nil => rfl
  | cons r rs ih => exact ih _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
