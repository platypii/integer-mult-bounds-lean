module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderRun
public import IntegerMultBounds.MathlibTM2.Cover.FallbackStoppedGoodRecord

/-! Execution and cost of a prepared ordinary record at a PR589 idle. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime prime_prime)
open IntegerMultBounds.MathlibTM2.Stack Host Cover Cover.Fallback GoodForm Matrix
open IntegerMultBounds.Swap.Modular (reduce)

/-- The scheduled interval determines the program. Each live ordinary record
supplies its actual conjugated projector to both physical adapters. -/
theorem remainderOrdinary_exec [M8.Machine.Net] {U : Type} {n Q : ℕ}
    (e : ℕ × ℕ) (member : e ∈ BitHosting.remainderIntervals)
    (cap : 217 ≤ Q) (fits : Record.leafCapacity 128 ≤ Q) (caller : Fin 58 ↪ Fin n) :
    let P : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i => if e.1 ≤ i.val ∧ i.val < e.2 then 1 else 0
    P.rank = e.2-e.1 ∧ Record.StoppedDirectoryRun (U := U) (d := 63) cap P caller := by
  intro P
  have fitsInterval := (BitHosting.remainder_counts e member).2.1
  exact ⟨intervalDiagonal_rank (by omega),Record.stoppedDirectoryRecord_exec (d := 63) (U := U) cap fits P
    (intervalDiagonal_idem 64 e.1 e.2) (intervalFactor 64 e.1 e.2)
    (intervalFactor_denominators 64 e.1 e.2) caller⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
