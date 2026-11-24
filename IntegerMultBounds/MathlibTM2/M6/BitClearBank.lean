module

public import IntegerMultBounds.MathlibTM2.M6.BitCleanupBound

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- Cost of clearing both stacks of a tape. -/
def cleanupWeight (l r : List (Fin (prime+4))) : ℕ := 4*l.length+2*r.length+4

/-- Charge the child once on the union of the cleared bank and the caller's
observed tapes. A cleared tape has minimum weight even when the caller observes it. -/
theorem cleanupBound_clearBank {T : ℕ} {S D F : Stacks T prime} {n m price localCost : ℕ}
    (work : List (Fin T)) (unique : work.Nodup) (child : CleanupBound S D n price)
    (time : m ≤ tapeCharge cleanupWeight work D + localCost)
    (empty : ∀ j ∈ work, F.L j = [] ∧ F.R j = [])
    (stock : ∀ j, (F.L j).length ≤ (D.L j).length ∧ (F.R j).length ≤ (D.R j).length) :
    CleanupBound S F (n+m) (price+tapeCharge cleanupWeight work S+localCost) := by
  intro js distinct
  let outside := js.filter fun j => j ∉ work
  have disjoint : work.Disjoint outside := by
    intro j hj hout
    exact (of_decide_eq_true (List.mem_filter.mp hout).2) hj
  have paid := child (work++outside) (List.nodup_append.mpr
    ⟨unique,distinct.filter _,fun _ ha _ hb eq => disjoint ha (eq ▸ hb)⟩)
  change n+tapeCharge cleanupWeight (work++outside) D ≤ tapeCharge cleanupWeight (work++outside) S+price at paid
  simp only [tapeCharge,List.map_append,List.sum_append] at paid
  have split (xs : List (Fin T)) :
      tapeCharge cleanupWeight xs F + tapeCharge cleanupWeight (xs.filter fun j => j ∉ work) S ≤
      tapeCharge cleanupWeight xs S + tapeCharge cleanupWeight (xs.filter fun j => j ∉ work) D := by
    induction xs with
    | nil => simp [tapeCharge]
    | cons j xs ih =>
      by_cases h : j ∈ work
      · obtain ⟨left,right⟩ := empty j h
        simp [tapeCharge,h,cleanupWeight,left,right] at ih ⊢
        omega
      · obtain ⟨left,right⟩ := stock j
        simp [tapeCharge,h,cleanupWeight] at ih ⊢
        omega
  have bound := split js
  change n+m+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+_
  dsimp only [outside,tapeCharge] at paid time bound ⊢
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
