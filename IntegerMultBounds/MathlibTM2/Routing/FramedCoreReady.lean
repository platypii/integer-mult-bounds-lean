module

public import IntegerMultBounds.MathlibTM2.Routing.FramedCoreLayout
public import IntegerMultBounds.MathlibTM2.Routing.RepairScheduleReady

/-! Between-call invariant for a fully generated core. Its entire non-stream bank
is reusable, while arbitrary record permutations preserve the stream contract. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node
variable {N A M B : ℕ}

structure FramedCoreReady (str : Fin N) (M B : ℕ) (S : Stacks (N + 3) A) : Prop where
  left : ∀ j, S.L (framedCoreEmbed N j) = []
  blank : ∀ j, j ≠ str → S.R (framedCoreEmbed N j) = []
  tmp : S.R (framedCoreAux N 1) = []
  stream : ∃ l : List (List (Fin (A + 4))), l.length = M ∧
    (∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) ∧ S.R (framedCoreEmbed N str) = l.flatten

theorem FramedCoreReady.advance (str : Fin N) (S : Stacks (N + 3) A)
    (ready : FramedCoreReady str M B S) (π : Equiv.Perm (Fin M))
    (frame rest : List (Fin (A + 4))) :
    FramedCoreReady str M B { S with R := delimitedCallAdvanced S.R (framedCoreAux N 0) (framedCoreAux N 2) (framedCoreEmbed N str) frame rest (repairStreamEffect π B (S.R (framedCoreEmbed N str))) } := by
  have hkeep (j : Fin (N + 3)) (hs : j ≠ framedCoreAux N 0) (ha : j ≠ framedCoreAux N 2)
      (ht : j ≠ framedCoreEmbed N str) :
      delimitedCallAdvanced S.R (framedCoreAux N 0) (framedCoreAux N 2) (framedCoreEmbed N str)
        frame rest (repairStreamEffect π B (S.R (framedCoreEmbed N str))) j = S.R j := by
    simp only [delimitedCallAdvanced, Function.update_of_ne hs, Function.update_of_ne ha, Function.update_of_ne ht]
  constructor <;> dsimp only
  · exact ready.left
  · intro j hj
    rw [hkeep _ (framedCoreEmbed_aux N j 0) (framedCoreEmbed_aux N j 2)
      ((framedCoreEmbed_injective N).ne hj)]
    exact ready.blank j hj
  · rw [hkeep _ ((framedCoreAux_injective N).ne (by decide : (1 : Fin 3) ≠ 0))
      ((framedCoreAux_injective N).ne (by decide : (1 : Fin 3) ≠ 2)) (framedCoreEmbed_aux N str 1).symm]
    exact ready.tmp
  · obtain ⟨l, hl, hrecords, hstream⟩ := ready.stream
    refine ⟨moveRecs π l, length_moveRecs π l, ?_, ?_⟩
    · intro r hr
      exact hrecords r (mem_moveRecs π hl hr)
    · simp only [delimitedCallAdvanced, Function.update_self]
      rw [repairStreamEffect, hstream, ← flatten_moveRecs π l (fun r hr => (hrecords r hr).1)]

end IntegerMultBounds.MathlibTM2.Routing
