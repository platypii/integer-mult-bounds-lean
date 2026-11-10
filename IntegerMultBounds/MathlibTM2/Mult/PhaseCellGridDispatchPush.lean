module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGridDispatchTrace
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Descriptor traffic has a fixed push bound, independent of bank placement.
Only the two fixed closed numerical programs contribute a solver coefficient. -/
@[expose] public section
set_option autoImplicit false
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

private theorem takeDescriptorPacket_push_le (src dst saved count tmp spare : Fin T) :
    mnProgPush (takeDescriptorPacket (P := P) (Q := Q) (A := A) (U := U) src dst saved count tmp spare) ≤ 2 := by
  simp [takeDescriptorPacket,preTake,preWhileTop,prePeek,twMvTop,copyR,copyStep,
    copyPrefix,transfer,transferAct,scanR,keepIn,drainR,popDo,pushN,moveR,moveStep,whileR,peekR,
    uclear,dropTop,mnProgPush,mnActPush]

private theorem takeDescriptorBank_push_le (src saved count tmp spare : Fin T) (ports : List (Fin T)) :
    mnProgPush (takeDescriptorBank (P := P) (Q := Q) (A := A) (U := U) src saved count tmp spare ports) ≤ 2 := by
  induction ports with
  | nil => simp [takeDescriptorBank,mnProgPush,mnActPush]
  | cons dst ports ih =>
    exact max_le (takeDescriptorPacket_push_le ..) ih

private theorem clearWords_push_le (ports : List (Fin T)) :
    mnProgPush (clearWords (P := P) (Q := Q) (A := A) (U := U) ports) ≤ 2 := by
  induction ports with
  | nil => simp [clearWords,mnProgPush,mnActPush]
  | cons r ports ih =>
    have hr : mnProgPush (uclear (P := P) (Q := Q) (A := A) (U := U) r) ≤ 2 := by
      simp [uclear,drainR,popDo,peekR,mnProgPush,mnActPush]
    exact max_le hr ih

/-- The two numerical programs are fixed; placement and metadata never enter. -/
@[irreducible] noncomputable def gridDispatchPush (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : ℕ :=
  max 2 (max (mnProgPush (gridFamilyInverseBatch (P := Empty) (A := A) (U := U) false hR hQ))
    (mnProgPush (gridFamilyInverseBatch (P := Empty) (A := A) (U := U) true hR hQ)))

theorem gridFamilyDispatch_push_le (work : Fin 303 → Fin T)
    (src saved count tmp spare result clock savedClock : Fin T) (recovery : Bool)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) :
    mnProgPush (gridFamilyDispatch (P := P) (A := A) (U := U) work src saved count tmp spare result
      clock savedClock recovery hR hQ) ≤ gridDispatchPush (A := A) (U := U) hR hQ := by
  have hload := takeDescriptorBank_push_le (P := P) (Q := Q) (A := A) (U := U) src saved count tmp spare (List.ofFn work)
  have hclear := clearWords_push_le (P := P) (Q := Q) (A := A) (U := U) (List.ofFn work)
  have hcontrol : ∀ a b c : Fin T,
      mnProgPush (copyR (P := P) (Q := Q) (A := A) (U := U) a b c id) ≤ 2 := by
    intro a b c
    simp [copyR,copyStep,scanR,keepIn,drainR,popDo,pushN,moveR,moveStep,whileR,peekR,mnProgPush,mnActPush]
  have hmove : ∀ a b : Fin T,
      mnProgPush (moveR (P := P) (Q := Q) (A := A) (U := U) a b id) ≤ 2 := by
    intro a b
    simp [moveR,moveStep,whileR,peekR,mnProgPush,mnActPush]
  have hsolve : mnProgPush (gridFamilyInverseBatch (P := Empty) (A := A) (U := U) recovery hR hQ) ≤
      gridDispatchPush (A := A) (U := U) hR hQ := by
    unfold gridDispatchPush
    cases recovery
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  have htwo : 2 ≤ gridDispatchPush (A := A) (U := U) hR hQ := by
    unfold gridDispatchPush
    exact le_max_left _ _
  simp only [gridFamilyDispatch,descriptorSolverSchedule,countedLoop,countedLoopBody,
    gridFamilyInverseBatchDispatchStep,descriptorSolverStep,descriptorSolverCall,takePlacedDescriptorBank,
    finishDescriptorBank,mnProgPush,embProg_push,mnActPush,peekR,Nat.zero_max,Nat.max_zero]
  exact max_le (hcontrol .. |>.trans htwo)
    (max_le (max_le (max_le (hload.trans htwo) hsolve)
      (max_le (hmove .. |>.trans htwo) (max_le (hmove .. |>.trans htwo) (hclear.trans htwo))))
      (max_le (hmove .. |>.trans htwo) (hmove .. |>.trans htwo)))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
