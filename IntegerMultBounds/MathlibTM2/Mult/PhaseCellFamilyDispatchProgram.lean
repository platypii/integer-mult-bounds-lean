module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyDispatchInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorSchedule

/-! Fixed numerical descriptor programs and their output relation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def familyDispatchLoop (work : Fin 303 → Fin T)
    (src saved count tmp spare result clock : Fin T) (recovery : Bool)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  countedLoop clock (familyInverseBatchDispatchStep work src saved count tmp spare result recovery hR hQ)

def FamilyDispatchProduced (p l t : ℕ)
    (x y : FamilyDispatchInput s A → (ZMod s → GaussianInt) → ZMod s → ℝ)
    (r : FamilyDispatchInput s A) (output : List (Fin (A+4))) : Prop :=
  ∃ Zs, output = r.output p l t Zs ∧ FamilyDispatchApprox p l t r (x r) (y r) Zs

noncomputable def familyDispatch (work : Fin 303 → Fin T)
    (src saved count tmp spare result clock savedClock : Fin T) (recovery : Bool)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (copyR clock savedClock tmp id)
    (.seq (familyDispatchLoop work src saved count tmp spare result clock recovery hR hQ)
      (.seq (moveR saved src id) (moveR savedClock clock id)))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
