module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizedDispatchInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorSchedule

/-! Fixed normalized descriptor programs and their uniform output relation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A s : ℕ} [NeZero s] {P U : Type}

noncomputable def normalizedFamilyDispatchLoop (work : Fin 303 → Fin T)
    (src saved count tmp spare result clock : Fin T) (recovery : Bool)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  countedLoop clock (normalizedFamilyInverseBatchDispatchStep work src saved count tmp spare result recovery hR hQ)

def NormalizedDispatchProduced (p : ℕ)
    (x y : FamilyDispatchInput s A → (ZMod s → GaussianInt) → ZMod s → ℝ)
    (r : FamilyDispatchInput s A) (output : List (Fin (A+4))) : Prop :=
  ∃ Zs, output = r.normalizedOutput p Zs ∧ NormalizedDispatchApprox p r (x r) (y r) Zs

noncomputable def normalizedFamilyDispatch (work : Fin 303 → Fin T)
    (src saved count tmp spare result clock savedClock : Fin T) (recovery : Bool)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (copyR clock savedClock tmp id)
    (.seq (normalizedFamilyDispatchLoop work src saved count tmp spare result clock recovery hR hQ)
      (.seq (moveR saved src id) (moveR savedClock clock id)))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
