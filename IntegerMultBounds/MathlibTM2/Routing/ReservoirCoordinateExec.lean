module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryCoordinateSchedule
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirExchangeSchedule

/-! The same three exchanges used for physical placement now execute on one
live binary coordinate. Metadata is rewound and every arithmetic tape restores. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}
variable (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3)

theorem reservoirCoordinateChain_forward (q : Fin n) :
    coordinateExchangeChain (reservoirExchangeSpecs n H hfit w hw k) [2, 1, 0] q =
      reservoirPlacement n H hfit w hw k q := by
  change (reservoirFrontSpec n H hfit k).coordinate
      (reservoirTailT n H hfit w hw (reservoirTailU n H hfit w hw q)) = _
  rw [reservoirFrontSpec_coordinate]
  rfl

theorem reservoirCoordinateChain_backward (q : Fin n) :
    coordinateExchangeChain (reservoirExchangeSpecs n H hfit w hw k) [0, 1, 2] q =
      (reservoirPlacement n H hfit w hw k).symm q := by
  change reservoirTailU n H hfit w hw
      (reservoirTailT n H hfit w hw ((reservoirFrontSpec n H hfit k).coordinate q)) = _
  rw [reservoirFrontSpec_coordinate]
  unfold reservoirPlacement reservoirFrontPerm
  split_ifs <;> rfl

def reservoirCoordinateOrder (inverse : Bool) : List (Fin 3) := if inverse then [0, 1, 2] else [2, 1, 0]

theorem reservoirCoordinate_exec (body : P → Pr P T Q A U)
    (rg : Fin 14 → Fin T) (hrg : Function.Injective rg) (L : ℕ) (hn : n < 2 ^ L)
    (inverse : Bool) (q : Fin n) (v : HS T Q A U) (S : Stacks T A)
    (hcoordinate : S.R (rg 0) = binSyms L q.val)
    (hblank : ∀ j : Fin 14, (1 ≤ j.val ∧ j.val < 10) ∨ j = 13 → S.R (rg j) = [])
    (hinput : S.R (rg 11) = delimitedScheduleInput
      (fun j => delimitedBankFrames separator (coordinateExchangeJobs (A := A) rg L (reservoirExchangeSpecs n H hfit w hw k j)))
      (reservoirCoordinateOrder inverse))
    (hsaved : S.R (rg 12) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ 276 * L + 328 ∧
      Exec body (binaryCoordinateScheduleProgram rg) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg 0) (binSyms L (if inverse then ((reservoirPlacement n H hfit w hw k).symm q).val else (reservoirPlacement n H hfit w hw k q).val)) }) := by
  obtain ⟨v', steps, hu, hm, he⟩ := binaryCoordinateSchedule_exec body rg hrg L hn
    (reservoirExchangeSpecs n H hfit w hw k) (reservoirCoordinateOrder inverse) q v S hcoordinate hblank hinput hsaved
  have hlen : (reservoirCoordinateOrder inverse).length = 3 := by cases inverse <;> rfl
  rw [hlen] at hm
  refine ⟨v', steps, hu, by omega, ?_⟩
  cases inverse
  · simpa only [reservoirCoordinateOrder, Bool.false_eq_true, ite_false,
      reservoirCoordinateChain_forward n H hfit w hw k] using he
  · simpa only [reservoirCoordinateOrder, ite_true, reservoirCoordinateChain_backward n H hfit w hw k] using he

end IntegerMultBounds.MathlibTM2.Routing
