module

public import IntegerMultBounds.MathlibTM2.M6.PortSwap
public import IntegerMultBounds.MathlibTM2.M8.Exchange

/-! Folding a simultaneous port permutation into already scheduled endpoint interchanges. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6

open IntegerMultBounds.Swap.Shear (Op State run interchanges)
open M8.Exchange (transform)

/-- Crossing the partners of two endpoint interchanges performs the ordinary
two interchanges followed by the port permutation on both address halves. -/
theorem crossed_port_swaps {R : Type*} [CommRing R] (s : State (Fin 8) R) :
    run [.interchange 0 7, .interchange 7 0] s =
      transform portSwap portSwap (run [.interchange 0 0, .interchange 7 7] s) := by
  apply Prod.ext <;> funext k <;>
    simp only [transform, portSwap_mulVec, IntegerMultBounds.Swap.Shear.run_cons,
      IntegerMultBounds.Swap.Shear.run_nil, Op.run] <;>
    fin_cases k <;> simp [Equiv.swap_apply_def, Function.update]

/-- An intervening program can stay in place when it commutes with the first
endpoint interchange in both partner assignments. Thus the two credited swaps
need not be consecutive. -/
theorem crossed_port_window {R : Type*} [CommRing R] (mid : List (Op (Fin 8) R))
    (commutes : ∀ j ∈ ([0, 7] : List (Fin 8)), ∀ s : State (Fin 8) R,
      run mid ((Op.interchange 0 j).run s) = (Op.interchange 0 j).run (run mid s))
    (s : State (Fin 8) R) :
    run (.interchange 0 7 :: mid ++ [.interchange 7 0]) s =
      transform portSwap portSwap (run (.interchange 0 0 :: mid ++ [.interchange 7 7]) s) := by
  simp only [IntegerMultBounds.Swap.Shear.run_cons, IntegerMultBounds.Swap.Shear.run_append,
    commutes 7 (by decide), commutes 0 (by decide)]
  exact crossed_port_swaps (run mid s)

theorem crossed_port_window_count {R : Type*} (mid : List (Op (Fin 8) R)) :
    interchanges (.interchange 0 7 :: mid ++ [.interchange 7 0]) = interchanges mid + 2 := by
  change interchanges ([.interchange 0 7] ++ (mid ++ [.interchange 7 0])) = _
  simp only [IntegerMultBounds.Swap.Shear.interchanges_append]
  change 1 + (interchanges mid + 1) = _
  omega

end IntegerMultBounds.MathlibTM2.M6
