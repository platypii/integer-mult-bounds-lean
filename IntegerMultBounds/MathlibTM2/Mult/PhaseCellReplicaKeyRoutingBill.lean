module

public import IntegerMultBounds.MathlibTM2.Host.ChunkSwap
public import Mathlib.Tactic.Ring

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host

/-- The complete counted packed router bill: two interchanges plus all codec,
counting, disposal and bank-normalization passes. `stock` is the initial sum of
lengths in the placed bank, not the payload volume. -/
noncomputable def packedReplicaKeyRoutingCost (T t₀ W h d stock : ℕ) (hs : Fin 5 → List Bool) : ℕ :=
  let V := 2^h*(2^d*W)
  (4*V+4)+((12*V+12)+2*((T+12*swapT t₀+5)*swapCost 1 1 W h d hs+
    6*(stock+2*V)+2*T+6*swapT t₀+15)+(2*V+2)+(8*V+6))

/-- In particular there is no separate traversal term for each key. All linear
passes use the compact routed volume; normalization also pays initial bank stock. -/
theorem packedReplicaKeyRoutingCost_eq (T t₀ W h d stock : ℕ) (hs : Fin 5 → List Bool) :
    packedReplicaKeyRoutingCost T t₀ W h d stock hs =
      2*(T+12*swapT t₀+5)*swapCost 1 1 W h d hs+
        12*stock+50*(2^h*(2^d*W))+4*T+12*swapT t₀+54 := by
  unfold packedReplicaKeyRoutingCost
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
