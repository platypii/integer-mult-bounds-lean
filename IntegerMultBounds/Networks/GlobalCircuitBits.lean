import IntegerMultBounds.Networks.GlobalCircuit
import IntegerMultBounds.Networks.CircuitBits

/-! The full three-coordinate bit network on the actual physical wire layout.
This establishes scalar routing and dirty-scratch restoration. Like the generic
global circuit, it does not establish grouped incidence topology or tape costs. -/

namespace IntegerMultBounds.Networks.GlobalCircuit

open Circuit NeighborCounts

/-- Enumerate local neighboring pairs using the actual global side-wire names. -/
def bitLocalPairs {h n a : ℕ} (eB : Fin n ≃ Triple h) (eA : Fin a ≃ BitPairs h) :
    Fin a ≃ BitPair (fun i => (eB i).val) :=
  eA.trans (pairsEquiv eB (@BitNeighbor h)).symm

/-- Three actual coordinate stages, each with its own scratch per invocation. -/
def bitProgram {h n a : ℕ} (eB : Fin n ≃ Triple h) (eA : Fin a ≃ BitPairs h) :
    Program (Wires.BitRole h) (ZMod 2) :=
  program eB eA (Equiv.refl (Fin h))
    (bitCopy (bitLocalPairs eB eA)) (bitGather (fun i => (eB i).val))
    (bitInject (bitLocalPairs eB eA)) (bitScatter (fun i => (eB i).val))

/-- In characteristic two the full signed exchange becomes a literal swap.
Every scratch scalar is restored, with no clean-scratch assumption. -/
theorem bitProgram_run {h n a : ℕ} (eB : Fin n ≃ Triple h) (eA : Fin a ≃ BitPairs h)
    (X Y : Wires.Address h → ZMod 2)
    (S : Wires.Invocation h × (BitPairs h ⊕ Fin h) → ZMod 2) :
    run (bitProgram eB eA) (contents X Y S) = contents Y X S := by
  have hr := program_run eB eA (Equiv.refl (Fin h))
    (bitCopy (bitLocalPairs eB eA)) (bitGather (fun i => (eB i).val))
    (bitInject (bitLocalPairs eB eA)) (bitScatter (fun i => (eB i).val))
    (bit_reconstruct _ (Subtype.val_injective.comp eB.injective) (fun i => (eB i).property)) X Y S
  have hn : -Y = Y := by funext b; exact ZMod.neg_eq_self_mod_two (Y b)
  simpa only [bitProgram, hn] using hr

theorem bitProgram_length {h n a : ℕ} (eB : Fin n ≃ Triple h)
    (eA : Fin a ≃ BitPairs h) :
    (bitProgram eB eA).length = 3 * n ^ 2 * (4 * n + 2 * a + 2 * h) :=
  program_length _ _ _ _ _ _ _

end IntegerMultBounds.Networks.GlobalCircuit
