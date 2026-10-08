import IntegerMultBounds.Machine.Shared50TapeInvocation

/-! The actual Shared50 three-coordinate reused-world scalar list compiled to
one fixed multitape program. This establishes exact stream-bank exchange and
restoration of arbitrary dirty scratch at linear stream-volume cost; affine
routing and recursive interchange composition remain separate operations. -/
namespace IntegerMultBounds.Machine.Shared50TapeGlobal
open Networks
open Shared50GlobalBudget (Address Scratch World)
variable {a L : ℕ}
noncomputable section

attribute [local irreducible] SharedPointReplay.circuit SharedPointExecution.code
  Shared50Finite.program Shared50GlobalCircuit.program50

abbrev roleCount := 406321422080000

def roleEquiv : Fin roleCount ≃ World :=
  (Fintype.equivFinOfCardEq Shared50GlobalBudget.world_card).symm

def contents (X Y : Address → Fin L → ZMod 2) (S : Scratch → Fin L → ZMod 2) :
    World → Fin L → ZMod 2 :=
  fun k i => Shared50GlobalCircuit.contents (fun j => X j i) (fun j => Y j i) (fun j => S j i) k

def bank (background : Fin roleCount → ℤ → Fin (a+4)) (origins : Fin roleCount → ℤ)
    (X Y : Address → Fin L → ZMod 2) (S : Scratch → Fin L → ZMod 2) (bs : List Bool) :=
  PointwiseRoleGate.bank background origins
    (SparseRoleCircuit.encoded (fun k i => contents X Y S (roleEquiv k) i)) bs

/-- This is the compiled real instruction list, independent of stream length. -/
def program :=
  OneSourceCircuit.program (a := a) roleEquiv Shared50GlobalCircuit.program50 Shared50XorLists.global50

/-- Exact global exchange with all reused side/central streams, outside-word
cells, payload heads, and count controls restored. No clean-scratch premise. -/
theorem exchange_hoare (background : Fin roleCount → ℤ → Fin (a+4)) (origins : Fin roleCount → ℤ)
    (X Y : Address → Fin L → ZMod 2) (S : Scratch → Fin L → ZMod 2)
    (bs : List Bool) (hL : Counter.value bs = L) :
    HoareTime (program (a := a)) (fun w => w = bank background origins X Y S bs)
      (fun w => w = bank background origins Y X S bs)
      (Shared50GlobalCircuit.program50.length*(14*L+14*bs.length+34)) := by
  have hh := OneSourceCircuit.circuit_hoare roleEquiv Shared50GlobalCircuit.program50
    Shared50XorLists.global50 background origins (contents X Y S) bs hL
  simpa only [program,bank,contents,Shared50GlobalCircuit.program50_run] using hh

theorem cost_linear (bs : List Bool) (hL : Counter.value bs = L)
    (hc : GrowingCounterData.Canonical bs) (hpos : 0 < L) :
    Shared50GlobalCircuit.program50.length*(14*L+14*bs.length+34) ≤
      (76*(3*19600^2*5209540))*L := by
  have ht := SparseRoleCircuit.cost_linear Shared50GlobalCircuit.program50.length L bs hL hc hpos
  have hg := Shared50GlobalCircuit.program50_instruction_bound
  nlinarith

/-- The concrete linear bound is a tape-transition bound for this fixed
machine, with the scalar certificate used only to bound its fixed gate count. -/
theorem exchange_hoare_linear (background : Fin roleCount → ℤ → Fin (a+4)) (origins : Fin roleCount → ℤ)
    (X Y : Address → Fin L → ZMod 2) (S : Scratch → Fin L → ZMod 2)
    (bs : List Bool) (hL : Counter.value bs = L)
    (hc : GrowingCounterData.Canonical bs) (hpos : 0 < L) :
    HoareTime (program (a := a)) (fun w => w = bank background origins X Y S bs)
      (fun w => w = bank background origins Y X S bs)
      ((76*(3*19600^2*5209540))*L) :=
  (exchange_hoare background origins X Y S bs hL).consequence (fun _ h => h) (fun _ h => h)
    (cost_linear bs hL hc hpos)

end
end IntegerMultBounds.Machine.Shared50TapeGlobal
