import IntegerMultBounds.Machine.Shared50XorLists

/-! Actual fixed tape machines for the certified Shared50 sparse invocation and
local exchange. Every scalar role is an encoded bit stream, with a shared
canonical length descriptor. Arbitrary dirty scratch streams are restored. -/
namespace IntegerMultBounds.Machine.Shared50TapeInvocation
open Networks Circuit NeighborCounts
variable {a n s L : ℕ}
noncomputable section

attribute [local irreducible] SharedPointReplay.circuit SharedPointExecution.code
  Shared50Finite.program Shared50SparseInvocation.program Shared50SparseInvocation.exchange

def roleCount (n s : ℕ) := n+(n+(509194+(50+s)))

def roleEquiv (n s : ℕ) : Fin (roleCount n s) ≃ Role n 509194 50 s :=
  (Fintype.equivFinOfCardEq (by simp [Role,roleCount])).symm

def contents (X Y : Fin n → Fin L → ZMod 2) (A : Fin 509194 → Fin L → ZMod 2)
    (C : Fin 50 → Fin L → ZMod 2) (S : Fin s → Fin L → ZMod 2) :
    Role n 509194 50 s → Fin L → ZMod 2 :=
  fun k i => banks (fun j => X j i) (fun j => Y j i) (fun j => A j i) (fun j => C j i) (fun j => S j i) k

def bank (background : Fin (roleCount n s) → ℤ → Fin (a+4)) (origins : Fin (roleCount n s) → ℤ)
    (X Y : Fin n → Fin L → ZMod 2) (A : Fin 509194 → Fin L → ZMod 2)
    (C : Fin 50 → Fin L → ZMod 2) (S : Fin s → Fin L → ZMod 2) (bs : List Bool) :=
  PointwiseRoleGate.bank background origins
    (SparseRoleCircuit.encoded (fun k i => contents X Y A C S (roleEquiv n s k) i)) bs

def program (e : Fin n ≃ Triple 50) :=
  OneSourceCircuit.program (a := a) (roleEquiv n s) (Shared50SparseInvocation.program e) (Shared50XorLists.invocation e)

def exchangeProgram (e : Fin n ≃ Triple 50) :=
  OneSourceCircuit.program (a := a) (roleEquiv n s) (Shared50SparseInvocation.exchange e) (Shared50XorLists.exchange e)

/-- Real sparse twelve-block identity shear. Every dirty side/central stream
and every spectator survives exactly, with all heads restored to origins. -/
theorem invocation_hoare (e : Fin n ≃ Triple 50)
    (background : Fin (roleCount n s) → ℤ → Fin (a+4)) (origins : Fin (roleCount n s) → ℤ)
    (X Y : Fin n → Fin L → ZMod 2) (A : Fin 509194 → Fin L → ZMod 2)
    (C : Fin 50 → Fin L → ZMod 2) (S : Fin s → Fin L → ZMod 2)
    (bs : List Bool) (hL : Counter.value bs = L) :
    HoareTime (program (a := a) (s := s) e) (fun w => w = bank background origins X Y A C S bs)
      (fun w => w = bank background origins X (fun j i => Y j i+X j i) A C S bs)
      ((Shared50SparseInvocation.program (s := s) e).length*(14*L+14*bs.length+34)) := by
  have hh := OneSourceCircuit.circuit_hoare (roleEquiv n s) (Shared50SparseInvocation.program e)
    (Shared50XorLists.invocation e) background origins (contents X Y A C S) bs hL
  simpa only [program,bank,contents,Shared50SparseInvocation.program_run,Pi.add_def] using hh

/-- Three actual sparse invocation lists exchange both full data-stream banks
while restoring all dirty scratch and every original payload head. -/
theorem exchange_hoare (e : Fin n ≃ Triple 50)
    (background : Fin (roleCount n s) → ℤ → Fin (a+4)) (origins : Fin (roleCount n s) → ℤ)
    (X Y : Fin n → Fin L → ZMod 2) (A : Fin 509194 → Fin L → ZMod 2)
    (C : Fin 50 → Fin L → ZMod 2) (S : Fin s → Fin L → ZMod 2)
    (bs : List Bool) (hL : Counter.value bs = L) :
    HoareTime (exchangeProgram (a := a) (s := s) e) (fun w => w = bank background origins X Y A C S bs)
      (fun w => w = bank background origins Y X A C S bs)
      ((Shared50SparseInvocation.exchange (s := s) e).length*(14*L+14*bs.length+34)) := by
  have hh := OneSourceCircuit.circuit_hoare (roleEquiv n s) (Shared50SparseInvocation.exchange e)
    (Shared50XorLists.exchange e) background origins (contents X Y A C S) bs hL
  simpa only [exchangeProgram,bank,contents,Shared50SparseInvocation.exchange_run] using hh

/-- Concrete linear transition coefficient for the actual fifty-point local
invocation, using the existing certified scalar-instruction bound. -/
theorem invocation_cost50 (e : Fin 19600 ≃ Triple 50) (bs : List Bool)
    (hL : Counter.value bs = L) (hc : GrowingCounterData.Canonical bs) (hpos : 0 < L) :
    (Shared50SparseInvocation.program (s := s) e).length*(14*L+14*bs.length+34) ≤
      (76*5209540)*L := by
  have ht := SparseRoleCircuit.cost_linear (Shared50SparseInvocation.program (s := s) e).length L bs hL hc hpos
  have hg := Shared50SparseInvocation.instruction_bound50 (s := s) e
  nlinarith

theorem exchange_cost50 (e : Fin 19600 ≃ Triple 50) (bs : List Bool)
    (hL : Counter.value bs = L) (hc : GrowingCounterData.Canonical bs) (hpos : 0 < L) :
    (Shared50SparseInvocation.exchange (s := s) e).length*(14*L+14*bs.length+34) ≤
      (76*15628620)*L := by
  have ht := SparseRoleCircuit.cost_linear (Shared50SparseInvocation.exchange (s := s) e).length L bs hL hc hpos
  have hg := Shared50SparseInvocation.exchange_instruction_bound50 (s := s) e
  nlinarith

end
end IntegerMultBounds.Machine.Shared50TapeInvocation
