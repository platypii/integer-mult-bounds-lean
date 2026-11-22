module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderPiece
public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedEndpoint

/-! Charge the independent borrowed-row node on its parent descriptor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open IntegerMultBounds.Networks.Certificates.PR589 IntegerMultBounds.Networks.Certificates.PR589.Nine
open BitHosting BitSchedule BitOccurrences Cover M8.RevMachine ActualAffineScaling
open IntegerMultBounds.Swap.Modular (reduce)
open M8.Machine.ArbitraryWidthOriginalTotalRun (cost)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- A remainder on another bank pair preserves the full source and target
equations of a sweep, including its independent label coordinates. -/
theorem BorrowedPorts.afterIdle {n : Fin 9} {w B K : ℕ} {x y z}
    (ports : BorrowedPorts n w B K x y) (i : Fin 9) (distinct : activePair n.val ≠ pairOf i)
    (off : ∀ j, (∀ k, j ≠ idleTape i k) → z j = y j) : BorrowedPorts n w B K x z := by
  intro run t g cell owner j src dst read input
  have same (a : Fin 661) (data : a.val < 222) : z (owner a) = y (owner a) := by
    apply off
    intro k eqn
    have roles : BitNode.owner n run.1 run.2 a = idleRole i k :=
      (Fintype.equivFin Role).injective (Fin.cast_injective _ (Fin.castSucc_injective _ eqn))
    have pair := (idleRole_coverage i _).mp ⟨k,roles.symm⟩
    simp only [BitNode.owner,data,ite_true] at pair
    exact distinct ((side_pair n run.1 run.2 _ (by unfold regSide; split <;> omega) _).symm.trans pair)
  have kept (a : Fin 661) (data : a.val < 222) : read z a = read y a := by
    funext s
    simpa only [read,phaseRead,Copy.extendStored,dite_eq_left a.isLt] using
      congrFun (same a data) (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j)
  rw [kept src (by dsimp [src]; omega),kept dst (by dsimp [dst]; omega)]
  exact ports run t g cell

/-- Follow an active pair across a sequence of remainders on other pairs. -/
theorem BorrowedPorts.afterIdles {n : Fin 9} {w B K : ℕ} {x y}
    (ports : BorrowedPorts n w B K x y) (idle : Fin 9 → OwnerStage _)
    (off : ∀ i a j, (∀ k, j ≠ idleTape i k) → (idle i).transform a j = a j)
    (windows : List (Fin 9)) (apart : ∀ i ∈ windows, activePair n.val ≠ pairOf i) :
    BorrowedPorts n w B K x (windows.foldl (fun a i => (idle i).transform a) y) := by
  induction windows generalizing y with
  | nil => exact ports
  | cons i rest ih =>
    exact ih (ports.afterIdle i (apart i List.mem_cons_self) (off i y))
      (fun k hk => apart k (List.mem_cons_of_mem _ hk))

/-- Cost of the borrowed-row sweeps and physical idle schedule on one aligned parent descriptor. -/
theorem borrowedNode_parentCost [M8.Machine.Net] (engine : CopyTranspose := CopyTranspose.original) :
    ∃ D : ℝ, ∀ (parent : Descriptor) (w B rows : ℕ), parent.Positive → 0 < w → 0 < B →
      parent.width = 64*w → parent.rows = 142080*rows → parent.beforeH = B*prime^(64*(w*64)) →
      let K := parent.beforeRows*rows*parent.between*parent.afterD
      let W := B*prime^(64*(w*64))*K
      let spectators := (prime^w)^112*K
      let phaseW := B*prime^(64*(w*64))*spectators
      let V := (prime^w)^16*phaseW
      let v : Descriptor := ⟨(prime^w)^128,1,B*prime^(64*(w*64)),0,1,K⟩
      ∃ (size : volume prime v = V)
        (inv idle : Fin 9 → OwnerStage V) (bridge : ℕ → ℕ → OwnerStage V) (exchange : OwnerStage V),
        BankActions bridge exchange ∧
        (∀ (price : ℕ → ℕ) (rate : ℕ → ℝ),
          (∀ p ∈ Geometry.Moves.phaseEdges, Geometry.moveRank p.1 p.2 ≠ 0 →
            phaseChildCost w phaseW p ≤ price (Geometry.moveRank p.1 p.2)) →
          engine.time (copyChild w phaseW) (fun j => FlatCoordinateSchedule.bits
            (RecursiveDimensionBank.values (copyChild w phaseW) j)) ≤ price 7 →
          (∀ (i : Fin 9) (c : Fin 222), let e := idleInterval i c
            let child := phaseIntervalChild e.1 e.2 w W 64
            cost child (fun j => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values child j)) ≤ price (e.2-e.1)) →
          (∀ j ∈ nodeChildren5, (price j : ℝ) ≤ V*rate j) →
          ((compiledNode inv idle bridge exchange).cost : ℝ) ≤
            volume prime parent*(D*(w : ℝ)^M8.Machine.BudgetBound.tau + (nodeChildren5.map rate).sum/142080)) ∧
        (∀ n x, stageRuns.foldr (fun k cont a => ∃ b, BorrowedStep n w B spectators k a b ∧ cont b)
          (fun a => a = (inv n).transform x) x ∧ BorrowedPorts n w B spectators x ((inv n).transform x) ∧
          BorrowedHelpers n w B spectators x ((inv n).transform x)) ∧
        (∀ n x (windows : List (Fin 9)), (∀ i ∈ windows, activePair n.val ≠ pairOf i) →
          BorrowedPorts n w B spectators x (windows.foldl (fun a i => (idle i).transform a) ((inv n).transform x))) ∧
        ∀ i x, (∀ k, IdleTransport i k w B K (fun t => x (idleTape i k) (Fin.cast size t))
          (fun t => (idle i).transform x (idleTape i k) (Fin.cast size t))) ∧
          ∀ j, (∀ k, j ≠ idleTape i k) → (idle i).transform x j = x j := by
  have assemble := compiledNode_cost_of_sweeps engine (2*(63*9+252*527)+1322*252) (fun w B K inv =>
    ∀ n x, stageRuns.foldr (fun k cont a => ∃ b, BorrowedStep n w B K k a b ∧ cont b)
      (fun a => a = (inv n).transform x) x ∧ BorrowedPorts n w B K x ((inv n).transform x) ∧
        BorrowedHelpers n w B K x ((inv n).transform x))
  obtain ⟨C,build⟩ := borrowedPieces_nodeCost engine
  obtain ⟨D,node⟩ := assemble ⟨C,fun w B K hw hb hk => by
    obtain ⟨inv,bill,trace⟩ := build w B K hw hb hk
    exact ⟨inv,bill,fun n x => ⟨trace n x,borrowedSweep_ports (trace n x),borrowedSweep_helpers (trace n x)⟩⟩⟩
  refine ⟨D,?_⟩
  intro parent w B rows positive hw hb width split label K W spectators phaseW V v
  obtain ⟨size,inv,idle,bridge,exchange,bank,bill,sweep,rest⟩ := node parent w B rows positive hw hb width split label
  exact ⟨size,inv,idle,bridge,exchange,bank,bill,sweep,fun n x windows apart =>
    (sweep n x).2.1.afterIdles idle (fun i a => (rest i a).2) windows apart,rest⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
