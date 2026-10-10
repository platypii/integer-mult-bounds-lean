import IntegerMultBounds.Machine.CompactComplexControllerDenominator
import IntegerMultBounds.Machine.CompactSpectatorInheritedGrid

/-! Semantic return policies distinguish stopped leaves from completed array
networks. A leaf keeps its actual n+axes denominator. A nonleaf has the proved
endpoint grid n+2*volume; enough real child calls exist to cover this target
once their actual live-denominator progression is connected to completion.
This file does not supply or assume a whole-stream execution callback. -/
namespace IntegerMultBounds.Machine.CompactComplexDenominatorPolicy
noncomputable section
open Networks Networks.GaussianPrecision Networks.ComplexRank25 NeighborCounts
open CompactComplexRecursiveGeometry CompactRecursiveDependencyBudget
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
attribute [local irreducible] RankTrace.loss ComplexRank25.rankSum ComplexRank25.program
  ComplexRecursiveCallSchema.calls ComplexFramedExecution.rows GlobalProjectionRank.rankSum

/-- A genuine lower bound from the actual finite network's rank balance,
complementing its existing upper branching bound. -/
theorem calls_ge_two_arity : 2*arity≤ComplexRecursiveCallSchema.calls.length := by
  have hb := GlobalProjectionRank.rank_balance_dimensions (Labels.binary 25) form_symm
    Labels.binary_nondegenerate vector vector_self triples pairs (Equiv.refl (Fin 26))
    owner gather inject scatter target inject_support neighbor_orthogonal wires wires_complete
  have hw : Fintype.card (GlobalCircuit.World (Triple 25) (ComplexPairs 25) (Fin 26)) =
      58645352620000 := NetworkBudget.complex_role_card_25
  rw [hw,triple_card,show Nat.choose 25 3=2300 by decide] at hb
  norm_num at hb
  have hlarge : 916333610353500000≤rankSum := by
    unfold rankSum
    omega
  rw [ComplexRecursiveCallSchema.calls_rankSum]
  unfold arity
  omega

def leafTarget (n k : ℕ) := n+arity^k
def networkTarget (n k : ℕ) := n+2*arity^(k+1)

/-- Counts the actual full scalar list and one child-volume advance for every
literal residual-coordinate call. It is a completed mathematical ledger;
its equality/lower bound to physical storage7 remains an execution obligation. -/
def minimumCompletedExponent (n k : ℕ) :=
  n+ComplexFramedExecution.rows.length+ComplexRecursiveCallSchema.calls.length*arity^k

private theorem count_budget (n rows calls width ar : ℕ) (hc : 2*ar≤calls) :
    n+2*(width*ar)≤n+rows+calls*width := by
  have hh := Nat.mul_le_mul_right width hc
  nlinarith

/-- The real nonleaf policy fits the real completed-call ledger. No abstract
branching-count allowance or guessed depth constant enters the inequality. -/
theorem network_target_le_completed (n k : ℕ) :
    networkTarget n k≤minimumCompletedExponent n k := by
  unfold networkTarget minimumCompletedExponent
  rw [pow_succ]
  exact count_budget n ComplexFramedExecution.rows.length
    ComplexRecursiveCallSchema.calls.length (arity^k) arity calls_ge_two_arity

/-- Interface for the physical live header: the execution proof must show
that the stored exponent covers the actual completed-call ledger. Merely
retaining the input exponent or a width reservation does not meet it. -/
theorem network_target_le_current (n k current : ℕ)
    (hcompleted : minimumCompletedExponent n k≤current) :
    networkTarget n k≤current :=
  (network_target_le_completed n k).trans hcompleted

/-- A genuine stopped-axis execution finishes at its own leaf grid. Keeping
that grid requires no precision contraction at the return boundary. The
equality premise is the physical axis-execution interface, not a width bound. -/
theorem leaf_actual_current (n k current : ℕ) (hcurrent : current=n+arity^k) :
    leafTarget n k=current ∧ current-leafTarget n k=0 := by
  subst current
  exact ⟨rfl,Nat.sub_self _⟩

/-- Full actual framed-network correctness gives a fresh endpoint budget,
removing internal scalar-growth overhead from the semantic returned value. -/
theorem network_grid (n k M : ℕ)
    (stored : ComplexFramedExecution.Wire → BinaryColumns.Arrays (25^3) (arity^k))
    (hs : ∀ i ω,BoundedGrid n M (stored i ω)) (i : ComplexFramedExecution.Wire)
    (ω : BinaryColumns.Address (25^3) (arity^k)) :
    BoundedGrid (networkTarget n k) (M*4^(2*arity^(k+1)))
      (FramedCircuit.run (ComplexFramedExecution.network (arity^k)) stored i ω) := by
  have hh := network_return_grid (arity^k) n M stored hs i ω
  simpa only [networkTarget,pow_succ,arity] using hh

/-- A stopped forward leaf keeps its genuine post-axis exponent. In
particular it does not attempt to return upward to n+twice-volume. -/
theorem leaf_forward_grid (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk)
    {left k : ℕ} (visit : Visit s.active left k) (n M : ℕ) (f : Array s rows ell)
    (hw : CompactSpectatorInheritedGrid.Width s rows ell q f)
    (hg : CompactSpectatorInheritedGrid.Grid s rows ell q n M f)
    (hguard : 4*(M*4^(arity^k))<2^(CompactSpectatorInheritedGrid.half s q)) :
    CompactSpectatorInheritedGrid.Grid s rows ell q (leafTarget n k) (M*4^(arity^k))
      (CompactSpectatorInheritedGrid.forward s rows ell q rho visit (arity^k) f) :=
  CompactSpectatorInheritedGrid.forward_grid s rows ell q rho visit (arity^k) n M le_rfl f hw hg hguard

theorem leaf_inverse_grid (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk)
    {left k : ℕ} (visit : Visit s.active left k) (n M : ℕ) (f : Array s rows ell)
    (hw : CompactSpectatorInheritedGrid.Width s rows ell q f)
    (hg : CompactSpectatorInheritedGrid.Grid s rows ell q n M f)
    (hguard : 4*(M*4^(arity^k))<2^(CompactSpectatorInheritedGrid.half s q)) :
    CompactSpectatorInheritedGrid.Grid s rows ell q (leafTarget n k) (M*4^(arity^k))
      (CompactSpectatorInheritedGrid.inverse s rows ell q rho visit (arity^k) f) :=
  CompactSpectatorInheritedGrid.inverse_grid s rows ell q rho visit (arity^k) n M le_rfl f hw hg hguard

/-- Both branches advance by at least their own volume and at most twice it.
A stopped leaf needs zero return gap at its actual physical post-axis grid. -/
theorem leaf_bounds (n k : ℕ) : n+arity^k≤leafTarget n k ∧ leafTarget n k≤n+2*arity^k ∧
    leafTarget n k-leafTarget n k=0 := by unfold leafTarget; omega

theorem network_bounds (n k : ℕ) : n+arity^(k+1)≤networkTarget n k ∧
    networkTarget n k=n+2*arity^(k+1) := by unfold networkTarget; omega

end
end IntegerMultBounds.Machine.CompactComplexDenominatorPolicy
