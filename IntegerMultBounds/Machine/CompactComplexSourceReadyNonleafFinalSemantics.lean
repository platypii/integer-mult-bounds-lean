import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalPath

/-! Exact semantic endpoint of the array physically emitted by tag3's actual
contraction and current-row merger; divisibility comes from the completed full
framed network and capacity from the real upper Path ledger. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalSemantics
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexControllerExactReturn (contracted)
open ButterflySigned (signedValue complexValue)
open Networks.GaussianPrecision (BoundedGrid)
open CompactNativeRoleTransferBudget (volume)
open CompactComplexRecursiveGeometry (arity)

 theorem completed (sh : Shape) (rows ell p current n k M : ℕ)
    (hP : 2*sh.bits≤p)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (wires : Fin (ButterflySpectatorGeometry.Size rows sh.bits (2^ell)) → Networks.ComplexFramedExecution.Wire)
    (addresses : Fin (ButterflySpectatorGeometry.Size rows sh.bits (2^ell)) →
      Networks.BinaryColumns.Address (25^3) (arity^k))
    (original : Networks.ComplexFramedExecution.Wire → Networks.BinaryColumns.Arrays (25^3) (arity^k))
    (hg : ∀ wire address,BoundedGrid n M (original wire address))
    (hcompleted : ∀ i,complexValue
      (signedValue (CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)) (f i).1)
      (signedValue (CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)) (f i).2) current=
      Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (arity^k)) original (wires i) (addresses i))
    (hledger : CompactComplexDenominatorPolicy.minimumCompletedExponent n k≤current)
    {left exponent levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left exponent levels frames returned)
    (R base usedRows : ℕ) (hb : base≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows) :
    ∀ i,complexValue
      (signedValue (CompactSpectatorInheritedGrid.half sh (p-2*sh.bits))
        (contracted (current-CompactComplexDenominatorPolicy.networkTarget n k) f i).1)
      (signedValue (CompactSpectatorInheritedGrid.half sh (p-2*sh.bits))
        (contracted (current-CompactComplexDenominatorPolicy.networkTarget n k) f i).2)
      (CompactComplexDenominatorPolicy.networkTarget n k)=
      Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (arity^k)) original (wires i) (addresses i) := by
  have hcapacity := CompactComplexControllerExactReturnBudget.current_capacity path R base (p-2*sh.bits)
    usedRows current hb hu hroom hlive
  have hgap : current-CompactComplexDenominatorPolicy.networkTarget n k≤
      CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)+1 := by omega
  have hwidth : ∀ i,(f i).1.length=CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)+1 ∧
      (f i).2.length=CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)+1 := by
    have hp : CompactNativeRoleHeaders.recordWidth sh p=CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)+1 := by
      unfold CompactNativeRoleHeaders.recordWidth CompactSpectatorInheritedGrid.half ButterflyGuard.width ButterflyGuard.halfWidth
      omega
    simpa only [hp] using hw
  have hgrid : ∀ i,BoundedGrid (CompactComplexDenominatorPolicy.networkTarget n k)
      (M*4^(2*arity^(k+1))) (complexValue
        (signedValue (CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)) (f i).1)
        (signedValue (CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)) (f i).2) current) := by
    intro i
    rw [hcompleted]
    exact CompactComplexDenominatorPolicy.network_grid n k M original hg (wires i) (addresses i)
  have he := CompactComplexControllerExactReturn.contracted_exact f
    (CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)) current _ _
    (CompactComplexDenominatorPolicy.network_target_le_current n k current hledger) hgap hwidth hgrid
  intro i
  exact (he.2 i).trans (hcompleted i)

/-- The original global row padding pays the entire actual finalization body. -/
theorem cost_original (c d K levels ell p : ℕ) (sh : Shape) (hc : 0<c) (hK : 0<K) :
    CompactComplexSourceReadyNonleafFinalPath.constant c*
      volume (CompactGlobalRowPadding.rowsAt c arity d K levels) sh ell p≤
    (2*CompactComplexSourceReadyNonleafFinalPath.constant c)*
      volume (CompactGlobalRowPadding.originalRows c arity d K) sh ell p := by
  have hv := Nat.mul_le_mul_right (CompactNativeRoleOriginal.symbols sh ell p)
    (CompactGlobalRowPadding.rowsAt_le_twice_original c arity d K levels hc hK)
  have hm := Nat.mul_le_mul_left (CompactComplexSourceReadyNonleafFinalPath.constant c) hv
  simpa only [volume,Nat.mul_assoc,Nat.mul_left_comm] using hm

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalSemantics
