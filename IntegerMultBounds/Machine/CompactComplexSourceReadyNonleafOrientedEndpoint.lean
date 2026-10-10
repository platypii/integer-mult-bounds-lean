import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafOrientedFinal

/-! Literal source bytes and original padded cost after the real tag3
post-orientation selector. The decoded inverse endpoint is a separate semantic
conjugation obligation; no unchanged forward endpoint is asserted. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafOrientedEndpoint
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactNativeRoleTransferBudget (volume)
open CompactComplexRecursiveGeometry (arity)
variable {s c : ℕ}

theorem source (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (call : Networks.ComplexRecursiveCallSchema.Call)
    (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2) :
    let w := CompactComplexSourceReadyNonleafFinalPorts.endpoint sh rows ell p rho left count slots right src dst f v leaf
    let out := (CompactComplexSourceReadyOrientation.output call w f).append scratch
    let port := Fin.castAdd CompactComplexSourceReadyScalarWorkspace.scratch
      (CompactComplexSourceReadyOrientation.source (s:=s) (c:=c))
    out.tape port=NativeZeroPadding.word (NativeZeroPaddingArray.word
      (CompactComplexSourceReadyOrientationInvariants.oriented call f)) ∧ out.head port=0 := by
  have hs := CompactComplexSourceReadyNonleafFinalPorts.source sh rows ell p rho left count slots right src dst f v leaf
  have h := CompactComplexSourceReadyOrientationInvariants.output_source call _ f hs.1 hs.2
  simpa only [Tapes.append,Fin.addCases_left] using h

/-- Original padding pays contraction, merging, post selector and both joins. -/
theorem cost_original (c d K levels ell p : ℕ) (sh : Shape) (hc : 0<c) (hK : 0<K) :
    CompactComplexSourceReadyNonleafOrientedFinal.constant c*
      volume (CompactGlobalRowPadding.rowsAt c arity d K levels) sh ell p≤
    (2*CompactComplexSourceReadyNonleafOrientedFinal.constant c)*
      volume (CompactGlobalRowPadding.originalRows c arity d K) sh ell p := by
  have hv := Nat.mul_le_mul_right (CompactNativeRoleOriginal.symbols sh ell p)
    (CompactGlobalRowPadding.rowsAt_le_twice_original c arity d K levels hc hK)
  have hm := Nat.mul_le_mul_left (CompactComplexSourceReadyNonleafOrientedFinal.constant c) hv
  simpa only [volume,Nat.mul_assoc,Nat.mul_left_comm] using hm

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafOrientedEndpoint
