import IntegerMultBounds.Machine.CompactComplexSourceReadySinkCorrections

/-! Every physical sink-correction join is absorbed by positive original volume.
The bound is stated with its literal static coefficient to keep proof checking
independent of unfolding the compiled machine. -/
namespace IntegerMultBounds.Machine.CompactComplexSinkCorrectionBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
private theorem paid_join (A B C V : ℕ) (hV : 0<V) :
    A*V+1+(B*V+1+(B*V+1+C*V))≤(A+2*B+C+3)*V := by nlinarith

/-- All three actual joins are absorbed by positive original native volume. -/
theorem cost_linear (rows ell p : ℕ) (hr : 0<rows) (sh : Shape) :
    NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor*
        CompactNativeRoleTransferBudget.volume rows sh ell p+1+
        (NativeUniformPolynomialRotationRoles.constant*
          CompactNativeRoleTransferBudget.volume rows sh ell p+1+
          (NativeUniformPolynomialRotationRoles.constant*
            CompactNativeRoleTransferBudget.volume rows sh ell p+1+
            CompactComplexEndpointRoleExchange.constant*
              CompactNativeRoleTransferBudget.volume rows sh ell p))≤
      (NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor+
        2*NativeUniformPolynomialRotationRoles.constant+CompactComplexEndpointRoleExchange.constant+3)*
          CompactNativeRoleTransferBudget.volume rows sh ell p := by
  have hV : 0<CompactNativeRoleTransferBudget.volume rows sh ell p :=
    Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  exact paid_join
    (NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor)
    NativeUniformPolynomialRotationRoles.constant CompactComplexEndpointRoleExchange.constant
    (CompactNativeRoleTransferBudget.volume rows sh ell p) hV

end
end IntegerMultBounds.Machine.CompactComplexSinkCorrectionBudget
