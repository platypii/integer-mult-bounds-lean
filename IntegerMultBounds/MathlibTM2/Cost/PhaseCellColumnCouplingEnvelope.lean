module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFeedCouplingWorkspaceBound

/-! Keep fixed program coefficients opaque during selected-size arithmetic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {P₀ U : Type}

@[irreducible] noncomputable def columnCouplingEnvelopeCoefficient (boundary : Bool) (K cw : ℕ) : ℕ :=
  K+2*cw+500000+packetCoefficientPush (Q := Q) (A := A) (U := U)+
    zeroPacketSpatialCouplingRowPush (P₀ := P₀) (Q := Q) (A := A) (U := U)+
    spatialCouplingSourcePush (P₀ := P₀) (Q := Q) (A := A) (U := U) boundary+
    couplingGuardPush (Q := Q) (A := A) (U := U)+retainedCouplingPacketPush (Q := Q) (A := A) (U := U)

theorem columnCouplingEnvelopeCoefficient_bounds (boundary : Bool) (K cw : ℕ) :
    let C := columnCouplingEnvelopeCoefficient (P₀ := P₀) (Q := Q) (A := A) (U := U) boundary K cw
    13 ≤ C ∧ K ≤ C ∧ cw ≤ C ∧ 2*cw+426064 ≤ C ∧ 32768 ≤ C ∧
    ∀ x ∈ [packetCoefficientPush (Q := Q) (A := A) (U := U),
      zeroPacketSpatialCouplingRowPush (P₀ := P₀) (Q := Q) (A := A) (U := U),
      spatialCouplingSourcePush (P₀ := P₀) (Q := Q) (A := A) (U := U) boundary,
      couplingGuardPush (Q := Q) (A := A) (U := U),retainedCouplingPacketPush (Q := Q) (A := A) (U := U)], x ≤ C := by
  dsimp only
  unfold columnCouplingEnvelopeCoefficient
  refine ⟨by omega,by omega,by omega,by omega,by omega,?_⟩
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  all_goals omega

end IntegerMultBounds.MathlibTM2.Cost
