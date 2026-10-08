import IntegerMultBounds.Networks.Shared50InvocationPhysicalEdges
import IntegerMultBounds.Networks.Shared50FramedOpposite
import IntegerMultBounds.Networks.ProjectionTrace
import IntegerMultBounds.Networks.ShearFrame

/-! Actual projector-difference matrices for the physical optimized invocations.
Every extracted physical frame change is the shear of its certified matrix,
in the same order. Matrix range ranks telescope with the exact local loss;
there is no assumed edge-cost or readiness contract. -/

namespace IntegerMultBounds.Networks.Shared50InvocationProjectionRank

open scoped TensorProduct
open MotifLabels Shared50StageFrames Shared50LabeledInvocation NeighborCounts

section Matrices
variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

/-- The rank of a real linear operator, measured by its actual range. -/
noncomputable def rangeRank (op : V →ₗ[ℚ] V) : ℕ := Module.finrank ℚ (LinearMap.range op)

noncomputable def matrix (B : LinearMap.BilinForm ℚ V) (hs : B.IsSymm)
    (p : Submodule ℚ V × Submodule ℚ V) : V →ₗ[ℚ] V :=
  ProjectionTrace.projector B hs p.2 - ProjectionTrace.projector B hs p.1

/-- Matrices retain every physical trace edge, including identity changes. -/
noncomputable def operators {ι : Type*} [DecidableEq ι]
    (B : LinearMap.BilinForm ℚ V) (hs : B.IsSymm)
    (current : ι → Submodule ℚ V) (updates : List (ι × Submodule ℚ V)) : List (V →ₗ[ℚ] V) :=
  (RankTrace.edges current updates).map (matrix B hs)

/-- Projector frames move addresses while preserving binary scalar values. -/
noncomputable def projectorFrame (B : LinearMap.BilinForm ℚ V) (hs : B.IsSymm)
    (U : Submodule ℚ V) : FramedCircuit.Frame (ZMod 2) ((V × V) → ZMod 2) :=
  ShearFrame.frame (ProjectionTrace.projector B hs U)

/-- The actual physical change, not merely its dimension, is this matrix shear. -/
def Realizes (p : FramedCircuit.Frame (ZMod 2) ((V × V) → ZMod 2) ×
    FramedCircuit.Frame (ZMod 2) ((V × V) → ZMod 2)) (op : V →ₗ[ℚ] V) : Prop :=
  ∀ f, p.2 (p.1.symm f) = ShearFrame.frame op f

theorem matrix_realizes (B : LinearMap.BilinForm ℚ V) (hs : B.IsSymm)
    (p : Submodule ℚ V × Submodule ℚ V) :
    Realizes (projectorFrame B hs p.1,projectorFrame B hs p.2) (matrix B hs p) :=
  ShearFrame.frame_change _ _

/-- Ordered physical pair equality supplies an operator certificate for every
actual edge, without assuming injectivity of an arbitrary frame assignment. -/
theorem physical_realizes {ι : Type*} [DecidableEq ι]
    (B : LinearMap.BilinForm ℚ V) (hs : B.IsSymm)
    (current : ι → Submodule ℚ V) (updates : List (ι × Submodule ℚ V))
    (physical : List (FramedCircuit.Instruction ι (ZMod 2) ((V × V) → ZMod 2)))
    (hp : FramedEdgeTrace.pairs physical = (RankTrace.edges current updates).map
      (fun p => (projectorFrame B hs p.1,projectorFrame B hs p.2))) :
    List.Forall₂ Realizes (FramedEdgeTrace.pairs physical) (operators B hs current updates) := by
  rw [hp,operators,List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
  exact fun p _ => matrix_realizes B hs p

theorem operator_balance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm ℚ V) (hs : B.IsSymm)
    (current : ι → Submodule ℚ V) (updates : List (ι × Submodule ℚ V))
    (hn : ∀ p ∈ RankTrace.edges current updates,
      (B.restrict p.1).Nondegenerate ∧ (B.restrict p.2).Nondegenerate)
    (hc : ∀ p ∈ RankTrace.edges current updates, p.1 ≤ p.2 ∨ p.2 ≤ p.1) :
    ((operators B hs current updates).map rangeRank).sum +
      RankTrace.total (fun U : Submodule ℚ V => Module.finrank ℚ U) current =
      RankTrace.total (fun U : Submodule ℚ V => Module.finrank ℚ U) (RankTrace.finish current updates) +
        2 * RankTrace.loss (fun U : Submodule ℚ V => Module.finrank ℚ U) current updates := by
  have hv : ((operators B hs current updates).map rangeRank).sum =
      RankTrace.variation (fun U : Submodule ℚ V => Module.finrank ℚ U) current updates := by
    unfold operators RankTrace.variation
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro p hp
    exact ProjectionTrace.edgeRank_eq B hs p.1 p.2 (hn p hp).1 (hn p hp).2 (hc p hp)
  rw [hv]
  exact RankTrace.variation_balance _ current updates
end Matrices

variable {n s : ℕ} {E H : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    [AddCommGroup H] [Module ℚ H] [FiniteDimensional ℚ H]

abbrev Ambient (E H : Type*) [AddCommGroup E] [Module ℚ E] [AddCommGroup H] [Module ℚ H] :=
  (E ⊗[ℚ] Factor) ⊗[ℚ] H

omit [FiniteDimensional ℚ E] [FiniteDimensional ℚ H] in
/-- Symmetry of the actual earlier/current/future tensor form. -/
theorem pairing_symm (g : Geometry ℚ E Factor) (D : LinearMap.BilinForm ℚ H) (hD : D.IsSymm) :
    (g.liftedPairing D).IsSymm :=
  LinearMap.BilinForm.isSymm_iff.mpr
    ((LinearMap.BilinForm.isSymm_iff.mp g.pairing_symm).tmul (LinearMap.BilinForm.isSymm_iff.mp hD))

/-- Exact projector frames used to instantiate the real physical programs. -/
noncomputable def frames (g : Geometry ℚ E Factor) (D : LinearMap.BilinForm ℚ H) (hD : D.IsSymm) :
    Space E H → FramedCircuit.Frame (ZMod 2) ((Ambient E H × Ambient E H) → ZMod 2) :=
  projectorFrame (g.liftedPairing D) (pairing_symm g D hD)

noncomputable def forwardOperators (g : Geometry ℚ E Factor) (D : LinearMap.BilinForm ℚ H) (hD : D.IsSymm)
    (q : H) (e : Fin n ≃ Triple 50) : List (Ambient E H →ₗ[ℚ] Ambient E H) :=
  operators (g.liftedPairing D) (pairing_symm g D hD) (commonInput (s := s) g q e)
    (Shared50InvocationRank.updates g q e)

noncomputable def oppositeOperators (g : Geometry ℚ E Factor) (D : LinearMap.BilinForm ℚ H) (hD : D.IsSymm)
    (q : H) (e : Fin n ≃ Triple 50) : List (Ambient E H →ₗ[ℚ] Ambient E H) :=
  operators (g.liftedPairing D) (pairing_symm g D hD) (commonInput (s := s) g q e)
    (Shared50OppositeRank.updates g q e)

/-- Every actual forward physical frame change is certified by its actual
projector-difference matrix, preserving the full instruction order. -/
theorem forward_realizes (g : Geometry ℚ E Factor) (D : LinearMap.BilinForm ℚ H) (hD : D.IsSymm)
    (q : H) (e : Fin n ≃ Triple 50) :
    List.Forall₂ Realizes
      (FramedEdgeTrace.pairs (Shared50FramedInvocation.program g q e (frames g D hD) (commonInput (s := s) g q e)))
      (forwardOperators (s := s) g D hD q e) :=
  physical_realizes (g.liftedPairing D) (pairing_symm g D hD) _ _ _
    (Shared50InvocationPhysicalEdges.program_pairs g q e (frames g D hD) (commonInput g q e))

/-- The opposite physical execution has the same ordered operator certificate,
using its actual complemented inverse middle computation. -/
theorem opposite_realizes (g : Geometry ℚ E Factor) (D : LinearMap.BilinForm ℚ H) (hD : D.IsSymm)
    (q : H) (e : Fin n ≃ Triple 50) :
    List.Forall₂ Realizes
      (FramedEdgeTrace.pairs (Shared50FramedOpposite.program g q e (frames g D hD) (commonInput (s := s) g q e)))
      (oppositeOperators (s := s) g D hD q e) :=
  physical_realizes (g.liftedPairing D) (pairing_symm g D hD) _ _ _
    (Shared50FramedOpposite.program_pairs g q e (frames g D hD) (commonInput g q e))

/-- Genuine forward operator-range ranks balance the exact physical endpoint
dimensions plus twice the proved loss of 2500. -/
theorem forward_balance (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (D : LinearMap.BilinForm ℚ H) (hD : D.IsSymm) (q : H) (hq : D q q ≠ 0) (e : Fin n ≃ Triple 50) :
    ((forwardOperators (s := s) g D hD q e).map rangeRank).sum +
      RankTrace.total (fun U : Space E H => Module.finrank ℚ U) (commonInput (s := s) g q e) =
      RankTrace.total (fun U : Space E H => Module.finrank ℚ U) (output (s := s) g q e) + 5000 := by
  have hh := operator_balance (g.liftedPairing D) (pairing_symm g D hD)
    (commonInput (s := s) g q e) (Shared50InvocationRank.updates g q e)
    (Shared50InvocationRank.common_nondegenerate g hcurrent D q hq e)
    (Shared50InvocationRank.common_comparable g hcurrent q e)
  rw [Shared50InvocationRank.common_endpoints,Shared50InvocationRank.common_loss g hcurrent D q hq e] at hh
  exact hh

/-- The opposite invocation pays the same total central-return penalty. -/
theorem opposite_balance (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (D : LinearMap.BilinForm ℚ H) (hD : D.IsSymm) (q : H) (hq : D q q ≠ 0) (e : Fin n ≃ Triple 50) :
    ((oppositeOperators (s := s) g D hD q e).map rangeRank).sum +
      RankTrace.total (fun U : Space E H => Module.finrank ℚ U) (commonInput (s := s) g q e) =
      RankTrace.total (fun U : Space E H => Module.finrank ℚ U) (output (s := s) g q e) + 5000 := by
  have hh := operator_balance (g.liftedPairing D) (pairing_symm g D hD)
    (commonInput (s := s) g q e) (Shared50OppositeRank.updates g q e)
    (Shared50OppositeRank.common_nondegenerate g hcurrent D q hq e)
    (Shared50OppositeRank.common_comparable g q e)
  rw [Shared50OppositeRank.common_endpoints,Shared50OppositeRank.common_loss g D q hq e] at hh
  exact hh

/-- A complete certificate over the literal forward physical edge list. The
witness contains one genuine address matrix per edge and its total range rank. -/
theorem forward_certificate (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (D : LinearMap.BilinForm ℚ H) (hD : D.IsSymm) (q : H) (hq : D q q ≠ 0) (e : Fin n ≃ Triple 50) :
    ∃ ops : List (Ambient E H →ₗ[ℚ] Ambient E H),
      List.Forall₂ Realizes
        (FramedEdgeTrace.pairs (Shared50FramedInvocation.program g q e (frames g D hD) (commonInput (s := s) g q e))) ops ∧
      (ops.map rangeRank).sum +
        RankTrace.total (fun U : Space E H => Module.finrank ℚ U) (commonInput (s := s) g q e) =
        RankTrace.total (fun U : Space E H => Module.finrank ℚ U) (output (s := s) g q e) + 5000 :=
  ⟨forwardOperators (s := s) g D hD q e,forward_realizes g D hD q e,
    forward_balance g hcurrent D hD q hq e⟩

/-- The same complete physical/operator certificate for the opposite invocation. -/
theorem opposite_certificate (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (D : LinearMap.BilinForm ℚ H) (hD : D.IsSymm) (q : H) (hq : D q q ≠ 0) (e : Fin n ≃ Triple 50) :
    ∃ ops : List (Ambient E H →ₗ[ℚ] Ambient E H),
      List.Forall₂ Realizes
        (FramedEdgeTrace.pairs (Shared50FramedOpposite.program g q e (frames g D hD) (commonInput (s := s) g q e))) ops ∧
      (ops.map rangeRank).sum +
        RankTrace.total (fun U : Space E H => Module.finrank ℚ U) (commonInput (s := s) g q e) =
        RankTrace.total (fun U : Space E H => Module.finrank ℚ U) (output (s := s) g q e) + 5000 :=
  ⟨oppositeOperators (s := s) g D hD q e,opposite_realizes g D hD q e,
    opposite_balance g hcurrent D hD q hq e⟩

end IntegerMultBounds.Networks.Shared50InvocationProjectionRank
