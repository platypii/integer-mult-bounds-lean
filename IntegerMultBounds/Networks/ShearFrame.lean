import IntegerMultBounds.Networks.ProjectionRank
import IntegerMultBounds.Networks.FramedCircuit

/-! Exact address-shear permutations and their action on wire arrays. The
address coefficient ring and the ring of scalar values are independent. This
supplies algebraic frame identities; finite-radix representation and tape
implementation of the shears are still separate obligations. -/

namespace IntegerMultBounds.Networks.ShearFrame

variable {K E R : Type*} [CommRing K] [AddCommGroup E] [Module K E]
    [CommRing R]

/-- Move the first address field by a fixed linear image of the second. -/
def address (M : E →ₗ[K] E) : (E × E) ≃ (E × E) where
  toFun := fun p => (p.1 + M p.2, p.2)
  invFun := fun p => (p.1 - M p.2, p.2)
  left_inv := by intro p; simp
  right_inv := by intro p; simp

theorem address_add (M N : E →ₗ[K] E) (p : E × E) :
    address N (address M p) = address (N + M) p := by
  simp only [address, Equiv.coe_fn_mk, LinearMap.add_apply]
  congr 1; abel

/-- An array entry follows the address permutation, so evaluation uses its
inverse. This convention is the manuscript's physical movement convention. -/
def frame (M : E →ₗ[K] E) : ((E × E) → R) ≃ₗ[R] ((E × E) → R) where
  toFun := fun f p => f ((address M).symm p)
  invFun := fun f p => f (address M p)
  left_inv := by intro f; funext p; simp
  right_inv := by intro f; funext p; simp
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem frame_apply (M : E →ₗ[K] E) (f : (E × E) → R) (p : E × E) :
    frame M f p = f (p.1 - M p.2, p.2) := rfl

theorem frame_symm_apply (M : E →ₗ[K] E) (f : (E × E) → R) (p : E × E) :
    (frame M).symm f p = f (p.1 + M p.2, p.2) := rfl

theorem frame_add (M N : E →ₗ[K] E) (f : (E × E) → R) :
    frame N (frame M f) = frame (N + M) f := by
  funext p
  simp only [frame_apply, LinearMap.add_apply]
  congr 1
  congr 1; abel

/-- Each edge between frame labels applies precisely their matrix difference. -/
theorem frame_change (source target : E →ₗ[K] E) (f : (E × E) → R) :
    frame target ((frame source).symm f) = frame (target - source) f := by
  funext p
  simp only [frame_apply, frame_symm_apply, LinearMap.sub_apply]
  congr 1
  congr 1; abel

theorem frame_zero (f : (E × E) → R) : frame (0 : E →ₗ[K] E) f = f := by
  funext p
  simp [frame_apply]

/-- The identity matrix in the label space is the full field shear. -/
theorem full_shear (f : (E × E) → R) (p : E × E) :
    frame (LinearMap.id : E →ₗ[K] E) f p = f (p.1 - p.2, p.2) := rfl

section Endpoints
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- The X-to-Y endpoint route applies the same full shear as the other
manuscript routes. Its negative source label is accounted for exactly. -/
theorem projection_endpoint (B : LinearMap.BilinForm F V) (hs : B.IsSymm)
    (hn : B.Nondegenerate) (U : Submodule F V) (hu : (B.restrict U).Nondegenerate)
    (f : (V × V) → R) :
    frame (ProjectionRank.project B hs (B.orthogonal U)
      (ProjectionRank.orthogonal_nondegenerate B hs hn U hu))
      ((frame (-ProjectionRank.project B hs U hu)).symm f) =
        frame (LinearMap.id : V →ₗ[F] V) f := by
  rw [frame_change, ProjectionRank.routed_endpoint B hs hn U hu]

end Endpoints

end IntegerMultBounds.Networks.ShearFrame
