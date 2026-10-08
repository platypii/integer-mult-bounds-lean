import IntegerMultBounds.Networks.Shared50GlobalTrace
import IntegerMultBounds.Networks.ShearFrame
import IntegerMultBounds.Networks.GroupedModuleFrames

/-! The actual two-bank data exchange has a uniform rational address shear
between its negative source frames and sink frames, including every dirty
scratch wire. This is an exact array identity, not a finite-radix tape cost. -/

namespace IntegerMultBounds.Networks.Shared50ShearEndpoints

noncomputable section
open Shared50GlobalTrace
open Shared50GlobalBudget (World Ambient)
open Shared50ReuseLabels (cubeForm cube_symm cube_nondegenerate)

/-- The source wire routed to a physical output: exchange data, retain scratch. -/
def route : World → World
  | .inl b => .inr (.inl b)
  | .inr (.inl b) => .inl b
  | .inr (.inr s) => .inr (.inr s)

theorem route_involutive : Function.Involutive route := by
  intro i
  rcases i with b | b | s <;> rfl

/-- The literal global scalar program implements this exact routing. -/
theorem scalar_route {n : ℕ} (e : Fin n ≃ Shared50GlobalBudget.Triple) (state : World → ZMod 2) :
    Circuit.run (Shared50GlobalCircuit.program e) state = fun i => state (route i) := by
  have he : Shared50GlobalCircuit.contents (fun b => state (.inl b))
      (fun b => state (.inr (.inl b))) (fun s => state (.inr (.inr s))) = state := by
    funext i
    rcases i with b | b | s <;> rfl
  have hh := Shared50GlobalCircuit.program_run e (fun b => state (.inl b))
    (fun b => state (.inr (.inl b))) (fun s => state (.inr (.inr s)))
  rw [he] at hh
  rw [hh]
  funext i
  rcases i with b | b | s <;> rfl

/-- Data exchange and scratch restoration hold for arbitrary module contents. -/
theorem module_route {n : ℕ} {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (e : Fin n ≃ Shared50GlobalBudget.Triple) (state : World → M) :
    FramedCircuit.moduleRun (Shared50GlobalCircuit.program e) state = fun i => state (route i) :=
  GroupedModuleFrames.moduleRun_route _ route (scalar_route e) state

abbrev projector (U : Label) : Ambient →ₗ[ℚ] Ambient :=
  ProjectionTrace.projector cubeForm cube_symm U

private theorem projector_top {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (B : LinearMap.BilinForm ℚ V) (hs : B.IsSymm) (hn : B.Nondegenerate) :
    ProjectionTrace.projector B hs ⊤ = LinearMap.id := by
  rw [ProjectionTrace.projector_eq _ _ _ (MotifLabels.top_nondegenerate B hn)]
  ext x
  exact ProjectionRank.project_left _ _ _ _ (Submodule.mem_top)

private theorem projector_bot {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (B : LinearMap.BilinForm ℚ V) (hs : B.IsSymm) :
    ProjectionTrace.projector B hs ⊥ = 0 := by
  rw [ProjectionTrace.projector_eq _ _ _ (MotifLabels.bot_nondegenerate B)]
  ext x
  exact ProjectionRank.project_mem B hs ⊥ _ x

/-- Every routed sink-minus-signed-source projector is the full identity. -/
theorem routed_operator (i : World) :
    projector (sink i) - (-projector (source (route i))) = LinearMap.id := by
  rcases i with b | b | s
  · change ProjectionTrace.projector cubeForm cube_symm ⊤ -
      (-ProjectionTrace.projector cubeForm cube_symm ⊥) = _
    rw [projector_top _ _ cube_nondegenerate,projector_bot]
    apply LinearMap.ext
    intro x
    change x - -(0 : Ambient) = x
    abel
  · change ProjectionTrace.projector cubeForm cube_symm
        (cubeForm.orthogonal (GlobalLabels.terminal (K := ℚ) Shared50ReuseLabels.vector b)) -
      (-ProjectionTrace.projector cubeForm cube_symm
        (GlobalLabels.terminal (K := ℚ) Shared50ReuseLabels.vector b)) = _
    have hu : (cubeForm.restrict (GlobalLabels.terminal (K := ℚ) Shared50ReuseLabels.vector b)).Nondegenerate :=
      source_nondegenerate (.inl b)
    have hv := ProjectionRank.orthogonal_nondegenerate cubeForm cube_symm cube_nondegenerate _ hu
    rw [ProjectionTrace.projector_eq _ _ _ hv,ProjectionTrace.projector_eq _ _ _ hu]
    exact ProjectionRank.routed_endpoint _ _ cube_nondegenerate _ hu
  · change ProjectionTrace.projector cubeForm cube_symm ⊤ -
      (-ProjectionTrace.projector cubeForm cube_symm ⊥) = _
    rw [projector_top _ _ cube_nondegenerate,projector_bot]
    apply LinearMap.ext
    intro x
    change x - -(0 : Ambient) = x
    abel

/-- Binary arrays experience the same full address shear on every physical bank. -/
theorem frame_endpoint (i : World) (f : (Ambient × Ambient) → ZMod 2) :
    ShearFrame.frame (projector (sink i))
      ((ShearFrame.frame (-projector (source (route i)))).symm f) =
        ShearFrame.frame (LinearMap.id : Ambient →ₗ[ℚ] Ambient) f := by
  rw [ShearFrame.frame_change,routed_operator]

end
end IntegerMultBounds.Networks.Shared50ShearEndpoints
