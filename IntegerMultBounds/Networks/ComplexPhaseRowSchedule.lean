import IntegerMultBounds.Networks.ComplexPhaseBudget
import IntegerMultBounds.Networks.BinaryPhaseResidualRowProgram

/-! Every actual edge of the fixed complex25 network supplies its own binary
residual prerequisites and its own literal ambient row-addition word. -/
namespace IntegerMultBounds.Networks.ComplexPhaseRowSchedule
noncomputable section
open ComplexPhaseBudget
abbrev Edge := {p : Label × Label // p ∈ edges}
abbrev CoordinateLabel := Submodule (ZMod 2) (Fin (25 ^ 3) → ZMod 2)

def lower (rev : Bool) (p : Label × Label) : Label := if rev then p.2 else p.1
def upper (rev : Bool) (p : Label × Label) : Label := if rev then p.1 else p.2

def Valid (p : Label × Label) (rev : Bool) : Prop :=
  lower rev p ≤ upper rev p ∧
  (form.restrict (lower rev p)).Nondegenerate ∧
  (form.restrict (upper rev p)).Nondegenerate ∧
  BinaryMotifResiduals.Good form (ProjectionRank.residual form (lower rev p) (upper rev p))

theorem exists_valid (e : Edge) : ∃ rev, Valid e.val rev := by
  obtain ⟨hsource, htarget⟩ := edges_nondegenerate e.val e.property
  rcases edges_residuals e.val e.property with ⟨hle,hgood⟩ | ⟨hle,hgood⟩
  · exact ⟨false, hle,hsource,htarget,hgood⟩
  · exact ⟨true, hle,htarget,hsource,hgood⟩

def direction (e : Edge) : Bool := Classical.choose (exists_valid e)
theorem valid (e : Edge) : Valid e.val (direction e) := Classical.choose_spec (exists_valid e)

def low (e : Edge) : CoordinateLabel :=
  LabelTransport.label (TensorCoordinates.coordinates 25) (lower (direction e) e.val)
def high (e : Edge) : CoordinateLabel :=
  LabelTransport.label (TensorCoordinates.coordinates 25) (upper (direction e) e.val)

theorem comparable (e : Edge) : low e ≤ high e :=
  Submodule.map_mono (valid e).1

theorem low_nondegenerate (e : Edge) : ((Labels.binary (25 ^ 3)).restrict (low e)).Nondegenerate :=
  LabelTransport.nondegenerate form (Labels.binary (25 ^ 3)) (TensorCoordinates.coordinates 25)
    (TensorCoordinates.coordinates_isometry 25) _ (valid e).2.1

theorem high_nondegenerate (e : Edge) : ((Labels.binary (25 ^ 3)).restrict (high e)).Nondegenerate :=
  LabelTransport.nondegenerate form (Labels.binary (25 ^ 3)) (TensorCoordinates.coordinates 25)
    (TensorCoordinates.coordinates_isometry 25) _ (valid e).2.2.1

theorem residual_good (e : Edge) : BinaryMotifResiduals.Good (Labels.binary (25 ^ 3))
    (ProjectionRank.residual (Labels.binary (25 ^ 3)) (low e) (high e)) :=
  BinaryMotifResiduals.residual_good_transport form (Labels.binary (25 ^ 3))
    (TensorCoordinates.coordinates 25) (TensorCoordinates.coordinates_isometry 25)
    _ _ (valid e).2.2.2

def word (e : Edge) : List (BinaryRowProgram.Op (Fin (25 ^ 3))) :=
  BinaryPhaseResidualRowProgram.word coordinateSymm (low e) (high e)
    (low_nondegenerate e) (high_nondegenerate e) (comparable e) (residual_good e)

abbrev dimension (e : Edge) := BinaryPhaseResidualRowProgram.dimension (low e) (high e)
def slot (e : Edge) (i : Fin (dimension e)) : Fin (25 ^ 3) :=
  BinaryPhaseResidualRowProgram.slot coordinateSymm (low e) (high e)
    (low_nondegenerate e) (high_nondegenerate e) (comparable e) (residual_good e) i

theorem slot_val (e : Edge) (i : Fin (dimension e)) : (slot e i).val = i.val := rfl

/-- No residual certificate is an input: membership in the actual fixed edge
list determines all of them. The chosen direction records inverse phase. -/
theorem phase (e : Edge) (x : Fin (25 ^ 3) → ZMod 2) :
    BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25 ^ 3)) coordinateSymm
      (high e) (high_nondegenerate e) x) -
    BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25 ^ 3)) coordinateSymm
      (low e) (low_nondegenerate e) x) =
    ∑ i : Fin (dimension e),
      BinaryPhase.weightPhase
        (BinaryPhaseResidualRowProgram.basis coordinateSymm (low e) (high e)
          (low_nondegenerate e) (high_nondegenerate e) (comparable e) (residual_good e) i :
            Fin (25 ^ 3) → ZMod 2) *
      BinaryPhase.bitLift (BinaryRowProgram.run (word e) x (slot e i)) :=
  BinaryPhaseResidualRowProgram.phase_difference coordinateSymm (low e) (high e)
    (low_nondegenerate e) (high_nondegenerate e) (comparable e) (residual_good e) x

def source (e : Edge) : CoordinateLabel :=
  LabelTransport.label (TensorCoordinates.coordinates 25) e.val.1
def target (e : Edge) : CoordinateLabel :=
  LabelTransport.label (TensorCoordinates.coordinates 25) e.val.2

theorem source_nondegenerate (e : Edge) : ((Labels.binary (25 ^ 3)).restrict (source e)).Nondegenerate :=
  LabelTransport.nondegenerate form (Labels.binary (25 ^ 3)) (TensorCoordinates.coordinates 25)
    (TensorCoordinates.coordinates_isometry 25) _ (edges_nondegenerate e.val e.property).1

theorem target_nondegenerate (e : Edge) : ((Labels.binary (25 ^ 3)).restrict (target e)).Nondegenerate :=
  LabelTransport.nondegenerate form (Labels.binary (25 ^ 3)) (TensorCoordinates.coordinates 25)
    (TensorCoordinates.coordinates_isometry 25) _ (edges_nondegenerate e.val e.property).2

/-- The retained orientation recovers the literal source-to-target phase of
the original ordered edge, including descending edges. -/
theorem original_phase (e : Edge) (x : Fin (25 ^ 3) → ZMod 2) :
    BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25 ^ 3)) coordinateSymm
      (target e) (target_nondegenerate e) x) -
    BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25 ^ 3)) coordinateSymm
      (source e) (source_nondegenerate e) x) =
    if direction e then
      -(BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25 ^ 3)) coordinateSymm
        (high e) (high_nondegenerate e) x) -
        BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25 ^ 3)) coordinateSymm
          (low e) (low_nondegenerate e) x))
    else
      BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25 ^ 3)) coordinateSymm
        (high e) (high_nondegenerate e) x) -
        BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25 ^ 3)) coordinateSymm
          (low e) (low_nondegenerate e) x) := by
  cases hd : direction e <;> simp [low, high, lower, upper, source, target, hd]

/-- Exact fixed edge order, before any runtime column count is chosen. -/
def words : List (List (BinaryRowProgram.Op (Fin (25 ^ 3)))) := edges.attach.map word

theorem words_length : words.length = edges.length := by simp [words]

end
end IntegerMultBounds.Networks.ComplexPhaseRowSchedule
