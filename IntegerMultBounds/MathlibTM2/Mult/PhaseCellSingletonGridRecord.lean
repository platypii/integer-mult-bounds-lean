module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCanonicalGridInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGridDispatchReady

/-! An ordinary singleton descriptor is constructed from scalar inputs and a p-grid line. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

noncomputable def singletonGridRecord {A s : ℕ} [NeZero s] (p u l target t : ℕ)
    (F : ZMod s → GaussianInt) : FamilyDispatchInput s A :=
  ⟨u,target,0,s,[F],(canonicalGridInput p u l target s t F).R,
    List.replicate (inverseCallerWordWidth p u l target s t) Node.tick⟩

theorem singletonGridRecord_ready {A s : ℕ} [NeZero s] (p u l target t : ℕ) {d : ℝ}
    (hu : 1 ≤ u) (hwidth : 8*p ≤ 2^u) (hbudget : (u : ℝ)*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (F : ZMod s → GaussianInt) (hF : ∀ i, ‖value p (F i)‖ ≤ 1) :
    GridDispatchReady p l t d (singletonGridRecord (A := A) p u l target t F) := by
  refine { toFamilyDispatchFrame := {
    uPositive := hu, width := hwidth, budget := hbudget, band := hband,
    a := Nat.zero_le s, b := le_rfl, padding := hpad,
    outputBlank := canonicalGridInput_core p u l target s t F 132 (by decide) (by decide),
    scalarWidth := by simp only [singletonGridRecord,List.length_replicate],
    scalars := canonicalGridInput_scalars p u l target s t F,
    blank := fun i hi _ hc => canonicalGridInput_core p u l target s t F i hi hc,
    source := ?_, count := ?_ }, inputBound := ?_ }
  · simpa only [singletonGridRecord,FamilyDispatchInput.width,inverseFullInputWidth,List.map_cons,List.map_nil,
      List.flatten_cons,List.flatten_nil,List.append_nil] using canonicalGridInput_source (A := A) p u l target s t F
  · exact canonicalGridInput_count p u l target s t F
  · intro G hG i
    simpa only [List.mem_singleton.mp hG] using hF i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
