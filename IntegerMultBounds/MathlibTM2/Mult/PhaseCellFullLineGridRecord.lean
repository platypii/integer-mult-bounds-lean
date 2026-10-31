module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyDispatchBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCanonicalGridInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGridDispatchReady

/-! A constructed full-period grid record for arbitrary replicas. One scalar
setup serves the whole batch and all later retained seam crops. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

noncomputable def fullLineGridBank {A s : ℕ} [NeZero s] (p u l target t : ℕ)
    (Fs : List (ZMod s → GaussianInt)) : Stacks 303 A :=
  let B := inverseCallerWordWidth p u l target s t
  familyDispatchBank ⟨[],[],fun _ => [],fun _ => []⟩ B (List.replicate B tick)
    (inverseInputScalars p u l target s t 0 s) Fs.length
    (cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten)

noncomputable def fullLineGridRecord {A s : ℕ} [NeZero s] (p u l target t : ℕ)
    (Fs : List (ZMod s → GaussianInt)) : FamilyDispatchInput s A :=
  ⟨u,target,0,s,Fs,(fullLineGridBank p u l target t Fs).R,
    List.replicate (inverseCallerWordWidth p u l target s t) tick⟩

/-- Physical host tapes do not enter the serialized full-line descriptor. -/
theorem fullLineGridRecord_words {A s : ℕ} [NeZero s] (p u l target t : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (H : Stacks 303 A) :
    (fullLineGridRecord (A := A) p u l target t Fs).words =
      (familyDispatchBank H (inverseCallerWordWidth p u l target s t)
        (List.replicate (inverseCallerWordWidth p u l target s t) tick)
        (inverseInputScalars p u l target s t 0 s) Fs.length
        (cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten)).R := rfl

theorem fullLineGridRecord_core {A s : ℕ} [NeZero s] (p u l target t : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (i : Fin 263) :
    (fullLineGridRecord (A := A) p u l target t Fs).words (familyInverseCoreReg i) =
      if i = 246 then List.replicate Fs.length tick else if i = 110 then
        cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten else [] :=
  familyDispatchBank_core ⟨[],[],fun _ => [],fun _ => []⟩ _ _ _ _ _ i

theorem fullLineGridRecord_ready {A s : ℕ} [NeZero s] (p u l target t : ℕ) {d : ℝ}
    (hu : 1 ≤ u) (hwidth : 8*p ≤ 2^u) (hbudget : (u : ℝ)*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (Fs : List (ZMod s → GaussianInt)) (hFs : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1) :
    GridDispatchReady p l t d (fullLineGridRecord (A := A) p u l target t Fs) := by
  have h110 : familyInverseCoreReg 110 = 110 := by decide
  have h132 : familyInverseCoreReg 132 = 132 := by decide
  refine { toFamilyDispatchFrame := {
    uPositive := hu, width := hwidth, budget := hbudget, band := hband,
    a := Nat.zero_le s, b := le_rfl, padding := hpad,
    outputBlank := ?_, scalarWidth := by simp only [fullLineGridRecord,List.length_replicate],
    scalars := ?_, blank := ?_, source := ?_, count := ?_ }, inputBound := hFs }
  · simpa only [h132,Fin.reduceEq,ite_false] using fullLineGridRecord_core p u l target t Fs 132
  · exact familyDispatchBank_scalars ⟨[],[],fun _ => [],fun _ => []⟩ _ _ _ _ _
  · intro i hi _ hc
    simpa only [hc,hi,ite_false] using fullLineGridRecord_core p u l target t Fs i
  · simpa only [h110,Fin.reduceEq,ite_false,ite_true,fullLineGridRecord,FamilyDispatchInput.width,inverseFullInputWidth] using
      fullLineGridRecord_core p u l target t Fs 110
  · have hh := fullLineGridRecord_core (A := A) p u l target t Fs 246
    simpa only [fullLineGridRecord,Fin.reduceEq,ite_true,List.length_replicate] using congrArg List.length hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
