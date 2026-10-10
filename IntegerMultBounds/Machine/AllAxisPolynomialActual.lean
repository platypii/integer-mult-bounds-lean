import IntegerMultBounds.Machine.CompactAllAxisPhaseDispatchBudget
import IntegerMultBounds.Machine.AllAxisPhaseGeometry
import IntegerMultBounds.Machine.CompactNativeTensorPhaseCoordinates
import IntegerMultBounds.Machine.UnitPhaseGuard

/-! Actual complex25 edges instantiate the executable whole-array aggregate
phase and its volume bound. At native basis-word destinations its coefficient
operation is the complete tensor phase, guarded by the existing bounded grid. -/
namespace IntegerMultBounds.Machine.AllAxisPolynomialActual
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageHeadersData (Order)
open ButterflyStreamData (Coefficient)
open Networks Networks.ComplexPhaseRowSchedule
open CompactAllAxisPhaseDispatch (count edge)
variable {s : Shape}

theorem runs (d : Inputs s) (hslots : d.stage.slots=25^3) (pc : Fin count)
    (hm : 0<dimension (edge pc)) (order : Order) (ell w : ℕ)
    (xs : Fin ((d.rows*2^s.bits)*2^ell) → Coefficient)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) :
    HoareTime (CompactAllAxisPhaseDispatch.call pc)
      (fun t => t=(AllAxisPolynomialStreamInit.input order d.stage d.rows
        (AllAxisPolynomialLiteral.tail (fun _ => blank) (fun _ => blank) 0 0 xs) ell).append (SharedBank.empty 1 2))
      (fun t => t=(AllAxisPolynomialNative.output order d.stage d.rows (dimension (edge pc))
        (CompactComplexPhaseControlCodec.weights (edge pc)).reverse ell xs).append (SharedBank.empty 1 2))
      (2*count+3+AllAxisPolynomialNative.cost order d.stage d.rows (dimension (edge pc)) ell w) :=
  CompactAllAxisPhaseDispatch.call_runs pc hm order d.stage d.rows d.hr
    (CompactComplexPhaseSparseControls.dimension_le d hslots (edge pc))
    (AllAxisPhaseGeometry.span d hslots (edge pc) hm) ell w xs hw

theorem volume_bound (d : Inputs s) (hslots : d.stage.slots=25^3) (pc : Fin count)
    (hm : 0<dimension (edge pc)) (order : Order) (ell w : ℕ) (hR : 2^ell≤s.payload) :
    2*count+3+AllAxisPolynomialNative.cost order d.stage d.rows (dimension (edge pc)) ell w≤
      (d.rows*2^s.bits)*(((2*FixedBasePowerDescriptor.constant 2+15000)+(2*count+3))*s.payload+34*2^ell*w) :=
  CompactAllAxisPhaseDispatchBudget.call_bound pc hm order d.stage d.rows d.hr ell w
    (CompactComplexPhaseSparseControls.dimension_le d hslots (edge pc))
    (AllAxisPhaseGeometry.span d hslots (edge pc) hm) d.hrecord hR

theorem phase_eq (d : Inputs s) (hslots : d.stage.slots=25^3) (e : Edge)
    (hm : 0<dimension e) (r : Fin (ActivePrefixStageTripleWords.count d)) :
    AllAxisPolynomialLiteralEndpoint.phase d.stage (dimension e)
      (CompactComplexPhaseControlCodec.weights e).reverse r.val=
      CompactNativeTensorPhaseCoordinates.phase d hslots e hm r := by
  unfold AllAxisPolynomialLiteralEndpoint.phase AllAxisPhaseFlagsCaller.phase
    CompactNativeTensorPhaseCoordinates.phase AllAxisPhaseFlagsCaller.controls
    CompactNativeTensorPhaseCoordinates.controls
  rw [AllAxisPhaseGeometry.offset_start d hslots e hm]

theorem coefficient_phase (d : Inputs s) (hslots : d.stage.slots=25^3) (e : Edge)
    (hm : 0<dimension e) (r : Fin (ActivePrefixStageTripleWords.count d))
    (a : Coefficient) (b n : ℕ) (hw : a.1.length=b+1 ∧ a.2.length=b+1)
    (hg : ∀ j : Fin 2,|ButterflySigned.signedValue b (UnitPhasePolynomialArray.components a j.val)|<(2^b : ℕ)) :
    let p := AllAxisPolynomialLiteralEndpoint.phase d.stage (dimension e)
      (CompactComplexPhaseControlCodec.weights e).reverse
      (ActivePrefixStageNativePairCoordinates.run d (CompactComplexPhasePhysical.word d hslots e) r).val
    ButterflySigned.complexValue
      (ButterflySigned.signedValue b (UnitPhaseNumerator.words p 0 (UnitPhasePolynomialArray.components a)))
      (ButterflySigned.signedValue b (UnitPhaseNumerator.words p 1 (UnitPhasePolynomialArray.components a))) n=
      (∏ axis : Fin d.stage.f,BinaryPhase.phase
        (CompactAllAxisPhaseReadout.delta d hslots e (ActivePrefixStageNativePairCoordinates.start d r) axis))*
        ButterflySigned.complexValue (ButterflySigned.signedValue b a.1) (ButterflySigned.signedValue b a.2) n := by
  have hc : ∀ j,(UnitPhasePolynomialArray.components a j).length=b+1 := by
    intro j
    unfold UnitPhasePolynomialArray.components
    split_ifs <;> first | exact hw.1 | exact hw.2
  have h := CompactNativeTensorPhaseCoordinates.coefficient_phase d hslots e hm r
    (UnitPhasePolynomialArray.components a) b n hc hg
  rw [←phase_eq] at h
  exact h

theorem bounded_grid_guard (a : Coefficient) (p D j : ℕ) (hj : j≤D)
    (hgrid : Networks.GaussianPrecision.BoundedGrid (p+j) ((2^p)*4^j)
      (ButterflySigned.complexValue
        (ButterflySigned.signedValue (ButterflyGuard.halfWidth p D) a.1)
        (ButterflySigned.signedValue (ButterflyGuard.halfWidth p D) a.2) (p+j))) :
    ∀ i : Fin 2,|ButterflySigned.signedValue (ButterflyGuard.halfWidth p D)
      (UnitPhasePolynomialArray.components a i.val)|<(2^(ButterflyGuard.halfWidth p D) : ℕ) :=
  UnitPhaseGuard.strict a p D j hj hgrid

/-- The existing prefix-depth grid invariant pays the actual tensor phase
negations; no independent strict signed-value guard is supplied. -/
theorem coefficient_phase_of_grid (d : Inputs s) (hslots : d.stage.slots=25^3) (e : Edge)
    (hm : 0<dimension e) (r : Fin (ActivePrefixStageTripleWords.count d))
    (a : Coefficient) (p D j : ℕ) (hj : j≤D)
    (hw : a.1.length=ButterflyGuard.halfWidth p D+1 ∧ a.2.length=ButterflyGuard.halfWidth p D+1)
    (hgrid : Networks.GaussianPrecision.BoundedGrid (p+j) ((2^p)*4^j)
      (ButterflySigned.complexValue
        (ButterflySigned.signedValue (ButterflyGuard.halfWidth p D) a.1)
        (ButterflySigned.signedValue (ButterflyGuard.halfWidth p D) a.2) (p+j))) :
    let q := AllAxisPolynomialLiteralEndpoint.phase d.stage (dimension e)
      (CompactComplexPhaseControlCodec.weights e).reverse
      (ActivePrefixStageNativePairCoordinates.run d (CompactComplexPhasePhysical.word d hslots e) r).val
    ButterflySigned.complexValue
      (ButterflySigned.signedValue (ButterflyGuard.halfWidth p D)
        (UnitPhaseNumerator.words q 0 (UnitPhasePolynomialArray.components a)))
      (ButterflySigned.signedValue (ButterflyGuard.halfWidth p D)
        (UnitPhaseNumerator.words q 1 (UnitPhasePolynomialArray.components a))) (p+j)=
      (∏ axis : Fin d.stage.f,BinaryPhase.phase
        (CompactAllAxisPhaseReadout.delta d hslots e (ActivePrefixStageNativePairCoordinates.start d r) axis))*
        ButterflySigned.complexValue
          (ButterflySigned.signedValue (ButterflyGuard.halfWidth p D) a.1)
          (ButterflySigned.signedValue (ButterflyGuard.halfWidth p D) a.2) (p+j) :=
  coefficient_phase d hslots e hm r a (ButterflyGuard.halfWidth p D) (p+j) hw
    (bounded_grid_guard a p D j hj hgrid)

end
end IntegerMultBounds.Machine.AllAxisPolynomialActual
