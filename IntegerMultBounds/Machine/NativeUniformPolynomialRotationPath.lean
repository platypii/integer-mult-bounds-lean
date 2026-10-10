import IntegerMultBounds.Machine.NativeUniformPolynomialRotationSemantics
import IntegerMultBounds.Machine.CompactSpectatorInheritedGrid
import IntegerMultBounds.Networks.ComplexEndpointGrid

/-! Runtime column phase and fixed negation inherit their strict signed
reserve from the original recursive Path. They preserve the exact denominator,
numerator bound and literal word widths without further precision growth. -/
namespace IntegerMultBounds.Machine.NativeUniformPolynomialRotationPath
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Width Grid decoded half)
open Networks.GaussianPrecision
variable {sh : Shape} {rows ell q left k levels frames returned : ℕ}

 theorem rotation_width (columns : ℕ) (f : Array sh rows ell)
    (hw : Width sh rows ell q f) :
    Width sh rows ell q (NativeUniformPolynomialRotationSemantics.array columns f) := by
  intro i
  exact NativeUniformPolynomialRotationSemantics.width columns f _ hw i

 theorem negative_width (f : Array sh rows ell) (hw : Width sh rows ell q f) :
    Width sh rows ell q (UnitPhasePolynomialArray.result 2 f) := by
  intro i
  exact UnitPhasePolynomialArray.result_width _ _ _ hw i

 theorem rotation_decoded (columns : ℕ)
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (p C n : ℕ) (hp : p≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (f : Array sh rows ell) (hw : Width sh rows ell q f)
    (hg : Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) f) :
    decoded sh rows ell q n (NativeUniformPolynomialRotationSemantics.array columns f)=
      fun i => Complex.I^(27*columns)*decoded sh rows ell q n f i := by
  funext i
  apply NativeUniformPolynomialRotationSemantics.decoded
  · intro j
    simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using hw j
  · exact fun j => CompactSpectatorInheritedGrid.signed_guards_from_path
      sh rows ell q path p C n hp hchunk f hg j

 theorem negative_decoded
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (p C n : ℕ) (hp : p≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (f : Array sh rows ell) (hw : Width sh rows ell q f)
    (hg : Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) f) :
    decoded sh rows ell q n (UnitPhasePolynomialArray.result 2 f)=
      fun i => -decoded sh rows ell q n f i := by
  funext i
  apply NativeUniformPolynomialRotationSemantics.negative_decoded
  · intro j
    simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using hw j
  · exact fun j => CompactSpectatorInheritedGrid.signed_guards_from_path
      sh rows ell q path p C n hp hchunk f hg j

 theorem rotation_grid (columns : ℕ)
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (p C n : ℕ) (hp : p≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (f : Array sh rows ell) (hw : Width sh rows ell q f)
    (hg : Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) f) :
    Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned))
      (NativeUniformPolynomialRotationSemantics.array columns f) := by
  intro i
  rw [rotation_decoded columns path p C n hp hchunk f hw hg]
  exact bounded_I_pow_mul (27*columns) (hg i)

 theorem negative_grid
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (p C n : ℕ) (hp : p≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (f : Array sh rows ell) (hw : Width sh rows ell q f)
    (hg : Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) f) :
    Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned))
      (UnitPhasePolynomialArray.result 2 f) := by
  intro i
  rw [negative_decoded path p C n hp hchunk f hw hg]
  exact bounded_neg (hg i)

end
end IntegerMultBounds.Machine.NativeUniformPolynomialRotationPath
