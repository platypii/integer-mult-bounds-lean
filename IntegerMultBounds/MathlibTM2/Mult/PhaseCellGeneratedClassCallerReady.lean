module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCommonClassMasterSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClassCallerReady

/-! Derive selected-call readiness from the two generated class words.
Geometry and table inputs share one binary format; no class word is supplied
as a readiness premise. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  CommonClassGeometry
variable {N A : ℕ}

/-- A restored setup frame preserves every port except the two exported words. -/
theorem masterLoaded_right_off (core halo k : Fin N) (D : ℕ) (clipped : Bool)
    (s width radius : ℕ) (S : Stacks N A) (hcore : k ≠ core) (hhalo : k ≠ halo) :
    (masterLoaded core halo D clipped s width radius S).R k = S.R k := by
  simp only [masterLoaded,Function.update_of_ne hcore,Function.update_of_ne hhalo]

/-- The generated halo word also supplies the fourth geometry header. The other
three headers and ten common inputs are retained global words. -/
theorem classCallerReady_of_generated
    (bank : ComputedClassBank → Fin N) (rg : TblR 12 → Fin N)
    (src : Fin 4 → Fin N) (masters : Fin 12 → Fin N)
    (hinj : Function.Injective masters) (widthMaster zeroMaster : Fin N)
    (D : ℕ) (clipped : Bool) (p u l target s t B W rowCount radius width : ℕ)
    (value : Fin N → ℕ) (S : Stacks N A)
    (hvalues : ∀ j, value (masters j) =
      commonInputValues p u l target s t B W rowCount radius (haloRows clipped s width radius) j)
    (hprefix : ∀ j, j ≠ 10 → j ≠ 11 → S.R (masters j) =
      binSyms D (seedValues p u l target s t B W rowCount radius width (Fin.castAdd 1 j)))
    (hhaloSource : src 3 = masters 11)
    (hgeometryOff : ∀ j, j ≠ 3 → src j ≠ masters 10 ∧ src j ≠ masters 11)
    (hgeometry : ∀ j, j ≠ 3 → S.R (src j) =
      binSyms D (![s,width,radius,haloRows clipped s width radius] j))
    (hwidthOff : widthMaster ≠ masters 10 ∧ widthMaster ≠ masters 11)
    (hzeroOff : zeroMaster ≠ masters 10 ∧ zeroMaster ≠ masters 11)
    (htableOff : ∀ r, rg r ≠ masters 10 ∧ rg r ≠ masters 11)
    (hbankOff : ∀ j, bank j ≠ masters 10 ∧ bank j ≠ masters 11)
    (hwidth : (S.R widthMaster).length = D) (hzero : S.R zeroMaster = [])
    (htable : ∀ r, S.R (rg r) = [])
    (hbank : ∀ j, j ≠ .control .source → S.R (bank j) = [])
    (hleft : ∀ j, S.L (recovery bank (.work j)) = []) :
    ClassCallerReady bank rg src masters widthMaster zeroMaster D D s width radius
      (haloRows clipped s width radius) value
      (masterLoaded (masters 10) (masters 11) D clipped s width radius S) := by
  have hframe (k : Fin N) (hk : k ≠ masters 10 ∧ k ≠ masters 11) :=
    masterLoaded_right_off (masters 10) (masters 11) k D clipped s width radius S hk.1 hk.2
  refine ⟨?_,?_,?_,?_,?_,?_,hleft⟩
  · intro j
    by_cases hj : j = 3
    · subst j
      simp [hhaloSource,masterLoaded]
    · exact (hframe _ (hgeometryOff j hj)).trans (hgeometry j hj)
  · rw [hframe _ hwidthOff]; exact hwidth
  · exact (hframe _ hzeroOff).trans hzero
  · intro j
    rw [hvalues j]
    exact masterLoaded_words masters hinj D clipped p u l target s t B W rowCount radius width S hprefix j
  · intro r; exact (hframe _ (htableOff r)).trans (htable r)
  · intro j hj; exact (hframe _ (hbankOff j)).trans (hbank j hj)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
