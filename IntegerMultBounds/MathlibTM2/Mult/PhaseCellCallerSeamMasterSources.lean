module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSeamNarrowWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySeamLoadedReady

/-! Bind the seam loader to retained caller sources. Three crop counts and the
narrow ruler borrow restored publication headers after proper publication. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN.PhaseCellMatrix CommonClassGeometry ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
variable {T A s : ℕ}
noncomputable section

def seamMasterSources (T : ℕ) (src : Fin 11 → Fin T) (widthSource : Fin T) :
    Fin 11 → Fin ((T+headerCount)+175) :=
  ![Fin.castAdd 175 (bank id (src 8)),Fin.castAdd 175 (bank id (src 4)),
    Fin.castAdd 175 (bank id (src 7)),Fin.castAdd 175 (header T (.publication 3)),
    Fin.castAdd 175 (header T (.scalar 4)),Fin.castAdd 175 (header T (.scalar 10)),
    Fin.castAdd 175 (header T (.scalar 7)),Fin.castAdd 175 (bank id widthSource),
    Fin.castAdd 175 (header T (.publication 0)),Fin.castAdd 175 (header T (.publication 1)),
    Fin.castAdd 175 (header T (.publication 2))]

theorem seamMasterSources_headerWords (p u l target t B W D N radius width : ℕ)
    (src : Fin 11 → Fin T) (widthSource : Fin T) (seedValue : Fin 117 → ℕ)
    (hseed : ∀ j, seedValue (boundarySeedGlobals j) = ![s,width,W] j)
    (S : Stacks (MachineTapes T) A)
    (hraw : ∀ i, (S.R (unarySource T (src i))).length = globalValues p u l target s t B W N radius width i)
    (hwidth : (S.R (unarySource T widthSource)).length = D)
    (hscalars : ∀ i, S.R (globals T i) = binSyms D (globalValues p u l target s t B W N radius width i))
    (hnarrow : (S.R (fullHeader T (.publication 3))).length = 2*p+13)
    (hcrops : ∀ slot : Fin 3, (S.R (fullHeader T (.publication (Fin.castAdd 4 slot)))).length =
      coreLength s width (boundaryCropIndex s width slot)*(2*p+13)) :
    BoundarySeamHeaderWords (s := s) p width W D N seedValue
      (fun i => S.R (Fin.castAdd tapeCount (seamMasterSources T src widthSource i))) := by
  constructor
  · change (S.R (unarySource T (src 8))).length = N
    simpa [globalValues] using hraw 8
  · change (S.R (unarySource T (src 4))).length = s
    simpa [globalValues] using hraw 4
  · change (S.R (unarySource T (src 7))).length = W
    simpa [globalValues] using hraw 7
  · change (S.R (fullHeader T (.publication 3))).length = 2*p+13
    exact hnarrow
  · intro j
    rw [hseed j]
    fin_cases j
    · change S.R (globals T 4) = binSyms D s
      simpa [globalValues] using hscalars 4
    · change S.R (globals T 10) = binSyms D width
      simpa [globalValues] using hscalars 10
    · change S.R (globals T 7) = binSyms D W
      simpa [globalValues] using hscalars 7
  · change (S.R (unarySource T widthSource)).length = D
    exact hwidth
  · intro slot
    fin_cases slot
    · exact hcrops 0
    · exact hcrops 1
    · exact hcrops 2

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
