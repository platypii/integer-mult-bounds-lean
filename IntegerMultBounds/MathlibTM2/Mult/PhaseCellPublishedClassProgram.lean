module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedPublicationMasterWords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExposedClassGeometryFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedPublicationGeometryControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedPublicationOrigins

/-! The restoring publication continuation of an actual numerical class run.
Its syntax depends on physical ports, not semantic row witnesses or input values. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
open ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q K : ℕ} {P U : Type}
noncomputable section

def publishedClassProgram (numerical : Pr P ((T+175)+tapeCount) Q (prime+K) U)
    (routeSrc : Fin 7 → Fin T) (pubSrc : Fin 10 → Fin T) (result output : Fin T)
    (hstates : FixedStreamedBank.stateCount ≤ Q) : Pr P ((T+175)+tapeCount) Q (prime+K) U :=
  let origins := publicationRetainedOriginSources routeSrc pubSrc
  let e := publicationOriginPlacement (Fin.castAdd 175 ∘ origins)
  let sources := Fin.castAdd 175 ∘ pubSrc
  let geometry := publicationGeometryPlacement
    (publicationGeometrySources (Fin.castAdd 175 ∘ origins) sources)
  let dimensions := publicationDimensionSources sources
  .seq numerical (.seq (PublicationGeometryControls.program geometry)
    (.seq (placedPublicationOrigins e) (.seq (publicationDimensionsProgram dimensions)
      (.seq (callerPublicationProgram sources (Fin.castAdd 175 result) (Fin.castAdd 175 output) hstates)
        (.seq (clearWords [Fin.castAdd tapeCount (dimensions 2),Fin.castAdd tapeCount (dimensions 3),
          Fin.castAdd tapeCount (dimensions 4)])
          (.seq (clearWords [classCallerRegister (pubSrc 9),classCallerRegister (pubSrc 6)])
            (clearWords [geometry 3,geometry 4])))))))

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
