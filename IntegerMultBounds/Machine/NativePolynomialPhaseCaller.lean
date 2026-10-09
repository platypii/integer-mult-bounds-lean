import IntegerMultBounds.Machine.CompactPolynomialPhasePlacement

/-! The phase source contract is derived from the literal original native
basis-word caller, including its full appended converter and header workspace.
No supplied serialization or alphabet compatibility premise is needed. -/
namespace IntegerMultBounds.Machine.NativePolynomialPhaseCaller
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ButterflyStreamData (Coefficient)
open ActivePrefixStageNativePolynomial (rows flattenArray)
variable {s : Shape} {R w : ℕ}

def source : Fin ActivePrefixStageNativePairSchedule.count :=
  Fin.castAdd 1 ActivePrefixStageNative.raw

theorem source_val : source.val=65 := rfl

/-- The source required by the actual physical phase caller is precisely the
source installed at the boundary of every literal native basis-word stage. -/
theorem source_word (d : Inputs s)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin R → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    (ActivePrefixStageNativePairRun.bank d (rows d xs hw)).tape source=
      SymbolTriplePlaced.mapTape ActivePrefixStageNative.ha
        (putWord (fun _ => blank) 0
          (UnitPhaseFullStreamNormalized.serialized (flattenArray xs))) := by
  change (ActivePrefixStageNativeRows.core d (rows d xs hw)).tape 65=_
  exact ActivePrefixStageNativePolynomial.source_word d xs hw

theorem source_head (d : Inputs s)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin R → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    (ActivePrefixStageNativePairRun.bank d (rows d xs hw)).head source=0 := rfl

end
end IntegerMultBounds.Machine.NativePolynomialPhaseCaller
