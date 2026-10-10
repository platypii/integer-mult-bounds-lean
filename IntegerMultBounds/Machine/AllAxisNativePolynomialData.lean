import IntegerMultBounds.Machine.AllAxisPhasePreparedBridge
import IntegerMultBounds.Machine.AllAxisPolynomialTensorResult
import IntegerMultBounds.Machine.NativePolynomialPhaseCaller

/-! Physical aggregate phase output is again a valid literal native row bank,
with unchanged polynomial multiplicity and signed field widths. Count casts
only identify the already-proved common global address count. -/
namespace IntegerMultBounds.Machine.AllAxisNativePolynomialData
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ButterflyStreamData (Coefficient)
open ActivePrefixStageNativePolynomial (rows symbols flattenArray)
open AllAxisPolynomialTensorResult (flatten count_eq)
open UnitPhaseFullStreamNormalized (serialized)
variable {s : Shape}

def result (d : Inputs s) (ell m : ℕ) (ws : List (ZMod 4))
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (i : Fin (ActivePrefixStageTripleWords.count d)) (j : Fin (2^ell)) : Coefficient :=
  let p := AllAxisPolynomialLiteralEndpoint.phase d.stage m ws i.val
  (UnitPhaseNumerator.words p 0 (UnitPhasePolynomialArray.components (xs i j)),
    UnitPhaseNumerator.words p 1 (UnitPhasePolynomialArray.components (xs i j)))

theorem flatten_result (d : Inputs s) (ell m : ℕ) (ws : List (ZMod 4))
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient) :
    AllAxisPolynomialLiteralEndpoint.result d.stage m ws (flatten d ell xs)=
      flatten d ell (result d ell m ws xs) := by
  funext k
  rfl

theorem result_width (d : Inputs s) (ell m w : ℕ) (ws : List (ZMod 4))
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    ∀ i j,(result d ell m ws xs i j).1.length=w ∧ (result d ell m ws xs i j).2.length=w := by
  intro i j
  have hc : ∀ k,(UnitPhasePolynomialArray.components (xs i j) k).length=w := by
    intro k
    by_cases hk : k=0
    · simpa [UnitPhasePolynomialArray.components,hk] using (hw i j).1
    · simpa [UnitPhasePolynomialArray.components,hk] using (hw i j).2
  exact ⟨UnitPhaseNumerator.words_length _ _ _ w hc,UnitPhaseNumerator.words_length _ _ _ w hc⟩

theorem serialized_flatten (d : Inputs s) (ell : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient) :
    serialized (flatten d ell xs)=serialized (flattenArray xs) := by
  unfold serialized
  have h := List.ofFn_congr (congrArg (fun n => n*2^ell) (count_eq d))
    (fun i => ButterflyStreamData.encoded (flattenArray xs i))
  exact congrArg List.flatten h.symm

def source : Fin AllAxisPhaseOriginalScalar.outer :=
  Fin.castAdd 1 NativePolynomialPhaseCaller.source

theorem source_word (d : Inputs s) (ell w : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    (AllAxisPhaseOriginalScalar.caller d (rows d xs hw) ell).tape source=
      SymbolTriplePlaced.mapTape ActivePrefixStageNative.ha
        (putWord (fun _ => blank) 0 (serialized (flatten d ell xs))) := by
  simp only [AllAxisPhaseOriginalScalar.caller,source,Tapes.append,Fin.addCases_left]
  rw [serialized_flatten]
  exact NativePolynomialPhaseCaller.source_word d xs hw

theorem source_head (d : Inputs s) (ell w : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    (AllAxisPhaseOriginalScalar.caller d (rows d xs hw) ell).head source=0 := by
  simpa only [AllAxisPhaseOriginalScalar.caller,source,Tapes.append,Fin.addCases_left] using
    NativePolynomialPhaseCaller.source_head d xs hw

theorem replace_rows (d : Inputs s) (ell w : ℕ)
    (xs ys : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hx : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w)
    (hy : ∀ i j,(ys i j).1.length=w ∧ (ys i j).2.length=w) :
    SharedPlacementAlphabet.setTape (AllAxisPhaseOriginalScalar.caller d (rows d xs hx) ell) source
      (SymbolTriplePlaced.mapTape ActivePrefixStageNative.ha
        (putWord (fun _ => blank) 0 (serialized (flatten d ell ys)))) 0=
      AllAxisPhaseOriginalScalar.caller d (rows d ys hy) ell := by
  unfold AllAxisPhaseOriginalScalar.caller source
  rw [SharedPlacementAlphabet.setTape_append_left]
  apply congrArg (fun z : Tapes ActivePrefixStageNativePairSchedule.count Networks.Shared50ModularControl.prime =>
    z.append (AllAxisPhaseOriginalScalar.scalar ell))
  rw [serialized_flatten]
  have hs := NativePolynomialPhaseCaller.source_word d ys hy
  have hn : SymbolTriplePlaced.native ActivePrefixStageNative.ha
      (ActivePrefixStageNativeRows.flat (rows d ys hy))=
      SymbolTriplePlaced.mapTape ActivePrefixStageNative.ha
        (putWord (fun _ => blank) 0 (serialized (flattenArray ys))) := hs
  rw [←hn]
  exact NativePolynomialPhaseCaller.replace_rows d _ _

end
end IntegerMultBounds.Machine.AllAxisNativePolynomialData
