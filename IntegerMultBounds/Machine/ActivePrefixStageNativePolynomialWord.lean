import IntegerMultBounds.Machine.ActivePrefixStageNativePolynomial
import IntegerMultBounds.Machine.ActivePrefixStageNativeConjugation

/-! A literal native basis word acts on genuine serialized polynomial arrays.
Its chronological row destination retains every coefficient and field width;
the reversed word restores the original row after an arbitrary row-local action.
The fixed native executable supplies the corresponding physical word contract. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageNativePolynomialWord
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageTripleWords (count)
open ActivePrefixStageNativePolynomial (rows symbols)
open ActivePrefixStageNativePairSchedule (result)
open ButterflyStreamData (Coefficient)
open Networks.BinaryRowProgram (Op)
variable {s : Shape} {R w : ℕ}

theorem forward_restores_row (d : Inputs s) (ops : List (Op (Fin d.stage.slots)))
    (r : Fin (count d)) : ActivePrefixStageNativePairCoordinates.run d ops (ActivePrefixStageNativePairCoordinates.run d ops.reverse r)=r := by
  simpa only [List.reverse_reverse] using
    ActivePrefixStageNativeConjugation.reverse_restores_row d ops.reverse r

/-- Pullback of a physical output row is the reversed chronological word. -/
theorem result_entry (d : Inputs s) (ops : List (Op (Fin d.stage.slots))) {B : ℕ}
    (xs : ActivePrefixStageNativeRows.Rows d B) (r : Fin (count d)) (j : Fin B) :
    result d ops xs r j=xs (ActivePrefixStageNativePairCoordinates.run d ops.reverse r) j := by
  have h := ActivePrefixStageNativePairCoordinates.run_entry d ops xs (ActivePrefixStageNativePairCoordinates.run d ops.reverse r) j
  rwa [forward_restores_row] at h

def word (d : Inputs s) (ops : List (Op (Fin d.stage.slots)))
    (xs : Fin (count d) → Fin R → Coefficient) : Fin (count d) → Fin R → Coefficient :=
  fun i j => xs (ActivePrefixStageNativePairCoordinates.run d ops.reverse i) j

theorem word_width (d : Inputs s) (ops : List (Op (Fin d.stage.slots)))
    (xs : Fin (count d) → Fin R → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    ∀ i j,(word d ops xs i j).1.length=w ∧ (word d ops xs i j).2.length=w :=
  fun i j => hw (ActivePrefixStageNativePairCoordinates.run d ops.reverse i) j

/-- Exact equality of native output digits with newly serialized coefficients;
there is no codec or coordinate equality hypothesis. -/
theorem result_rows (d : Inputs s) (ops : List (Op (Fin d.stage.slots)))
    (xs : Fin (count d) → Fin R → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    result d ops (rows d xs hw)=rows d (word d ops xs) (word_width d ops xs hw) := by
  funext i k
  rw [result_entry]
  rfl

theorem word_nonblank (d : Inputs s) (ops : List (Op (Fin d.stage.slots)))
    (xs : Fin (count d) → Fin R → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    ∀ i k,rows d (word d ops xs) (word_width d ops xs hw) i k≠blank :=
  ActivePrefixStageNativePolynomial.rows_nonblank d _ _

/-- Original coefficient recovery at the actual chronological destination. -/
theorem word_destination (d : Inputs s) (ops : List (Op (Fin d.stage.slots)))
    (xs : Fin (count d) → Fin R → Coefficient) (r : Fin (count d)) (j : Fin R) :
    word d ops xs (ActivePrefixStageNativePairCoordinates.run d ops r) j=xs r j := by
  unfold word
  rw [ActivePrefixStageNativeConjugation.reverse_restores_row]

theorem word_reverse_entry (d : Inputs s) (ops : List (Op (Fin d.stage.slots)))
    (ys : Fin (count d) → Fin R → Coefficient) (r : Fin (count d)) (j : Fin R) :
    word d ops.reverse ys r j=ys (ActivePrefixStageNativePairCoordinates.run d ops r) j := by
  simp only [word,List.reverse_reverse]

/-- The full coefficient-level forward/local/reverse semantics. The local
function may act on all polynomial coefficients of its row simultaneously. -/
theorem conjugated_entry (d : Inputs s) (ops : List (Op (Fin d.stage.slots)))
    (F : Fin (count d) → (Fin R → Coefficient) → Fin R → Coefficient)
    (xs : Fin (count d) → Fin R → Coefficient) (r : Fin (count d)) (j : Fin R) :
    word d ops.reverse (fun i => F i (word d ops xs i)) r j=
      F (ActivePrefixStageNativePairCoordinates.run d ops r) (xs r) j := by
  rw [word_reverse_entry]
  have h : word d ops xs (ActivePrefixStageNativePairCoordinates.run d ops r)=xs r := by
    funext k
    exact word_destination d ops xs r k
  rw [h]

/-- One fixed native program implements every literal basis word on the actual
serialized coefficient bank, with conversion and pair-header lifecycle paid. -/
theorem exists_stage_program :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q Networks.Shared50ModularControl.prime,
    ∀ (D : ℕ) (s : Shape) (R w : ℕ) (d : Inputs s)
      (_hcode : s.payload=symbols R w*3+0)
      (hp : ∀ op,1<d.stage.f → ActivePrefixStageRuntimeData.Packed
        (ActivePrefixStagePairData.changePair d op) D)
      (ops : List (Op (Fin d.stage.slots)))
      (xs : Fin (count d) → Fin R → Coefficient)
      (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w),
      HoareTime (ActivePrefixStageNativePairSchedule.program P ops)
        (fun t => t=ActivePrefixStageNativePairRun.bank d (rows d xs hw))
        (fun t => t=ActivePrefixStageNativePairRun.bank d
          (rows d (word d ops xs) (word_width d ops xs hw)))
        (ActivePrefixStageNativePairSchedule.cost
          (ActivePrefixStageNativePairSchedule.stageCost (B:=symbols R w) D d hp) ops) := by
  obtain ⟨q,P,hP⟩ := ActivePrefixStageNativePairSchedule.exists_stage_program
  refine ⟨q,P,?_⟩
  intro D s R w d hcode hp ops xs hw
  have h := hP D s (symbols R w) d hcode hp ops (rows d xs hw)
    (ActivePrefixStageNativePolynomial.rows_nonblank d xs hw)
  rwa [result_rows] at h

end
end IntegerMultBounds.Machine.ActivePrefixStageNativePolynomialWord
