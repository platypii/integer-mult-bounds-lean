import IntegerMultBounds.Machine.AllAxisPolynomialActual
import IntegerMultBounds.Machine.ActivePrefixStageNativePolynomial

/-! The literal polynomial array quotient is the actual native row ordinal.
This connects the physical whole-stream result with the native tensor phase
at every polynomial spectator, without a row-address compatibility premise. -/
namespace IntegerMultBounds.Machine.AllAxisPolynomialTensorResult
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ButterflyStreamData (Coefficient)
open Networks Networks.ComplexPhaseRowSchedule
variable {s : Shape}

theorem count_eq (d : Inputs s) : ActivePrefixStageTripleWords.count d=d.rows*2^s.bits := by
  simp only [ActivePrefixStageTripleWords.count,ActiveRepairLayoutRecordsShape.address_width]

def flatten (d : Inputs s) (ell : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (k : Fin ((d.rows*2^s.bits)*2^ell)) : Coefficient :=
  xs ⟨k.val/2^ell,by rw [count_eq]; exact Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using k.isLt)⟩
    ⟨k.val%2^ell,Nat.mod_lt _ (by positivity)⟩

/-- This is the existing native row-major polynomial serialization, with
only the proved address-count equality cast. -/
theorem flatten_eq (d : Inputs s) (ell : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient) :
    flatten d ell xs=fun k => ActivePrefixStageNativePolynomial.flattenArray xs
      (Fin.cast (congrArg (fun n => n*2^ell) (count_eq d).symm) k) := by
  rfl

theorem flatten_width (d : Inputs s) (ell w : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hw : ∀ r j,(xs r j).1.length=w ∧ (xs r j).2.length=w)
    (k : Fin ((d.rows*2^s.bits)*2^ell)) :
    (flatten d ell xs k).1.length=w ∧ (flatten d ell xs k).2.length=w :=
  hw _ _

def index (d : Inputs s) (ell : ℕ) (r : Fin (ActivePrefixStageTripleWords.count d))
    (j : Fin (2^ell)) : Fin ((d.rows*2^s.bits)*2^ell) :=
  ⟨r.val*2^ell+j.val,by
    have hr : r.val<d.rows*2^s.bits := by simpa only [count_eq] using r.isLt
    have h := Nat.mul_le_mul_right (2^ell) (Nat.succ_le_of_lt hr)
    nlinarith [j.isLt]⟩

theorem quotient (d : Inputs s) (ell : ℕ) (r : Fin (ActivePrefixStageTripleWords.count d))
    (j : Fin (2^ell)) : (index d ell r j).val/2^ell=r.val := by
  simp only [index]
  rw [Nat.mul_comm r.val, Nat.mul_add_div (by positivity : 0<2^ell),Nat.div_eq_of_lt j.isLt,Nat.add_zero]

theorem flatten_index (d : Inputs s) (ell : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (r : Fin (ActivePrefixStageTripleWords.count d)) (j : Fin (2^ell)) :
    flatten d ell xs (index d ell r j)=xs r j := by
  unfold flatten
  have hq := quotient d ell r j
  have hj : (index d ell r j).val%2^ell=j.val := by
    change (r.val*2^ell+j.val)%2^ell=j.val
    rw [Nat.add_comm,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt j.isLt]
  simp only [hq,hj]

/-- Exact literal whole-array output at the reached native row, for every
polynomial coefficient. The phase value refers to the original input row. -/
theorem result_phase (d : Inputs s) (hslots : d.stage.slots=25^3) (e : Edge)
    (hm : 0<dimension e) (ell : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (r : Fin (ActivePrefixStageTripleWords.count d)) (j : Fin (2^ell)) (b n : ℕ)
    (hw : (xs (ActivePrefixStageNativePairCoordinates.run d (CompactComplexPhasePhysical.word d hslots e) r) j).1.length=b+1 ∧
      (xs (ActivePrefixStageNativePairCoordinates.run d (CompactComplexPhasePhysical.word d hslots e) r) j).2.length=b+1)
    (hg : ∀ k : Fin 2,|ButterflySigned.signedValue b (UnitPhasePolynomialArray.components
      (xs (ActivePrefixStageNativePairCoordinates.run d (CompactComplexPhasePhysical.word d hslots e) r) j) k.val)|<(2^b : ℕ)) :
    let a := AllAxisPolynomialLiteralEndpoint.result d.stage (dimension e)
      (CompactComplexPhaseControlCodec.weights e).reverse (flatten d ell xs)
      (index d ell (ActivePrefixStageNativePairCoordinates.run d (CompactComplexPhasePhysical.word d hslots e) r) j)
    ButterflySigned.complexValue (ButterflySigned.signedValue b a.1) (ButterflySigned.signedValue b a.2) n=
      (∏ axis : Fin d.stage.f,BinaryPhase.phase
        (CompactAllAxisPhaseReadout.delta d hslots e (ActivePrefixStageNativePairCoordinates.start d r) axis))*
        ButterflySigned.complexValue
          (ButterflySigned.signedValue b (xs (ActivePrefixStageNativePairCoordinates.run d (CompactComplexPhasePhysical.word d hslots e) r) j).1)
          (ButterflySigned.signedValue b (xs (ActivePrefixStageNativePairCoordinates.run d (CompactComplexPhasePhysical.word d hslots e) r) j).2) n := by
  dsimp only [AllAxisPolynomialLiteralEndpoint.result]
  rw [quotient,flatten_index]
  exact AllAxisPolynomialActual.coefficient_phase d hslots e hm r _ b n hw hg

end
end IntegerMultBounds.Machine.AllAxisPolynomialTensorResult
