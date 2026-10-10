import IntegerMultBounds.Machine.CompactNativeRoleConjugatedPorts

/-! Every copied original descriptor and the immutable ell word is charged
against actual stage record volume. Enlarging the native codec supplies the
polynomial count and signed-width premises without a cost allowance. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleConjugatedBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageHeadersData (Order)
open RecursiveChildQuotientsConstant (bits)
variable {s : Shape}

theorem polynomial_bounds (s : Shape) (ell p : ℕ) :
    2^ell≤(NativePolynomialStageShape.shape s ell p).payload ∧
    2^ell*NativePolynomialStageShape.width s p≤(NativePolynomialStageShape.shape s ell p).payload := by
  change 2^ell≤NativePolynomialStageShape.payload s ell p ∧
    2^ell*NativePolynomialStageShape.width s p≤NativePolynomialStageShape.payload s ell p
  unfold NativePolynomialStageShape.payload ActivePrefixStageNativePolynomial.symbols
  constructor <;> ring_nf <;> omega

theorem words_canonical (d : Inputs s) (ell : ℕ) :
    ∀ i,GrowingCounterData.Canonical (AllAxisPhaseOriginalScalar.words d ell i) := by
  intro i
  induction i using Fin.addCases (m:=13) (n:=1) with
  | left i => simpa only [AllAxisPhaseOriginalScalar.words,Fin.addCases_left,AllAxisPhaseOriginalPorts.words] using RecursiveChildQuotientsConstant.bits_canonical (ActivePrefixStageHeadersData.originalValues d.stage d.rows i)
  | right i => simpa only [AllAxisPhaseOriginalScalar.words,Fin.addCases_right] using RecursiveChildQuotientsConstant.bits_canonical ell

theorem words_bound (order : Order) (d : Inputs s)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order d.stage) (ell : ℕ) (hR : 2^ell≤s.payload) :
    ∀ i,Counter.value (AllAxisPhaseOriginalScalar.words d ell i)≤d.rows*s.recordWidth := by
  have hv := (ActivePrefixStageHeadersBudget.original_bounds order d.stage d.rows
    d.hG d.hGK ho d.hr d.hrecord).1
  have hpay : s.payload≤d.rows*s.recordWidth := by
    simpa [ActivePrefixStageHeadersData.originalValues] using hv (5 : Fin 13)
  intro i
  induction i using Fin.addCases (m:=13) (n:=1) with
  | left i =>
    simpa only [AllAxisPhaseOriginalScalar.words,Fin.addCases_left,AllAxisPhaseOriginalPorts.words,
      RecursiveChildQuotientsConstant.bits_value] using hv i
  | right i =>
    simpa only [AllAxisPhaseOriginalScalar.words,Fin.addCases_right,RecursiveChildQuotientsConstant.bits_value] using
      (Nat.le_of_lt (Nat.lt_two_pow_self (n:=ell))).trans (hR.trans hpay)

theorem lifecycle_linear (t : ℕ) (order : Order) (d : Inputs s)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order d.stage) (ell : ℕ) (hR : 2^ell≤s.payload) :
    FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 14) (AllAxisPhaseOriginalScalar.words d ell)+
      FixedHeaderBankCopy.cleanupCost (t:=t) (AllAxisPhaseOriginalScalar.words d ell)≤
        266*(d.rows*s.recordWidth) := by
  have hr := d.hr
  have hp : 0<s.payload := by have := d.hrecord; omega
  have hV : 0<d.rows*s.recordWidth := by unfold Shape.recordWidth; positivity
  have hs := FixedHeaderBankCopy.cost_linear (AllAxisPhaseOriginalScalar.words d ell)
    (d.rows*s.recordWidth) hV (words_canonical d ell) (words_bound order d ho ell hR)
  have hc := FixedHeaderBankCopy.cleanup_cost_linear (t:=t) (AllAxisPhaseOriginalScalar.words d ell)
    (d.rows*s.recordWidth) hV (words_canonical d ell) (words_bound order d ho ell hR)
  omega

end
end IntegerMultBounds.Machine.CompactNativeRoleConjugatedBudget
