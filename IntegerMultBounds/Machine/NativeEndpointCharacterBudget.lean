import IntegerMultBounds.Machine.NativeEndpointCharacterLifecycle
import IntegerMultBounds.Machine.AllAxisPolynomialNativeBudget

/-! All original descriptor copies, metadata construction, aggregate
traversal, overwrite and cleanup joins are paid by polynomial row volume. -/
namespace IntegerMultBounds.Machine.NativeEndpointCharacterBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ActivePrefixStageHeadersData (Order)
open NativeEndpointCharacterHeaders (words)
variable {s : Shape} {t : ℕ}

private theorem canonical (v : Stage s) (rows ell : ℕ) :
    ∀ i,GrowingCounterData.Canonical (words v rows ell i) := by
  intro i
  induction i using Fin.addCases (m:=13) (n:=1) with
  | left i => simpa only [words,Fin.addCases_left,Fin.addCases_right] using RecursiveChildQuotientsConstant.bits_canonical _
  | right i => simpa only [words,Fin.addCases_left,Fin.addCases_right] using RecursiveChildQuotientsConstant.bits_canonical _

private theorem values_bound (order : Order) (v : Stage s) (rows ell : ℕ)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order v)
    (hr : 0<rows) (hrecord : s.bits+1≤s.payload) (hR : 2^ell≤s.payload) :
    ∀ i,Counter.value (words v rows ell i)≤rows*s.recordWidth := by
  have hv := (ActivePrefixStageHeadersBudget.original_bounds order v rows hG hGK ho hr hrecord).1
  have hp : s.payload≤rows*s.recordWidth := by
    simpa [ActivePrefixStageHeadersData.originalValues] using hv (5 : Fin 13)
  intro i
  induction i using Fin.addCases (m:=13) (n:=1) with
  | left i => simpa only [words,Fin.addCases_left,RecursiveChildQuotientsConstant.bits_value] using hv i
  | right i =>
    simpa only [words,Fin.addCases_right,RecursiveChildQuotientsConstant.bits_value] using
      (Nat.le_of_lt (Nat.lt_two_pow_self (n:=ell))).trans (hR.trans hp)

theorem lifecycle_bound (order : Order) (v : Stage s) (rows ell : ℕ)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order v)
    (hr : 0<rows) (hrecord : s.bits+1≤s.payload) (hR : 2^ell≤s.payload) :
    FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 14) (words v rows ell)+
      ActivePrefixStageHeadersRun.cost order v rows+
      AllAxisPhaseStageMetadata.cleanupCost order v rows+
      FixedHeaderBankCopy.cleanupCost (t:=t) (words v rows ell)≤
      804266*(rows*s.recordWidth) := by
  have hpay : 0<s.payload := by omega
  have hV : 0<rows*s.recordWidth := by unfold Shape.recordWidth; positivity
  have hv := values_bound order v rows ell hG hGK ho hr hrecord hR
  have hc := FixedHeaderBankCopy.cost_linear (words v rows ell) (rows*s.recordWidth) hV (canonical _ _ _) hv
  have he := FixedHeaderBankCopy.cleanup_cost_linear (t:=t) (words v rows ell)
    (rows*s.recordWidth) hV (canonical _ _ _) hv
  have hm := AllAxisPhaseStageMetadata.lifecycle_bound order v rows hG hGK ho hr hrecord
  omega

def constant := 804304+(2*FixedBasePowerDescriptor.constant 2+15000)

theorem cost_linear (order : Order) (v : Stage s) (rows m ell w : ℕ)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order v)
    (hr : 0<rows) (hm : 0<m) (hslots : m≤v.slots)
    (hspan : AllAxisPhaseHeadersData.offset v m+(m*v.f-1)*s.chunk<s.bits)
    (hrecord : s.bits+1≤s.payload) (hR : 2^ell≤s.payload)
    (hw : 2^ell*w≤s.payload) :
    NativeEndpointCharacterLifecycle.cost (t:=t) order v rows m ell w≤
      constant*(rows*s.recordWidth) := by
  have hl := lifecycle_bound (t:=t) order v rows ell hG hGK ho hr hrecord hR
  have hs := AllAxisPolynomialNativeBudget.cost_bound order v rows hr m ell w hm
    hslots hspan hrecord hR
  have hpay : 0<s.payload := by omega
  have hV : 0<rows*s.recordWidth := by unfold Shape.recordWidth; positivity
  have hp : 34*2^ell*w≤34*s.payload := by nlinarith
  have hp' := Nat.mul_le_mul_left (rows*2^s.bits)
    (Nat.add_le_add_left hp ((2*FixedBasePowerDescriptor.constant 2+15000)*s.payload))
  have he : rows*s.recordWidth=(rows*2^s.bits)*s.payload := by
    simp only [Shape.recordWidth,Nat.mul_assoc]
  unfold NativeEndpointCharacterLifecycle.cost constant
  rw [he] at hl hV ⊢
  nlinarith

end
end IntegerMultBounds.Machine.NativeEndpointCharacterBudget
