import IntegerMultBounds.Machine.CompactNativeRoleConjugatedBudget
import IntegerMultBounds.Machine.CompactNativeConjugatedPhaseFamily

/-! One actual native basis witness discharges every selected-role conjugated
phase. Original13 and ell are copied from generated numeric43, the genuine
six-symbol role source is shared through explicit alphabet encoding, and all
copied controls are erased. Packed repair geometry remains a genuine premise. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleConjugatedCaller
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageParameters (Stage)
open ActivePrefixStageHeadersData (Order)
open ButterflyStreamData (Coefficient)
open ActivePrefixStageNativePolynomial (rows symbols)
open Networks.Shared50ModularControl (prime)
open CompactAllAxisPhaseDispatch (count edge)
open Networks.ComplexPhaseRowSchedule (dimension)
open CompactNativeRoleSourcePorts (external callerTapes)
open SharedPlacementAlphabet (setTape)
variable {s : Shape}

def order (v : Stage s) : Order := if v.source.val<v.target.val then .early else .late

theorem ordered (v : Stage s) : ActivePrefixStageHeadersSchedule.Ordered (order v) v := by
  have hn : v.source.val≠v.target.val := by intro h; exact v.distinct (Fin.ext h)
  by_cases h : v.source.val<v.target.val
  · simp [order,h,ActivePrefixStageHeadersSchedule.Ordered]
  · simp only [order,ite_eq_right h,ActivePrefixStageHeadersSchedule.Ordered]
    omega

theorem expanded_ordered (v : Stage s) (ell p : ℕ) :
    ActivePrefixStageHeadersSchedule.Ordered (order v) (NativePolynomialStageShape.stage v ell p) := by
  have h := ordered v
  cases ho : order v <;> simpa [ho,ActivePrefixStageHeadersSchedule.Ordered,NativePolynomialStageShape.stage] using h

def outputCoefficients (d : Inputs s) (hslots : d.stage.slots=25^3) (pc : Fin count) (ell : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient) :=
  if 0<dimension (edge pc) then CompactNativeConjugatedPhase.result d hslots pc ell xs else xs

theorem output_width (d : Inputs s) (hslots : d.stage.slots=25^3) (pc : Fin count) (ell w : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    ∀ i j,(outputCoefficients d hslots pc ell xs i j).1.length=w ∧
      (outputCoefficients d hslots pc ell xs i j).2.length=w := by
  by_cases hm : 0<dimension (edge pc)
  · simp only [outputCoefficients,ite_eq_left hm]
    exact CompactNativeConjugatedPhase.result_width d hslots pc ell w xs hw
  · simpa only [outputCoefficients,ite_eq_right hm] using hw

private theorem rows_congr (d : Inputs s) (ell w : ℕ)
    (xs ys : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hx : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w)
    (hy : ∀ i j,(ys i j).1.length=w ∧ (ys i j).2.length=w)
    (h : xs=ys) : rows d xs hx=rows d ys hy := by
  subst ys
  rfl

theorem output_bank (d : Inputs s) (hslots : d.stage.slots=25^3) (pc : Fin count) (ell w : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    CompactNativeConjugatedPhaseFamily.output d hslots pc ell w xs hw=
      CompactNativeConjugatedPhase.bank d ell
        (rows d (outputCoefficients d hslots pc ell xs) (output_width d hslots pc ell w xs hw)) := by
  by_cases hm : 0<dimension (edge pc)
  · have ho : outputCoefficients d hslots pc ell xs=CompactNativeConjugatedPhase.result d hslots pc ell xs := by
      simp [outputCoefficients,hm]
    simp only [CompactNativeConjugatedPhaseFamily.output,ite_eq_left hm]
    rw [rows_congr d ell w _ _ (output_width d hslots pc ell w xs hw)
      (CompactNativeConjugatedPhase.result_width d hslots pc ell w xs hw) ho]
  · have ho : outputCoefficients d hslots pc ell xs=xs := by simp [outputCoefficients,hm]
    simp only [CompactNativeConjugatedPhaseFamily.output,ite_eq_right hm]
    rw [rows_congr d ell w _ _ (output_width d hslots pc ell w xs hw) hw ho]

/-- Each edge executes through the same native basis witness. No execution,
phase routine or complexity allowance is supplied by the caller. -/
theorem exists_program (D : ℕ) :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q prime, ∃ C : ℝ, 0<C ∧
    ∀ (t c : ℕ) (old : Tapes t 2) (ht : 43<t) (payload : Tapes (1+c) 2) (j : Fin c)
      (s : Shape) (v : Stage s) (rowsCount ell p : ℕ)
      (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (hr : 0<rowsCount)
      (hslots : v.slots=25^3) (pc : Fin count)
      (hp : ∀ op,1<v.f → ActivePrefixStageRuntimeData.Packed
        (ActivePrefixStagePairData.changePair
          (NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr) op) D)
      (xs : Fin (ActivePrefixStageTripleWords.count (NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr)) → Fin (2^ell) → Coefficient)
      (hw : ∀ i k,(xs i k).1.length=NativePolynomialStageShape.width s p ∧
        (xs i k).2.length=NativePolynomialStageShape.width s p)
      (_hword : payload.tape ⟨j.val+1,by omega⟩=SymbolTripleClean.word
        (List.ofFn (ActivePrefixStageNativeRows.flat
          (rows (NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr) xs hw))))
      (_hhead : payload.head ⟨j.val+1,by omega⟩=0),
      let d := NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr
      let st := NativePolynomialStageHeaders.prepared s rowsCount ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val
      let caller := Alphabet.mapTapes CompactNativeRoleConjugatedPorts.encoding (external old ht st payload)
      let ys := rows d (outputCoefficients d hslots pc ell xs)
        (output_width d hslots pc ell (NativePolynomialStageShape.width s p) xs hw)
      let time := CompactNativeConjugatedSharedCaller.cost (callerTapes t c) d ell
        (CompactNativeConjugatedPhaseFamily.cost D d hslots (order v) pc ell (NativePolynomialStageShape.width s p) hp)
      HoareTime (CompactNativeRoleConjugatedPorts.program P t c j (order v) pc)
        (fun z => z=caller.append (FixedHeaderBankCopy.empty CompactNativeConjugatedHeaderBank.tapes))
        (fun z => z=(setTape caller (CompactNativeRoleConjugatedPorts.selected t j)
          ((CompactNativeConjugatedPhase.bank d ell ys).tape CompactNativeConjugatedHeaderBank.source)
          ((CompactNativeConjugatedPhase.bank d ell ys).head CompactNativeConjugatedHeaderBank.source)).append
          (FixedHeaderBankCopy.empty CompactNativeConjugatedHeaderBank.tapes)) time ∧
      (time : ℝ)≤C*ActivePrefixStageInverseBudget.scale d := by
  obtain ⟨q,P,C,hC,hP⟩ := CompactNativeConjugatedPhaseFamily.exists_program D
  refine ⟨q,P,C+268,by positivity,?_⟩
  intro t c old ht payload j s v rowsCount ell p hG hGK hr hslots pc hp xs hw hword hhead
  dsimp only
  let d := NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr
  have hslotsD : d.stage.slots=25^3 := hslots
  have ho := expanded_ordered v ell p
  have hbounds := CompactNativeRoleConjugatedBudget.polynomial_bounds s ell p
  obtain ⟨hphase,hbound⟩ := hP _ d hslotsD (order v) ho pc ell (NativePolynomialStageShape.width s p)
    (NativePolynomialStageShape.code s ell p) hbounds.1 hbounds.2 hp xs hw
  rw [output_bank d hslotsD pc ell (NativePolynomialStageShape.width s p) xs hw] at hphase
  constructor
  · exact CompactNativeRoleConjugatedPorts.prepared_runs P old ht payload j v rowsCount ell p hG hGK hr
      (order v) pc _ _ hword hhead hphase
  · have hlife := CompactNativeRoleConjugatedBudget.lifecycle_linear (callerTapes t c) (order v) d ho ell hbounds.1
    have hvolume := CompactNativeConjugatedPhaseFamily.volume_le_scale d
    have hlifeR :
        ((FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 14) (AllAxisPhaseOriginalScalar.words d ell)+
          FixedHeaderBankCopy.cleanupCost (t:=callerTapes t c) (AllAxisPhaseOriginalScalar.words d ell) : ℕ) : ℝ)≤
            266*ActivePrefixStageInverseBudget.scale d := by
      exact (Nat.cast_le.mpr hlife).trans (by
        simpa only [Nat.cast_mul,Nat.cast_ofNat] using
          mul_le_mul_of_nonneg_left hvolume (by norm_num : (0 : ℝ)≤266))
    have hunit := ActivePrefixStageInverseBudget.one_le_scale d
    unfold CompactNativeConjugatedSharedCaller.cost
    push_cast at hlifeR ⊢
    dsimp only [d] at hbound hlifeR hunit
    linarith

end
end IntegerMultBounds.Machine.CompactNativeRoleConjugatedCaller
