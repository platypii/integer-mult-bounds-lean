import IntegerMultBounds.Machine.CompactNativeRoleConjugatedLifecycle
import IntegerMultBounds.Machine.CompactComplexRecursiveGeometry
import IntegerMultBounds.Networks.ComplexRecursiveCallSchema

/-! Every actual complex25 edge occurrence selects its original named role
and its actual native phase kernel. Stage geometry is derived from a genuine
recursive Visit; repeated equal labels retain distinct occurrence indices.
This supplies physical phase blocks, not a whole scalar/recursive network. -/
namespace IntegerMultBounds.Machine.CompactComplexRolePhaseSite
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (Visit node arity)
open Networks.ComplexRecursiveCallSchema (Wire Occurrence)
open CompactNativeRoleConjugatedLifecycle (caller resultPayload)
open CompactNativeRoleConjugatedCaller (order)
open ButterflyStreamData (Coefficient)
open ActivePrefixStageNativePolynomial (rows)
open Networks.Shared50ModularControl (prime)
attribute [local irreducible] Networks.ComplexPhaseBudget.edges
variable {s : Shape}

/-- The proved fixed named-layout cardinality, never a runtime role count. -/
def roleCount : ℕ := 58645352620000

def roleEncoding : Wire ≃ Fin roleCount :=
  Fintype.equivFinOfCardEq Networks.NetworkBudget.complex_role_card_25

def role (site : Occurrence) : Fin roleCount := roleEncoding (Networks.ComplexRecursiveCallSchema.role site)

theorem site_count : Networks.ComplexRecursiveCallSchema.sites.length=CompactAllAxisPhaseDispatch.count :=
  List.length_attach

def pc (site : Occurrence) : Fin CompactAllAxisPhaseDispatch.count := Fin.cast site_count site

theorem pc_injective : Function.Injective pc := Fin.cast_injective site_count

private theorem cast_get_attach {α : Type*} (l : List α) (i : Fin l.attach.length) :
    l.get (Fin.cast List.length_attach i)=(l.attach.get i).val := by
  simpa only [List.get_eq_getElem,Fin.val_cast] using (List.get_attach l i).symm

theorem actual_edge (site : Occurrence) :
    CompactAllAxisPhaseDispatch.edge (pc site)=Networks.ComplexRecursiveCallSchema.edge site := by
  apply Subtype.ext
  exact cast_get_attach Networks.ComplexPhaseBudget.edges site

def program {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime) (t : ℕ)
    (site : Occurrence) (order : ActivePrefixStageHeadersData.Order) :=
  CompactNativeRoleConjugatedLifecycle.program P t roleCount (role site) order (pc site)

/-- Actual occurrence and original role placement discharge every phase block.
No edge, source role, codec setup, execution or time allowance is supplied. -/
theorem exists_program (D : ℕ) :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q prime, ∃ C : ℝ, 0<C ∧
    ∀ (t : ℕ) (old : Tapes t 2) (ht : 43<t) (payload : Tapes (1+roleCount) 2)
      (site : Occurrence) (s : Shape) (rho : Fin s.chunk) (left k : ℕ)
      (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
      (pair : Networks.BinaryRowProgram.Op (Fin arity)) (rowsCount ell p : ℕ)
      (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (hr : 0<rowsCount) (_hpay : s.payload=1)
      (hp : ∀ op,1<(NativePolynomialStageShape.inputs
        (CompactBinaryBasisSchedule.stage (node rho visit hactive) pair) rowsCount ell p hG hGK hr).stage.f →
        ActivePrefixStageRuntimeData.Packed (ActivePrefixStagePairData.changePair
          (NativePolynomialStageShape.inputs (CompactBinaryBasisSchedule.stage (node rho visit hactive) pair)
            rowsCount ell p hG hGK hr) op) D)
      (xs : Fin (ActivePrefixStageTripleWords.count (NativePolynomialStageShape.inputs
        (CompactBinaryBasisSchedule.stage (node rho visit hactive) pair) rowsCount ell p hG hGK hr)) → Fin (2^ell) → Coefficient)
      (hw : ∀ i z,(xs i z).1.length=NativePolynomialStageShape.width s p ∧
        (xs i z).2.length=NativePolynomialStageShape.width s p)
      (_hword : payload.tape ⟨(role site).val+1,by have := (role site).isLt; omega⟩=
        SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat (rows
          (NativePolynomialStageShape.inputs (CompactBinaryBasisSchedule.stage (node rho visit hactive) pair)
            rowsCount ell p hG hGK hr) xs hw))))
      (_hhead : payload.head ⟨(role site).val+1,by have := (role site).isLt; omega⟩=0),
      let v := CompactBinaryBasisSchedule.stage (node rho visit hactive) pair
      let d := NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr
      let hslotsD : d.stage.slots=25^3 := rfl
      let out := resultPayload d hslotsD (pc site) ell (NativePolynomialStageShape.width s p) xs hw payload (role site)
      let phaseTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes t roleCount) d ell
        (CompactNativeConjugatedPhaseFamily.cost D d hslotsD (order v) (pc site) ell (NativePolynomialStageShape.width s p) hp)
      let time := CompactNativeRoleConjugatedLifecycle.cost v rowsCount ell p phaseTime
      HoareTime (program P t site (order v))
        (fun z => z=(caller old ht v rowsCount ell p payload).append
          (FixedHeaderBankCopy.empty CompactNativeRoleConjugatedLifecycle.privateTapes))
        (fun z => z=(caller old ht v rowsCount ell p out).append
          (FixedHeaderBankCopy.empty CompactNativeRoleConjugatedLifecycle.privateTapes)) time ∧
      (time : ℝ)≤C*ActivePrefixStageInverseBudget.scale d := by
  obtain ⟨q,P,C,hC,hP⟩ := CompactNativeRoleConjugatedLifecycle.exists_program D
  refine ⟨q,P,C,hC,?_⟩
  intro t old ht payload site s rho left k visit hactive pair rowsCount ell p hG hGK hr hpay hp xs hw hword hhead
  exact hP t roleCount old ht payload (role site) s
    (CompactBinaryBasisSchedule.stage (node rho visit hactive) pair) rowsCount ell p hG hGK hr hpay rfl
    (pc site) hp xs hw hword hhead

end
end IntegerMultBounds.Machine.CompactComplexRolePhaseSite
