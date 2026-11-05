module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSolverAllocation
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFullLineInputFrame

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
noncomputable section

theorem solverHeader_ne_parameter (T : ℕ) (src : Fin 11 → Fin T) (i : Fin 8)
    (r : Role) (hr : r ≠ .zero) :
    fullHeader (T+solverRegisterCount) r ≠ solverParameter T src i := by
  unfold solverParameter
  cases solverParameterSource i with
  | none => exact (fullHeader_injective _).ne hr
  | some j =>
    intro he
    exact header_ne_bank id r (solverSource (src j)) (classCallerRegister_injective he)

theorem solverHeader_ne_source (T : ℕ) (r : Role) (i : Fin T) :
    fullHeader (T+solverRegisterCount) r ≠ unarySource _ (solverSource i) := by
  intro he
  exact header_ne_bank id r (solverSource i) (classCallerRegister_injective he)

theorem callerFullLineInput_off_header (T : ℕ) (src : Fin 11 → Fin T) (r : Role)
    (hz : r ≠ .zero) :
    fullHeader (T+solverRegisterCount) r ∉ (callerFullLineInput T src).support := by
  simp only [FullLineInputPlan.support,List.mem_append,List.mem_ofFn,List.mem_cons,
    List.not_mem_nil,or_false,not_or,not_exists]
  refine ⟨⟨?_,?_⟩,?_,?_,?_,?_,?_,?_⟩
  · intro i; exact solverRegister_ne_header T (.input i) r
  · intro i; exact (solverHeader_ne_parameter T src i r hz).symm
  · exact (solverRegister_ne_header T (.scratch 0) r).symm
  · exact (solverRegister_ne_header T (.scratch 1) r).symm
  · exact (solverRegister_ne_header T (.scratch 2) r).symm
  · exact (solverRegister_ne_header T (.scratch 3) r).symm
  · exact (solverRegister_ne_header T (.scratch 4) r).symm
  · exact solverHeader_ne_source T r (src 8)

theorem callerFullLineProducer_off_header (T Q : ℕ) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (r : Role) :
    fullHeader (T+solverRegisterCount) r ∉ (callerFullLineProducer T Q hR hQ).support := by
  simp only [PackedProducerPlan.support,List.mem_append,List.mem_ofFn,List.mem_cons,
    List.not_mem_nil,or_false,not_or,not_exists]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i; exact solverRegister_ne_header T (.worker i) r
  all_goals exact (solverRegister_ne_header T _ r).symm

theorem callerFullLine_controls_separated (T Q : ℕ) (src : Fin 11 → Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (widthSource : Fin (T+solverRegisterCount))
    (slot : Fin 3) :
    (slot ≠ 0 → boundaryGeometryRegister (T+solverRegisterCount) widthSource (boundarySeamCropSkip slot) ∉
      (callerFullLineInput T src).support++(callerFullLineProducer T Q hR hQ).support) ∧
    boundaryGeometryRegister (T+solverRegisterCount) widthSource (boundarySeamCropCount slot) ∉
      (callerFullLineInput T src).support++(callerFullLineProducer T Q hR hQ).support := by
  have hoff (r : Role) (hz : r ≠ .zero) :
      fullHeader (T+solverRegisterCount) r ∉
        (callerFullLineInput T src).support++(callerFullLineProducer T Q hR hQ).support := by
    rw [List.mem_append]
    exact not_or.mpr ⟨callerFullLineInput_off_header T src r hz,
      callerFullLineProducer_off_header T Q hR hQ r⟩
  constructor
  · intro hs
    fin_cases slot
    · exact (hs rfl).elim
    · change boundaryGeometryRegister (T+solverRegisterCount) widthSource (boundarySeamCropSkip 1) ∉ _
      rw [boundaryGeometryRegister_skip_one]
      exact hoff _ (by simp)
    · change boundaryGeometryRegister (T+solverRegisterCount) widthSource (boundarySeamCropSkip 2) ∉ _
      rw [boundaryGeometryRegister_skip_two]
      exact hoff _ (by simp)
  · rw [boundaryGeometryRegister_count]
    exact hoff _ (by simp)

theorem callerFullLine_result (T : ℕ) (cropSources : Fin 2 → Fin (T+solverRegisterCount)) :
    callerFullLineResult T = boundaryCropRegister (T+solverRegisterCount) cropSources 94 := by
  rw [boundaryCropRegister_private _ _ 94 (by decide +kernel)]
  rfl

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
