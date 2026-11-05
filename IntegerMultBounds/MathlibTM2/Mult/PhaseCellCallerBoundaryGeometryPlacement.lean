module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerBoundaryCountPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExportSlotBoundaryGeometry

/-! Extend count placement with two retained skip headers and the caller zero
port. Existing count/ruler/dimension mappings and private storage are reused. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
variable {T : ℕ}
noncomputable section

def boundarySkipKeys : Fin 3 → Fin 117 := ![63,64,65]
def boundarySkipRole : Fin 3 → Role := ![.publication 4,.publication 5,.zero]

theorem boundarySkipKeys_injective : Function.Injective boundarySkipKeys := by decide +kernel

theorem boundarySkipRole_injective : Function.Injective boundarySkipRole := by decide +kernel

def boundarySkipIndex (i : Fin 117) : Option (Fin 3) := by
  classical
  exact if h : ∃ j, boundarySkipKeys j = i then some h.choose else none

theorem boundarySkipIndex_key (j : Fin 3) : boundarySkipIndex (boundarySkipKeys j) = some j := by
  classical
  have h : ∃ k, boundarySkipKeys k = boundarySkipKeys j := ⟨j,rfl⟩
  simp only [boundarySkipIndex,dite_eq_left h]
  exact congrArg some (boundarySkipKeys_injective h.choose_spec)

theorem boundarySkipIndex_recovers (i : Fin 117) (j : Fin 3) (h : boundarySkipIndex i = some j) :
    boundarySkipKeys j = i := by
  classical
  unfold boundarySkipIndex at h
  split_ifs at h with hi
  have hj := Option.some.inj h
  exact hj ▸ hi.choose_spec

theorem boundaryCountRegister_off_skip (T : ℕ) (widthSource : Fin T) (i : Fin 117) (j : Fin 3) :
    boundaryCountRegister T widthSource i ≠ fullHeader T (boundarySkipRole j) := by
  unfold boundaryCountRegister sharedRegisterPlacement
  cases hr : boundaryCountRole i with
  | none => exact (prefix_ne_routing (Fin.castAdd 175 (header T (boundarySkipRole j))) (publicationReg i)).symm
  | some k =>
    intro he
    have he' := (Fin.castAdd_injective _ _) he
    have htags : ∀ k : Fin 7, ∀ j : Fin 3, boundaryCountPortTag k ≠ Sum.inl (boundarySkipRole j) := by decide +kernel
    cases ht : boundaryCountPortTag k with
    | inl role =>
      rw [ht] at he'
      change Fin.castAdd 175 (header T role) = Fin.castAdd 175 (header T (boundarySkipRole j)) at he'
      have hrole := (header_injective T) ((Fin.castAdd_injective _ _) he')
      exact htags k j (ht.trans (congrArg Sum.inl hrole))
    | inr n =>
      rw [ht] at he'
      change Fin.castAdd 175 (bank id widthSource) = Fin.castAdd 175 (header T (boundarySkipRole j)) at he'
      exact header_ne_bank id (boundarySkipRole j) widthSource ((Fin.castAdd_injective _ _) he'.symm)

def boundaryGeometryRegister (T : ℕ) (widthSource : Fin T) : Fin 117 → Fin (MachineTapes T) :=
  sharedRegisterPlacement (boundaryCountRegister T widthSource)
    (fun j => fullHeader T (boundarySkipRole j)) boundarySkipIndex

theorem boundaryGeometryRegister_injective (T : ℕ) (widthSource : Fin T) :
    Function.Injective (boundaryGeometryRegister T widthSource) := by
  apply sharedRegisterPlacement_injective
  · exact boundaryCountRegister_injective T widthSource
  · exact (fullHeader_injective T).comp boundarySkipRole_injective
  · exact boundaryCountRegister_off_skip T widthSource
  · intro i k j hi hk
    exact (boundarySkipIndex_recovers i j hi).symm.trans (boundarySkipIndex_recovers k j hk)

theorem boundaryGeometryRegister_existing (T : ℕ) (widthSource : Fin T) (i : Fin 117)
    (hi : ∀ j, boundarySkipKeys j ≠ i) :
    boundaryGeometryRegister T widthSource i = boundaryCountRegister T widthSource i := by
  classical
  have hn : ¬∃ j, boundarySkipKeys j = i := by rintro ⟨j,hj⟩; exact hi j hj
  simp only [boundaryGeometryRegister,sharedRegisterPlacement,boundarySkipIndex,dite_eq_right hn]

theorem boundaryGeometryRegister_skip (T : ℕ) (widthSource : Fin T) (j : Fin 3) :
    boundaryGeometryRegister T widthSource (boundarySkipKeys j) = fullHeader T (boundarySkipRole j) := by
  simp only [boundaryGeometryRegister,sharedRegisterPlacement,boundarySkipIndex_key]

@[simp] theorem boundaryGeometryRegister_word (T : ℕ) (widthSource : Fin T) :
    boundaryGeometryRegister T widthSource 17 = fullHeader T (.publication 3) := by
  rw [boundaryGeometryRegister_existing T widthSource 17 (by decide +kernel),boundaryCountRegister_word]

@[simp] theorem boundaryGeometryRegister_line (T : ℕ) (widthSource : Fin T) :
    boundaryGeometryRegister T widthSource 55 = globals T 4 := by
  rw [boundaryGeometryRegister_existing T widthSource 55 (by decide +kernel),boundaryCountRegister_line]

@[simp] theorem boundaryGeometryRegister_width (T : ℕ) (widthSource : Fin T) :
    boundaryGeometryRegister T widthSource 56 = globals T 10 := by
  rw [boundaryGeometryRegister_existing T widthSource 56 (by decide +kernel),boundaryCountRegister_width]

@[simp] theorem boundaryGeometryRegister_ruler (T : ℕ) (widthSource : Fin T) :
    boundaryGeometryRegister T widthSource 58 = unarySource T widthSource := by
  rw [boundaryGeometryRegister_existing T widthSource 58 (by decide +kernel),boundaryCountRegister_ruler]

@[simp] theorem boundaryGeometryRegister_count (T : ℕ) (widthSource : Fin T) (slot : Fin 3) :
    boundaryGeometryRegister T widthSource (boundarySeamCropCount slot) = fullHeader T (.publication (Fin.castAdd 4 slot)) := by
  rw [boundaryGeometryRegister_existing T widthSource _ (by fin_cases slot <;> decide +kernel),boundaryCountRegister_output]

@[simp] theorem boundaryGeometryRegister_zero (T : ℕ) (widthSource : Fin T) :
    boundaryGeometryRegister T widthSource (boundarySeamCropSkip 0) = fullHeader T .zero :=
  boundaryGeometryRegister_skip T widthSource 2

@[simp] theorem boundaryGeometryRegister_skip_one (T : ℕ) (widthSource : Fin T) :
    boundaryGeometryRegister T widthSource (boundarySeamCropSkip 1) = fullHeader T (.publication 4) :=
  boundaryGeometryRegister_skip T widthSource 0

@[simp] theorem boundaryGeometryRegister_skip_two (T : ℕ) (widthSource : Fin T) :
    boundaryGeometryRegister T widthSource (boundarySeamCropSkip 2) = fullHeader T (.publication 5) :=
  boundaryGeometryRegister_skip T widthSource 1

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
