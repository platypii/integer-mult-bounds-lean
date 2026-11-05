module

public import IntegerMultBounds.MathlibTM2.Host.SharedRegisterPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerBoundaryGeometryPlacement

/-! Crop execution shares the retained replica and line rulers and the generated
control headers. Data and scratch remain in the existing private routing bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
variable {T : ℕ}
noncomputable section

def boundaryCropKeys : Fin 9 → Fin 117 := ![15,16,17,60,61,62,63,64,65]
def boundaryCropPortTag : Fin 9 → Role ⊕ Fin 2 :=
  ![.inr 0,.inr 1,.inl (.publication 3),.inl (.publication 0),
    .inl (.publication 1),.inl (.publication 2),.inl (.publication 4),
    .inl (.publication 5),.inl .zero]

theorem boundaryCropKeys_injective : Function.Injective boundaryCropKeys := by decide +kernel

theorem boundaryCropPortTag_injective : Function.Injective boundaryCropPortTag := by decide +kernel

def boundaryCropPort (T : ℕ) (src : Fin 2 → Fin T) : Role ⊕ Fin 2 → Fin ((T+headerCount)+175)
  | .inl r => Fin.castAdd 175 (header T r)
  | .inr j => Fin.castAdd 175 (bank id (src j))

theorem boundaryCropPort_injective (T : ℕ) (src : Fin 2 → Fin T)
    (hsrc : Function.Injective src) : Function.Injective (boundaryCropPort T src) := by
  intro x y he
  cases x with
  | inl r =>
    cases y with
    | inl k =>
      exact congrArg Sum.inl ((header_injective T) ((Fin.castAdd_injective _ _) he))
    | inr k =>
      exact False.elim (header_ne_bank id r (src k) ((Fin.castAdd_injective _ _) he))
  | inr r =>
    cases y with
    | inl k =>
      exact False.elim (header_ne_bank id k (src r) ((Fin.castAdd_injective _ _) he.symm))
    | inr k => exact congrArg Sum.inr (hsrc ((bank_injective id Function.injective_id) ((Fin.castAdd_injective _ _) he)))

noncomputable def boundaryCropRole (i : Fin 117) : Option (Fin 9) := by
  classical
  exact if h : ∃ j, boundaryCropKeys j = i then some h.choose else none

theorem boundaryCropRole_key (j : Fin 9) : boundaryCropRole (boundaryCropKeys j) = some j := by
  classical
  have h : ∃ k, boundaryCropKeys k = boundaryCropKeys j := ⟨j,rfl⟩
  simp only [boundaryCropRole,dite_eq_left h]
  exact congrArg some (boundaryCropKeys_injective h.choose_spec)

theorem boundaryCropRole_recovers (i : Fin 117) (j : Fin 9) (h : boundaryCropRole i = some j) :
    boundaryCropKeys j = i := by
  classical
  unfold boundaryCropRole at h
  split_ifs at h with hi
  · have hj := Option.some.inj h
    exact hj ▸ hi.choose_spec

def boundaryCropRegister (T : ℕ) (src : Fin 2 → Fin T) : Fin 117 → Fin (MachineTapes T) :=
  sharedRegisterPlacement (fun i => Fin.natAdd ((T+headerCount)+175) (publicationReg i))
    (fun j => Fin.castAdd tapeCount (boundaryCropPort T src (boundaryCropPortTag j))) boundaryCropRole

theorem boundaryCropRegister_injective (T : ℕ) (src : Fin 2 → Fin T)
    (hsrc : Function.Injective src) : Function.Injective (boundaryCropRegister T src) := by
  apply sharedRegisterPlacement_injective
  · exact (Fin.natAdd_injective _ _).comp publicationReg_injective
  · exact (Fin.castAdd_injective _ _).comp
      ((boundaryCropPort_injective T src hsrc).comp boundaryCropPortTag_injective)
  · intro i j
    exact (prefix_ne_routing _ _).symm
  · intro i k j hi hk
    exact (boundaryCropRole_recovers i j hi).symm.trans (boundaryCropRole_recovers k j hk)

theorem boundaryCropRegister_shared (T : ℕ) (src : Fin 2 → Fin T) (i : Fin 9) :
    boundaryCropRegister T src (boundaryCropKeys i) =
      Fin.castAdd tapeCount (boundaryCropPort T src (boundaryCropPortTag i)) := by
  simp only [boundaryCropRegister,sharedRegisterPlacement,boundaryCropRole_key]

theorem boundaryCropRegister_private (T : ℕ) (src : Fin 2 → Fin T) (i : Fin 117)
    (hi : ∀ j, boundaryCropKeys j ≠ i) :
    boundaryCropRegister T src i = Fin.natAdd ((T+headerCount)+175) (publicationReg i) := by
  classical
  have hn : ¬∃ j, boundaryCropKeys j = i := by rintro ⟨j,hj⟩; exact hi j hj
  simp only [boundaryCropRegister,sharedRegisterPlacement,boundaryCropRole,dite_eq_right hn]

@[simp] theorem boundaryCropRegister_clock (T : ℕ) (src : Fin 2 → Fin T) :
    boundaryCropRegister T src 15 = unarySource T (src 0) :=
  boundaryCropRegister_shared T src 0

@[simp] theorem boundaryCropRegister_rows (T : ℕ) (src : Fin 2 → Fin T) :
    boundaryCropRegister T src 16 = unarySource T (src 1) :=
  boundaryCropRegister_shared T src 1

@[simp] theorem boundaryCropRegister_word (T : ℕ) (src : Fin 2 → Fin T) :
    boundaryCropRegister T src 17 = fullHeader T (.publication 3) :=
  boundaryCropRegister_shared T src 2

theorem boundaryCropRegister_count (T : ℕ) (src : Fin 2 → Fin T) (slot : Fin 3) :
    boundaryCropRegister T src (boundarySeamCropCount slot) =
      fullHeader T (.publication (Fin.castAdd 4 slot)) := by
  fin_cases slot
  · exact boundaryCropRegister_shared T src 3
  · exact boundaryCropRegister_shared T src 4
  · exact boundaryCropRegister_shared T src 5

theorem boundaryCropRegister_skip_agrees (T : ℕ) (src : Fin 2 → Fin T)
    (widthSource : Fin T) (slot : Fin 3) :
    boundaryCropRegister T src (boundarySeamCropSkip slot) =
      boundaryGeometryRegister T widthSource (boundarySeamCropSkip slot) := by
  fin_cases slot
  · change boundaryCropRegister T src (boundarySeamCropSkip 0) =
      boundaryGeometryRegister T widthSource (boundarySeamCropSkip 0)
    rw [boundaryGeometryRegister_zero]
    exact boundaryCropRegister_shared T src 8
  · change boundaryCropRegister T src (boundarySeamCropSkip 1) =
      boundaryGeometryRegister T widthSource (boundarySeamCropSkip 1)
    rw [boundaryGeometryRegister_skip_one]
    exact boundaryCropRegister_shared T src 6
  · change boundaryCropRegister T src (boundarySeamCropSkip 2) =
      boundaryGeometryRegister T widthSource (boundarySeamCropSkip 2)
    rw [boundaryGeometryRegister_skip_two]
    exact boundaryCropRegister_shared T src 7

theorem boundaryCropRegister_count_agrees (T : ℕ) (src : Fin 2 → Fin T)
    (widthSource : Fin T) (slot : Fin 3) :
    boundaryCropRegister T src (boundarySeamCropCount slot) =
      boundaryGeometryRegister T widthSource (boundarySeamCropCount slot) := by
  rw [boundaryCropRegister_count,boundaryGeometryRegister_count]

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
