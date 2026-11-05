module

public import IntegerMultBounds.MathlibTM2.Host.SharedRegisterPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSeamMasterSources

/-! Count generation shares only retained inputs and three output headers with
the caller. All temporary metadata uses the existing private routing bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
variable {T : ℕ}
noncomputable section

def boundaryCountKeys : Fin 7 → Fin 117 := ![17,55,56,58,60,61,62]
def boundaryCountPortTag : Fin 7 → Role ⊕ Fin 1 :=
  ![.inl (.publication 3),.inl (.scalar 4),.inl (.scalar 10),.inr 0,
    .inl (.publication 0),.inl (.publication 1),.inl (.publication 2)]

theorem boundaryCountKeys_injective : Function.Injective boundaryCountKeys := by decide +kernel

theorem boundaryCountPortTag_injective : Function.Injective boundaryCountPortTag := by decide +kernel

def boundaryCountPort (T : ℕ) (widthSource : Fin T) : Role ⊕ Fin 1 → Fin ((T+headerCount)+175)
  | .inl r => Fin.castAdd 175 (header T r)
  | .inr _ => Fin.castAdd 175 (bank id widthSource)

theorem boundaryCountPort_injective (T : ℕ) (widthSource : Fin T) :
    Function.Injective (boundaryCountPort T widthSource) := by
  intro x y he
  cases x with
  | inl r =>
    cases y with
    | inl k =>
      exact congrArg Sum.inl ((header_injective T) ((Fin.castAdd_injective _ _) he))
    | inr k =>
      exact False.elim (header_ne_bank id r widthSource ((Fin.castAdd_injective _ _) he))
  | inr r =>
    cases y with
    | inl k =>
      exact False.elim (header_ne_bank id k widthSource ((Fin.castAdd_injective _ _) he.symm))
    | inr k => exact congrArg Sum.inr (Subsingleton.elim r k)

noncomputable def boundaryCountRole (i : Fin 117) : Option (Fin 7) := by
  classical
  exact if h : ∃ j, boundaryCountKeys j = i then some h.choose else none

theorem boundaryCountRole_key (j : Fin 7) : boundaryCountRole (boundaryCountKeys j) = some j := by
  classical
  have h : ∃ k, boundaryCountKeys k = boundaryCountKeys j := ⟨j,rfl⟩
  simp only [boundaryCountRole,dite_eq_left h]
  exact congrArg some (boundaryCountKeys_injective h.choose_spec)

theorem boundaryCountRole_recovers (i : Fin 117) (j : Fin 7) (h : boundaryCountRole i = some j) :
    boundaryCountKeys j = i := by
  classical
  unfold boundaryCountRole at h
  split_ifs at h with hi
  · have hj := Option.some.inj h
    exact hj ▸ hi.choose_spec

def boundaryCountRegister (T : ℕ) (widthSource : Fin T) : Fin 117 → Fin (MachineTapes T) :=
  sharedRegisterPlacement (fun i => Fin.natAdd ((T+headerCount)+175) (publicationReg i))
    (fun j => Fin.castAdd tapeCount (boundaryCountPort T widthSource (boundaryCountPortTag j))) boundaryCountRole

theorem boundaryCountRegister_injective (T : ℕ) (widthSource : Fin T) :
    Function.Injective (boundaryCountRegister T widthSource) := by
  apply sharedRegisterPlacement_injective
  · exact (Fin.natAdd_injective _ _).comp publicationReg_injective
  · exact (Fin.castAdd_injective _ _).comp
      ((boundaryCountPort_injective T widthSource).comp boundaryCountPortTag_injective)
  · intro i j
    exact (prefix_ne_routing _ _).symm
  · intro i k j hi hk
    exact (boundaryCountRole_recovers i j hi).symm.trans (boundaryCountRole_recovers k j hk)

theorem boundaryCountRegister_shared (T : ℕ) (widthSource : Fin T) (i : Fin 7) :
    boundaryCountRegister T widthSource (boundaryCountKeys i) =
      Fin.castAdd tapeCount (boundaryCountPort T widthSource (boundaryCountPortTag i)) := by
  simp only [boundaryCountRegister,sharedRegisterPlacement,boundaryCountRole_key]

theorem boundaryCountRegister_private (T : ℕ) (widthSource : Fin T) (i : Fin 117)
    (hi : ∀ j, boundaryCountKeys j ≠ i) :
    boundaryCountRegister T widthSource i = Fin.natAdd ((T+headerCount)+175) (publicationReg i) := by
  classical
  have hn : ¬∃ j, boundaryCountKeys j = i := by rintro ⟨j,hj⟩; exact hi j hj
  simp only [boundaryCountRegister,sharedRegisterPlacement,boundaryCountRole,dite_eq_right hn]

@[simp] theorem boundaryCountRegister_word (T : ℕ) (widthSource : Fin T) :
    boundaryCountRegister T widthSource 17 = fullHeader T (.publication 3) := by
  exact boundaryCountRegister_shared T widthSource 0

@[simp] theorem boundaryCountRegister_line (T : ℕ) (widthSource : Fin T) :
    boundaryCountRegister T widthSource 55 = globals T 4 := by
  exact boundaryCountRegister_shared T widthSource 1

@[simp] theorem boundaryCountRegister_width (T : ℕ) (widthSource : Fin T) :
    boundaryCountRegister T widthSource 56 = globals T 10 := by
  exact boundaryCountRegister_shared T widthSource 2

@[simp] theorem boundaryCountRegister_ruler (T : ℕ) (widthSource : Fin T) :
    boundaryCountRegister T widthSource 58 = unarySource T widthSource := by
  exact boundaryCountRegister_shared T widthSource 3

@[simp] theorem boundaryCountRegister_output (T : ℕ) (widthSource : Fin T) (slot : Fin 3) :
    boundaryCountRegister T widthSource (boundarySeamCropCount slot) =
      fullHeader T (.publication (Fin.castAdd 4 slot)) := by
  fin_cases slot
  · exact boundaryCountRegister_shared T widthSource 4
  · exact boundaryCountRegister_shared T widthSource 5
  · exact boundaryCountRegister_shared T widthSource 6

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
