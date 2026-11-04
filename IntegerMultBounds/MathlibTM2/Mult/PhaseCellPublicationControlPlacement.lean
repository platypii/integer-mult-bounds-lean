module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationHeaderFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationDimensionSetup

/-! Concrete working roles share one injective generator-bank language.
Small port lists instantiate generic injectivity only after their shape is fixed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds.MathlibTM2.Host
noncomputable section

def publicationDimensionIndex : PublicationDimensionReg → Fin 117
  | .a => 61 | .b => 62 | .coreLength => 33 | .wordWidth => 34
  | .rowCount => 36 | .capacity => 60 | .replicas => 59
  | .exponent => 51 | .packet => 52 | .padding => 53 | .clock => 54
  | .missing => 55 | .saved => 56 | .tmp => 57

theorem publicationDimensionIndex_injective : Function.Injective publicationDimensionIndex := by
  intro x y h
  cases x <;> cases y <;> simp_all [publicationDimensionIndex]

def publicationDimensionBank (r : PublicationDimensionReg) : Fin tapeCount :=
  publicationReg (publicationDimensionIndex r)

theorem publicationDimensionBank_injective : Function.Injective publicationDimensionBank :=
  publicationReg_injective.comp publicationDimensionIndex_injective

def publicationPort : Option (Fin 117) → Fin tapeCount
  | none => extra 1
  | some i => publicationReg i

theorem publicationPort_injective : Function.Injective publicationPort := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some j => exact False.elim (base_extra _ _ h.symm)
  | some i =>
    cases y with
    | none => exact False.elim (base_extra _ _ h)
    | some j => exact congrArg some (publicationReg_injective h)

@[simp] theorem publicationPageBank_control : publicationPageBank 92 = publicationReg 92 := by
  simp [publicationPageBank,publicationPageIndex,Equiv.trans_apply,Equiv.swap_apply_def]
@[simp] theorem publicationPageBank_window : publicationPageBank 103 = publicationReg 103 := by
  simp [publicationPageBank,publicationPageIndex,Equiv.trans_apply,Equiv.swap_apply_def]

theorem publicationCopy_registers :
    [publicationReg 54,publicationReg 52,publicationReg 36,publicationReg 69,publicationReg 68,numericalPort,publicationReg 70,extra 1,
      publicationReg 71,publicationReg 72].Nodup := by
  have h : ([some 54,some 52,some 36,some 69,some 68,some 95,some 70,none,some 71,some 72] : List (Option (Fin 117))).Nodup := by decide +kernel
  simpa only [List.map_cons,List.map_nil,publicationPort,publicationReg,numericalPort] using h.map publicationPort_injective

theorem publicationPadding_registers :
    [publicationReg 51,publicationReg 52,extra 1,publicationReg 58,publicationReg 65,publicationReg 66].Nodup := by
  have h : ([some 51,some 52,none,some 58,some 65,some 66] : List (Option (Fin 117))).Nodup := by decide +kernel
  simpa only [List.map_cons,List.map_nil,publicationPort] using h.map publicationPort_injective

theorem publicationScatter_registers :
    [publicationReg 54,publicationReg 67,publicationReg 53,publicationReg 34,publicationReg 73,publicationPageBank 92,
      publicationReg 74,publicationReg 75,publicationPageBank 103,extra 1,ambientPort,publicationReg 76,
      publicationReg 77,publicationReg 78,publicationReg 79,publicationReg 80,publicationReg 81].Nodup := by
  have h : ([some 54,some 67,some 53,some 34,some 73,some 92,some 74,some 75,some 103,none,some 96,
    some 76,some 77,some 78,some 79,some 80,some 81] : List (Option (Fin 117))).Nodup := by decide +kernel
  simpa only [List.map_cons,List.map_nil,publicationPort,publicationPageBank_control,
    publicationPageBank_window,publicationReg,ambientPort] using h.map publicationPort_injective


def publicationGeometryInput (i : Fin 3) : Fin tapeCount :=
  publicationReg ⟨82+i.val,by have := i.isLt; omega⟩

theorem publicationGeometryInput_retained (i : Fin 3) :
    publicationRetainedIndex ⟨82+i.val,by have := i.isLt; omega⟩ := by
  dsimp only [publicationRetainedIndex]
  have := i.isLt
  omega

theorem publicationGeometryInput_off_numerical (i : Fin 3) : publicationGeometryInput i ≠ numericalPort := by
  apply publicationReg_injective.ne
  intro h
  have hv := congrArg (fun j : Fin 117 => j.val) h
  change 82+i.val = 95 at hv
  have := i.isLt
  omega

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
