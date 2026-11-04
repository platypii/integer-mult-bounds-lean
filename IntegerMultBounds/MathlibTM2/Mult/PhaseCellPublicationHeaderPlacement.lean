module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedPublicationBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalGroupHost

/-! Unary page dimensions and binary router geometry occupy different roles
inside the existing fixed bank. Three swaps reuse the origin-page generator. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds.MathlibTM2.Fast.TableVM FixedStreamedBank
noncomputable section

def publicationReg (i : Fin 117) : Fin tapeCount := base (callerGenerator i)

theorem publicationReg_injective : Function.Injective publicationReg :=
  base_injective.comp (TransposeRegisterPlacement.generator_injective _)

def publicationPageIndex : Equiv.Perm (Fin 117) :=
  (Equiv.swap 102 33).trans ((Equiv.swap 94 34).trans (Equiv.swap 116 36))

def publicationPageBank (i : Fin 117) : Fin tapeCount := publicationReg (publicationPageIndex i)

theorem publicationPageBank_injective : Function.Injective publicationPageBank :=
  publicationReg_injective.comp publicationPageIndex.injective

@[simp] theorem publicationPageBank_coreLength : publicationPageBank 102 = publicationReg 33 := by
  simp [publicationPageBank,publicationPageIndex,Equiv.trans_apply,Equiv.swap_apply_def]
@[simp] theorem publicationPageBank_wordWidth : publicationPageBank 94 = publicationReg 34 := by
  simp [publicationPageBank,publicationPageIndex,Equiv.trans_apply,Equiv.swap_apply_def]
@[simp] theorem publicationPageBank_count : publicationPageBank 116 = publicationReg 36 := by
  simp [publicationPageBank,publicationPageIndex,Equiv.trans_apply,Equiv.swap_apply_def]
@[simp] theorem publicationPageBank_width : publicationPageBank 115 = publicationReg 115 := by
  simp [publicationPageBank,publicationPageIndex,Equiv.trans_apply,Equiv.swap_apply_def]
@[simp] theorem publicationPageBank_origins : publicationPageBank 109 = publicationReg 109 := by
  simp [publicationPageBank,publicationPageIndex,Equiv.trans_apply,Equiv.swap_apply_def]

theorem publicationPageBank_small (i : Fin 117) (hi : i.val < 31) :
    publicationPageBank i = publicationReg i := by
  have hoff (j : Fin 117) (hj : 31 ≤ j.val) : i ≠ j := by intro he; subst i; omega
  simp [publicationPageBank,publicationPageIndex,Equiv.trans_apply,Equiv.swap_apply_def,
    hoff 102 (by decide),hoff 33 (by decide),hoff 94 (by decide),hoff 34 (by decide),
    hoff 116 (by decide),hoff 36 (by decide)]

def publicationGeometryVariable (i : Fin 3) : Fin 117 :=
  ⟨if i.val < 2 then 97+i.val else 102,by split_ifs <;> omega⟩

def publicationGeometryIndex : TblR 3 → Fin 117
  | .v i => publicationGeometryVariable i
  | .wr => 115
  | .wn => 31
  | .acc => 32
  | .z i => ⟨37+i.val,by have := i.isLt; omega⟩

theorem publicationGeometryIndex_injective : Function.Injective publicationGeometryIndex := by
  intro x y h
  cases x <;> cases y <;> simp only [publicationGeometryIndex,publicationGeometryVariable,Fin.ext_iff] at h
  all_goals (try split_ifs at h) <;> (try simp_all [Fin.ext_iff]) <;> omega

def publicationGeometryBank (r : TblR 3) : Fin tapeCount := publicationReg (publicationGeometryIndex r)

theorem publicationGeometryBank_injective : Function.Injective publicationGeometryBank :=
  publicationReg_injective.comp publicationGeometryIndex_injective

theorem publicationGeometryBank_variables (i : Fin 3) :
    publicationGeometryBank (.v i) = ![publicationReg 97,publicationReg 98,publicationReg 102] i := by
  fin_cases i <;> simp [publicationGeometryBank,publicationGeometryIndex,publicationGeometryVariable]

@[simp] theorem publicationGeometryBank_width : publicationGeometryBank .wr = publicationReg 115 := rfl

theorem publicationGeometryIndex_lower (r : TblR 3) : 31 ≤ (publicationGeometryIndex r).val := by
  cases r <;> simp only [publicationGeometryIndex,publicationGeometryVariable]
  all_goals (try split_ifs) <;> omega

theorem publicationGeometryBank_off_origin (r : TblR 3) (o : TblR 16) :
    publicationGeometryBank r ≠ publicationReg (originReg o) := by
  intro he
  have hv := publicationReg_injective he
  have hr := publicationGeometryIndex_lower r
  have ho := originReg_range o
  rw [hv] at hr
  omega

theorem publicationGeometryBank_off_pages (r : TblR 3) :
    publicationGeometryBank r ≠ publicationPageBank 102 ∧
    publicationGeometryBank r ≠ publicationPageBank 94 ∧
    publicationGeometryBank r ≠ publicationPageBank 116 := by
  simp only [publicationPageBank_coreLength,publicationPageBank_wordWidth,publicationPageBank_count,
    publicationGeometryBank,publicationReg_injective.ne_iff]
  cases r <;> simp only [publicationGeometryIndex,publicationGeometryVariable]
  all_goals (try split_ifs) <;> (try simp_all [Fin.ext_iff]) <;> omega


theorem publicationGeometryBank_off_ports (r : TblR 3) :
    publicationGeometryBank r ≠ numericalPort ∧ publicationGeometryBank r ≠ ambientPort := by
  change publicationReg (publicationGeometryIndex r) ≠ publicationReg 95 ∧
    publicationReg (publicationGeometryIndex r) ≠ publicationReg 96
  simp only [publicationReg_injective.ne_iff]
  cases r <;> simp only [publicationGeometryIndex,publicationGeometryVariable]
  all_goals (try split_ifs) <;> (try simp_all [Fin.ext_iff]) <;> omega

theorem publicationPageBank_off_payload (i : Fin 117) : publicationPageBank i ≠ extra 1 :=
  base_extra _ _

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
