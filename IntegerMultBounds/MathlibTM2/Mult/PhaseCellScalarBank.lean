module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarUnary
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoad
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankRoleCode

/-! # Load the scalar dimension bank from generated unary conversions -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

def bank (r : TblR 5) : Fin 117 := ⟨(ForwardBankPlacement.code r).val, by
  have hh := (ForwardBankPlacement.code r).isLt
  omega⟩

theorem bank_injective : Function.Injective bank := by
  intro r s h
  apply ForwardBankPlacement.code_injective
  apply Fin.ext
  exact congrArg (fun k : Fin 117 => k.val) h

theorem bank_lt (r : TblR 5) : (bank r).val < 20 := (ForwardBankPlacement.code r).isLt

def bankInput : Fin 5 → Fin 117 := ![20, 21, 22, 22, 22]

def inputBits (w : ℕ) (k : Fin 117) : ℕ := if k = 20 ∨ k = 21 then w else 0

def inputValue (q w : ℕ) (k : Fin 117) : ℕ := if k = 20 then q else if k = 21 then w else 0

def loadedR {A : ℕ} (q w : ℕ) (R : Regs 117 A) : Regs 117 A :=
  chirpBankLoadR bank bankInput w w (inputValue q w) (unarySetupR q w R)

def loadBank : Pr P 117 Q A U := .seq unarySetup (chirpBankLoad bank bankInput 23 23)

/-- Initialize the entire arithmetic bank from unary q/w and empty owned ports. -/
theorem loadBank_exec_of_width {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}
    (q w : ℕ) (hw5 : 5 ≤ w) (hw : q + 4 ≤ w) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hqR : (S.R 100).length = q) (hwR : (S.R 94).length = w)
    (hclean : ∀ k : Fin 117, k.val < 26 → S.R k = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (q + w) * (4 * w + 10) + 12 * w + 20 +
        chirpBankLoadCost bank bankInput w w (inputBits w) ∧
      Exec body loadBank (mk v S) m (mk v' { S with R := loadedR q w S.R }) := by
  have hfit := unarySetup_room_of_width hw5 hw
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unarySetup_exec (body := body) q w v S hqR hwR (by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> exact hclean _ (by decide))
  let S₁ : Stacks 117 A := { S with R := unarySetupR q w S.R }
  have hblank (r : TblR 5) : S₁.R (bank r) = [] := by
    have hh := bank_lt r
    simp [S₁, unarySetupR, show bank r ≠ (20 : Fin 117) by intro h; have := congrArg Fin.val h; omega,
      show bank r ≠ (21 : Fin 117) by intro h; have := congrArg Fin.val h; omega,
      show bank r ≠ (23 : Fin 117) by intro h; have := congrArg Fin.val h; omega,
      hclean (bank r) (by omega)]
  have hoff (r : TblR 5) : bank r ≠ (23 : Fin 117) := by
    have hh := bank_lt r
    intro h
    have he := congrArg Fin.val h
    omega
  have hin (i : Fin 5) (r : TblR 5) : bank r ≠ bankInput i := by
    have hh := bank_lt r
    have hi : 20 ≤ (bankInput i).val := by fin_cases i <;> decide
    intro h
    have he := congrArg Fin.val h
    omega
  obtain ⟨v₂, hu₂, he₂⟩ := chirpBankLoad_exec (body := body) bank bank_injective bankInput 23 23 hoff hoff hin
    w w (inputBits w) (inputValue q w)
    (by intro i; fin_cases i <;> simp [bankInput, inputValue, inputBits, hfit.1, hfit.2.1])
    (by intro i; fin_cases i <;> simp [bankInput, inputBits])
    v₁ S₁ (by simp [S₁, unarySetupR]) (by simp [S₁, unarySetupR])
    (by intro i; fin_cases i <;> simp [S₁, unarySetupR, bankInput, inputBits, inputValue, hclean 22 (by decide), binSyms]) hblank
  exact ⟨v₂, m₁ + chirpBankLoadCost bank bankInput w w (inputBits w), hu₂.trans hu₁,
    by omega, Exec.seq he₁ he₂⟩

theorem loadBank_exec {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}
    (q w : ℕ) (hq : 1 ≤ q) (hw : q + 4 ≤ w) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hqR : (S.R 100).length = q) (hwR : (S.R 94).length = w)
    (hclean : ∀ k : Fin 117, k.val < 26 → S.R k = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (q + w) * (4 * w + 10) + 12 * w + 20 +
        chirpBankLoadCost bank bankInput w w (inputBits w) ∧
      Exec body loadBank (mk v S) m (mk v' { S with R := loadedR q w S.R }) := by
  exact loadBank_exec_of_width (body := body) q w (by omega) hw v S hqR hwR hclean

/-- The initialized value bank consumed by the existing multiplier-size program. -/
def bankState {A : ℕ} (q w : ℕ) : TblSt 5 A := ⟨![q, w, 0, 0, 0], []⟩

theorem loadedR_off {A : ℕ} (q w : ℕ) (R : Regs 117 A) (k : Fin 117) (hk : 26 ≤ k.val) :
    loadedR q w R k = R k := by
  unfold loadedR
  rw [chirpBankLoad_off _ _ _ _ _ _ _ (by
    intro r
    have hh := bank_lt r
    intro h
    have he := congrArg Fin.val h
    omega)]
  simp [unarySetupR, show k ≠ (20 : Fin 117) by intro h; have := congrArg Fin.val h; omega,
    show k ≠ (21 : Fin 117) by intro h; have := congrArg Fin.val h; omega,
    show k ≠ (23 : Fin 117) by intro h; have := congrArg Fin.val h; omega]

/-- The loader establishes every semantic and scratch field of the table bank. -/
theorem loadBank_holds {A : ℕ} (q w : ℕ) (S : Stacks 117 A)
    (hclean : ∀ k : Fin 117, k.val < 26 → S.R k = []) :
    tblHolds bank { S with R := loadedR q w S.R }
      (tblRho w (List.replicate w tick) (List.replicate w tick) (bankState q w)) := by
  have hblank (r : TblR 5) : unarySetupR q w S.R (bank r) = [] := by
    have hh := bank_lt r
    simp [unarySetupR, show bank r ≠ (20 : Fin 117) by intro h; have := congrArg Fin.val h; omega,
      show bank r ≠ (21 : Fin 117) by intro h; have := congrArg Fin.val h; omega,
      show bank r ≠ (23 : Fin 117) by intro h; have := congrArg Fin.val h; omega,
      hclean (bank r) (by omega)]
  have hv : (fun i => inputValue q w (bankInput i)) = ![q, w, 0, 0, 0] := by
    funext i
    fin_cases i <;> simp [inputValue, bankInput]
  have hh := chirpBankLoad_holds bank bank_injective bankInput w w (inputValue q w)
    { S with R := unarySetupR q w S.R } hblank
  simpa only [loadedR, hv, bankState] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
