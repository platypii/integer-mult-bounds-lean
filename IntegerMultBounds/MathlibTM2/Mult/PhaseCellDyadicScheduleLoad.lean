module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalGroupHost
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoad

/-! Load the dyadic generator from three retained binary headers. All other
variables, word counters, accumulator and arithmetic scratch are constructed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def dyadicScheduleInput (i : Fin 16) : Fin 117 :=
  if i = 6 then 97 else if i = 7 then 98 else if i = 9 then 102 else 106

def dyadicScheduleInputValue (a b C : ℕ) (r : Fin 117) : ℕ :=
  if r = 97 then a else if r = 98 then b else if r = 102 then C else 0

def dyadicScheduleInputBits (V : ℕ) (r : Fin 117) : ℕ := if r = 106 then 0 else V

def loadDyadicScheduleInputs : Pr P 117 Q A U := chirpBankLoad originReg dyadicScheduleInput 115 115

def dyadicScheduleInitialState (a b C : ℕ) : TblSt 16 A :=
  ⟨fun i => dyadicScheduleInputValue a b C (dyadicScheduleInput i),[]⟩

theorem dyadicScheduleInitialState_value (a b C : ℕ) (i : Fin 16) :
    (dyadicScheduleInitialState (A := A) a b C).val i =
      if i = 6 then a else if i = 7 then b else if i = 9 then C else 0 := by
  simp only [dyadicScheduleInitialState,dyadicScheduleInput]
  split_ifs <;> simp [dyadicScheduleInputValue]

theorem dyadicScheduleInitialState_bounded (a b C V : ℕ) (hbits : a+b < V)
    (hfit : C*2^(a+b) < 2^V) : ∀ i, (dyadicScheduleInitialState (A := A) a b C).val i < 2^V := by
  have hwide : a+b < 2^V := hbits.trans Nat.lt_two_pow_self
  have hseed : C < 2^V := (Nat.le_mul_of_pos_right C (Nat.two_pow_pos _)).trans_lt hfit
  intro i
  rw [dyadicScheduleInitialState_value]
  split_ifs <;> omega

theorem loadDyadicScheduleInputs_exec (a b C V : ℕ) (hbits : a+b < V)
    (hfit : C*2^(a+b) < 2^V) (v : HS 117 Q A U) (S : Stacks 117 A)
    (ha : S.R 97 = binSyms V a) (hb : S.R 98 = binSyms V b) (hC : S.R 102 = binSyms V C)
    (hz : S.R 106 = []) (hwidth : (S.R 115).length = V) (hblank : ∀ r, S.R (originReg r) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body loadDyadicScheduleInputs (mk v S) (110*V+137)
        (mk v' {S with R := (chirpBankLoadR originReg dyadicScheduleInput V V
          (dyadicScheduleInputValue a b C) S.R)}) ∧
      tblHolds originReg {S with R := (chirpBankLoadR originReg dyadicScheduleInput V V
          (dyadicScheduleInputValue a b C) S.R)}
        (tblRho V (List.replicate V tick) (List.replicate V tick) (dyadicScheduleInitialState a b C)) := by
  have hhigh : ∀ i, 31 ≤ (dyadicScheduleInput i).val := by
    intro i
    unfold dyadicScheduleInput
    split_ifs <;> decide
  have hoff (r : TblR 16) (i : Fin 117) (hi : 31 ≤ i.val) : originReg r ≠ i := by
    have hr := originReg_range r
    intro he
    rw [he] at hr
    omega
  have hwide : a+b < 2^V := hbits.trans Nat.lt_two_pow_self
  have hseed : C < 2^V := (Nat.le_mul_of_pos_right C (Nat.two_pow_pos _)).trans_lt hfit
  obtain ⟨v',hu,he⟩ := chirpBankLoad_exec (body := body) originReg originReg_injective
    dyadicScheduleInput 115 115 (fun r => hoff r 115 (by decide)) (fun r => hoff r 115 (by decide))
    (fun i r => hoff r _ (hhigh i)) V V (dyadicScheduleInputBits V) (dyadicScheduleInputValue a b C)
    (by intro i; unfold dyadicScheduleInput; split_ifs <;> simp [dyadicScheduleInputValue,dyadicScheduleInputBits] <;> omega)
    (by intro i; unfold dyadicScheduleInputBits; split_ifs <;> omega) v S hwidth hwidth
    (by intro i; unfold dyadicScheduleInput; split_ifs <;> simp [dyadicScheduleInputBits,dyadicScheduleInputValue,ha,hb,hC,hz,binSyms]) hblank
  have hcost : chirpBankLoadCost originReg dyadicScheduleInput V V (dyadicScheduleInputBits V) = 110*V+137 := by
    simp [chirpBankLoadCost,chirpBankCopiesCost,chirpBankInputAssignments,
      dyadicScheduleInput,dyadicScheduleInputBits,List.ofFn_succ]
    ring
  exact ⟨v',hu,he.cast hcost rfl,
    chirpBankLoad_holds originReg originReg_injective dyadicScheduleInput V V
      (dyadicScheduleInputValue a b C) S hblank⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
