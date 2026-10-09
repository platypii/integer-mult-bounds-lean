import IntegerMultBounds.Machine.RoundedRowDescriptor
import IntegerMultBounds.Compact.Layout

/-! Construct the compact least enclosing role multiple from only the original
runtime row count and record width. The role count is physically installed as
a fixed machine constant and erased after division. -/
namespace IntegerMultBounds.Machine.CompactRowPaddingRound
noncomputable section
variable {a : ℕ}
open IntegerMultBounds.Compact.Layout (paddedRows)

theorem padded_bounds (r c : ℕ) (hc : 0 < c) :
    r ≤ paddedRows r c ∧ paddedRows r c < r+c ∧ c ∣ paddedRows r c := by
  have hm := Nat.mod_lt r hc
  have hp := Nat.mod_lt (c-r%c) hc
  have hd : paddedRows r c % c = 0 := by
    unfold paddedRows
    rw [Nat.add_mod,Nat.mod_mod]
    by_cases hz : r%c = 0
    · simp [hz]
    · rw [Nat.mod_eq_of_lt (by omega : c-r%c < c)]
      rw [show r%c+(c-r%c)=c by omega,Nat.mod_self]
  exact ⟨by unfold paddedRows; omega,by unfold paddedRows; omega,Nat.dvd_of_mod_eq_zero hd⟩

theorem rounded_eq (r c : ℕ) (hr : 0 < r) (hc : 0 < c) :
    RoundedRowDescriptor.rounded r c = paddedRows r c := by
  obtain ⟨hp,hlt,hd⟩ := padded_bounds r c hc
  have hR := RoundedRowDescriptor.rows_le r c hr hc
  have hltR := RoundedRowDescriptor.rounded_lt r c hr
  have hdR := RoundedRowDescriptor.rounded_dvd r c
  by_cases h : paddedRows r c ≤ RoundedRowDescriptor.rounded r c
  · have hdiv := Nat.dvd_sub hdR hd
    have he := Nat.eq_zero_of_dvd_of_lt hdiv (by omega : RoundedRowDescriptor.rounded r c-paddedRows r c < c)
    omega
  · have hdiv := Nat.dvd_sub hd hdR
    have he := Nat.eq_zero_of_dvd_of_lt hdiv (by omega : paddedRows r c-RoundedRowDescriptor.rounded r c < c)
    omega

private def head : Option (List Bool) → ℤ | none => 0 | some _ => 1
private def tape : Option (List Bool) → ℤ → Fin (a+4)
  | none => fun _ => blank
  | some bs => RadixZeroFill.encodedBinary bs

def bank (rs ls : List Bool) (cs out : Option (List Bool)) : Tapes 16 a :=
  ⟨![1,1,head cs,head out,0,0,0,0,0,0,0,0,0,0,0,0],
   ![RadixZeroFill.encodedBinary rs,RadixZeroFill.encodedBinary ls,tape cs,tape out,
     fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,
     fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,
     fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank]⟩
def input (rs ls : List Bool) := bank (a := a) rs ls none none
def bits (r c : ℕ) := RoundedRowDescriptor.bits r c
def output (rs ls : List Bool) (r c : ℕ) := bank (a := a) rs ls none (some (bits r c))

def roundPlace : Fin (15+1) ≃ Fin 16 where
  toFun := ![0,2,4,5,6,3,7,8,9,10,11,12,13,14,15,1]
  invFun := ![0,15,1,5,2,3,4,6,7,8,9,10,11,12,13,14]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def writeProgram (c : ℕ) := Placement.placed (RecursiveChildQuotientsConstant.program (a := a) c)
  (FiniteReturnStackAt.placement (2 : Fin 16))
def roundProgram := Placement.placed (RoundedRowDescriptor.program (q := a)) roundPlace
def clearProgram := BinaryDescriptorCleanupList.oneProgram (a := a) (2 : Fin 16)
def program (c : ℕ) := seq (seq (writeProgram (a := a) c) roundProgram) clearProgram

theorem constructs (c : ℕ) (rs ls : List Bool) (r : ℕ)
    (hr : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs)
    (hR : 0 < r) (hc : 0 < c) :
    HoareTime (program (a := a) c) (fun w => w = input rs ls)
      (fun w => w = output rs ls r c)
      (4096*paddedRows r c+5*(RecursiveChildQuotientsConstant.bits c).length+12) := by
  let cs := RecursiveChildQuotientsConstant.bits c
  have h0 : HoareTime (writeProgram (a := a) c)
      (fun w => w = input rs ls) (fun w => w = bank rs ls (some cs) none)
      (RecursiveChildQuotientsConstant.cost c) := by
    have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) c)
      (FiniteReturnStackAt.placement (2 : Fin 16)) (input rs ls)
      (by rw [FiniteReturnStackAt.active_bank]; rfl)
    apply h.consequence (fun _ h => h) ?_ le_rfl
    rintro w ⟨z,rfl,rfl⟩
    rw [FiniteReturnStackAt.replace_bank]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [input,bank,head,tape,
        BinaryDescriptorStackRoundtrip.descriptor_encoded,cs]
  have h1 : HoareTime (roundProgram (a := a))
      (fun w => w = bank rs ls (some cs) none)
      (fun w => w = bank rs ls (some cs) (some (bits r c)))
      (4096*RoundedRowDescriptor.rounded r c) := by
    have h := Placement.hoare_at (RoundedRowDescriptor.construct_hoare (q := a) rs cs r c
      hr (RecursiveChildQuotientsConstant.bits_value c) cr
      (RecursiveChildQuotientsConstant.bits_canonical c) hR hc) roundPlace
      (bank rs ls (some cs) none) (by
        apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl)
    apply h.consequence (fun _ h => h) ?_ le_rfl
    rintro w ⟨z,rfl,rfl⟩
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have h2 := BinaryDescriptorCleanupList.one_hoare (2 : Fin 16)
    (bank (a := a) rs ls (some cs) (some (bits r c))) cs
    (BinaryDescriptorStackRoundtrip.descriptor_encoded cs).symm rfl
  have hclear : SharedPlacementAlphabet.setTape
      (bank (a := a) rs ls (some cs) (some (bits r c))) 2 (fun _ => blank) 0 = output rs ls r c := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [hclear] at h2
  apply ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h)
  rw [rounded_eq r c hR hc]
  unfold RecursiveChildQuotientsConstant.cost
  dsimp [cs]
  omega

theorem bits_value (r c : ℕ) (hr : 0 < r) (hc : 0 < c) :
    Counter.value (bits r c) = paddedRows r c := by
  rw [bits,RoundedRowDescriptor.bits_value,rounded_eq r c hr hc]

theorem bits_canonical (r c : ℕ) : GrowingCounterData.Canonical (bits r c) :=
  RoundedRowDescriptor.bits_canonical r c

end
end IntegerMultBounds.Machine.CompactRowPaddingRound
