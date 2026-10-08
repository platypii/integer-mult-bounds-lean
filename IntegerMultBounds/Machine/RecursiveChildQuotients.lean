import IntegerMultBounds.Machine.RecursiveChildQuotientsConstant
import IntegerMultBounds.Machine.BinaryDescriptorDivision
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList
import IntegerMultBounds.Machine.RecursiveChildDimensionsClean

/-! Produce child width/row quotients on the constructor's actual 38-tape bank.
Both fixed divisors are physically written, used, and erased. No quotient or
constant descriptor is supplied as input; parent headers are preserved. -/
namespace IntegerMultBounds.Machine.RecursiveChildQuotients
open SharedPlacementAlphabet (setTape)
variable {a : ℕ}
noncomputable section

def headerHead : Option (List Bool) → ℤ | none => 0 | some _ => 1
def headerTape : Option (List Bool) → ℤ → Fin (a+4)
  | none => fun _ => blank
  | some xs => BinaryDescriptorStack.descriptor xs

def bank (hs : Fin 6 → List Bool) (bs rs divisor : Option (List Bool)) : Tapes 38 a where
  head i := if i.val = 0 then headerHead divisor else if 3 ≤ i.val ∧ i.val < 9 then 1
    else if i.val = 9 then headerHead bs else if i.val = 10 then headerHead rs else 0
  tape i := if i.val = 0 then headerTape divisor
    else if i.val = 3 then BinaryDescriptorStack.descriptor (hs 0)
    else if i.val = 4 then BinaryDescriptorStack.descriptor (hs 1)
    else if i.val = 5 then BinaryDescriptorStack.descriptor (hs 2)
    else if i.val = 6 then BinaryDescriptorStack.descriptor (hs 3)
    else if i.val = 7 then BinaryDescriptorStack.descriptor (hs 4)
    else if i.val = 8 then BinaryDescriptorStack.descriptor (hs 5)
    else if i.val = 9 then headerTape bs else if i.val = 10 then headerTape rs else fun _ => blank

def input (hs : Fin 6 → List Bool) : Tapes 38 a := bank hs none none none

theorem output_eq (hs : Fin 6 → List Bool) (bs rs : List Bool) :
    bank (a := a) hs (some bs) (some rs) none = RecursiveChildDimensionsClean.input hs bs rs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [RecursiveChildDimensions.input,
      RecursiveChildDimensions.bank,RecursiveChildDimensions.ds0,RecursiveDimensionBank.head,
      RecursiveDimensionBank.tape,headerHead,headerTape,SharedBank.empty,
      BinaryDescriptorStackRoundtrip.descriptor_encoded] <;> rfl

def widthPlacement : Fin (12+26) ≃ Fin 38 where
  toFun := ![6,0,1,2,11,9,12,13,14,15,16,17,3,4,5,7,8,10,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
  invFun := ![1,2,3,12,13,14,0,15,16,5,17,4,6,7,8,9,10,11,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def rowsPlacement : Fin (12+26) ≃ Fin 38 where
  toFun := ![4,0,1,2,11,10,12,13,14,15,16,17,3,5,6,7,8,9,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
  invFun := ![1,2,3,12,0,13,14,15,16,17,5,4,6,7,8,9,10,11,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private theorem placed_exact {s u t r cost : ℕ} {M : Program s r a}
    (e : Fin (s+u) ≃ Fin t) (v w : Tapes t a) (small small' : Tapes s a)
    (ha : Placement.active e v = small) (hf : Placement.active e w = small')
    (he : Placement.extra e v = Placement.extra e w)
    (hh : HoareTime M (fun x => x = small) (fun x => x = small') cost) :
    HoareTime (Placement.placed M e) (fun x => x = v) (fun x => x = w) cost := by
  apply (Placement.hoare_at hh e v ha).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨y,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

private theorem width_hoare (hs : Fin 6 → List Bool) (ds bs : List Bool)
    (hh : HoareTime (BinaryDescriptorDivision.program a)
      (fun v => v = BinaryDescriptorDivision.input (hs 3) ds)
      (fun v => v = BinaryDescriptorDivision.output (hs 3) ds bs)
      (BinaryDescriptorDivision.cost (hs 3) ds)) :
    HoareTime (Placement.placed (BinaryDescriptorDivision.program a) widthPlacement)
      (fun v => v = bank hs none none (some ds)) (fun v => v = bank hs (some bs) none (some ds))
      (BinaryDescriptorDivision.cost (hs 3) ds) := by
  apply placed_exact widthPlacement _ _ _ _ _ _ _ hh
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem rows_hoare (hs : Fin 6 → List Bool) (ds bs rs : List Bool)
    (hh : HoareTime (BinaryDescriptorDivision.program a)
      (fun v => v = BinaryDescriptorDivision.input (hs 1) ds)
      (fun v => v = BinaryDescriptorDivision.output (hs 1) ds rs)
      (BinaryDescriptorDivision.cost (hs 1) ds)) :
    HoareTime (Placement.placed (BinaryDescriptorDivision.program a) rowsPlacement)
      (fun v => v = bank hs (some bs) none (some ds)) (fun v => v = bank hs (some bs) (some rs) (some ds))
      (BinaryDescriptorDivision.cost (hs 1) ds) := by
  apply placed_exact rowsPlacement _ _ _ _ _ _ _ hh
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def initializeProgram (n : ℕ) :=
  Placement.placed (RecursiveChildQuotientsConstant.program (a := a) n) (FiniteReturnStackAt.placement (0 : Fin 38))

private theorem initialize_hoare (n : ℕ) (hs : Fin 6 → List Bool) (bs rs : Option (List Bool)) :
    HoareTime (initializeProgram (a := a) n) (fun v => v = bank hs bs rs none)
      (fun v => v = bank hs bs rs (some (RecursiveChildQuotientsConstant.bits n))) (RecursiveChildQuotientsConstant.cost n) := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) n)
    (FiniteReturnStackAt.placement (0 : Fin 38)) (bank hs bs rs none) (by rw [FiniteReturnStackAt.active_bank]; rfl)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [bank,headerHead,headerTape]

private theorem erase_hoare (ds : List Bool) (hs : Fin 6 → List Bool) (bs rs : Option (List Bool)) :
    HoareTime (BinaryDescriptorCleanupList.oneProgram (a := a) (0 : Fin 38))
      (fun v => v = bank hs bs rs (some ds)) (fun v => v = bank hs bs rs none) (2*ds.length+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare (a := a) (0 : Fin 38) (bank hs bs rs (some ds)) ds rfl rfl
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [bank,headerHead,headerTape]

def program (m roles : ℕ) :=
  seq (seq (seq (seq (seq (initializeProgram (a := a) m)
    (Placement.placed (BinaryDescriptorDivision.program a) widthPlacement))
    (BinaryDescriptorCleanupList.oneProgram (0 : Fin 38))) (initializeProgram roles))
    (Placement.placed (BinaryDescriptorDivision.program a) rowsPlacement))
    (BinaryDescriptorCleanupList.oneProgram (0 : Fin 38))

def cost (m roles : ℕ) (hs : Fin 6 → List Bool) :=
  BinaryDescriptorDivision.cost (hs 3) (RecursiveChildQuotientsConstant.bits m)+
  BinaryDescriptorDivision.cost (hs 1) (RecursiveChildQuotientsConstant.bits roles)+
  5*((RecursiveChildQuotientsConstant.bits m).length+(RecursiveChildQuotientsConstant.bits roles).length)+25

/-- Both quotients are physically generated; all temporary divisor/scratch
storage is erased, exactly matching the clean child constructor's input. -/
theorem quotients_hoare (m roles : ℕ) (hm : 0 < m) (hr : 0 < roles) (hs : Fin 6 → List Bool) :
    ∃ bs rs : List Bool, GrowingCounterData.Canonical bs ∧ GrowingCounterData.Canonical rs ∧
      Counter.value bs = Counter.value (hs 3)/m ∧ Counter.value rs = Counter.value (hs 1)/roles ∧
      HoareTime (program (a := a) m roles) (fun v => v = input hs)
        (fun v => v = RecursiveChildDimensionsClean.input hs bs rs) (cost m roles hs) := by
  obtain ⟨bs,hbc,hbv,_,hb⟩ := BinaryDescriptorDivision.divide_hoare (a := a) (hs 3) (RecursiveChildQuotientsConstant.bits m)
    (by rw [RecursiveChildQuotientsConstant.bits_value]; exact hm)
  obtain ⟨rs,hrc,hrv,_,hr'⟩ := BinaryDescriptorDivision.divide_hoare (a := a) (hs 1) (RecursiveChildQuotientsConstant.bits roles)
    (by rw [RecursiveChildQuotientsConstant.bits_value]; exact hr)
  rw [RecursiveChildQuotientsConstant.bits_value] at hbv hrv
  have h := (((((initialize_hoare m hs none none).seq (width_hoare hs _ bs hb)).seq
    (erase_hoare _ hs (some bs) none)).seq (initialize_hoare roles hs (some bs) none)).seq
    (rows_hoare hs _ bs rs hr')).seq (erase_hoare _ hs (some bs) (some rs))
  refine ⟨bs,rs,hbc,hrc,hbv,hrv,h.consequence (fun _ h => h) ?_ ?_⟩
  · intro v hv; exact hv.trans (output_eq hs bs rs)
  · unfold cost RecursiveChildQuotientsConstant.cost
    omega

end
end IntegerMultBounds.Machine.RecursiveChildQuotients
