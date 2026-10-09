import IntegerMultBounds.Machine.PlacedDescriptorConstruction
import IntegerMultBounds.Machine.PackedOffsetPowerHeader
import IntegerMultBounds.Machine.RecursiveDimensionBank

/-! Physically derive the packed front-action fiber count P*2^w*G from the
four original interchange headers. Only the derived count survives; all
power/product workspace is physically erased. -/
namespace IntegerMultBounds.Machine.BinaryPackedRowCount
noncomputable section
variable {a : ℕ}
open SharedPlacementAlphabet (setTape)
open RecursiveDimensionBank (head tape)

def bank (hs : Fin 4 → List Bool) (ds : Fin 3 → Option (List Bool)) : Tapes 13 a :=
  ⟨![1,1,1,1,head (ds 0),head (ds 1),head (ds 2),0,0,0,0,0,0],
    ![RadixZeroFill.encodedBinary (hs 0),RadixZeroFill.encodedBinary (hs 1),
      RadixZeroFill.encodedBinary (hs 2),RadixZeroFill.encodedBinary (hs 3),
      tape (ds 0),tape (ds 1),tape (ds 2),fun _ => blank,fun _ => blank,fun _ => blank,
      fun _ => blank,fun _ => blank,fun _ => blank]⟩

def powerBits (w : ℕ) := FixedBasePowerStep.bits 2 w
def productBits (P w : ℕ) := DimensionProductDescriptor.bits P (2^w)
def rowBits (P w G : ℕ) := DimensionProductDescriptor.bits (P*2^w) G

def input (hs : Fin 4 → List Bool) := bank (a := a) hs ![none,none,none]
def powered (hs : Fin 4 → List Bool) (w : ℕ) := bank (a := a) hs ![none,some (powerBits w),none]
def multiplied (hs : Fin 4 → List Bool) (P w : ℕ) :=
  bank (a := a) hs ![none,some (powerBits w),some (productBits P w)]
def prepared (hs : Fin 4 → List Bool) (P w G : ℕ) :=
  bank (a := a) hs ![some (rowBits P w G),some (powerBits w),some (productBits P w)]
def output (hs : Fin 4 → List Bool) (P w G : ℕ) :=
  bank (a := a) hs ![some (rowBits P w G),none,none]

def powerPlacement : Fin (8+5) ≃ Fin 13 where
  toFun := ![7,8,9,10,11,5,12,3,0,1,2,4,6]
  invFun := ![8,9,10,7,11,5,12,0,1,2,3,4,6]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def firstPlacement : Fin (6+7) ≃ Fin 13 where
  toFun := ![7,6,8,5,9,0,1,2,3,4,10,11,12]
  invFun := ![5,6,7,8,9,3,1,0,2,4,10,11,12]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def secondPlacement : Fin (6+7) ≃ Fin 13 where
  toFun := ![7,4,8,1,9,6,0,2,3,5,10,11,12]
  invFun := ![6,3,7,8,1,9,5,0,2,4,10,11,12]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def powerProgram : Program 13 101 a := Placement.placed (FixedBasePowerDescriptor.program (q := a) 2) powerPlacement
def firstProgram : Program 13 40 a := Placement.placed (DimensionProductDescriptor.program (q := a)) firstPlacement
def secondProgram : Program 13 40 a := Placement.placed (DimensionProductDescriptor.program (q := a)) secondPlacement
def cleanup := seq (BinaryDescriptorCleanupList.oneProgram (a := a) (5 : Fin 13))
  (BinaryDescriptorCleanupList.oneProgram (a := a) (6 : Fin 13))
def program : Program 13 189 a := seq (seq (seq (powerProgram (a := a)) firstProgram) secondProgram) cleanup

private theorem placed_exact {s u k cost : ℕ} {M : Program s k a}
    (e : Fin (s+u) ≃ Fin 13) (v w : Tapes 13 a) (x y : Tapes s a)
    (ha : Placement.active e v=x) (hb : Placement.active e w=y)
    (he : Placement.extra e v=Placement.extra e w)
    (h : HoareTime M (fun z => z=x) (fun z => z=y) cost) :
    HoareTime (Placement.placed M e) (fun z => z=v) (fun z => z=w) cost := by
  refine (Placement.hoare_at h e v ha).consequence (fun _ h => h) ?_ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  rw [Placement.replace,he,← hb]
  exact Placement.view _ _

theorem power (hs : Fin 4 → List Bool) (w : ℕ)
    (hw : Counter.value (hs 3)=w) (cw : GrowingCounterData.Canonical (hs 3)) :
    HoareTime (powerProgram (a := a)) (fun z => z=input hs) (fun z => z=powered hs w)
      (FixedBasePowerDescriptor.constant 2*2^w) := by
  have ha : Placement.active powerPlacement (input (a := a) hs)=FixedBasePowerDescriptor.input (hs 3) := by
    apply congrArg₂ Tapes.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> first | rfl | exact CountedLoopReuseAlphabet.encoding_binary _
  have hp := PlacedDescriptorConstruction.power_hoare powerPlacement (input (a := a) hs)
    2 w (by decide) (hs 3) hw cw ha
  have he : setTape (input (a := a) hs) 5 (RadixZeroFill.encodedBinary (powerBits w)) 1=powered hs w := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  exact hp.consequence (fun _ h => h) (fun _ h => h.trans he) le_rfl

private theorem first_input (hs : Fin 4 → List Bool) (w : ℕ) :
    Placement.active firstPlacement (powered (a := a) hs w) =
      DimensionProductDescriptor.input (powerBits w) (hs 0) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem first_output (hs : Fin 4 → List Bool) (P w : ℕ) :
    Placement.active firstPlacement (multiplied (a := a) hs P w) =
      DimensionProductDescriptor.output (powerBits w) (hs 0) P (2^w) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem first_extra (hs : Fin 4 → List Bool) (ds : Fin 3 → Option (List Bool)) :
    Placement.extra firstPlacement (bank (a := a) hs ds) =
      (⟨![1,1,1,head (ds 0),0,0,0],![RadixZeroFill.encodedBinary (hs 1),
        RadixZeroFill.encodedBinary (hs 2),RadixZeroFill.encodedBinary (hs 3),tape (ds 0),
        fun _ => blank,fun _ => blank,fun _ => blank]⟩ : Tapes 7 a) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem first_frame (hs : Fin 4 → List Bool) (P w : ℕ) :
    Placement.extra firstPlacement (powered (a := a) hs w) =
      Placement.extra firstPlacement (multiplied hs P w) := by
  rw [powered,multiplied,first_extra,first_extra]
  simp only [Matrix.cons_val_zero]

theorem first_product (hs : Fin 4 → List Bool) (P w : ℕ)
    (hP : Counter.value (hs 0)=P) (cP : GrowingCounterData.Canonical (hs 0)) :
    HoareTime (firstProgram (a := a)) (fun z => z=powered hs w) (fun z => z=multiplied hs P w)
      (53*(P*2^w)+28) := by
  have hv : Counter.value (powerBits w)=2^w := by
    rw [powerBits,PackedOffsetPowerHeader.power_bits,RecursiveChildQuotientsConstant.bits_value]
  have hc : GrowingCounterData.Canonical (powerBits w) := by
    rw [powerBits,PackedOffsetPowerHeader.power_bits]
    exact RecursiveChildQuotientsConstant.bits_canonical _
  exact placed_exact firstPlacement _ _ _ _ (first_input hs w) (first_output hs P w) (first_frame hs P w)
    (DimensionProductDescriptor.construct_hoare (powerBits w) (hs 0) P (2^w) (by positivity) hv hP hc cP)

theorem second_product (hs : Fin 4 → List Bool) (P w G : ℕ) (hG : 0 < G)
    (hv : Counter.value (hs 1)=G) (hc : GrowingCounterData.Canonical (hs 1)) :
    HoareTime (secondProgram (a := a)) (fun z => z=multiplied hs P w) (fun z => z=prepared hs P w G)
      (53*(P*2^w*G)+28) := by
  apply placed_exact secondPlacement _ _ _ _ _ _ _
    (DimensionProductDescriptor.construct_hoare (hs 1) (productBits P w) (P*2^w) G hG hv
      (DimensionProductDescriptor.bits_value P (2^w)) hc (DimensionProductDescriptor.bits_canonical P (2^w)))
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private def cleanCost (P w : ℕ) := 2*(powerBits w).length+2*(productBits P w).length+12

theorem cleans (hs : Fin 4 → List Bool) (P w G : ℕ) :
    HoareTime (cleanup (a := a)) (fun z => z=prepared hs P w G) (fun z => z=output hs P w G) (cleanCost P w) := by
  have h₀ := BinaryDescriptorCleanupList.one_hoare (5 : Fin 13) (prepared (a := a) hs P w G)
    (powerBits w) (by rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]; rfl) rfl
  have h₁ := BinaryDescriptorCleanupList.one_hoare (6 : Fin 13)
    (setTape (prepared (a := a) hs P w G) 5 (fun _ => blank) 0) (productBits P w) (by rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]; rfl) rfl
  have h := h₀.seq h₁
  have he : setTape (setTape (prepared (a := a) hs P w G) 5 (fun _ => blank) 0) 6 (fun _ => blank) 0 =
      output hs P w G := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  refine h.consequence (fun _ h => h) (fun _ h => h.trans he) ?_
  dsimp only [cleanCost]
  omega

theorem constructs (hs : Fin 4 → List Bool) (P w G : ℕ) (hG : 0 < G)
    (hP : Counter.value (hs 0)=P) (hGv : Counter.value (hs 1)=G) (hw : Counter.value (hs 3)=w)
    (cP : GrowingCounterData.Canonical (hs 0)) (cG : GrowingCounterData.Canonical (hs 1))
    (cw : GrowingCounterData.Canonical (hs 3)) :
    HoareTime (program (a := a)) (fun z => z=input hs) (fun z => z=output hs P w G)
      (FixedBasePowerDescriptor.constant 2*2^w+53*(P*2^w)+53*(P*2^w*G)+cleanCost P w+59) := by
  exact ((((power hs w hw cw).seq (first_product hs P w hP cP)).seq
    (second_product hs P w G hG hGv cG)).seq (cleans hs P w G)).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

theorem row_value (P w G : ℕ) : Counter.value (rowBits P w G)=P*2^w*G :=
  DimensionProductDescriptor.bits_value _ _
theorem row_canonical (P w G : ℕ) : GrowingCounterData.Canonical (rowBits P w G) :=
  DimensionProductDescriptor.bits_canonical _ _

end
end IntegerMultBounds.Machine.BinaryPackedRowCount
