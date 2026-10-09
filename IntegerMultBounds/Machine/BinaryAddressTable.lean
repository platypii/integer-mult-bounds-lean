import IntegerMultBounds.Machine.BinaryAddressTableFill

/-! A fixed nine-tape machine writes every width-w binary address in increasing
order from only the original width header. Power/count/zero-counter generation,
copying, head returns and full private erasure are all physical and charged. -/
namespace IntegerMultBounds.Machine.BinaryAddressTable
open BinaryAddressTableData
open CountedCopyReuse (empty binary)
open SharedPlacementAlphabet (setTape)
noncomputable section

def bank (counter out clock count : ℤ → Fin 4) (pc po pl pn : ℤ) (ws : List Bool) : Tapes 9 0 :=
  ⟨![pc,po,pl,pn,0,1,0,0,0],![counter,out,clock,count,(fun _ => blank),binary ws,
    (fun _ => blank),(fun _ => blank),(fun _ => blank)]⟩
def countBits (w : ℕ) := FixedBasePowerStep.bits 2 w
def outputTape (w : ℕ) := putWord (fun _ => blank) 0 ((table w (2^w)).map (bitSymbol (a := 0)))
def input (ws : List Bool) := bank (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0 0 ws

def states (ws : List Bool) (w : ℕ) : Fin 9 → Tapes 9 0 :=
  ![input ws,
    bank (fun _ => blank) (fun _ => blank) (fun _ => blank) (binary (countBits w)) 0 0 0 1 ws,
    bank (binary (List.replicate w false)) (fun _ => blank) (fun _ => blank) (binary (countBits w)) 1 0 0 1 ws,
    bank (binary (List.replicate w false)) (fun _ => blank) empty (binary (countBits w)) 1 0 1 1 ws,
    bank (binary (List.replicate w false)) (outputTape w) empty (binary (countBits w)) 1 (2^w*w) 1 1 ws,
    bank (fun _ => blank) (outputTape w) empty (binary (countBits w)) 0 (2^w*w) 1 1 ws,
    bank (fun _ => blank) (outputTape w) (fun _ => blank) (binary (countBits w)) 0 (2^w*w) 0 1 ws,
    bank (fun _ => blank) (outputTape w) (fun _ => blank) (fun _ => blank) 0 (2^w*w) 0 0 ws,
    bank (fun _ => blank) (outputTape w) (fun _ => blank) (fun _ => blank) 0 0 0 0 ws]

def powerPlace : Fin (8+1) ≃ Fin 9 where
  toFun := ![0,2,4,6,7,3,8,5,1]
  invFun := ![0,8,1,5,2,7,3,4,6]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def fillPlace : Fin (3+6) ≃ Fin 9 where
  toFun := ![0,4,5,1,2,3,6,7,8]
  invFun := ![0,3,4,5,1,2,6,7,8]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def power := Placement.placed (FixedBasePowerDescriptor.program (q := 0) 2) powerPlace
def fill := Placement.placed BinaryAddressTableFill.program fillPlace
def clockInit := Placement.placed (RecursiveChildQuotientsConstant.program (a := 0) 0)
  (FiniteReturnStackAt.placement (2 : Fin 9))
def loop := extend (CountedLoopReuse.program BinaryAddressTableStep.program) 5
def clearCounter := BinaryDescriptorCleanupList.oneProgram (a := 0) (0 : Fin 9)
def clearClock := BinaryDescriptorCleanupList.oneProgram (a := 0) (2 : Fin 9)
def clearCount := BinaryDescriptorCleanupList.oneProgram (a := 0) (3 : Fin 9)
def rewind := Placement.placed (ReturnOrigin.program (a := 0)) (FiniteReturnStackAt.placement (1 : Fin 9))
def program := seq (seq (seq (seq (seq (seq (seq power fill) clockInit) loop) clearCounter) clearClock) clearCount) rewind

theorem binary_encoded (xs : List Bool) : RadixZeroFill.encodedBinary (q := 0) xs=binary xs := by
  funext z
  rfl

theorem power_hoare (ws : List Bool) (w : ℕ) (hw : Counter.value ws=w)
    (cw : GrowingCounterData.Canonical ws) :
    HoareTime power (fun z => z=states ws w 0) (fun z => z=states ws w 1)
      (FixedBasePowerDescriptor.constant 2*2^w) := by
  have ha : Placement.active powerPlace (states ws w 0)=FixedBasePowerDescriptor.input ws := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> first | rfl | exact CountedLoopReuseAlphabet.encoding_binary ws
  have h := Placement.hoare_at (FixedBasePowerDescriptor.constructs_linear 2 w (by decide) ws hw cw)
    powerPlace (states ws w 0) ha
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> first | rfl | exact (CountedLoopReuseAlphabet.encoding_binary ws).symm

theorem fill_hoare (ws : List Bool) (w : ℕ) (hw : Counter.value ws=w) :
    HoareTime fill (fun z => z=states ws w 1) (fun z => z=states ws w 2)
      (8*w+7*ws.length+39) := by
  have ha : Placement.active fillPlace (states ws w 1)=BinaryAddressTableFill.input ws := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have h := Placement.hoare_at (BinaryAddressTableFill.runs ws w hw) fillPlace (states ws w 1) ha
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem clock_hoare (ws : List Bool) (w : ℕ) :
    HoareTime clockInit (fun z => z=states ws w 2) (fun z => z=states ws w 3) 6 := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := 0) 0)
    (FiniteReturnStackAt.placement (2 : Fin 9)) (states ws w 2) (by
      rw [FiniteReturnStackAt.active_bank]; rfl)
  apply h.consequence (fun _ h => h) _ (by decide)
  rintro z ⟨small,rfl,rfl⟩
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def tail (ws : List Bool) : Tapes 5 0 :=
  ⟨![0,1,0,0,0],![(fun _ => blank),binary ws,(fun _ => blank),(fun _ => blank),(fun _ => blank)]⟩

theorem loop_hoare (ws : List Bool) (w : ℕ) :
    HoareTime loop (fun z => z=states ws w 3) (fun z => z=states ws w 4)
      (2^w*(4*w+7)+6*2^w+7*(countBits w).length+16) := by
  have h := CountedLoopReuse.loop_hoare BinaryAddressTableStep.program (countBits w) (2^w)
    (fun i => BinaryAddressTableStep.state w i (fun _ => blank) 0) (fun _ => 4*w+7)
    (FixedBasePowerDescriptor.result_value 2 w)
    (fun i _ => BinaryAddressTableStep.step w i (fun _ => blank) 0)
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at h
  have hh := hoare_extend_eq h (tail ws)
  have he0 : (CountedLoopReuse.bank (BinaryAddressTableStep.state w 0 (fun _ => blank) 0)
      empty (binary (countBits w)) 1 1).append (tail ws)=states ws w 3 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> first | rfl | (change (0 : ℤ)+(0*w : ℕ)=0; simp)
  have he1 : (CountedLoopReuse.bank (BinaryAddressTableStep.state w (2^w) (fun _ => blank) 0)
      empty (binary (countBits w)) 1 1).append (tail ws)=states ws w 4 := by
    unfold BinaryAddressTableStep.state
    rw [row_wrap]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> first | rfl | (change (0 : ℤ)+(2^w*w : ℕ)=2^w*w; simp)
  rw [he0,he1] at hh
  exact hh

theorem counter_clean (ws : List Bool) (w : ℕ) :
    HoareTime clearCounter (fun z => z=states ws w 4) (fun z => z=states ws w 5) (2*w+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare (0 : Fin 9) (states ws w 4)
    (List.replicate w false) (by exact BinaryAddressTableStep.bits_word _ _ _) rfl
  have he : setTape (states ws w 4) 0 (fun _ => blank) 0=states ws w 5 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  simpa only [he,List.length_replicate,clearCounter] using h

theorem clock_clean (ws : List Bool) (w : ℕ) :
    HoareTime clearClock (fun z => z=states ws w 5) (fun z => z=states ws w 6) 4 := by
  have h := BinaryDescriptorCleanupList.one_hoare (2 : Fin 9) (states ws w 5) [] rfl rfl
  have he : setTape (states ws w 5) 2 (fun _ => blank) 0=states ws w 6 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  simpa only [he,List.length_nil,clearClock] using h

theorem count_clean (ws : List Bool) (w : ℕ) :
    HoareTime clearCount (fun z => z=states ws w 6) (fun z => z=states ws w 7)
      (2*(countBits w).length+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare (3 : Fin 9) (states ws w 6)
    (countBits w) (by exact BinaryAddressTableStep.bits_word _ _ _) rfl
  have he : setTape (states ws w 6) 3 (fun _ => blank) 0=states ws w 7 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  simpa only [he,clearCount] using h

theorem rewinds (ws : List Bool) (w : ℕ) :
    HoareTime rewind (fun z => z=states ws w 7) (fun z => z=states ws w 8) (2^w*w+2) := by
  have hr := ReturnOrigin.return_hoare_at (fun _ => (blank : Fin 4)) 0
    ((table w (2^w)).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl
  simp only [List.length_map,table_length,zero_add] at hr
  have ha : Placement.active (FiniteReturnStackAt.placement (1 : Fin 9)) (states ws w 7) =
      (StepRight.cfg (outputTape w) (2^w*w) 0).tapes := by
    rw [FiniteReturnStackAt.active_bank]; rfl
  have hh := Placement.hoare_at hr (FiniteReturnStackAt.placement (1 : Fin 9)) (states ws w 7) ha
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  change Placement.replace (FiniteReturnStackAt.placement (1 : Fin 9)) (states ws w 7)
    (FiniteReturnStack.bank (outputTape w) 0) = _
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def exactCost (ws : List Bool) (w : ℕ) :=
  FixedBasePowerDescriptor.constant 2*2^w+(8*w+7*ws.length+39)+6+
    (2^w*(4*w+7)+6*2^w+7*(countBits w).length+16)+(2*w+4)+4+
    (2*(countBits w).length+4)+(2^w*w+2)+7

theorem runs (ws : List Bool) (w : ℕ) (hw : Counter.value ws=w)
    (cw : GrowingCounterData.Canonical ws) :
    HoareTime program (fun z => z=input ws) (fun z => z=states ws w 8) (exactCost ws w) := by
  have h1 := (power_hoare ws w hw cw).seq (fill_hoare ws w hw)
  have h2 := h1.seq (clock_hoare ws w)
  have h3 := h2.seq (loop_hoare ws w)
  have h4 := h3.seq (counter_clean ws w)
  have h5 := h4.seq (clock_clean ws w)
  have h6 := h5.seq (count_clean ws w)
  have h7 := h6.seq (rewinds ws w)
  apply h7.consequence (fun _ h => h) (fun _ h => h) _
  unfold exactCost
  omega

/-- One fixed constant bounds every actual transition, including empty-width
initialization and cleanup. -/
def constant : ℕ := FixedBasePowerDescriptor.constant 2+150

theorem cost_bound (ws : List Bool) (w : ℕ) (hw : Counter.value ws=w)
    (cw : GrowingCounterData.Canonical ws) : exactCost ws w ≤ constant*((w+1)*2^w) := by
  have hn : 1 ≤ 2^w := Nat.one_le_pow _ _ (by decide)
  have hd := FixedBasePowerDescriptor.depth_le_power 2 w (by decide)
  have hws := GrowingCounterData.canonical_width ws cw
  rw [hw] at hws
  have hwlog := Nat.log2_le_self w
  have hns := GrowingCounterData.canonical_width (countBits w)
    (FixedBasePowerDescriptor.result_canonical 2 w)
  rw [show Counter.value (countBits w)=2^w from FixedBasePowerDescriptor.result_value 2 w] at hns
  have hnlog := Nat.log2_le_self (2^w)
  have hv : 2^w ≤ (w+1)*2^w := Nat.le_mul_of_pos_left _ (by omega)
  have hC := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) hv
  have hmul : w*2^w ≤ (w+1)*2^w := Nat.mul_le_mul_right _ (by omega)
  unfold exactCost constant
  nlinarith

/-- The only prepared input is canonical w at tape5. Tape1 is the literal
concatenation of all width-w words in increasing rank, restored to head zero;
the original descriptor is retained and every other tape is blank at zero. -/
theorem constructs (ws : List Bool) (w : ℕ) (hw : Counter.value ws=w)
    (cw : GrowingCounterData.Canonical ws) :
    HoareTime program (fun z => z=input ws)
      (fun z => z=bank (fun _ => blank) (outputTape w) (fun _ => blank) (fun _ => blank) 0 0 0 0 ws)
      (constant*((w+1)*2^w)) :=
  (runs ws w hw cw).consequence (fun _ h => h) (fun _ h => h) (cost_bound ws w hw cw)

/-- Charging address generation to payload is conditional on actual record
width. The table alone is not a constant-cost or free-address primitive. -/
theorem cost_volume (w R : ℕ) (hR : w+1 ≤ R) :
    constant*((w+1)*2^w) ≤ constant*(2^w*R) := by
  apply Nat.mul_le_mul_left
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_right (2^w) hR

end
end IntegerMultBounds.Machine.BinaryAddressTable
