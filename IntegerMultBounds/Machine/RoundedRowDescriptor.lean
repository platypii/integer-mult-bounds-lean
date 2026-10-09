import IntegerMultBounds.Machine.RowPaddingSpanCounts
import IntegerMultBounds.Machine.BinaryDescriptorDivision
import IntegerMultBounds.Machine.RecursiveChildQuotientsConstant
import IntegerMultBounds.Machine.RecursiveDescriptorDivision

/-! A physical constructor for the least positive multiple of D above or equal
to a positive R. Only R and D are supplied; one, R-1, the quotient, all markers,
and the rounded result are actually written. All private tapes finish blank. -/
namespace IntegerMultBounds.Machine.RoundedRowDescriptor
variable {q : ℕ}
noncomputable section

def rounded (R D : ℕ) : ℕ := ((R-1)/D+1)*D

theorem rounded_pos (R D : ℕ) (hD : 0 < D) : 0 < rounded R D := by
  unfold rounded
  exact Nat.mul_pos (Nat.succ_pos _) hD

theorem divisor_le (R D : ℕ) : D ≤ rounded R D := by
  unfold rounded
  generalize (R-1)/D = Q at *
  nlinarith

theorem rows_le (R D : ℕ) (hR : 0 < R) (hD : 0 < D) : R ≤ rounded R D := by
  have hm := Nat.mod_lt (R-1) hD
  have he := Nat.mod_add_div (R-1) D
  have hr : R-1+1 = R := by omega
  unfold rounded
  generalize (R-1)/D = Q at *
  nlinarith

theorem rounded_lt (R D : ℕ) (hR : 0 < R) : rounded R D < R+D := by
  unfold rounded
  rw [Nat.add_mul,Nat.one_mul]
  exact lt_of_le_of_lt (Nat.add_le_add_right (Nat.div_mul_le_self (R-1) D) D)
    (Nat.add_lt_add_right (by omega) D)

theorem rounded_lt_twice (R D : ℕ) (hR : 0 < R) (hD : D ≤ R) : rounded R D < 2*R := by
  have h := rounded_lt R D hR
  omega

theorem rounded_eq_ceiling (R D : ℕ) (hR : 0 < R) (hD : 0 < D) :
    rounded R D = D*((R+D-1)/D) := by
  rw [show R+D-1 = (R-1)+D by omega,Nat.add_div_right _ hD]
  exact Nat.mul_comm _ _

theorem rounded_dvd (R D : ℕ) : D ∣ rounded R D := by
  exact dvd_mul_left _ _

theorem rounded_le_multiple (R D n : ℕ) (hR : 0 < R) (hn : R ≤ n*D) : rounded R D ≤ n*D := by
  by_cases hd : D = 0
  · simp [rounded,hd]
  · have hquot : (R-1)/D < n := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
    exact Nat.mul_le_mul_right D (by omega)

private def hd : Option (List Bool) → ℤ
  | none => 0
  | some _ => 1
private def tp : Option (List Bool) → ℤ → Fin (q+4)
  | none => fun _ => blank
  | some xs => RadixZeroFill.encodedBinary xs

/-- Input R and D, temporary one/decrement/quotient, rounded output, nine
scratch tapes. All present descriptors have their head on their first bit. -/
def bank (rs ds : List Bool) (one dec quot out : Option (List Bool)) : Tapes 15 q :=
  ⟨![1,1,hd one,hd dec,hd quot,hd out,0,0,0,0,0,0,0,0,0],
   ![RadixZeroFill.encodedBinary rs,RadixZeroFill.encodedBinary ds,tp one,tp dec,tp quot,tp out,
     fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,
     fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank]⟩

def input (rs ds : List Bool) : Tapes 15 q := bank rs ds none none none none

def bits (R D : ℕ) : List Bool := BoundedProductDescriptor.bits ((R-1)/D+1) D

def output (rs ds : List Bool) (R D : ℕ) : Tapes 15 q := bank rs ds none none none (some (bits R D))

private def oneBits := RecursiveChildQuotientsConstant.bits 1
private def decBits (rs : List Bool) := BinarySubReuse.difference rs oneBits
private def incBits := GrowingCounterData.increment

def subPlacement : Fin (3+12) ≃ Fin 15 where
  toFun := ![0,2,3,1,4,5,6,7,8,9,10,11,12,13,14]
  invFun := ![0,3,1,2,4,5,6,7,8,9,10,11,12,13,14]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def divPlacement : Fin (12+3) ≃ Fin 15 where
  toFun := ![3,1,6,7,8,4,9,10,11,12,13,14,0,2,5]
  invFun := ![12,1,13,0,5,14,2,3,4,6,7,8,9,10,11]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def mulPlacement : Fin (6+9) ≃ Fin 15 where
  toFun := ![6,5,7,1,8,4,0,2,3,9,10,11,12,13,14]
  invFun := ![6,3,7,8,5,1,0,2,4,9,10,11,12,13,14]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def initProgram := Placement.placed (RecursiveChildQuotientsConstant.program (a := q) 1)
  (FiniteReturnStackAt.placement (2 : Fin 15))
def subProgram := Placement.placed
  (Alphabet.program (RadixToBinary.binaryEncoding (q := q)) BinarySubReuse.program) subPlacement
def divProgram := Placement.placed (BinaryDescriptorDivision.program q) divPlacement
def incProgram := Placement.placed
  (Alphabet.program (RadixToBinary.binaryEncoding (q := q)) GrowingCounter.program)
  (FiniteReturnStackAt.placement (4 : Fin 15))
def mulProgram := Placement.placed (BoundedProductDescriptor.program (q := q)) mulPlacement
private def cleanSlots : List (Fin 15) := [2,3,4]
def cleanProgram := BinaryDescriptorCleanupList.program (a := q) (by decide : 0 < 15) cleanSlots

/-- Finite control is independent of R and D. -/
def program := seq (seq (seq (seq (seq (initProgram (q := q)) subProgram) divProgram) incProgram) mulProgram) cleanProgram

private theorem placed_exact {s u t r cost : ℕ} {M : Program s r q}
    (e : Fin (s+u) ≃ Fin t) (v w : Tapes t q) (small small' : Tapes s q)
    (ha : Placement.active e v = small) (hf : Placement.active e w = small')
    (he : Placement.extra e v = Placement.extra e w)
    (hh : HoareTime M (fun x => x = small) (fun x => x = small') cost) :
    HoareTime (Placement.placed M e) (fun x => x = v) (fun x => x = w) cost := by
  apply (Placement.hoare_at hh e v ha).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨y,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

private theorem init_hoare (rs ds : List Bool) :
    HoareTime (initProgram (q := q)) (fun v => v = input rs ds)
      (fun v => v = bank rs ds (some oneBits) none none none) 9 := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := q) 1)
    (FiniteReturnStackAt.placement (2 : Fin 15)) (input rs ds)
    (by rw [FiniteReturnStackAt.active_bank]; rfl)
  apply h.consequence (fun _ h => h) _ (by decide)
  rintro v ⟨z,rfl,rfl⟩
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [input,bank,hd,tp,
      BinaryDescriptorStackRoundtrip.descriptor_encoded,oneBits]

private theorem sub_hoare (rs ds : List Bool) :
    HoareTime (subProgram (q := q))
      (fun v => v = bank rs ds (some oneBits) none none none)
      (fun v => v = bank rs ds (some oneBits) (some (decBits rs)) none none)
      (4*BinarySubReuse.width rs oneBits+14) := by
  have h := Alphabet.map_hoare (RadixToBinary.binaryEncoding (q := q))
    (BinarySubReuse.sub_hoare rs oneBits)
  have hh : HoareTime (Alphabet.program (RadixToBinary.binaryEncoding (q := q)) BinarySubReuse.program)
      (fun v => v = Alphabet.mapTapes RadixToBinary.binaryEncoding
        (BinarySubReuse.bank rs oneBits (fun _ => blank) 1 1 0))
      (fun v => v = Alphabet.mapTapes RadixToBinary.binaryEncoding
        (BinarySubReuse.bank rs oneBits (CountedCopyReuse.binary (decBits rs)) 1 1 1))
      (4*BinarySubReuse.width rs oneBits+14) :=
    h.consequence (fun _ h => ⟨_,rfl,h⟩) (by rintro v ⟨w,rfl,h⟩; exact h) le_rfl
  apply placed_exact subPlacement _ _ _ _ _ _ _ hh
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem div_hoare (rs ds zs : List Bool)
    (hdiv : HoareTime (BinaryDescriptorDivision.program q)
      (fun v => v = BinaryDescriptorDivision.input (decBits rs) ds)
      (fun v => v = BinaryDescriptorDivision.output (decBits rs) ds zs)
      (BinaryDescriptorDivision.cost (decBits rs) ds)) :
    HoareTime (divProgram (q := q))
      (fun v => v = bank rs ds (some oneBits) (some (decBits rs)) none none)
      (fun v => v = bank rs ds (some oneBits) (some (decBits rs)) (some zs) none)
      (BinaryDescriptorDivision.cost (decBits rs) ds) := by
  apply placed_exact divPlacement _ _ _ _ _ _ _ hdiv
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    first | rfl | exact BinaryDescriptorStackRoundtrip.descriptor_encoded _ | exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm

private theorem inc_hoare (rs ds zs : List Bool) :
    HoareTime (incProgram (q := q))
      (fun v => v = bank rs ds (some oneBits) (some (decBits rs)) (some zs) none)
      (fun v => v = bank rs ds (some oneBits) (some (decBits rs)) (some (incBits zs)) none)
      (2*GrowingCounterData.carrySteps zs) := by
  have h := Alphabet.map_hoare (RadixToBinary.binaryEncoding (q := q))
    (GrowingCounter.increment_hoare CountedCopyReuse.empty zs rfl
      (by simp [CountedCopyReuse.empty,show (1 : ℤ)+zs.length ≠ 0 by omega]))
  have hh : HoareTime (Alphabet.program (RadixToBinary.binaryEncoding (q := q)) GrowingCounter.program)
      (fun v => v = FiniteReturnStack.bank (RadixZeroFill.encodedBinary zs) 1)
      (fun v => v = FiniteReturnStack.bank (RadixZeroFill.encodedBinary (incBits zs)) 1)
      (2*GrowingCounterData.carrySteps zs) :=
    h.consequence (fun _ h => ⟨_,rfl,h⟩) (by rintro v ⟨w,rfl,h⟩; exact h) le_rfl
  have hi := Placement.hoare_at hh (FiniteReturnStackAt.placement (4 : Fin 15))
    (bank rs ds (some oneBits) (some (decBits rs)) (some zs) none)
    (by rw [FiniteReturnStackAt.active_bank]; rfl)
  apply hi.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem mul_input (rs ds one dec zs : List Bool) :
    Placement.active mulPlacement (bank (q := q) rs ds (some one) (some dec) (some zs) none) =
      BoundedProductDescriptor.input ds zs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem mul_output (rs ds one dec zs : List Bool) (N D : ℕ) :
    Placement.active mulPlacement
      (bank (q := q) rs ds (some one) (some dec) (some zs) (some (BoundedProductDescriptor.bits N D))) =
      BoundedProductDescriptor.output ds zs N D := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem mul_extra (rs ds one dec zs bs : List Bool) :
    Placement.extra mulPlacement (bank (q := q) rs ds (some one) (some dec) (some zs) none) =
      Placement.extra mulPlacement (bank rs ds (some one) (some dec) (some zs) (some bs)) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [mulPlacement,bank]

private theorem mul_hoare (rs ds zs : List Bool) (R D : ℕ)
    (hd : Counter.value ds = D) (hz : Counter.value zs = (R-1)/D)
    (cd : GrowingCounterData.Canonical ds) (cz : GrowingCounterData.Canonical zs)
    (hD : 0 < D) :
    HoareTime (mulProgram (q := q))
      (fun v => v = bank rs ds (some oneBits) (some (decBits rs)) (some (incBits zs)) none)
      (fun v => v = bank rs ds (some oneBits) (some (decBits rs)) (some (incBits zs)) (some (bits R D)))
      (53*rounded R D+28) := by
  have hv : Counter.value (incBits zs) = (R-1)/D+1 := by
    rw [incBits,GrowingCounterData.increment_value,hz]
  have wi := GrowingCounterData.canonical_width (incBits zs) (GrowingCounterData.increment_canonical zs cz)
  have wd := GrowingCounterData.canonical_width ds cd
  have li := Nat.log2_le_self (Counter.value (incBits zs))
  have ld := Nat.log2_le_self (Counter.value ds)
  rw [hv] at wi li
  rw [hd] at wd ld
  apply placed_exact mulPlacement _ _ _ _ (mul_input _ _ _ _ _) (mul_output _ _ _ _ _ _ _) (mul_extra _ _ _ _ _ _)
    (BoundedProductDescriptor.construct_hoare ds (incBits zs) ((R-1)/D+1) D ((R-1)/D+1)
      hD hd hv le_rfl (by omega) (by omega))

private theorem clean_hoare (rs ds zs : List Bool) (R D : ℕ) :
    HoareTime (cleanProgram (q := q))
      (fun v => v = bank rs ds (some oneBits) (some (decBits rs)) (some (incBits zs)) (some (bits R D)))
      (fun v => v = output rs ds R D)
      (2*(decBits rs).length+2*(incBits zs).length+17) := by
  let words : Fin 15 → List Bool := fun i => if i = 2 then oneBits else if i = 3 then decBits rs else incBits zs
  have h := BinaryDescriptorCleanupList.cleanup_hoare (by decide : 0 < 15) cleanSlots (by decide)
    words (bank (q := q) rs ds (some oneBits) (some (decBits rs)) (some (incBits zs)) (some (bits R D))) (by
      intro i hi
      simp only [cleanSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl <;> constructor <;>
        first | rfl | simpa [words,bank,tp] using (BinaryDescriptorStackRoundtrip.descriptor_encoded (a := q) _).symm)
  apply h.consequence (fun _ h => h) _ _
  · rintro v rfl
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · simp [BinaryDescriptorCleanupList.cost,cleanSlots,words,oneBits,
      RecursiveChildQuotientsConstant.bits,GrowingCounterData.advance,GrowingCounterData.increment]
    omega

/-- Word-sensitive construction, before converting binary lengths to a uniform
linear rounded-row budget. No quotient or auxiliary descriptor is assumed. -/
theorem construct_words (rs ds : List Bool) (R D : ℕ)
    (hr : Counter.value rs = R) (hd : Counter.value ds = D)
    (cd : GrowingCounterData.Canonical ds) (hR : 0 < R) (hD : 0 < D) :
    ∃ zs : List Bool, GrowingCounterData.Canonical zs ∧ Counter.value zs = (R-1)/D ∧
      zs.length ≤ (decBits rs).length ∧
      HoareTime (program (q := q)) (fun v => v = input rs ds)
        (fun v => v = output rs ds R D)
        (BinaryDescriptorDivision.cost (decBits rs) ds+53*rounded R D+
          6*(decBits rs).length+2*GrowingCounterData.carrySteps zs+2*(incBits zs).length+83) := by
  have hv : Counter.value (decBits rs) = R-1 := by
    rw [decBits,BinarySubReuse.difference_value _ _ (by
      rw [hr,show Counter.value oneBits = 1 from RecursiveChildQuotientsConstant.bits_value 1]; omega),hr]
    rw [show Counter.value oneBits = 1 from RecursiveChildQuotientsConstant.bits_value 1]
  obtain ⟨zs,cz,hz,wz,hdiv⟩ := BinaryDescriptorDivision.divide_hoare (a := q) (decBits rs) ds (by omega)
  rw [hv,hd] at hz
  have h := (((((init_hoare (q := q) rs ds).seq (sub_hoare rs ds)).seq (div_hoare rs ds zs hdiv)).seq
    (inc_hoare rs ds zs)).seq (mul_hoare rs ds zs R D hd hz cd cz hD)).seq (clean_hoare rs ds zs R D)
  refine ⟨zs,cz,hz,wz,h.consequence (fun _ h => h) (fun _ h => h) ?_⟩
  have hw : (decBits rs).length = BinarySubReuse.width rs oneBits := BinarySubReuse.difference_length _ _
  omega

private theorem division_bound (ys ds : List Bool) (V : ℕ) (hV : 0 < V)
    (hy : ys.length ≤ Nat.log2 V+1) (hd : ds.length ≤ Nat.log2 V+1) :
    BinaryDescriptorDivision.cost ys ds ≤ 3910*V := by
  have h := BinaryDescriptorDivision.cost_le ys ds
  have hs := RecursiveDescriptorDivision.square_log_le V hV
  have hl : Nat.log2 V+1 ≤ 2*V := by have := Nat.log2_le_self V; omega
  have hsq : ys.length^2 ≤ (Nat.log2 V+1)^2 := Nat.pow_le_pow_left hy 2
  have hprod : ys.length*ds.length ≤ (Nat.log2 V+1)^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hy hd
  nlinarith

/-- The complete fixed program constructs the least enclosing multiple from
canonical R,D, preserving both inputs and physically cleaning every temporary.
The runtime has one explicit constant independent of both input values. -/
theorem construct_hoare (rs ds : List Bool) (R D : ℕ)
    (hr : Counter.value rs = R) (hd : Counter.value ds = D)
    (cr : GrowingCounterData.Canonical rs) (cd : GrowingCounterData.Canonical ds)
    (hR : 0 < R) (hD : 0 < D) :
    HoareTime (program (q := q)) (fun v => v = input rs ds)
      (fun v => v = output rs ds R D) (4096*rounded R D) := by
  obtain ⟨zs,cz,hz,wz,h⟩ := construct_words (q := q) rs ds R D hr hd cd hR hD
  have hV := rounded_pos R D hD
  have hRV := rows_le R D hR hD
  have hDV := divisor_le R D
  have wr := GrowingCounterData.canonical_width rs cr
  have wd := GrowingCounterData.canonical_width ds cd
  rw [hr] at wr
  rw [hd] at wd
  have lr : Nat.log2 R ≤ Nat.log2 (rounded R D) := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right (b := 2) hRV
  have ld : Nat.log2 D ≤ Nat.log2 (rounded R D) := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right (b := 2) hDV
  have ww : (decBits rs).length ≤ Nat.log2 (rounded R D)+1 := by
    rw [decBits,BinarySubReuse.difference_length]
    have hone : oneBits.length = 1 := rfl
    rw [hone]
    omega
  have hdiv := division_bound (decBits rs) ds (rounded R D) hV ww (by omega)
  have hc := (GrowingCounterData.carrySteps_bounds zs).2
  have hi := (GrowingCounterData.increment_length zs).2
  have hlog := Nat.log2_le_self (rounded R D)
  apply h.consequence (fun _ h => h) (fun _ h => h) _
  dsimp only [incBits]
  omega

theorem bits_value (R D : ℕ) : Counter.value (bits R D) = rounded R D :=
  BoundedProductDescriptor.bits_value _ _

theorem bits_canonical (R D : ℕ) : GrowingCounterData.Canonical (bits R D) :=
  BoundedProductDescriptor.bits_canonical _ _

theorem ready (rs ds : List Bool) (R D : ℕ) :
    (output (q := q) rs ds R D).head 5 = 1 ∧
    (output (q := q) rs ds R D).tape 5 = RadixZeroFill.encodedBinary (bits R D) := ⟨rfl,rfl⟩

end
end IntegerMultBounds.Machine.RoundedRowDescriptor
