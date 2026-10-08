import IntegerMultBounds.Machine.RecursiveDimensionBank
import IntegerMultBounds.Machine.RadixPowerMultipleDescriptor
import IntegerMultBounds.Machine.ExactFrame

/-! Physical child dimensions from six parent headers and two explicit canonical
quotient headers. Quotient production is a separate operation. No derived power
or spectator product is supplied; all eight outputs start blank. -/
namespace IntegerMultBounds.Machine.RecursiveChildDimensions
open RecursiveInterchangeLayout (Descriptor child volume)
variable {q : ℕ} (hq : 2 ≤ q)

/-- Scratch0..2, parent headers3..8, quotient width9/rows10, outputs11..18. -/
def bank (hs : Fin 6 → List Bool) (bs rs : List Bool) (ds : Fin 8 → Option (List Bool)) : Tapes 19 q :=
  ⟨![0,0,0,1,1,1,1,1,1,1,1,
      RecursiveDimensionBank.head (ds 0),RecursiveDimensionBank.head (ds 1),
      RecursiveDimensionBank.head (ds 2),RecursiveDimensionBank.head (ds 3),
      RecursiveDimensionBank.head (ds 4),RecursiveDimensionBank.head (ds 5),
      RecursiveDimensionBank.head (ds 6),RecursiveDimensionBank.head (ds 7)],
   ![fun _ => blank,fun _ => blank,fun _ => blank,
      RadixZeroFill.encodedBinary (hs 0),RadixZeroFill.encodedBinary (hs 1),
      RadixZeroFill.encodedBinary (hs 2),RadixZeroFill.encodedBinary (hs 3),
      RadixZeroFill.encodedBinary (hs 4),RadixZeroFill.encodedBinary (hs 5),
      RadixZeroFill.encodedBinary bs,RadixZeroFill.encodedBinary rs,
      RecursiveDimensionBank.tape (ds 0),RecursiveDimensionBank.tape (ds 1),
      RecursiveDimensionBank.tape (ds 2),RecursiveDimensionBank.tape (ds 3),
      RecursiveDimensionBank.tape (ds 4),RecursiveDimensionBank.tape (ds 5),
      RecursiveDimensionBank.tape (ds 6),RecursiveDimensionBank.tape (ds 7)]⟩

def prefixBits (k b : ℕ) := RadixPowerMultipleDescriptor.bits hq (k*b)
def beforeBits (v : Descriptor) (k b : ℕ) := DimensionProductDescriptor.bits v.beforeH (q^(k*b))
def middleBits (v : Descriptor) (k b : ℕ) := DimensionProductDescriptor.bits (q^(k*b)) v.between
def betweenBits (v : Descriptor) (k l b : ℕ) := DimensionProductDescriptor.bits (q^(k*b)*v.between) (q^(l*b))
def afterBits (v : Descriptor) (k b : ℕ) := DimensionProductDescriptor.bits (q^(k*b)) v.afterD

def ds0 : Fin 8 → Option (List Bool) := ![none,none,none,none,none,none,none,none]

def ds1 (_v : Descriptor) (b : ℕ) {m : ℕ} (i : Fin m) (_j : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (prefixBits hq i.val b),none,none,none,none,none,none,none]

def ds2 (_v : Descriptor) (b : ℕ) {m : ℕ} (i : Fin m) (_j : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (prefixBits hq i.val b),some (prefixBits hq (m-1-i.val) b),none,none,none,none,none,none]

def ds3 (_v : Descriptor) (b : ℕ) {m : ℕ} (i j : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (prefixBits hq i.val b),some (prefixBits hq (m-1-i.val) b),some (prefixBits hq j.val b),none,none,none,none,none]

def ds4 (_v : Descriptor) (b : ℕ) {m : ℕ} (i j : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (prefixBits hq i.val b),some (prefixBits hq (m-1-i.val) b),some (prefixBits hq j.val b),some (prefixBits hq (m-1-j.val) b),none,none,none,none]

def ds5 (v : Descriptor) (b : ℕ) {m : ℕ} (i j : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (prefixBits hq i.val b),some (prefixBits hq (m-1-i.val) b),some (prefixBits hq j.val b),some (prefixBits hq (m-1-j.val) b),some (beforeBits (q := q) v i.val b),none,none,none]

def ds6 (v : Descriptor) (b : ℕ) {m : ℕ} (i j : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (prefixBits hq i.val b),some (prefixBits hq (m-1-i.val) b),some (prefixBits hq j.val b),some (prefixBits hq (m-1-j.val) b),some (beforeBits (q := q) v i.val b),some (middleBits (q := q) v (m-1-i.val) b),none,none]

def ds7 (v : Descriptor) (b : ℕ) {m : ℕ} (i j : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (prefixBits hq i.val b),some (prefixBits hq (m-1-i.val) b),some (prefixBits hq j.val b),some (prefixBits hq (m-1-j.val) b),some (beforeBits (q := q) v i.val b),some (middleBits (q := q) v (m-1-i.val) b),some (betweenBits (q := q) v (m-1-i.val) j.val b),none]

def ds8 (v : Descriptor) (b : ℕ) {m : ℕ} (i j : Fin m) : Fin 8 → Option (List Bool) :=
  ![some (prefixBits hq i.val b),some (prefixBits hq (m-1-i.val) b),some (prefixBits hq j.val b),some (prefixBits hq (m-1-j.val) b),some (beforeBits (q := q) v i.val b),some (middleBits (q := q) v (m-1-i.val) b),some (betweenBits (q := q) v (m-1-i.val) j.val b),some (afterBits (q := q) v (m-1-j.val) b)]

private theorem placed_exact {t u n r a cost : ℕ} {M : Program t r a}
    (e : Fin (t+u) ≃ Fin n) (v w : Tapes n a) (small small' : Tapes t a)
    (ha : Placement.active e v = small) (hf : Placement.active e w = small')
    (he : Placement.extra e v = Placement.extra e w)
    (hh : HoareTime M (fun x => x = small) (fun x => x = small') cost) :
    HoareTime (Placement.placed M e) (fun x => x = v) (fun x => x = w) cost := by
  apply (Placement.hoare_at hh e v ha).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨y,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

def placement1 : Fin (4+15) ≃ Fin 19 where
  toFun := ![0,1,9,11,2,3,4,5,6,7,8,10,12,13,14,15,16,17,18]
  invFun := ![0,1,4,5,6,7,8,9,10,2,11,3,12,13,14,15,16,17,18]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def program1 (k : ℕ) := Placement.placed (RadixPowerMultipleDescriptor.program hq k) placement1

private theorem frame1 (hs : Fin 6 → List Bool) (bs rs : List Bool) (xs : Fin 8 → List Bool) :
    Placement.extra placement1 (bank (q := q) hs bs rs ![none,none,none,none,none,none,none,none]) =
      Placement.extra placement1 (bank (q := q) hs bs rs ![some (xs 0),none,none,none,none,none,none,none]) := by
  unfold Placement.extra placement1 bank
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,Matrix.cons_val,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;>
    norm_num

def placement2 : Fin (4+15) ≃ Fin 19 where
  toFun := ![0,1,9,12,2,3,4,5,6,7,8,10,11,13,14,15,16,17,18]
  invFun := ![0,1,4,5,6,7,8,9,10,2,11,12,3,13,14,15,16,17,18]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def program2 (k : ℕ) := Placement.placed (RadixPowerMultipleDescriptor.program hq k) placement2

private theorem frame2 (hs : Fin 6 → List Bool) (bs rs : List Bool) (xs : Fin 8 → List Bool) :
    Placement.extra placement2 (bank (q := q) hs bs rs ![some (xs 0),none,none,none,none,none,none,none]) =
      Placement.extra placement2 (bank (q := q) hs bs rs ![some (xs 0),some (xs 1),none,none,none,none,none,none]) := by
  unfold Placement.extra placement2 bank
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,Matrix.cons_val,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;>
    norm_num

def placement3 : Fin (4+15) ≃ Fin 19 where
  toFun := ![0,1,9,13,2,3,4,5,6,7,8,10,11,12,14,15,16,17,18]
  invFun := ![0,1,4,5,6,7,8,9,10,2,11,12,13,3,14,15,16,17,18]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def program3 (k : ℕ) := Placement.placed (RadixPowerMultipleDescriptor.program hq k) placement3

private theorem frame3 (hs : Fin 6 → List Bool) (bs rs : List Bool) (xs : Fin 8 → List Bool) :
    Placement.extra placement3 (bank (q := q) hs bs rs ![some (xs 0),some (xs 1),none,none,none,none,none,none]) =
      Placement.extra placement3 (bank (q := q) hs bs rs ![some (xs 0),some (xs 1),some (xs 2),none,none,none,none,none]) := by
  unfold Placement.extra placement3 bank
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,Matrix.cons_val,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;>
    norm_num

def placement4 : Fin (4+15) ≃ Fin 19 where
  toFun := ![0,1,9,14,2,3,4,5,6,7,8,10,11,12,13,15,16,17,18]
  invFun := ![0,1,4,5,6,7,8,9,10,2,11,12,13,14,3,15,16,17,18]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def program4 (k : ℕ) := Placement.placed (RadixPowerMultipleDescriptor.program hq k) placement4

private theorem frame4 (hs : Fin 6 → List Bool) (bs rs : List Bool) (xs : Fin 8 → List Bool) :
    Placement.extra placement4 (bank (q := q) hs bs rs ![some (xs 0),some (xs 1),some (xs 2),none,none,none,none,none]) =
      Placement.extra placement4 (bank (q := q) hs bs rs ![some (xs 0),some (xs 1),some (xs 2),some (xs 3),none,none,none,none]) := by
  unfold Placement.extra placement4 bank
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,Matrix.cons_val,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;>
    norm_num

def placement5 : Fin (6+13) ≃ Fin 19 where
  toFun := ![0,15,1,11,2,5,3,4,6,7,8,9,10,12,13,14,16,17,18]
  invFun := ![0,2,4,6,7,5,8,9,10,11,12,3,13,14,15,1,16,17,18]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def program5 : Program 19 40 q := Placement.placed DimensionProductDescriptor.program placement5

private theorem frame5 (hs : Fin 6 → List Bool) (bs rs : List Bool) (xs : Fin 8 → List Bool) :
    Placement.extra placement5 (bank (q := q) hs bs rs ![some (xs 0),some (xs 1),some (xs 2),some (xs 3),none,none,none,none]) =
      Placement.extra placement5 (bank (q := q) hs bs rs ![some (xs 0),some (xs 1),some (xs 2),some (xs 3),some (xs 4),none,none,none]) := by
  unfold Placement.extra placement5 bank
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,Matrix.cons_val,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;>
    norm_num

def placement6 : Fin (6+13) ≃ Fin 19 where
  toFun := ![0,16,1,7,2,12,3,4,5,6,8,9,10,11,13,14,15,17,18]
  invFun := ![0,2,4,6,7,8,9,3,10,11,12,13,5,14,15,16,1,17,18]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def program6 : Program 19 40 q := Placement.placed DimensionProductDescriptor.program placement6

private theorem frame6 (hs : Fin 6 → List Bool) (bs rs : List Bool) (xs : Fin 8 → List Bool) :
    Placement.extra placement6 (bank (q := q) hs bs rs ![some (xs 0),some (xs 1),some (xs 2),some (xs 3),some (xs 4),none,none,none]) =
      Placement.extra placement6 (bank (q := q) hs bs rs ![some (xs 0),some (xs 1),some (xs 2),some (xs 3),some (xs 4),some (xs 5),none,none]) := by
  unfold Placement.extra placement6 bank
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,Matrix.cons_val,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;>
    norm_num

def placement7 : Fin (6+13) ≃ Fin 19 where
  toFun := ![0,17,1,13,2,16,3,4,5,6,7,8,9,10,11,12,14,15,18]
  invFun := ![0,2,4,6,7,8,9,10,11,12,13,14,15,3,16,17,5,1,18]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def program7 : Program 19 40 q := Placement.placed DimensionProductDescriptor.program placement7

private theorem frame7 (hs : Fin 6 → List Bool) (bs rs : List Bool) (xs : Fin 8 → List Bool) :
    Placement.extra placement7 (bank (q := q) hs bs rs ![some (xs 0),some (xs 1),some (xs 2),some (xs 3),some (xs 4),some (xs 5),none,none]) =
      Placement.extra placement7 (bank (q := q) hs bs rs ![some (xs 0),some (xs 1),some (xs 2),some (xs 3),some (xs 4),some (xs 5),some (xs 6),none]) := by
  unfold Placement.extra placement7 bank
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,Matrix.cons_val,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;>
    norm_num

def placement8 : Fin (6+13) ≃ Fin 19 where
  toFun := ![0,18,1,8,2,14,3,4,5,6,7,9,10,11,12,13,15,16,17]
  invFun := ![0,2,4,6,7,8,9,10,3,11,12,13,14,15,5,16,17,18,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def program8 : Program 19 40 q := Placement.placed DimensionProductDescriptor.program placement8

private theorem frame8 (hs : Fin 6 → List Bool) (bs rs : List Bool) (xs : Fin 8 → List Bool) :
    Placement.extra placement8 (bank (q := q) hs bs rs ![some (xs 0),some (xs 1),some (xs 2),some (xs 3),some (xs 4),some (xs 5),some (xs 6),none]) =
      Placement.extra placement8 (bank (q := q) hs bs rs ![some (xs 0),some (xs 1),some (xs 2),some (xs 3),some (xs 4),some (xs 5),some (xs 6),some (xs 7)]) := by
  unfold Placement.extra placement8 bank
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,Matrix.cons_val,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;>
    norm_num

theorem stage1_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (i j : Fin m) (hb : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (program1 hq i.val) (fun w => w = bank hs bs rs (ds0))
      (fun w => w = bank hs bs rs (ds1 hq v b i j)) ((24*i.val+75)*q^(i.val*b)) := by
  have hh := RadixPowerMultipleDescriptor.construct_hoare_linear hq i.val bs b hb cb
  exact placed_exact placement1 _ _ _ _
    (by simp only [Placement.active,placement1,bank,ds0]
        apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (by simp only [Placement.active,placement1,bank,ds1]
        apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (frame1 hs bs rs ![prefixBits hq i.val b,prefixBits hq (m-1-i.val) b,prefixBits hq j.val b,prefixBits hq (m-1-j.val) b,beforeBits (q := q) v i.val b,middleBits (q := q) v (m-1-i.val) b,betweenBits (q := q) v (m-1-i.val) j.val b,afterBits (q := q) v (m-1-j.val) b]) hh

theorem stage2_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (i j : Fin m) (hb : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (program2 hq (m-1-i.val)) (fun w => w = bank hs bs rs (ds1 hq v b i j))
      (fun w => w = bank hs bs rs (ds2 hq v b i j)) ((24*(m-1-i.val)+75)*q^((m-1-i.val)*b)) := by
  have hh := RadixPowerMultipleDescriptor.construct_hoare_linear hq (m-1-i.val) bs b hb cb
  exact placed_exact placement2 _ _ _ _
    (by simp only [Placement.active,placement2,bank,ds1]
        apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (by simp only [Placement.active,placement2,bank,ds2]
        apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (frame2 hs bs rs ![prefixBits hq i.val b,prefixBits hq (m-1-i.val) b,prefixBits hq j.val b,prefixBits hq (m-1-j.val) b,beforeBits (q := q) v i.val b,middleBits (q := q) v (m-1-i.val) b,betweenBits (q := q) v (m-1-i.val) j.val b,afterBits (q := q) v (m-1-j.val) b]) hh

theorem stage3_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (i j : Fin m) (hb : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (program3 hq j.val) (fun w => w = bank hs bs rs (ds2 hq v b i j))
      (fun w => w = bank hs bs rs (ds3 hq v b i j)) ((24*j.val+75)*q^(j.val*b)) := by
  have hh := RadixPowerMultipleDescriptor.construct_hoare_linear hq j.val bs b hb cb
  exact placed_exact placement3 _ _ _ _
    (by simp only [Placement.active,placement3,bank,ds2]
        apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (by simp only [Placement.active,placement3,bank,ds3]
        apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (frame3 hs bs rs ![prefixBits hq i.val b,prefixBits hq (m-1-i.val) b,prefixBits hq j.val b,prefixBits hq (m-1-j.val) b,beforeBits (q := q) v i.val b,middleBits (q := q) v (m-1-i.val) b,betweenBits (q := q) v (m-1-i.val) j.val b,afterBits (q := q) v (m-1-j.val) b]) hh

theorem stage4_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (i j : Fin m) (hb : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (program4 hq (m-1-j.val)) (fun w => w = bank hs bs rs (ds3 hq v b i j))
      (fun w => w = bank hs bs rs (ds4 hq v b i j)) ((24*(m-1-j.val)+75)*q^((m-1-j.val)*b)) := by
  have hh := RadixPowerMultipleDescriptor.construct_hoare_linear hq (m-1-j.val) bs b hb cb
  exact placed_exact placement4 _ _ _ _
    (by simp only [Placement.active,placement4,bank,ds3]
        apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (by simp only [Placement.active,placement4,bank,ds4]
        apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (frame4 hs bs rs ![prefixBits hq i.val b,prefixBits hq (m-1-i.val) b,prefixBits hq j.val b,prefixBits hq (m-1-j.val) b,beforeBits (q := q) v i.val b,middleBits (q := q) v (m-1-i.val) b,betweenBits (q := q) v (m-1-i.val) j.val b,afterBits (q := q) v (m-1-j.val) b]) hh

theorem stage5_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (i j : Fin m) (hv : RecursiveDimensionBank.Headers v hs) (_hvpos : v.Positive) :
    HoareTime (program5 (q := q)) (fun w => w = bank hs bs rs (ds4 hq v b i j))
      (fun w => w = bank hs bs rs (ds5 hq v b i j)) (53*((v.beforeH)*(q^(i.val*b)))+28) := by
  have hh := DimensionProductDescriptor.construct_hoare (q := q) (prefixBits hq i.val b) (hs 2) (v.beforeH) (q^(i.val*b))
    (pow_pos (by omega) _) (RadixPowerMultipleDescriptor.bits_value _ _) (hv.1 2) (RadixPowerMultipleDescriptor.bits_canonical _ _) (hv.2 2)
  exact placed_exact placement5 _ _ _ _
    (by simp only [Placement.active,placement5,bank,ds4]
        apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (by simp only [Placement.active,placement5,bank,ds5]
        apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (frame5 hs bs rs ![prefixBits hq i.val b,prefixBits hq (m-1-i.val) b,prefixBits hq j.val b,prefixBits hq (m-1-j.val) b,beforeBits (q := q) v i.val b,middleBits (q := q) v (m-1-i.val) b,betweenBits (q := q) v (m-1-i.val) j.val b,afterBits (q := q) v (m-1-j.val) b]) hh

theorem stage6_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (i j : Fin m) (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (program6 (q := q)) (fun w => w = bank hs bs rs (ds5 hq v b i j))
      (fun w => w = bank hs bs rs (ds6 hq v b i j)) (53*((q^((m-1-i.val)*b))*(v.between))+28) := by
  have hh := DimensionProductDescriptor.construct_hoare (q := q) (hs 4) (prefixBits hq (m-1-i.val) b) (q^((m-1-i.val)*b)) (v.between)
    (hvpos.2.2.2.1) (hv.1 4) (RadixPowerMultipleDescriptor.bits_value _ _) (hv.2 4) (RadixPowerMultipleDescriptor.bits_canonical _ _)
  exact placed_exact placement6 _ _ _ _
    (by simp only [Placement.active,placement6,bank,ds5]
        apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (by simp only [Placement.active,placement6,bank,ds6]
        apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (frame6 hs bs rs ![prefixBits hq i.val b,prefixBits hq (m-1-i.val) b,prefixBits hq j.val b,prefixBits hq (m-1-j.val) b,beforeBits (q := q) v i.val b,middleBits (q := q) v (m-1-i.val) b,betweenBits (q := q) v (m-1-i.val) j.val b,afterBits (q := q) v (m-1-j.val) b]) hh

theorem stage7_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (i j : Fin m) (_hv : RecursiveDimensionBank.Headers v hs) (_hvpos : v.Positive) :
    HoareTime (program7 (q := q)) (fun w => w = bank hs bs rs (ds6 hq v b i j))
      (fun w => w = bank hs bs rs (ds7 hq v b i j)) (53*((q^((m-1-i.val)*b)*v.between)*(q^(j.val*b)))+28) := by
  have hh := DimensionProductDescriptor.construct_hoare (q := q) (prefixBits hq j.val b) (middleBits (q := q) v (m-1-i.val) b) (q^((m-1-i.val)*b)*v.between) (q^(j.val*b))
    (pow_pos (by omega) _) (RadixPowerMultipleDescriptor.bits_value _ _) (DimensionProductDescriptor.bits_value _ _) (RadixPowerMultipleDescriptor.bits_canonical _ _) (DimensionProductDescriptor.bits_canonical _ _)
  exact placed_exact placement7 _ _ _ _
    (by simp only [Placement.active,placement7,bank,ds6]
        apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (by simp only [Placement.active,placement7,bank,ds7]
        apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (frame7 hs bs rs ![prefixBits hq i.val b,prefixBits hq (m-1-i.val) b,prefixBits hq j.val b,prefixBits hq (m-1-j.val) b,beforeBits (q := q) v i.val b,middleBits (q := q) v (m-1-i.val) b,betweenBits (q := q) v (m-1-i.val) j.val b,afterBits (q := q) v (m-1-j.val) b]) hh

theorem stage8_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (i j : Fin m) (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (program8 (q := q)) (fun w => w = bank hs bs rs (ds7 hq v b i j))
      (fun w => w = bank hs bs rs (ds8 hq v b i j)) (53*((q^((m-1-j.val)*b))*(v.afterD))+28) := by
  have hh := DimensionProductDescriptor.construct_hoare (q := q) (hs 5) (prefixBits hq (m-1-j.val) b) (q^((m-1-j.val)*b)) (v.afterD)
    (hvpos.2.2.2.2) (hv.1 5) (RadixPowerMultipleDescriptor.bits_value _ _) (hv.2 5) (RadixPowerMultipleDescriptor.bits_canonical _ _)
  exact placed_exact placement8 _ _ _ _
    (by simp only [Placement.active,placement8,bank,ds7]
        apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (by simp only [Placement.active,placement8,bank,ds8]
        apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (frame8 hs bs rs ![prefixBits hq i.val b,prefixBits hq (m-1-i.val) b,prefixBits hq j.val b,prefixBits hq (m-1-j.val) b,beforeBits (q := q) v i.val b,middleBits (q := q) v (m-1-i.val) b,betweenBits (q := q) v (m-1-i.val) j.val b,afterBits (q := q) v (m-1-j.val) b]) hh


def input (hs : Fin 6 → List Bool) (bs rs : List Bool) : Tapes 19 q := bank hs bs rs ds0
def output (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (i j : Fin m) : Tapes 19 q := bank hs bs rs (ds8 hq v b i j)

def program {m : ℕ} (i j : Fin m) :=
  seq (seq (seq (seq (seq (seq (seq
    (program1 hq i.val) (program2 hq (m-1-i.val))) (program3 hq j.val))
      (program4 hq (m-1-j.val))) program5) program6) program7) program8

private theorem factor_bounds (hq : 2 ≤ q) (v : Descriptor) (hv : v.Positive) :
    v.beforeH ≤ volume q v ∧ v.between ≤ volume q v ∧ v.afterD ≤ volume q v := by
  rcases hv with ⟨hA,hR,hB,hC,hE⟩
  have hQ : 0 < q^v.width := pow_pos (by omega) _
  constructor
  · have hh := Nat.le_mul_of_pos_right v.beforeH (by positivity : 0 < v.beforeRows*v.rows*q^v.width*v.between*q^v.width*v.afterD)
    convert hh using 1
    simp only [volume]
    ring
  · constructor
    · have hh := Nat.le_mul_of_pos_right v.between (by positivity : 0 < v.beforeRows*v.rows*v.beforeH*q^v.width*q^v.width*v.afterD)
      convert hh using 1
      simp only [volume]
      ring
    · exact Nat.le_mul_of_pos_left _ (by positivity : 0 < v.beforeRows*v.rows*v.beforeH*q^v.width*v.between*q^v.width)

private theorem dimension_bounds (hq : 2 ≤ q) (roles b : ℕ) (v : Descriptor) {m : ℕ} (i j : Fin m)
    (hr : 0 < roles) (hdiv : roles ∣ v.rows) (hv : v.Positive) :
    let V := volume q (child q roles b v i j)
    q^(i.val*b) ≤ V ∧ q^((m-1-i.val)*b) ≤ V ∧ q^(j.val*b) ≤ V ∧ q^((m-1-j.val)*b) ≤ V ∧
    v.beforeH*q^(i.val*b) ≤ V ∧ q^((m-1-i.val)*b)*v.between ≤ V ∧
    (q^((m-1-i.val)*b)*v.between)*q^(j.val*b) ≤ V ∧ q^((m-1-j.val)*b)*v.afterD ≤ V := by
  obtain ⟨hB,hC,hE⟩ := factor_bounds hq (child q roles b v i j)
    (RecursiveInterchangeLayout.child_positive q roles b v i j (by omega) hr hdiv hv)
  have hPi : 0 < q^(i.val*b) := pow_pos (by omega) _
  have hSi : 0 < q^((m-1-i.val)*b) := pow_pos (by omega) _
  have hPj : 0 < q^(j.val*b) := pow_pos (by omega) _
  have hSj : 0 < q^((m-1-j.val)*b) := pow_pos (by omega) _
  have hmid : q^((m-1-i.val)*b)*v.between ≤ volume q (child q roles b v i j) :=
    (Nat.le_mul_of_pos_right _ hPj).trans hC
  exact ⟨(Nat.le_mul_of_pos_left _ hv.2.2.1).trans hB,
    (Nat.le_mul_of_pos_right _ hv.2.2.2.1).trans hmid,
    (Nat.le_mul_of_pos_left _ (Nat.mul_pos hSi hv.2.2.2.1)).trans hC,
    (Nat.le_mul_of_pos_right _ hv.2.2.2.2).trans hE,hB,hmid,hC,hE⟩

/-- All power construction and products cost linear time in the actual child
volume; no row split or quotient production is hidden in this statement. -/
theorem constructs_hoare (roles b : ℕ) (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    {m : ℕ} (i j : Fin m) (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive)
    (hb : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs)
    (hr : 0 < roles) (hdiv : roles ∣ v.rows) :
    HoareTime (program hq i j) (fun w => w = input hs bs rs)
      (fun w => w = output hq v hs bs rs b i j)
      ((48*(m-1)+512)*volume q (child q roles b v i j)+119) := by
  have hh := (((((((stage1_hoare hq v hs bs rs b i j hb cb).seq
    (stage2_hoare hq v hs bs rs b i j hb cb)).seq
    (stage3_hoare hq v hs bs rs b i j hb cb)).seq
    (stage4_hoare hq v hs bs rs b i j hb cb)).seq
    (stage5_hoare hq v hs bs rs b i j hv hvpos)).seq
    (stage6_hoare hq v hs bs rs b i j hv hvpos)).seq
    (stage7_hoare hq v hs bs rs b i j hv hvpos)).seq
    (stage8_hoare hq v hs bs rs b i j hv hvpos)
  apply hh.consequence (fun _ h => h) (fun _ h => h) ?_
  obtain ⟨hpi,hsi,hpj,hsj,hB,hmid,hC,hE⟩ := dimension_bounds hq roles b v i j hr hdiv hvpos
  have hi := i.isLt
  have hj := j.isLt
  have hm : i.val+(m-1-i.val)+j.val+(m-1-j.val) = 2*(m-1) := by omega
  have h1 := Nat.mul_le_mul_left (24*i.val+75) hpi
  have h2 := Nat.mul_le_mul_left (24*(m-1-i.val)+75) hsi
  have h3 := Nat.mul_le_mul_left (24*j.val+75) hpj
  have h4 := Nat.mul_le_mul_left (24*(m-1-j.val)+75) hsj
  nlinarith

def childHeaders (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (i j : Fin m) : Fin 6 → List Bool :=
  ![hs 0,rs,beforeBits (q := q) v i.val b,bs,
    betweenBits (q := q) v (m-1-i.val) j.val b,afterBits (q := q) v (m-1-j.val) b]

def childSlots : Fin 6 → Fin 19 := ![3,10,15,9,17,18]

theorem child_headers (roles b : ℕ) (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    {m : ℕ} (i j : Fin m) (hv : RecursiveDimensionBank.Headers v hs)
    (hb : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs)
    (hrows : Counter.value rs = v.rows/roles) (crows : GrowingCounterData.Canonical rs) :
    RecursiveDimensionBank.Headers (child q roles b v i j) (childHeaders (q := q) v hs bs rs b i j) := by
  constructor
  · intro z
    fin_cases z
    · exact hv.1 0
    · exact hrows
    · exact DimensionProductDescriptor.bits_value _ _
    · exact hb
    · exact DimensionProductDescriptor.bits_value _ _
    · exact DimensionProductDescriptor.bits_value _ _
  · intro z
    fin_cases z
    · exact hv.2 0
    · exact crows
    · exact DimensionProductDescriptor.bits_canonical _ _
    · exact cb
    · exact DimensionProductDescriptor.bits_canonical _ _
    · exact DimensionProductDescriptor.bits_canonical _ _

theorem output_headers (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (i j : Fin m) (z : Fin 6) :
    (output hq v hs bs rs b i j).head (childSlots z) = 1 ∧
    (output hq v hs bs rs b i j).tape (childSlots z) =
      RadixZeroFill.encodedBinary (childHeaders (q := q) v hs bs rs b i j z) := by
  fin_cases z <;> exact ⟨rfl,rfl⟩


def inputSlot (z : Fin 8) : Fin 19 := Fin.castAdd 8 (Fin.natAdd 3 z)

private theorem bank_inputs (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (ds : Fin 8 → Option (List Bool)) (z : Fin 8) :
    (bank (q := q) hs bs rs ds).head (inputSlot z) =
      (input (q := q) hs bs rs).head (inputSlot z) ∧
    (bank (q := q) hs bs rs ds).tape (inputSlot z) =
      (input (q := q) hs bs rs).tape (inputSlot z) := by
  unfold inputSlot bank input
  fin_cases z <;> norm_num [bank,Matrix.cons_val,Fin.natAdd,Fin.castAdd,Fin.castLE]

/-- All original six parent headers and both explicit quotients are preserved. -/
theorem inputs_preserved (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (i j : Fin m) (z : Fin 8) :
    (output hq v hs bs rs b i j).head (inputSlot z) =
      (input (q := q) hs bs rs).head (inputSlot z) ∧
    (output hq v hs bs rs b i j).tape (inputSlot z) =
      (input (q := q) hs bs rs).tape (inputSlot z) :=
  bank_inputs hs bs rs _ z

theorem input_blank (hs : Fin 6 → List Bool) (bs rs : List Bool) (z : Fin 19)
    (hz : ¬ (3 ≤ z.val ∧ z.val < 11)) :
    (input (q := q) hs bs rs).head z = 0 ∧
    (input (q := q) hs bs rs).tape z = fun _ => blank := by
  fin_cases z <;> first | exact ⟨rfl,rfl⟩ | (exfalso; exact hz (by decide))

end IntegerMultBounds.Machine.RecursiveChildDimensions
