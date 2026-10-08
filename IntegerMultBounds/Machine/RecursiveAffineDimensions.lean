import IntegerMultBounds.Machine.RecursiveChildDimensions
import IntegerMultBounds.Machine.RecursiveAffineViews

/-! Paid construction of within-H and within-D coordinate-view dimensions.
All four required powers and four spectator products are emitted by fixed tape
programs. Only six original headers and canonical quotient-width/row descriptors
are supplied. Neither payload regrouping nor free arithmetic is assumed. -/
namespace IntegerMultBounds.Machine.RecursiveAffineDimensions
open RecursiveInterchangeLayout (Descriptor volume)
variable {q : ℕ} (hq : 2 ≤ q)

inductive Group | h | d

abbrev bank := @RecursiveChildDimensions.bank

def exponent {m : ℕ} (j i : Fin m) : Fin 4 → ℕ := ![j.val,i.val-j.val-1,m-1-i.val,m]
def powerBits (k b : ℕ) := RadixPowerMultipleDescriptor.bits hq (k*b)

def productLeft (v : Descriptor) (b : ℕ) {m : ℕ} (_j i : Fin m) : Group → Fin 4 → ℕ
  | .h => ![v.beforeH,q^((m-1-i.val)*b),q^((m-1-i.val)*b)*v.between,
      q^((m-1-i.val)*b)*v.between*q^(m*b)]
  | .d => ![v.beforeH,v.beforeH*q^(m*b),v.beforeH*q^(m*b)*v.between,q^((m-1-i.val)*b)]

def productRight (v : Descriptor) (b : ℕ) {m : ℕ} (j _i : Fin m) : Group → Fin 4 → ℕ
  | .h => ![q^(j.val*b),v.between,q^(m*b),v.afterD]
  | .d => ![q^(m*b),v.between,q^(j.val*b),v.afterD]

def words (v : Descriptor) (b : ℕ) {m : ℕ} (j i : Fin m) (g : Group) : Fin 8 → List Bool :=
  fun z => Fin.addCases (motive := fun _ => List Bool) (fun k : Fin 4 => powerBits hq (exponent j i k) b)
    (fun k : Fin 4 => DimensionProductDescriptor.bits (productLeft (q := q) v b j i g k)
      (productRight (q := q) v b j i g k)) z

def descriptors (xs : Fin 8 → List Bool) (n : ℕ) : Fin 8 → Option (List Bool) :=
  fun k => if k.val < n then some (xs k) else none

def state (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (j i : Fin m) (g : Group) (n : ℕ) :=
  bank (q := q) hs bs rs (descriptors (words hq v b j i g) n)

attribute [local irreducible] RadixPowerDescriptor.bits DimensionProductDescriptor.bits

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

def power0 (k : ℕ) := RecursiveChildDimensions.program1 hq k

private theorem power0_frame (hs : Fin 6 → List Bool) (bs rs : List Bool) (xs : Fin 8 → List Bool) :
    Placement.extra RecursiveChildDimensions.placement1 (bank (q := q) hs bs rs (descriptors xs 0)) =
      Placement.extra RecursiveChildDimensions.placement1 (bank hs bs rs (descriptors xs 1)) := by
  unfold Placement.extra RecursiveChildDimensions.placement1 bank RecursiveChildDimensions.bank descriptors
  apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;> norm_num

private theorem power0_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (j i : Fin m) (g : Group)
    (hb : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (power0 hq (exponent j i 0))
      (fun w => w = state hq v hs bs rs b j i g 0)
      (fun w => w = state hq v hs bs rs b j i g 1)
      ((24*exponent j i 0+75)*q^(exponent j i 0*b)) := by
  have hh := RadixPowerMultipleDescriptor.construct_hoare_linear hq (exponent j i 0) bs b hb cb
  exact placed_exact RecursiveChildDimensions.placement1
    (state hq v hs bs rs b j i g 0) (state hq v hs bs rs b j i g 1)
    (RadixPowerMultipleDescriptor.input bs) (RadixPowerMultipleDescriptor.output hq bs (exponent j i 0*b))
    (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (power0_frame hs bs rs (words hq v b j i g)) hh

def power1 (k : ℕ) := RecursiveChildDimensions.program2 hq k

private theorem power1_frame (hs : Fin 6 → List Bool) (bs rs : List Bool) (xs : Fin 8 → List Bool) :
    Placement.extra RecursiveChildDimensions.placement2 (bank (q := q) hs bs rs (descriptors xs 1)) =
      Placement.extra RecursiveChildDimensions.placement2 (bank hs bs rs (descriptors xs 2)) := by
  unfold Placement.extra RecursiveChildDimensions.placement2 bank RecursiveChildDimensions.bank descriptors
  apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;> norm_num

private theorem power1_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (j i : Fin m) (g : Group)
    (hb : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (power1 hq (exponent j i 1))
      (fun w => w = state hq v hs bs rs b j i g 1)
      (fun w => w = state hq v hs bs rs b j i g 2)
      ((24*exponent j i 1+75)*q^(exponent j i 1*b)) := by
  have hh := RadixPowerMultipleDescriptor.construct_hoare_linear hq (exponent j i 1) bs b hb cb
  exact placed_exact RecursiveChildDimensions.placement2
    (state hq v hs bs rs b j i g 1) (state hq v hs bs rs b j i g 2)
    (RadixPowerMultipleDescriptor.input bs) (RadixPowerMultipleDescriptor.output hq bs (exponent j i 1*b))
    (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (power1_frame hs bs rs (words hq v b j i g)) hh

def power2 (k : ℕ) := RecursiveChildDimensions.program3 hq k

private theorem power2_frame (hs : Fin 6 → List Bool) (bs rs : List Bool) (xs : Fin 8 → List Bool) :
    Placement.extra RecursiveChildDimensions.placement3 (bank (q := q) hs bs rs (descriptors xs 2)) =
      Placement.extra RecursiveChildDimensions.placement3 (bank hs bs rs (descriptors xs 3)) := by
  unfold Placement.extra RecursiveChildDimensions.placement3 bank RecursiveChildDimensions.bank descriptors
  apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;> norm_num

private theorem power2_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (j i : Fin m) (g : Group)
    (hb : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (power2 hq (exponent j i 2))
      (fun w => w = state hq v hs bs rs b j i g 2)
      (fun w => w = state hq v hs bs rs b j i g 3)
      ((24*exponent j i 2+75)*q^(exponent j i 2*b)) := by
  have hh := RadixPowerMultipleDescriptor.construct_hoare_linear hq (exponent j i 2) bs b hb cb
  exact placed_exact RecursiveChildDimensions.placement3
    (state hq v hs bs rs b j i g 2) (state hq v hs bs rs b j i g 3)
    (RadixPowerMultipleDescriptor.input bs) (RadixPowerMultipleDescriptor.output hq bs (exponent j i 2*b))
    (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (power2_frame hs bs rs (words hq v b j i g)) hh

def power3 (k : ℕ) := RecursiveChildDimensions.program4 hq k

private theorem power3_frame (hs : Fin 6 → List Bool) (bs rs : List Bool) (xs : Fin 8 → List Bool) :
    Placement.extra RecursiveChildDimensions.placement4 (bank (q := q) hs bs rs (descriptors xs 3)) =
      Placement.extra RecursiveChildDimensions.placement4 (bank hs bs rs (descriptors xs 4)) := by
  unfold Placement.extra RecursiveChildDimensions.placement4 bank RecursiveChildDimensions.bank descriptors
  apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;> norm_num

private theorem power3_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (j i : Fin m) (g : Group)
    (hb : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (power3 hq (exponent j i 3))
      (fun w => w = state hq v hs bs rs b j i g 3)
      (fun w => w = state hq v hs bs rs b j i g 4)
      ((24*exponent j i 3+75)*q^(exponent j i 3*b)) := by
  have hh := RadixPowerMultipleDescriptor.construct_hoare_linear hq (exponent j i 3) bs b hb cb
  exact placed_exact RecursiveChildDimensions.placement4
    (state hq v hs bs rs b j i g 3) (state hq v hs bs rs b j i g 4)
    (RadixPowerMultipleDescriptor.input bs) (RadixPowerMultipleDescriptor.output hq bs (exponent j i 3*b))
    (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
    (power3_frame hs bs rs (words hq v b j i g)) hh

def product0hPlacement : Fin (6+13) ≃ Fin 19 where
  toFun := ![0,15,1,11,2,5,3,4,6,7,8,9,10,12,13,14,16,17,18]
  invFun := ![0,2,4,6,7,5,8,9,10,11,12,3,13,14,15,1,16,17,18]
  left_inv := by intro z; fin_cases z <;> rfl
  right_inv := by intro z; fin_cases z <;> rfl

def product0dPlacement : Fin (6+13) ≃ Fin 19 where
  toFun := ![0,15,1,14,2,5,3,4,6,7,8,9,10,11,12,13,16,17,18]
  invFun := ![0,2,4,6,7,5,8,9,10,11,12,13,14,15,3,1,16,17,18]
  left_inv := by intro z; fin_cases z <;> rfl
  right_inv := by intro z; fin_cases z <;> rfl

private theorem product0h_frame (hs : Fin 6 → List Bool) (bs rs : List Bool) (xs : Fin 8 → List Bool) :
    Placement.extra product0hPlacement (bank (q := q) hs bs rs (descriptors xs 4)) =
      Placement.extra product0hPlacement (bank hs bs rs (descriptors xs 5)) := by
  unfold Placement.extra product0hPlacement bank RecursiveChildDimensions.bank descriptors
  apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;> norm_num

private theorem product0d_frame (hs : Fin 6 → List Bool) (bs rs : List Bool) (xs : Fin 8 → List Bool) :
    Placement.extra product0dPlacement (bank (q := q) hs bs rs (descriptors xs 4)) =
      Placement.extra product0dPlacement (bank hs bs rs (descriptors xs 5)) := by
  unfold Placement.extra product0dPlacement bank RecursiveChildDimensions.bank descriptors
  apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;> norm_num

def product0Program : Group → Program 19 40 q
  | .h => Placement.placed DimensionProductDescriptor.program product0hPlacement
  | .d => Placement.placed DimensionProductDescriptor.program product0dPlacement

private theorem product0_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (j i : Fin m) (g : Group)
    (hv : RecursiveDimensionBank.Headers v hs) (_hp : v.Positive) :
    HoareTime (product0Program (q := q) g)
      (fun w => w = state hq v hs bs rs b j i g 4)
      (fun w => w = state hq v hs bs rs b j i g 5)
      (53*(productLeft (q := q) v b j i g 0*productRight (q := q) v b j i g 0)+28) := by
  cases g with
  | h =>
    have hh := DimensionProductDescriptor.construct_hoare (q := q) (powerBits hq j.val b) (hs 2)
      (productLeft (q := q) v b j i .h 0) (productRight (q := q) v b j i .h 0)
      (pow_pos (by omega) _) (RadixPowerMultipleDescriptor.bits_value _ _) (hv.1 2) (RadixPowerMultipleDescriptor.bits_canonical _ _) (hv.2 2)
    exact placed_exact product0hPlacement
      (state hq v hs bs rs b j i .h 4) (state hq v hs bs rs b j i .h 5)
      (DimensionProductDescriptor.input (powerBits hq j.val b) (hs 2))
      (DimensionProductDescriptor.output (powerBits hq j.val b) (hs 2)
        (productLeft (q := q) v b j i .h 0) (productRight (q := q) v b j i .h 0))
      (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
      (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
      (product0h_frame hs bs rs (words hq v b j i .h)) hh
  | d =>
    have hh := DimensionProductDescriptor.construct_hoare (q := q) (powerBits hq m b) (hs 2)
      (productLeft (q := q) v b j i .d 0) (productRight (q := q) v b j i .d 0)
      (pow_pos (by omega) _) (RadixPowerMultipleDescriptor.bits_value _ _) (hv.1 2) (RadixPowerMultipleDescriptor.bits_canonical _ _) (hv.2 2)
    exact placed_exact product0dPlacement
      (state hq v hs bs rs b j i .d 4) (state hq v hs bs rs b j i .d 5)
      (DimensionProductDescriptor.input (powerBits hq m b) (hs 2))
      (DimensionProductDescriptor.output (powerBits hq m b) (hs 2)
        (productLeft (q := q) v b j i .d 0) (productRight (q := q) v b j i .d 0))
      (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
      (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
      (product0d_frame hs bs rs (words hq v b j i .d)) hh

def product1hPlacement : Fin (6+13) ≃ Fin 19 where
  toFun := ![0,16,1,7,2,13,3,4,5,6,8,9,10,11,12,14,15,17,18]
  invFun := ![0,2,4,6,7,8,9,3,10,11,12,13,14,5,15,16,1,17,18]
  left_inv := by intro z; fin_cases z <;> rfl
  right_inv := by intro z; fin_cases z <;> rfl

def product1dPlacement : Fin (6+13) ≃ Fin 19 where
  toFun := ![0,16,1,7,2,15,3,4,5,6,8,9,10,11,12,13,14,17,18]
  invFun := ![0,2,4,6,7,8,9,3,10,11,12,13,14,15,16,5,1,17,18]
  left_inv := by intro z; fin_cases z <;> rfl
  right_inv := by intro z; fin_cases z <;> rfl

private theorem product1h_frame (hs : Fin 6 → List Bool) (bs rs : List Bool) (xs : Fin 8 → List Bool) :
    Placement.extra product1hPlacement (bank (q := q) hs bs rs (descriptors xs 5)) =
      Placement.extra product1hPlacement (bank hs bs rs (descriptors xs 6)) := by
  unfold Placement.extra product1hPlacement bank RecursiveChildDimensions.bank descriptors
  apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;> norm_num

private theorem product1d_frame (hs : Fin 6 → List Bool) (bs rs : List Bool) (xs : Fin 8 → List Bool) :
    Placement.extra product1dPlacement (bank (q := q) hs bs rs (descriptors xs 5)) =
      Placement.extra product1dPlacement (bank hs bs rs (descriptors xs 6)) := by
  unfold Placement.extra product1dPlacement bank RecursiveChildDimensions.bank descriptors
  apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;> norm_num

def product1Program : Group → Program 19 40 q
  | .h => Placement.placed DimensionProductDescriptor.program product1hPlacement
  | .d => Placement.placed DimensionProductDescriptor.program product1dPlacement

private theorem product1_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (j i : Fin m) (g : Group)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) :
    HoareTime (product1Program (q := q) g)
      (fun w => w = state hq v hs bs rs b j i g 5)
      (fun w => w = state hq v hs bs rs b j i g 6)
      (53*(productLeft (q := q) v b j i g 1*productRight (q := q) v b j i g 1)+28) := by
  cases g with
  | h =>
    have hh := DimensionProductDescriptor.construct_hoare (q := q) (hs 4) (powerBits hq (m-1-i.val) b)
      (productLeft (q := q) v b j i .h 1) (productRight (q := q) v b j i .h 1)
      (hp.2.2.2.1) (hv.1 4) (RadixPowerMultipleDescriptor.bits_value _ _) (hv.2 4) (RadixPowerMultipleDescriptor.bits_canonical _ _)
    exact placed_exact product1hPlacement
      (state hq v hs bs rs b j i .h 5) (state hq v hs bs rs b j i .h 6)
      (DimensionProductDescriptor.input (hs 4) (powerBits hq (m-1-i.val) b))
      (DimensionProductDescriptor.output (hs 4) (powerBits hq (m-1-i.val) b)
        (productLeft (q := q) v b j i .h 1) (productRight (q := q) v b j i .h 1))
      (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
      (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
      (product1h_frame hs bs rs (words hq v b j i .h)) hh
  | d =>
    have hh := DimensionProductDescriptor.construct_hoare (q := q) (hs 4) (DimensionProductDescriptor.bits v.beforeH (q^(m*b)))
      (productLeft (q := q) v b j i .d 1) (productRight (q := q) v b j i .d 1)
      (hp.2.2.2.1) (hv.1 4) (DimensionProductDescriptor.bits_value _ _) (hv.2 4) (DimensionProductDescriptor.bits_canonical _ _)
    exact placed_exact product1dPlacement
      (state hq v hs bs rs b j i .d 5) (state hq v hs bs rs b j i .d 6)
      (DimensionProductDescriptor.input (hs 4) (DimensionProductDescriptor.bits v.beforeH (q^(m*b))))
      (DimensionProductDescriptor.output (hs 4) (DimensionProductDescriptor.bits v.beforeH (q^(m*b)))
        (productLeft (q := q) v b j i .d 1) (productRight (q := q) v b j i .d 1))
      (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
      (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
      (product1d_frame hs bs rs (words hq v b j i .d)) hh

def product2hPlacement : Fin (6+13) ≃ Fin 19 where
  toFun := ![0,17,1,14,2,16,3,4,5,6,7,8,9,10,11,12,13,15,18]
  invFun := ![0,2,4,6,7,8,9,10,11,12,13,14,15,16,3,17,5,1,18]
  left_inv := by intro z; fin_cases z <;> rfl
  right_inv := by intro z; fin_cases z <;> rfl

def product2dPlacement : Fin (6+13) ≃ Fin 19 where
  toFun := ![0,17,1,11,2,16,3,4,5,6,7,8,9,10,12,13,14,15,18]
  invFun := ![0,2,4,6,7,8,9,10,11,12,13,3,14,15,16,17,5,1,18]
  left_inv := by intro z; fin_cases z <;> rfl
  right_inv := by intro z; fin_cases z <;> rfl

private theorem product2h_frame (hs : Fin 6 → List Bool) (bs rs : List Bool) (xs : Fin 8 → List Bool) :
    Placement.extra product2hPlacement (bank (q := q) hs bs rs (descriptors xs 6)) =
      Placement.extra product2hPlacement (bank hs bs rs (descriptors xs 7)) := by
  unfold Placement.extra product2hPlacement bank RecursiveChildDimensions.bank descriptors
  apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;> norm_num

private theorem product2d_frame (hs : Fin 6 → List Bool) (bs rs : List Bool) (xs : Fin 8 → List Bool) :
    Placement.extra product2dPlacement (bank (q := q) hs bs rs (descriptors xs 6)) =
      Placement.extra product2dPlacement (bank hs bs rs (descriptors xs 7)) := by
  unfold Placement.extra product2dPlacement bank RecursiveChildDimensions.bank descriptors
  apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;> norm_num

def product2Program : Group → Program 19 40 q
  | .h => Placement.placed DimensionProductDescriptor.program product2hPlacement
  | .d => Placement.placed DimensionProductDescriptor.program product2dPlacement

private theorem product2_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (j i : Fin m) (g : Group)
    (_hv : RecursiveDimensionBank.Headers v hs) (_hp : v.Positive) :
    HoareTime (product2Program (q := q) g)
      (fun w => w = state hq v hs bs rs b j i g 6)
      (fun w => w = state hq v hs bs rs b j i g 7)
      (53*(productLeft (q := q) v b j i g 2*productRight (q := q) v b j i g 2)+28) := by
  cases g with
  | h =>
    have hh := DimensionProductDescriptor.construct_hoare (q := q) (powerBits hq m b) (DimensionProductDescriptor.bits (q^((m-1-i.val)*b)) v.between)
      (productLeft (q := q) v b j i .h 2) (productRight (q := q) v b j i .h 2)
      (pow_pos (by omega) _) (RadixPowerMultipleDescriptor.bits_value _ _) (DimensionProductDescriptor.bits_value _ _) (RadixPowerMultipleDescriptor.bits_canonical _ _) (DimensionProductDescriptor.bits_canonical _ _)
    exact placed_exact product2hPlacement
      (state hq v hs bs rs b j i .h 6) (state hq v hs bs rs b j i .h 7)
      (DimensionProductDescriptor.input (powerBits hq m b) (DimensionProductDescriptor.bits (q^((m-1-i.val)*b)) v.between))
      (DimensionProductDescriptor.output (powerBits hq m b) (DimensionProductDescriptor.bits (q^((m-1-i.val)*b)) v.between)
        (productLeft (q := q) v b j i .h 2) (productRight (q := q) v b j i .h 2))
      (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
      (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
      (product2h_frame hs bs rs (words hq v b j i .h)) hh
  | d =>
    have hh := DimensionProductDescriptor.construct_hoare (q := q) (powerBits hq j.val b) (DimensionProductDescriptor.bits (v.beforeH*q^(m*b)) v.between)
      (productLeft (q := q) v b j i .d 2) (productRight (q := q) v b j i .d 2)
      (pow_pos (by omega) _) (RadixPowerMultipleDescriptor.bits_value _ _) (DimensionProductDescriptor.bits_value _ _) (RadixPowerMultipleDescriptor.bits_canonical _ _) (DimensionProductDescriptor.bits_canonical _ _)
    exact placed_exact product2dPlacement
      (state hq v hs bs rs b j i .d 6) (state hq v hs bs rs b j i .d 7)
      (DimensionProductDescriptor.input (powerBits hq j.val b) (DimensionProductDescriptor.bits (v.beforeH*q^(m*b)) v.between))
      (DimensionProductDescriptor.output (powerBits hq j.val b) (DimensionProductDescriptor.bits (v.beforeH*q^(m*b)) v.between)
        (productLeft (q := q) v b j i .d 2) (productRight (q := q) v b j i .d 2))
      (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
      (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
      (product2d_frame hs bs rs (words hq v b j i .d)) hh

def product3hPlacement : Fin (6+13) ≃ Fin 19 where
  toFun := ![0,18,1,8,2,17,3,4,5,6,7,9,10,11,12,13,14,15,16]
  invFun := ![0,2,4,6,7,8,9,10,3,11,12,13,14,15,16,17,18,5,1]
  left_inv := by intro z; fin_cases z <;> rfl
  right_inv := by intro z; fin_cases z <;> rfl

def product3dPlacement : Fin (6+13) ≃ Fin 19 where
  toFun := ![0,18,1,8,2,13,3,4,5,6,7,9,10,11,12,14,15,16,17]
  invFun := ![0,2,4,6,7,8,9,10,3,11,12,13,14,5,15,16,17,18,1]
  left_inv := by intro z; fin_cases z <;> rfl
  right_inv := by intro z; fin_cases z <;> rfl

private theorem product3h_frame (hs : Fin 6 → List Bool) (bs rs : List Bool) (xs : Fin 8 → List Bool) :
    Placement.extra product3hPlacement (bank (q := q) hs bs rs (descriptors xs 7)) =
      Placement.extra product3hPlacement (bank hs bs rs (descriptors xs 8)) := by
  unfold Placement.extra product3hPlacement bank RecursiveChildDimensions.bank descriptors
  apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;> norm_num

private theorem product3d_frame (hs : Fin 6 → List Bool) (bs rs : List Bool) (xs : Fin 8 → List Bool) :
    Placement.extra product3dPlacement (bank (q := q) hs bs rs (descriptors xs 7)) =
      Placement.extra product3dPlacement (bank hs bs rs (descriptors xs 8)) := by
  unfold Placement.extra product3dPlacement bank RecursiveChildDimensions.bank descriptors
  apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;> norm_num

def product3Program : Group → Program 19 40 q
  | .h => Placement.placed DimensionProductDescriptor.program product3hPlacement
  | .d => Placement.placed DimensionProductDescriptor.program product3dPlacement

private theorem product3_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (j i : Fin m) (g : Group)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) :
    HoareTime (product3Program (q := q) g)
      (fun w => w = state hq v hs bs rs b j i g 7)
      (fun w => w = state hq v hs bs rs b j i g 8)
      (53*(productLeft (q := q) v b j i g 3*productRight (q := q) v b j i g 3)+28) := by
  cases g with
  | h =>
    have hh := DimensionProductDescriptor.construct_hoare (q := q) (hs 5) (DimensionProductDescriptor.bits (q^((m-1-i.val)*b)*v.between) (q^(m*b)))
      (productLeft (q := q) v b j i .h 3) (productRight (q := q) v b j i .h 3)
      (hp.2.2.2.2) (hv.1 5) (DimensionProductDescriptor.bits_value _ _) (hv.2 5) (DimensionProductDescriptor.bits_canonical _ _)
    exact placed_exact product3hPlacement
      (state hq v hs bs rs b j i .h 7) (state hq v hs bs rs b j i .h 8)
      (DimensionProductDescriptor.input (hs 5) (DimensionProductDescriptor.bits (q^((m-1-i.val)*b)*v.between) (q^(m*b))))
      (DimensionProductDescriptor.output (hs 5) (DimensionProductDescriptor.bits (q^((m-1-i.val)*b)*v.between) (q^(m*b)))
        (productLeft (q := q) v b j i .h 3) (productRight (q := q) v b j i .h 3))
      (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
      (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
      (product3h_frame hs bs rs (words hq v b j i .h)) hh
  | d =>
    have hh := DimensionProductDescriptor.construct_hoare (q := q) (hs 5) (powerBits hq (m-1-i.val) b)
      (productLeft (q := q) v b j i .d 3) (productRight (q := q) v b j i .d 3)
      (hp.2.2.2.2) (hv.1 5) (RadixPowerMultipleDescriptor.bits_value _ _) (hv.2 5) (RadixPowerMultipleDescriptor.bits_canonical _ _)
    exact placed_exact product3dPlacement
      (state hq v hs bs rs b j i .d 7) (state hq v hs bs rs b j i .d 8)
      (DimensionProductDescriptor.input (hs 5) (powerBits hq (m-1-i.val) b))
      (DimensionProductDescriptor.output (hs 5) (powerBits hq (m-1-i.val) b)
        (productLeft (q := q) v b j i .d 3) (productRight (q := q) v b j i .d 3))
      (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
      (by apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl)
      (product3d_frame hs bs rs (words hq v b j i .d)) hh

def program {m : ℕ} (j i : Fin m) (g : Group) :=
  seq (seq (seq (seq (seq (seq (seq
    (power0 hq (exponent j i 0)) (power1 hq (exponent j i 1)))
    (power2 hq (exponent j i 2))) (power3 hq (exponent j i 3)))
    (product0Program (q := q) g)) (product1Program (q := q) g))
    (product2Program (q := q) g)) (product3Program (q := q) g)

def cost (v : Descriptor) (b : ℕ) {m : ℕ} (j i : Fin m) (g : Group) :=
  (∑ k : Fin 4, (24*exponent j i k+75)*q^(exponent j i k*b))+
    (∑ k : Fin 4, (53*(productLeft (q := q) v b j i g k*productRight (q := q) v b j i g k)+28))+7

theorem constructs_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (j i : Fin m) (g : Group)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive)
    (hb : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (program hq j i g) (fun w => w = RecursiveChildDimensions.input hs bs rs)
      (fun w => w = state hq v hs bs rs b j i g 8) (cost (q := q) v b j i g) := by
  have hh := (((((((power0_hoare hq v hs bs rs b j i g hb cb).seq
    (power1_hoare hq v hs bs rs b j i g hb cb)).seq
    (power2_hoare hq v hs bs rs b j i g hb cb)).seq
    (power3_hoare hq v hs bs rs b j i g hb cb)).seq
    (product0_hoare hq v hs bs rs b j i g hv hp)).seq
    (product1_hoare hq v hs bs rs b j i g hv hp)).seq
    (product2_hoare hq v hs bs rs b j i g hv hp)).seq
    (product3_hoare hq v hs bs rs b j i g hv hp)
  apply hh.consequence ?_ (fun _ h => h) ?_
  · intro w hw
    rw [hw]
    apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl
  · apply le_of_eq
    simp only [cost,Fin.sum_univ_four]
    ring

end IntegerMultBounds.Machine.RecursiveAffineDimensions
