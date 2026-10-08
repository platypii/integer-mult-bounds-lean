import IntegerMultBounds.Machine.RecursiveInterchangeLayout
import IntegerMultBounds.Machine.RadixPowerDescriptor
import IntegerMultBounds.Machine.DimensionProductDescriptor

/-! Runtime dimension arithmetic for seven-factor layouts. Six original binary
headers are retained; Q and successive prefix products are physically computed
from blank output/scratch tapes. -/
namespace IntegerMultBounds.Machine.RecursiveDimensionBank
open RecursiveInterchangeLayout (Descriptor volume)
variable {q : ℕ} (hq : 2 ≤ q)

def head : Option (List Bool) → ℤ | none => 0 | some _ => 1
def tape : Option (List Bool) → ℤ → Fin (q+4)
  | none => fun _ => blank
  | some bs => RadixZeroFill.encodedBinary bs

/-- Three blank scratch tapes, six immutable headers, four generated outputs. -/
def bank (hs : Fin 6 → List Bool) (ds : Fin 4 → Option (List Bool)) : Tapes 13 q :=
  ⟨![0,0,0,1,1,1,1,1,1,head (ds 0),head (ds 1),head (ds 2),head (ds 3)],
    ![fun _ => blank,fun _ => blank,fun _ => blank,RadixZeroFill.encodedBinary (hs 0),
      RadixZeroFill.encodedBinary (hs 1),RadixZeroFill.encodedBinary (hs 2),RadixZeroFill.encodedBinary (hs 3),
      RadixZeroFill.encodedBinary (hs 4),RadixZeroFill.encodedBinary (hs 5),tape (ds 0),tape (ds 1),tape (ds 2),tape (ds 3)]⟩

def values (v : Descriptor) : Fin 6 → ℕ := ![v.beforeRows,v.rows,v.beforeH,v.width,v.between,v.afterD]
def Headers (v : Descriptor) (hs : Fin 6 → List Bool) : Prop :=
  (∀ i, Counter.value (hs i) = values v i) ∧ (∀ i, GrowingCounterData.Canonical (hs i))

def qBits (v : Descriptor) := RadixPowerDescriptor.bits hq v.width
def arBits (v : Descriptor) := DimensionProductDescriptor.bits v.beforeRows v.rows
def arbBits (v : Descriptor) := DimensionProductDescriptor.bits (v.beforeRows*v.rows) v.beforeH
def nBits (v : Descriptor) := DimensionProductDescriptor.bits (v.beforeRows*v.rows*v.beforeH) (q^v.width)

def ds0 : Fin 4 → Option (List Bool) := fun _ => none
def ds1 (v : Descriptor) : Fin 4 → Option (List Bool) := ![some (qBits hq v),none,none,none]
def ds2 (v : Descriptor) : Fin 4 → Option (List Bool) := ![some (qBits hq v),some (arBits v),none,none]
def ds3 (v : Descriptor) : Fin 4 → Option (List Bool) := ![some (qBits hq v),some (arBits v),some (arbBits v),none]
def ds4 (v : Descriptor) : Fin 4 → Option (List Bool) := ![some (qBits hq v),some (arBits v),some (arbBits v),some (nBits (q := q) v)]

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

def powerPlacement : Fin (4+9) ≃ Fin 13 where
  toFun := ![0,1,6,9,2,3,4,5,7,8,10,11,12]
  invFun := ![0,1,4,5,6,7,2,8,9,3,10,11,12]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def arPlacement : Fin (6+7) ≃ Fin 13 where
  toFun := ![0,10,1,4,2,3,5,6,7,8,9,11,12]
  invFun := ![0,2,4,5,3,6,7,8,9,10,1,11,12]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def arbPlacement : Fin (6+7) ≃ Fin 13 where
  toFun := ![0,11,1,5,2,10,3,4,6,7,8,9,12]
  invFun := ![0,2,4,6,7,3,8,9,10,11,5,1,12]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def nPlacement : Fin (6+7) ≃ Fin 13 where
  toFun := ![0,12,1,9,2,11,3,4,5,6,7,8,10]
  invFun := ![0,2,4,6,7,8,9,10,11,3,12,5,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def powerProgram := Placement.placed (RadixPowerDescriptor.program hq) powerPlacement
def arProgram : Program 13 40 q := Placement.placed DimensionProductDescriptor.program arPlacement
def arbProgram : Program 13 40 q := Placement.placed DimensionProductDescriptor.program arbPlacement
def nProgram : Program 13 40 q := Placement.placed DimensionProductDescriptor.program nPlacement

private theorem power_frame (hs : Fin 6 → List Bool) (ds : Fin 4 → List Bool) :
    Placement.extra powerPlacement (bank (q := q) hs ![none,none,none,none]) =
      Placement.extra powerPlacement (bank hs ![some (ds 0),none,none,none]) := by
  unfold Placement.extra powerPlacement bank
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,Matrix.cons_val,head,tape] <;> norm_num

private theorem ar_frame (hs : Fin 6 → List Bool) (ds : Fin 4 → List Bool) :
    Placement.extra arPlacement (bank (q := q) hs ![some (ds 0),none,none,none]) =
      Placement.extra arPlacement (bank hs ![some (ds 0),some (ds 1),none,none]) := by
  unfold Placement.extra arPlacement bank
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,Matrix.cons_val,head,tape] <;> norm_num

private theorem arb_frame (hs : Fin 6 → List Bool) (ds : Fin 4 → List Bool) :
    Placement.extra arbPlacement (bank (q := q) hs ![some (ds 0),some (ds 1),none,none]) =
      Placement.extra arbPlacement (bank hs ![some (ds 0),some (ds 1),some (ds 2),none]) := by
  unfold Placement.extra arbPlacement bank
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,Matrix.cons_val,head,tape] <;> norm_num

private theorem n_frame (hs : Fin 6 → List Bool) (ds : Fin 4 → List Bool) :
    Placement.extra nPlacement (bank (q := q) hs ![some (ds 0),some (ds 1),some (ds 2),none]) =
      Placement.extra nPlacement (bank hs ![some (ds 0),some (ds 1),some (ds 2),some (ds 3)]) := by
  unfold Placement.extra nPlacement bank
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,Matrix.cons_val,head,tape] <;> norm_num

theorem power_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (hv : Headers v hs) :
    HoareTime (powerProgram hq) (fun w => w = bank hs ds0) (fun w => w = bank hs (ds1 hq v))
      (99*q^v.width) := by
  have hh := RadixPowerDescriptor.construct_hoare_linear hq (hs 3) v.width (hv.1 3) (hv.2 3)
  apply (placed_exact powerPlacement (bank hs ds0) (bank hs (ds1 hq v)) _ _ ?_ ?_ ?_ hh).consequence
    (fun _ h => h) (fun _ h => h) ?_
  · unfold Placement.active powerPlacement bank ds0
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [head,tape] <;> rfl
  · unfold Placement.active powerPlacement bank ds1
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [head,tape,qBits]
  · exact power_frame hs ![qBits hq v,[],[],[]]
  · omega

theorem ar_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (hv : Headers v hs) (hvpos : v.Positive) :
    HoareTime (arProgram (q := q)) (fun w => w = bank hs (ds1 hq v))
      (fun w => w = bank hs (ds2 hq v)) (53*((v.beforeRows)*(v.rows))+28) := by
  have hh := DimensionProductDescriptor.construct_hoare (q := q) (hs 1) (hs 0) (v.beforeRows) (v.rows)
    (hvpos.2.1) (hv.1 1) (hv.1 0) (hv.2 1) (hv.2 0)
  exact placed_exact arPlacement (bank hs (ds1 hq v)) (bank hs (ds2 hq v)) _ _
    (by unfold Placement.active arPlacement bank ds1; apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [head,tape,qBits])
    (by unfold Placement.active arPlacement bank ds2; apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [head,tape,qBits,arBits])
    (ar_frame hs ![qBits hq v,arBits v,arbBits v,nBits (q := q) v]) hh

theorem arb_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (hv : Headers v hs) (hvpos : v.Positive) :
    HoareTime (arbProgram (q := q)) (fun w => w = bank hs (ds2 hq v))
      (fun w => w = bank hs (ds3 hq v)) (53*((v.beforeRows*v.rows)*(v.beforeH))+28) := by
  have hh := DimensionProductDescriptor.construct_hoare (q := q) (hs 2) (arBits v) (v.beforeRows*v.rows) (v.beforeH)
    (hvpos.2.2.1) (hv.1 2) (DimensionProductDescriptor.bits_value _ _) (hv.2 2) (DimensionProductDescriptor.bits_canonical _ _)
  exact placed_exact arbPlacement (bank hs (ds2 hq v)) (bank hs (ds3 hq v)) _ _
    (by unfold Placement.active arbPlacement bank ds2; apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [head,tape,qBits,arBits])
    (by unfold Placement.active arbPlacement bank ds3; apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [head,tape,qBits,arBits,arbBits])
    (arb_frame hs ![qBits hq v,arBits v,arbBits v,nBits (q := q) v]) hh

theorem n_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (_hv : Headers v hs) (_hvpos : v.Positive) :
    HoareTime (nProgram (q := q)) (fun w => w = bank hs (ds3 hq v))
      (fun w => w = bank hs (ds4 hq v)) (53*((v.beforeRows*v.rows*v.beforeH)*(q^v.width))+28) := by
  have hh := DimensionProductDescriptor.construct_hoare (q := q) (qBits hq v) (arbBits v) (v.beforeRows*v.rows*v.beforeH) (q^v.width)
    (pow_pos (by omega) _) (RadixPowerDescriptor.bits_value _ _) (DimensionProductDescriptor.bits_value _ _) (RadixPowerDescriptor.bits_canonical _ _) (DimensionProductDescriptor.bits_canonical _ _)
  exact placed_exact nPlacement (bank hs (ds3 hq v)) (bank hs (ds4 hq v)) _ _
    (by unfold Placement.active nPlacement bank ds3; apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [head,tape,qBits,arBits,arbBits])
    (by unfold Placement.active nPlacement bank ds4; apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [head,tape,qBits,arBits,arbBits,nBits])
    (n_frame hs ![qBits hq v,arBits v,arbBits v,nBits (q := q) v]) hh


def program := seq (seq (seq (powerProgram hq) arProgram) arbProgram) nProgram

theorem construct_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (hv : Headers v hs) (hvpos : v.Positive) :
    HoareTime (program hq) (fun w => w = bank hs ds0) (fun w => w = bank hs (ds4 hq v))
      (258*volume q v+87) := by
  have hh := (((power_hoare hq v hs hv).seq (ar_hoare hq v hs hv hvpos)).seq
    (arb_hoare hq v hs hv hvpos)).seq (n_hoare hq v hs hv hvpos)
  apply hh.consequence (fun _ h => h) (fun _ h => h) ?_
  rcases hvpos with ⟨hA,hR,hB,hC,hE⟩
  have hQ : 0 < q^v.width := pow_pos (by omega) _
  have hAR : 0 < v.beforeRows*v.rows := Nat.mul_pos hA hR
  have hARB : 0 < v.beforeRows*v.rows*v.beforeH := Nat.mul_pos hAR hB
  have hN : v.beforeRows*v.rows*v.beforeH*q^v.width ≤ volume q v := by
    have hh := Nat.le_mul_of_pos_right (v.beforeRows*v.rows*v.beforeH*q^v.width)
      (Nat.mul_pos hC (Nat.mul_pos hQ hE))
    convert hh using 1
    simp only [volume]
    ring
  have hQ' : q^v.width ≤ v.beforeRows*v.rows*v.beforeH*q^v.width := Nat.le_mul_of_pos_left _ hARB
  have hARB' : v.beforeRows*v.rows*v.beforeH ≤ v.beforeRows*v.rows*v.beforeH*q^v.width := Nat.le_mul_of_pos_right _ hQ
  have hAR' : v.beforeRows*v.rows ≤ v.beforeRows*v.rows*v.beforeH := Nat.le_mul_of_pos_right _ hB
  omega

/-- The emitted dimensions are canonical, with no caller-supplied product. -/
theorem dimensions (v : Descriptor) :
    Counter.value (qBits hq v) = q^v.width ∧
    Counter.value (nBits (q := q) v) = v.beforeRows*v.rows*v.beforeH*q^v.width ∧
    GrowingCounterData.Canonical (qBits hq v) ∧ GrowingCounterData.Canonical (nBits (q := q) v) :=
  ⟨RadixPowerDescriptor.bits_value _ _,DimensionProductDescriptor.bits_value _ _,
    RadixPowerDescriptor.bits_canonical _ _,DimensionProductDescriptor.bits_canonical _ _⟩


/-- All six original descriptor tapes and their heads remain unchanged. -/
theorem headers_preserved (hs : Fin 6 → List Bool) (ds : Fin 4 → Option (List Bool)) (i : Fin 6) :
    (bank (q := q) hs ds).head (Fin.castAdd 4 (Fin.natAdd 3 i)) = 1 ∧
    (bank (q := q) hs ds).tape (Fin.castAdd 4 (Fin.natAdd 3 i)) = RadixZeroFill.encodedBinary (hs i) := by
  fin_cases i <;> exact ⟨rfl,rfl⟩

/-- Reused scratch is genuinely blank, including each marker cell. -/
theorem scratch_blank (hs : Fin 6 → List Bool) (ds : Fin 4 → Option (List Bool)) (i : Fin 3) :
    (bank (q := q) hs ds).head (Fin.castAdd 10 i) = 0 ∧
    (bank (q := q) hs ds).tape (Fin.castAdd 10 i) = (fun _ => blank) := by
  fin_cases i <;> exact ⟨rfl,rfl⟩


end IntegerMultBounds.Machine.RecursiveDimensionBank
