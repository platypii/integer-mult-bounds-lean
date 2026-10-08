import IntegerMultBounds.Machine.ExactFrame
import IntegerMultBounds.Machine.RecursiveDimensionBank
import IntegerMultBounds.Machine.RecursiveInterchangeScaling

/-! Additional physical products for heterogeneous H/D scaling dimensions.
Original six headers and generated Q/ARB/N stay intact; three extra output
slots hold Q*E, C*Q*E, and N*C as required by the selected static target. -/
namespace IntegerMultBounds.Machine.RecursiveScalingDimensions
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveInterchangeScaling (Target)
variable {q : ℕ} (hq : 2 ≤ q)

def tailBank (ds : Fin 3 → Option (List Bool)) : Tapes 3 q :=
  ⟨fun i => RecursiveDimensionBank.head (ds i),fun i => RecursiveDimensionBank.tape (ds i)⟩
def bank (base : Tapes 13 q) (ds : Fin 3 → Option (List Bool)) : Tapes 16 q := base.append (tailBank ds)
def qeBits (v : Descriptor) := DimensionProductDescriptor.bits (q^v.width) v.afterD
def cqeBits (v : Descriptor) := DimensionProductDescriptor.bits v.between (q^v.width*v.afterD)
def ncBits (v : Descriptor) := DimensionProductDescriptor.bits (v.beforeRows*v.rows*v.beforeH*q^v.width) v.between

def ds0 : Fin 3 → Option (List Bool) := ![none,none,none]
def ds1 (v : Descriptor) : Fin 3 → Option (List Bool) := ![some (qeBits (q := q) v),none,none]
def descriptors (v : Descriptor) : Target → Fin 3 → Option (List Bool)
  | .h => ![some (qeBits (q := q) v),some (cqeBits (q := q) v),none]
  | .d => ![none,none,some (ncBits (q := q) v)]

def base (hs : Fin 6 → List Bool) (v : Descriptor) : Tapes 13 q := RecursiveDimensionBank.bank hs (RecursiveDimensionBank.ds4 hq v)
def input (hs : Fin 6 → List Bool) : Tapes 16 q := bank (RecursiveDimensionBank.bank hs RecursiveDimensionBank.ds0) ds0
def output (hs : Fin 6 → List Bool) (v : Descriptor) (target : Target) := bank (base hq hs v) (descriptors (q := q) v target)

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

def qePlacement : Fin (6+10) ≃ Fin 16 where
  toFun := ![0,13,1,8,2,9,3,4,5,6,7,10,11,12,14,15]
  invFun := ![0,2,4,6,7,8,9,10,3,5,11,12,13,1,14,15]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def qeProgram : Program 16 40 q := Placement.placed DimensionProductDescriptor.program qePlacement

def cqePlacement : Fin (6+10) ≃ Fin 16 where
  toFun := ![0,14,1,13,2,7,3,4,5,6,8,9,10,11,12,15]
  invFun := ![0,2,4,6,7,8,9,5,10,11,12,13,14,3,1,15]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def cqeProgram : Program 16 40 q := Placement.placed DimensionProductDescriptor.program cqePlacement

def ncPlacement : Fin (6+10) ≃ Fin 16 where
  toFun := ![0,15,1,7,2,12,3,4,5,6,8,9,10,11,13,14]
  invFun := ![0,2,4,6,7,8,9,3,10,11,12,13,5,14,15,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def ncProgram : Program 16 40 q := Placement.placed DimensionProductDescriptor.program ncPlacement

private theorem qe_frame (v : Tapes 13 q) (ds : Fin 3 → List Bool) :
    Placement.extra qePlacement (bank v ![none,none,none]) =
      Placement.extra qePlacement (bank v ![some (ds 0),none,none]) := by
  unfold Placement.extra qePlacement bank tailBank
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;>
    norm_num [Tapes.append,Fin.addCases]

private theorem cqe_frame (v : Tapes 13 q) (ds : Fin 3 → List Bool) :
    Placement.extra cqePlacement (bank v ![some (ds 0),none,none]) =
      Placement.extra cqePlacement (bank v ![some (ds 0),some (ds 1),none]) := by
  unfold Placement.extra cqePlacement bank tailBank
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;>
    norm_num [Tapes.append,Fin.addCases]

private theorem nc_frame (v : Tapes 13 q) (ds : Fin 3 → List Bool) :
    Placement.extra ncPlacement (bank v ![none,none,none]) =
      Placement.extra ncPlacement (bank v ![none,none,some (ds 2)]) := by
  unfold Placement.extra ncPlacement bank tailBank
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp only [Equiv.coe_fn_mk,Fin.natAdd,RecursiveDimensionBank.head,RecursiveDimensionBank.tape] <;>
    norm_num [Tapes.append,Fin.addCases]

theorem qe_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (qeProgram (q := q)) (fun w => w = bank (base hq hs v) (ds0))
      (fun w => w = bank (base hq hs v) (ds1 (q := q) v)) (53*((q^v.width)*(v.afterD))+28) := by
  have hh := DimensionProductDescriptor.construct_hoare (q := q) (hs 5) (RecursiveDimensionBank.qBits hq v) (q^v.width) (v.afterD)
    (hvpos.2.2.2.2) (hv.1 5) (RadixPowerDescriptor.bits_value _ _) (hv.2 5) (RadixPowerDescriptor.bits_canonical _ _)
  exact placed_exact qePlacement _ _ _ _
    (by simp only [Placement.active,qePlacement,bank,base,tailBank,RecursiveDimensionBank.bank,RecursiveDimensionBank.ds4,ds0]
        apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl)
    (by simp only [Placement.active,qePlacement,bank,base,tailBank,RecursiveDimensionBank.bank,RecursiveDimensionBank.ds4,ds1]
        apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl)
    (qe_frame (base hq hs v) ![qeBits (q := q) v,cqeBits (q := q) v,ncBits (q := q) v]) hh

theorem cqe_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (cqeProgram (q := q)) (fun w => w = bank (base hq hs v) (ds1 (q := q) v))
      (fun w => w = bank (base hq hs v) (descriptors (q := q) v .h)) (53*((v.between)*(q^v.width*v.afterD))+28) := by
  have hh := DimensionProductDescriptor.construct_hoare (q := q) (qeBits (q := q) v) (hs 4) (v.between) (q^v.width*v.afterD)
    (Nat.mul_pos (pow_pos (by omega) _) hvpos.2.2.2.2) (DimensionProductDescriptor.bits_value _ _) (hv.1 4) (DimensionProductDescriptor.bits_canonical _ _) (hv.2 4)
  exact placed_exact cqePlacement _ _ _ _
    (by simp only [Placement.active,cqePlacement,bank,base,tailBank,RecursiveDimensionBank.bank,RecursiveDimensionBank.ds4,ds1]
        apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl)
    (by simp only [Placement.active,cqePlacement,bank,base,tailBank,RecursiveDimensionBank.bank,RecursiveDimensionBank.ds4,descriptors]
        apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl)
    (cqe_frame (base hq hs v) ![qeBits (q := q) v,cqeBits (q := q) v,ncBits (q := q) v]) hh

theorem nc_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (ncProgram (q := q)) (fun w => w = bank (base hq hs v) (ds0))
      (fun w => w = bank (base hq hs v) (descriptors (q := q) v .d)) (53*((v.beforeRows*v.rows*v.beforeH*q^v.width)*(v.between))+28) := by
  have hh := DimensionProductDescriptor.construct_hoare (q := q) (hs 4) (RecursiveDimensionBank.nBits (q := q) v) (v.beforeRows*v.rows*v.beforeH*q^v.width) (v.between)
    (hvpos.2.2.2.1) (hv.1 4) (DimensionProductDescriptor.bits_value _ _) (hv.2 4) (DimensionProductDescriptor.bits_canonical _ _)
  exact placed_exact ncPlacement _ _ _ _
    (by simp only [Placement.active,ncPlacement,bank,base,tailBank,RecursiveDimensionBank.bank,RecursiveDimensionBank.ds4,ds0]
        apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl)
    (by simp only [Placement.active,ncPlacement,bank,base,tailBank,RecursiveDimensionBank.bank,RecursiveDimensionBank.ds4,descriptors]
        apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl)
    (nc_frame (base hq hs v) ![qeBits (q := q) v,cqeBits (q := q) v,ncBits (q := q) v]) hh


def States : Target → ℕ | .h => 253 | .d => 213

def program (target : Target) : Program 16 (States target) q :=
  match target with
  | .h => seq (seq (extend (RecursiveDimensionBank.program hq) 3) qeProgram) cqeProgram
  | .d => seq (extend (RecursiveDimensionBank.program hq) 3) ncProgram

private theorem products_le (hq : 2 ≤ q) (v : Descriptor) (hv : v.Positive) :
    q^v.width*v.afterD ≤ volume q v ∧ v.between*(q^v.width*v.afterD) ≤ volume q v ∧
      (v.beforeRows*v.rows*v.beforeH*q^v.width)*v.between ≤ volume q v := by
  rcases hv with ⟨hA,hR,hB,hC,hE⟩
  have hQ : 0 < q^v.width := pow_pos (by omega) _
  have hN : 0 < v.beforeRows*v.rows*v.beforeH*q^v.width :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hA hR) hB) hQ
  have hs : v.between*(q^v.width*v.afterD) ≤ volume q v := by
    have hh := Nat.le_mul_of_pos_left (v.between*(q^v.width*v.afterD)) hN
    convert hh using 1
    simp only [volume]
    ring
  have hp : (v.beforeRows*v.rows*v.beforeH*q^v.width)*v.between ≤ volume q v := by
    have hh := Nat.le_mul_of_pos_right ((v.beforeRows*v.rows*v.beforeH*q^v.width)*v.between) (Nat.mul_pos hQ hE)
    convert hh using 1
    simp only [volume]
    ring
  exact ⟨(Nat.le_mul_of_pos_left (q^v.width*v.afterD) hC).trans hs,hs,hp⟩

theorem constructs_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (target : Target)
    (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (program hq target) (fun w => w = input hs) (fun w => w = output hq hs v target)
      (364*volume q v+145) := by
  have hd := hoare_extend_eq (RecursiveDimensionBank.construct_hoare hq v hs hv hvpos) (tailBank (q := q) ds0)
  obtain ⟨hqe,hcqe,hnc⟩ := products_le hq v hvpos
  cases target
  · have hh := (hd.seq (qe_hoare hq v hs hv hvpos)).seq (cqe_hoare hq v hs hv hvpos)
    exact hh.consequence (fun _ h => h) (fun _ h => h) (by omega)
  · have hh := hd.seq (nc_hoare hq v hs hv hvpos)
    exact hh.consequence (fun _ h => h) (fun _ h => h) (by omega)

def blockBits (v : Descriptor) (hs : Fin 6 → List Bool) : Target → List Bool
  | .h => cqeBits (q := q) v
  | .d => hs 5

def prefixBits (v : Descriptor) : Target → List Bool
  | .h => RecursiveDimensionBank.arbBits v
  | .d => ncBits (q := q) v


end IntegerMultBounds.Machine.RecursiveScalingDimensions
