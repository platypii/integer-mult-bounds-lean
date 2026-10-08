import IntegerMultBounds.Machine.RecursiveScalingDimensions
import IntegerMultBounds.Machine.SharedPlacementAlphabet

/-! A fixed physical constructor for the entire seven-factor stream volume.
The existing H-scaling dimensions produce N=A*rows*B*Q and C*Q*E; one actual
product emits their product V, then a one-step program initializes the XOR clock.
Six original canonical headers are retained. Private generated dimensions are
still present here and are erased by the separate clean wrapper. -/
namespace IntegerMultBounds.Machine.RecursiveVolumeConstruct
open RecursiveInterchangeLayout (Descriptor volume)
variable {q : ℕ} (hq : 2 ≤ q)

def bits (v : Descriptor) : List Bool :=
  DimensionProductDescriptor.bits (v.beforeRows*v.rows*v.beforeH*q^v.width)
    (v.between*(q^v.width*v.afterD))

theorem bits_value (v : Descriptor) : Counter.value (bits (q := q) v) = volume q v := by
  rw [bits,DimensionProductDescriptor.bits_value]
  unfold volume
  ring

theorem bits_canonical (v : Descriptor) : GrowingCounterData.Canonical (bits (q := q) v) :=
  DimensionProductDescriptor.bits_canonical _ _

def tailBank (bs : Option (List Bool)) : Tapes 1 q :=
  ⟨fun _ => RecursiveDimensionBank.head bs,fun _ => RecursiveDimensionBank.tape bs⟩

def input (hs : Fin 6 → List Bool) : Tapes 17 q :=
  (RecursiveScalingDimensions.input hs).append (tailBank none)

def bank (hs : Fin 6 → List Bool) (v : Descriptor) (bs : Option (List Bool)) : Tapes 17 q :=
  (RecursiveScalingDimensions.output hq hs v .h).append (tailBank bs)

def productPlacement : Fin (6+11) ≃ Fin 17 where
  toFun := ![0,16,1,14,2,12,3,4,5,6,7,8,9,10,11,13,15]
  invFun := ![0,2,4,6,7,8,9,10,11,12,13,14,5,15,3,16,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def productProgram : Program 17 40 q := Placement.placed DimensionProductDescriptor.program productPlacement

private theorem product_hoare (v : Descriptor) (hs : Fin 6 → List Bool) (hp : v.Positive) :
    HoareTime (productProgram (q := q)) (fun w => w = bank hq hs v none)
      (fun w => w = bank hq hs v (some (bits (q := q) v))) (53*volume q v+28) := by
  have hh := DimensionProductDescriptor.construct_hoare (q := q)
    (RecursiveScalingDimensions.cqeBits (q := q) v) (RecursiveDimensionBank.nBits (q := q) v)
    (v.beforeRows*v.rows*v.beforeH*q^v.width) (v.between*(q^v.width*v.afterD))
    (Nat.mul_pos hp.2.2.2.1 (Nat.mul_pos (pow_pos (by omega) _) hp.2.2.2.2))
    (DimensionProductDescriptor.bits_value _ _) (DimensionProductDescriptor.bits_value _ _)
    (DimensionProductDescriptor.bits_canonical _ _) (DimensionProductDescriptor.bits_canonical _ _)
  have hi : Placement.active productPlacement (bank hq hs v none) =
      DimensionProductDescriptor.input (RecursiveScalingDimensions.cqeBits (q := q) v)
        (RecursiveDimensionBank.nBits (q := q) v) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have ho : Placement.active productPlacement (bank hq hs v (some (bits (q := q) v))) =
      DimensionProductDescriptor.output (RecursiveScalingDimensions.cqeBits (q := q) v)
        (RecursiveDimensionBank.nBits (q := q) v)
        (v.beforeRows*v.rows*v.beforeH*q^v.width) (v.between*(q^v.width*v.afterD)) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hf : Placement.extra productPlacement (bank hq hs v none) =
      Placement.extra productPlacement (bank hq hs v (some (bits (q := q) v))) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  apply (Placement.hoare_at hh productPlacement _ hi).consequence (fun _ h => h) ?_ ?_
  · rintro x ⟨y,rfl,rfl⟩
    rw [Placement.replace,hf,← ho]
    exact Placement.view _ _
  · unfold volume
    ring_nf
    exact le_rfl

/-- Write the marker and move the previously blank clock from zero to one. -/
def clockProgram : Program 17 2 q where
  tapes_pos := by decide
  start := 0
  transition := fun s sy => if s = 0 then
    some (1,fun i => if i = 0 then (separator,.right) else (sy i,.stay)) else none

def output (hs : Fin 6 → List Bool) (v : Descriptor) : Tapes 17 q :=
  SharedPlacementAlphabet.setTape (bank hq hs v (some (bits (q := q) v))) 0 CountedLoopReuseAlphabet.empty 1

private theorem clock_hoare (v : Descriptor) (hs : Fin 6 → List Bool) :
    HoareTime (clockProgram (q := q)) (fun w => w = bank hq hs v (some (bits (q := q) v)))
      (fun w => w = output hq hs v) 1 := by
  rintro w rfl
  refine ⟨1,⟨1,(output hq hs v).head,(output hq hs v).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,clockProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i
      by_cases hi : i = 0
      · subst i; rfl
      · simp [output,SharedPlacementAlphabet.setTape,hi,Move.offset]
    · funext i z
      by_cases hi : i = 0
      · subst i
        have hhead : (bank hq hs v (some (bits (q := q) v))).head 0 = 0 := rfl
        have htape : (bank hq hs v (some (bits (q := q) v))).tape 0 = fun _ => blank := rfl
        by_cases hz : z = 0 <;>
          simp [output,SharedPlacementAlphabet.setTape,CountedLoopReuseAlphabet.empty,hz,hhead,htape]
      · by_cases hz : z = (bank hq hs v (some (bits (q := q) v))).head i <;>
          simp [output,SharedPlacementAlphabet.setTape,hi,hz]
  · simp [step,clockProgram]

def program : Program 17 295 q :=
  seq (seq (extend (RecursiveScalingDimensions.program hq .h) 1) productProgram) clockProgram

theorem constructs_hoare (v : Descriptor) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) :
    HoareTime (program hq) (fun w => w = input hs) (fun w => w = output hq hs v)
      (417*volume q v+176) := by
  have hd := hoare_extend_eq (RecursiveScalingDimensions.constructs_hoare hq v hs .h hv hp) (tailBank (q := q) none)
  exact ((hd.seq (product_hoare hq v hs hp)).seq (clock_hoare hq v hs)).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.RecursiveVolumeConstruct
