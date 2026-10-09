import IntegerMultBounds.Machine.BinaryPackedFieldSwap
import IntegerMultBounds.Machine.ActiveTargetHighestValue

/-! Exact conjugation for a highest target bit preceding its source. The two
one-bit fields are exchanged physically by the eventual caller machine. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestLaterValue
noncomputable section
open RadixRangePadding (volume index coordinates transpose)
variable {P G B : ℕ} {α : Type*}

def xorBit (a b : Fin 2) : Fin 2 := ⟨(a.val+b.val)%2,Nat.mod_lt _ (by decide)⟩
theorem xorBit_twice (a b : Fin 2) : xorBit (xorBit a b) b=a := by
  fin_cases a <;> fin_cases b <;> rfl

def earlier (x : Fin (volume P 2 G B) → α) : Fin (volume P 2 G B) → α := fun z =>
  let c := coordinates z
  x (index c.1 c.2.1 c.2.2.1 (xorBit c.2.2.2.1 c.2.1) c.2.2.2.2)
def later (x : Fin (volume P 2 G B) → α) : Fin (volume P 2 G B) → α := fun z =>
  let c := coordinates z
  x (index c.1 (xorBit c.2.1 c.2.2.2.1) c.2.2.1 c.2.2.2.1 c.2.2.2.2)

theorem conjugation (x : Fin (volume P 2 G B) → α) :
    transpose (earlier (transpose x))=later x := by
  funext z
  simp only [transpose,earlier,later,RadixRangePadding.coordinates_index]

theorem later_entry (x : Fin (volume P 2 G B) → α) (p : Fin P)
    (target source : Fin 2) (g : Fin G) (j : Fin B) :
    later x (index p (xorBit target source) g source j)=x (index p target g source j) := by
  simp only [later,RadixRangePadding.coordinates_index,xorBit_twice]

theorem earlier_entry (x : Fin (volume P 2 G B) → α) (p : Fin P)
    (source target : Fin 2) (g : Fin G) (j : Fin B) :
    earlier x (index p source g (xorBit target source) j)=x (index p source g target j) := by
  simp only [earlier,RadixRangePadding.coordinates_index,xorBit_twice]

theorem prefix_eq (G L : ℕ) : ActiveTargetHighestRun.prefixSize G L=2^L*2*2^G := by
  change 2^(G+(1+L))=2^L*2*2^G
  rw [pow_add,pow_add,pow_one]
  ring

theorem size_eq (G L B : ℕ) : ActiveTargetHighestRun.volume G L B=volume (2^L) 2 (2^G) B := by
  change ActiveTargetHighestRun.prefixSize G L*(2*B)=_
  rw [prefix_eq]
  unfold volume
  ring

def prefixIndex (G L : ℕ) (p : Fin (2^L)) (s : Fin 2) (g : Fin (2^G)) :
    Fin (ActiveTargetHighestRun.prefixSize G L) :=
  Fin.cast (prefix_eq G L).symm (RecursiveInterchangeRows.pack (RecursiveInterchangeRows.pack p s) g)

theorem prefixIndex_val (G L : ℕ) (p : Fin (2^L)) (s : Fin 2) (g : Fin (2^G)) :
    (prefixIndex G L p s g).val=(p.val*2+s.val)*2^G+g.val := by
  simp only [prefixIndex,Fin.val_cast,RecursiveInterchangeRows.pack_val]

theorem prefix_control (G L : ℕ) (p : Fin (2^L)) (s : Fin 2) (g : Fin (2^G)) :
    (prefixIndex G L p s g).val/2^G%2=s.val := by
  rw [prefixIndex_val]
  have hd : ((p.val*2+s.val)*2^G+g.val)/2^G=p.val*2+s.val := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by positivity : 0<2^G),Nat.div_eq_of_lt g.isLt]
    simp
  rw [hd]
  omega

theorem fullIndex (G L B : ℕ) (p : Fin (2^L)) (s d : Fin 2) (g : Fin (2^G)) (j : Fin B) :
    Fin.cast (size_eq G L B) (FiberLayoutData.index (prefixIndex G L p s g) d j)=index p s g d j := by
  apply Fin.ext
  change (FiberLayoutData.index (prefixIndex G L p s g) d j).val=(index p s g d j).val
  rw [FiberLayoutData.index_val,prefixIndex_val]
  simp only [index,RecursiveInterchangeRows.pack_val]
  ring

def nativeArray (G L B : ℕ) (x : Fin (volume (2^L) 2 (2^G) B) → Bool) : ActiveTargetHighestRun.Array G L B :=
  fun i => bitSymbol (x (Fin.cast (size_eq G L B) i))

/-- The previously checked physical highest machine is exactly the earlier
one-bit XOR in this literal rectangular view of the original full array. -/
theorem native_array_earlier (G L B : ℕ) (x : Fin (volume (2^L) 2 (2^G) B) → Bool) :
    ActiveTargetHighestRun.array G L (nativeArray G L B x)=nativeArray G L B (earlier x) := by
  funext i
  let z := Fin.cast (size_eq G L B) i
  let c := coordinates z
  have he : index c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2=z := RadixRangePadding.index_coordinates z
  have hi : FiberLayoutData.index (prefixIndex G L c.1 c.2.1 c.2.2.1) c.2.2.2.1 c.2.2.2.2=i := by
    apply Fin.cast_injective (size_eq G L B)
    exact (fullIndex G L B c.1 c.2.1 c.2.2.2.1 c.2.2.1 c.2.2.2.2).trans he
  rw [←hi]
  let d := xorBit c.2.2.2.1 c.2.1
  have h := FlatControlledShiftArray.array_entry (radix := 2) (1 : ℚ)
    ActiveTargetHighestRun.low ActiveTargetHighestRun.high (ActiveTargetHighestRun.width G L)
    (nativeArray G L B x) (prefixIndex G L c.1 c.2.1 c.2.2.1) d c.2.2.2.2
  have hoff := ActiveTargetHighestValue.offset G L (prefixIndex G L c.1 c.2.1 c.2.2.1).val
  rw [ActiveTargetHighestValue.sourceBit_value,prefix_control] at hoff
  rw [hoff] at h
  have hd : (⟨(d.val+c.2.1.val)%2,by omega⟩ : Fin 2)=c.2.2.2.1 := xorBit_twice _ _
  simp only [ActiveTargetHighestRun.width,Matrix.cons_val_zero,pow_one] at h
  rw [hd] at h
  change ActiveTargetHighestRun.array G L (nativeArray G L B x)
    (FiberLayoutData.index _ _ _)=_ at h
  apply h.trans
  have hf1 := fullIndex G L B c.1 c.2.1 d c.2.2.1 c.2.2.2.2
  have hf2 := fullIndex G L B c.1 c.2.1 c.2.2.2.1 c.2.2.1 c.2.2.2.2
  calc
    _ = bitSymbol (x (index c.1 c.2.1 c.2.2.1 d c.2.2.2.2)) := congrArg (fun j => (bitSymbol (x j) : Fin 4)) hf1
    _ = bitSymbol (earlier x (index c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2)) := by
      simp only [earlier,RadixRangePadding.coordinates_index]
      rfl
    _ = _ := (congrArg (fun j => (bitSymbol (earlier x j) : Fin 4)) hf2).symm


end
end IntegerMultBounds.Machine.ActiveTargetHighestLaterValue
