import IntegerMultBounds.Machine.RecursiveRowsQuotient
import IntegerMultBounds.Machine.RecursiveScalingDimensions
import IntegerMultBounds.Machine.RecursiveInterchangeRows

/-! Derive cyclic split/merge counters from six original recursive headers.
The fixed role divisor is written on tape, divided, and erased; all products
are produced by actual fixed programs. No derived counter is supplied. -/
namespace IntegerMultBounds.Machine.RecursiveRowsDimensions
open RecursiveInterchangeLayout (Descriptor volume)
variable {q : ℕ} (hq : 2 ≤ q)
noncomputable section

def scalingPlacement : Fin (16+22) ≃ Fin 38 where
  toFun := ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
  invFun := ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def extra (rs : List Bool) : Tapes 22 q where
  head i := if i = 0 then 1 else 0
  tape i := if i = 0 then RadixZeroFill.encodedBinary rs else fun _ => blank

def scaled (hs : Fin 6 → List Bool) (v : Descriptor) (rs : List Bool) : Tapes 38 q :=
  ((RecursiveScalingDimensions.output hq hs v .h).append (extra rs)).reindex scalingPlacement

def products (base : Tapes 38 q) (ds : Fin 3 → Option (List Bool)) : Tapes 38 q where
  head i := if i = 17 then RecursiveDimensionBank.head (ds 0)
    else if i = 18 then RecursiveDimensionBank.head (ds 1)
    else if i = 19 then RecursiveDimensionBank.head (ds 2) else base.head i
  tape i := if i = 17 then RecursiveDimensionBank.tape (ds 0)
    else if i = 18 then RecursiveDimensionBank.tape (ds 1)
    else if i = 19 then RecursiveDimensionBank.tape (ds 2) else base.tape i

def bqBits (v : Descriptor) := DimensionProductDescriptor.bits v.beforeH (q^v.width)
def rowBits (v : Descriptor) := DimensionProductDescriptor.bits (v.beforeH*q^v.width) (v.between*(q^v.width*v.afterD))
def groupBits (roles : ℕ) (v : Descriptor) := DimensionProductDescriptor.bits v.beforeRows (v.rows/roles)

def ds0 : Fin 3 → Option (List Bool) := ![none,none,none]
def ds1 (v : Descriptor) : Fin 3 → Option (List Bool) := ![some (bqBits (q := q) v),none,none]
def ds2 (v : Descriptor) : Fin 3 → Option (List Bool) := ![some (bqBits (q := q) v),some (rowBits (q := q) v),none]
def ds3 (roles : ℕ) (v : Descriptor) : Fin 3 → Option (List Bool) :=
  ![some (bqBits (q := q) v),some (rowBits (q := q) v),some (groupBits roles v)]

def output (roles : ℕ) (hs : Fin 6 → List Bool) (v : Descriptor) (rs : List Bool) :=
  products (scaled hq hs v rs) (ds3 (q := q) roles v)

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

theorem scaling_hoare (hs : Fin 6 → List Bool) (v : Descriptor) (rs : List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) :
    HoareTime (Placement.placed (RecursiveScalingDimensions.program hq .h) scalingPlacement)
      (fun w => w = RecursiveChildQuotients.bank hs none (some rs) none)
      (fun w => w = products (scaled hq hs v rs) ds0) (364*volume q v+145) := by
  have h := hoare_place (RecursiveScalingDimensions.constructs_hoare hq v hs .h hv hp)
    scalingPlacement (extra (q := q) rs)
  have hi : ((RecursiveScalingDimensions.input hs).append (extra (q := q) rs)).reindex scalingPlacement =
      RecursiveChildQuotients.bank hs none (some rs) none := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [Tapes.append,scalingPlacement,extra,
        RecursiveChildQuotients.headerTape,RecursiveChildQuotients.headerHead,
        BinaryDescriptorStackRoundtrip.descriptor_encoded] <;> rfl
  have ho : scaled hq hs v rs = products (scaled hq hs v rs) ds0 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  exact h.consequence (fun _ hw => hw.trans hi.symm) (fun _ hw => hw.trans ho) le_rfl

def bqPlacement : Fin (6+32) ≃ Fin 38 where
  toFun := ![0,17,1,9,2,5,3,4,6,7,8,10,11,12,13,14,15,16,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
  invFun := ![0,2,4,6,7,5,8,9,10,3,11,12,13,14,15,16,17,1,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def bqProgram : Program 38 40 q := Placement.placed DimensionProductDescriptor.program bqPlacement

def rowPlacement : Fin (6+32) ≃ Fin 38 where
  toFun := ![0,18,1,15,2,17,3,4,5,6,7,8,9,10,11,12,13,14,16,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
  invFun := ![0,2,4,6,7,8,9,10,11,12,13,14,15,16,17,3,18,5,1,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def rowProgram : Program 38 40 q := Placement.placed DimensionProductDescriptor.program rowPlacement

def groupPlacement : Fin (6+32) ≃ Fin 38 where
  toFun := ![0,19,1,10,2,3,4,5,6,7,8,9,11,12,13,14,15,16,17,18,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
  invFun := ![0,2,4,5,6,7,8,9,10,11,3,12,13,14,15,16,17,18,19,1,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def groupProgram : Program 38 40 q := Placement.placed DimensionProductDescriptor.program groupPlacement

private theorem bq_frame (base : Tapes 38 q) (v : Descriptor) (_roles : ℕ) :
    Placement.extra bqPlacement (products base (ds0)) =
      Placement.extra bqPlacement (products base (ds1 (q := q) v)) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem row_frame (base : Tapes 38 q) (v : Descriptor) (_roles : ℕ) :
    Placement.extra rowPlacement (products base (ds1 (q := q) v)) =
      Placement.extra rowPlacement (products base (ds2 (q := q) v)) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem group_frame (base : Tapes 38 q) (v : Descriptor) (roles : ℕ) :
    Placement.extra groupPlacement (products base (ds2 (q := q) v)) =
      Placement.extra groupPlacement (products base (ds3 (q := q) roles v)) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem bq_hoare (hs : Fin 6 → List Bool) (v : Descriptor) (rs : List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) :
    HoareTime (bqProgram (q := q)) (fun w => w = products (scaled hq hs v rs) ds0)
      (fun w => w = products (scaled hq hs v rs) (ds1 (q := q) v)) (53*(v.beforeH*q^v.width)+28) := by
  have h := DimensionProductDescriptor.construct_hoare (q := q) (RecursiveDimensionBank.qBits hq v) (hs 2)
    v.beforeH (q^v.width) (pow_pos (by omega) _) (RadixPowerDescriptor.bits_value _ _)
    (hv.1 2) (RadixPowerDescriptor.bits_canonical _ _) (hv.2 2)
  apply placed_exact bqPlacement _ _ _ _ _ _ (bq_frame _ v 0) h
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem row_hoare (hs : Fin 6 → List Bool) (v : Descriptor) (rs : List Bool) (hp : v.Positive) :
    HoareTime (rowProgram (q := q)) (fun w => w = products (scaled hq hs v rs) (ds1 (q := q) v))
      (fun w => w = products (scaled hq hs v rs) (ds2 (q := q) v))
      (53*((v.beforeH*q^v.width)*(v.between*(q^v.width*v.afterD)))+28) := by
  have h := DimensionProductDescriptor.construct_hoare (q := q) (RecursiveScalingDimensions.cqeBits (q := q) v)
    (bqBits (q := q) v) (v.beforeH*q^v.width) (v.between*(q^v.width*v.afterD))
    (Nat.mul_pos hp.2.2.2.1 (Nat.mul_pos (pow_pos (by omega) _) hp.2.2.2.2))
    (DimensionProductDescriptor.bits_value _ _) (DimensionProductDescriptor.bits_value _ _)
    (DimensionProductDescriptor.bits_canonical _ _) (DimensionProductDescriptor.bits_canonical _ _)
  apply placed_exact rowPlacement _ _ _ _ _ _ (row_frame _ v 0) h
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem group_hoare (roles : ℕ) (hs : Fin 6 → List Bool) (v : Descriptor) (rs : List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (hrc : GrowingCounterData.Canonical rs)
    (hrv : Counter.value rs = v.rows/roles) (hrpos : 0 < v.rows/roles) :
    HoareTime (groupProgram (q := q)) (fun w => w = products (scaled hq hs v rs) (ds2 (q := q) v))
      (fun w => w = output hq roles hs v rs) (53*(v.beforeRows*(v.rows/roles))+28) := by
  have h := DimensionProductDescriptor.construct_hoare (q := q) rs (hs 0) v.beforeRows (v.rows/roles)
    hrpos hrv (hv.1 0) hrc (hv.2 0)
  apply placed_exact groupPlacement _ _ _ _ _ _ (group_frame _ v roles) h
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def program (roles : ℕ) := seq (seq (seq (seq (RecursiveRowsQuotient.program (a := q) roles)
  (Placement.placed (RecursiveScalingDimensions.program hq .h) scalingPlacement)) bqProgram) rowProgram) groupProgram


theorem products_le (hq : 2 ≤ q) (roles : ℕ) (v : Descriptor) (hp : v.Positive) :
    v.beforeH*q^v.width ≤ volume q v ∧
    (v.beforeH*q^v.width)*(v.between*(q^v.width*v.afterD)) ≤ volume q v ∧
    v.beforeRows*(v.rows/roles) ≤ volume q v := by
  have hQ : 0 < q^v.width := pow_pos (by omega) _
  have hrow : 0 < (v.beforeH*q^v.width)*(v.between*(q^v.width*v.afterD)) := by
    rcases hp with ⟨ha,hr,hb,hc,he⟩
    positivity
  have hrowle : (v.beforeH*q^v.width)*(v.between*(q^v.width*v.afterD)) ≤ volume q v := by
    have h := Nat.le_mul_of_pos_left ((v.beforeH*q^v.width)*(v.between*(q^v.width*v.afterD))) (Nat.mul_pos hp.1 hp.2.1)
    convert h using 1
    unfold volume
    ring
  refine ⟨(Nat.le_mul_of_pos_right _ (Nat.mul_pos hp.2.2.2.1 (Nat.mul_pos hQ hp.2.2.2.2))).trans hrowle,hrowle,?_⟩
  have h := (Nat.mul_le_mul_left v.beforeRows (Nat.div_le_self v.rows roles)).trans
    (Nat.le_mul_of_pos_right (v.beforeRows*v.rows) hrow)
  convert h using 1
  unfold volume
  ring

def bound (roles V : ℕ) := (RecursiveRowsQuotient.constant roles+523)*V+233

/-- Complete physical counter setup. The only initially nonblank tapes are
six original headers, and program control depends on q and roles only. -/
theorem constructs_hoare (roles : ℕ) (hr : 0 < roles) (hs : Fin 6 → List Bool) (v : Descriptor)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) (hd : roles ∣ v.rows) :
    ∃ rs : List Bool, GrowingCounterData.Canonical rs ∧ Counter.value rs = v.rows/roles ∧
      rs.length ≤ (hs 1).length ∧
      HoareTime (program hq roles) (fun w => w = RecursiveChildQuotients.input hs)
        (fun w => w = output hq roles hs v rs) (bound roles (volume q v)) := by
  obtain ⟨rs,hrc,hrv,hlen,hquot⟩ := RecursiveRowsQuotient.quotient_hoare (a := q) roles hr hs
  have hvrow : Counter.value (hs 1) = v.rows := hv.1 1
  rw [hvrow] at hrv
  have hrpos : 0 < v.rows/roles := Nat.div_pos (Nat.le_of_dvd hp.2.1 hd) hr
  have h := (((hquot.seq (scaling_hoare hq hs v rs hv hp)).seq (bq_hoare hq hs v rs hv)).seq
    (row_hoare hq hs v rs hp)).seq (group_hoare hq roles hs v rs hv hrc hrv hrpos)
  have hV : 0 < volume q v := by
    have hQ : 0 < q^v.width := pow_pos (by omega) _
    rcases hp with ⟨ha,hrow,hb,hc,he⟩
    unfold volume
    positivity
  have hc := RecursiveRowsQuotient.cost_linear roles hs (volume q v) hV (hv.2 1)
    (by rw [hvrow]; exact RecursiveHeaderBounds.values_le_volume hq v hp 1)
  obtain ⟨hb,hl,hg⟩ := products_le hq roles v hp
  refine ⟨rs,hrc,hrv,hlen,h.consequence (fun _ h => h) (fun _ h => h) ?_⟩
  unfold bound
  simp only [Nat.add_mul]
  omega

def words (roles : ℕ) (v : Descriptor) : Fin 2 → List Bool := ![rowBits (q := q) v,groupBits roles v]
def sourceSlots : Fin 2 → Fin 38 := ![18,19]

theorem ready (roles : ℕ) (hs : Fin 6 → List Bool) (v : Descriptor) (rs : List Bool) (j : Fin 2) :
    (output hq roles hs v rs).head (sourceSlots j) = 1 ∧
    (output hq roles hs v rs).tape (sourceSlots j) = RadixZeroFill.encodedBinary (words (q := q) roles v j) := by
  fin_cases j <;> exact ⟨rfl,rfl⟩

theorem words_value (roles : ℕ) (v : Descriptor) :
    Counter.value (words (q := q) roles v 0) = RecursiveInterchangeRows.rowLength q v ∧
    Counter.value (words (q := q) roles v 1) = RecursiveInterchangeRows.groups roles v := by
  constructor
  · simp only [words,Matrix.cons_val_zero,rowBits,DimensionProductDescriptor.bits_value,RecursiveInterchangeRows.rowLength]
    ring
  · exact DimensionProductDescriptor.bits_value _ _

theorem words_canonical (roles : ℕ) (v : Descriptor) (j : Fin 2) :
    GrowingCounterData.Canonical (words (q := q) roles v j) := by
  fin_cases j <;> exact DimensionProductDescriptor.bits_canonical _ _

theorem words_length (hq : 2 ≤ q) (roles : ℕ) (v : Descriptor) (hp : v.Positive) (j : Fin 2) :
    (words (q := q) roles v j).length ≤ 2*volume q v := by
  obtain ⟨_,hl,hg⟩ := products_le hq roles v hp
  have hv : Counter.value (words (q := q) roles v j) ≤ volume q v := by
    fin_cases j
    · exact (DimensionProductDescriptor.bits_value _ _).trans_le hl
    · exact (DimensionProductDescriptor.bits_value _ _).trans_le hg
  have hV : 0 < volume q v := by
    have hQ : 0 < q^v.width := pow_pos (by omega) _
    rcases hp with ⟨ha,hr,hb,hc,he⟩
    unfold volume
    positivity
  have hw := GrowingCounterData.canonical_width _ (words_canonical (q := q) roles v j)
  have ht := Nat.log2_le_self (Counter.value (words (q := q) roles v j))
  omega

def headerSlot (j : Fin 6) : Fin 38 := ⟨3+j.val,Nat.lt_trans (Nat.add_lt_add_left j.isLt 3) (by decide)⟩

theorem headers_preserved (roles : ℕ) (hs : Fin 6 → List Bool) (v : Descriptor) (rs : List Bool) (j : Fin 6) :
    (output hq roles hs v rs).head (headerSlot j) = 1 ∧
    (output hq roles hs v rs).tape (headerSlot j) = RadixZeroFill.encodedBinary (hs j) := by
  fin_cases j <;> exact ⟨rfl,rfl⟩

theorem input_header (hs : Fin 6 → List Bool) (j : Fin 6) :
    (RecursiveChildQuotients.input (a := q) hs).head (headerSlot j) = 1 ∧
    (RecursiveChildQuotients.input (a := q) hs).tape (headerSlot j) = RadixZeroFill.encodedBinary (hs j) := by
  fin_cases j <;> constructor <;> first | rfl | exact BinaryDescriptorStackRoundtrip.descriptor_encoded _

theorem input_blank (hs : Fin 6 → List Bool) (i : Fin 38) (hi : ¬ (3 ≤ i.val ∧ i.val < 9)) :
    (RecursiveChildQuotients.input (a := q) hs).head i = 0 ∧
    (RecursiveChildQuotients.input (a := q) hs).tape i = fun _ => blank := by
  fin_cases i <;> first | exact ⟨rfl,rfl⟩ | (exfalso; exact hi (by decide))

end
end IntegerMultBounds.Machine.RecursiveRowsDimensions
