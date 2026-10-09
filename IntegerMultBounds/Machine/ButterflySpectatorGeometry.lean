import IntegerMultBounds.Machine.ButterflyAxisArray

/-! Arbitrary outer row spectators multiply higher groups, never polynomial
multiplicity or the binary dimension. The literal stream remains row-major. -/
namespace IntegerMultBounds.Machine.ButterflySpectatorGeometry
noncomputable section
open ButterflyAxisHeadersData
open RecursiveChildQuotientsConstant (bits)

def descriptor (rows D t R p : ℕ) :=
  CompactRowHeaders.descriptor (rows*higher D t*2) (rowLength D t R p)
def values (rows D t R p : ℕ) : Fin 6 → ℕ :=
  ![1,rows*higher D t*2,rowLength D t R p,0,1,1]
def headers (rows D t R p : ℕ) : Fin 6 → List Bool := fun i => bits (values rows D t R p i)
def words (rows D t R p : ℕ) (i : Fin 8) : List Bool :=
  Fin.addCases ![bits (rows*pairCount D t R),bits (rows*streamLength D t R p)] (headers rows D t R p) i

abbrev Size (rows D R : ℕ) := rows*(2^D*R)
abbrev Array (rows D R : ℕ) := Fin (Size rows D R) → ButterflyStreamData.Coefficient
abbrev Width (rows D R p : ℕ) (f : Array rows D R) :=
  ∀ i,(f i).1.length=ButterflyGuard.width p D ∧ (f i).2.length=ButterflyGuard.width p D

theorem groups_eq (rows D t R p : ℕ) :
    RecursiveInterchangeRows.groups 2 (descriptor rows D t R p)=rows*higher D t := by
  simp [RecursiveInterchangeRows.groups,descriptor,CompactRowHeaders.descriptor]

theorem size_eq (rows D t R p : ℕ) (ht : t<D) :
    RecursiveInterchangeRows.groups 2 (descriptor rows D t R p)*(2*lower t R)=Size rows D R := by
  rw [groups_eq]
  have he := ButterflyAxisArray.size_eq D t R p ht
  rw [ButterflyAxisHeadersGeometry.groups_eq] at he
  unfold Size ButterflyAxisArray.Size at *
  calc
    _ = rows*(higher D t*(2*lower t R)) := by ring
    _ = _ := by rw [he]

def reshape (rows D t R p : ℕ) (ht : t<D) (f : Array rows D R)
    (h : Fin (RecursiveInterchangeRows.groups 2 (descriptor rows D t R p)))
    (j : Fin 2) (k : Fin (lower t R)) :=
  f (Fin.cast (size_eq rows D t R p ht) (RecursiveInterchangeRows.pack h (RecursiveInterchangeRows.pack j k)))
def unshape (rows D t R p : ℕ) (ht : t<D)
    (xs : Fin (RecursiveInterchangeRows.groups 2 (descriptor rows D t R p)) → Fin 2 → Fin (lower t R) → ButterflyStreamData.Coefficient)
    (i : Fin (Size rows D R)) :=
  ButterflyAxisSerialization.joined xs (Fin.cast (size_eq rows D t R p ht).symm i)

theorem joined_reshape (rows D t R p : ℕ) (ht : t<D) (f : Array rows D R)
    (i : Fin (RecursiveInterchangeRows.groups 2 (descriptor rows D t R p)*(2*lower t R))) :
    ButterflyAxisSerialization.joined (reshape rows D t R p ht f) i=f (Fin.cast (size_eq rows D t R p ht) i) := by
  have hi : RecursiveInterchangeRows.pack (finProdFinEquiv.symm i).1
      (RecursiveInterchangeRows.pack (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1
        (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2)=i := by
    rw [show RecursiveInterchangeRows.pack (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1
        (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2=(finProdFinEquiv.symm i).2 from
      finProdFinEquiv.apply_symm_apply _]
    exact finProdFinEquiv.apply_symm_apply i
  exact congrArg (fun k => f (Fin.cast (size_eq rows D t R p ht) k)) hi

/-- A physical higher group factors into its unchanged outer row and the
ordinary binary high coordinate; every paired record stays in that same row. -/
theorem reshape_row (rows D t R p : ℕ) (ht : t<D) (f : Array rows D R)
    (row : Fin rows) (h : Fin (ButterflyAxisHeadersData.higher D t))
    (j : Fin 2) (k : Fin (lower t R)) :
    reshape rows D t R p ht f
      (Fin.cast (groups_eq rows D t R p).symm (RecursiveInterchangeRows.pack row h)) j k=
      ButterflyAxisArray.reshape D t R p ht
        (fun i => f (RecursiveInterchangeRows.pack row i))
        (Fin.cast (ButterflyAxisHeadersGeometry.groups_eq D t R p).symm h) j k := by
  unfold reshape ButterflyAxisArray.reshape
  apply congrArg f
  apply Fin.ext
  simp only [Fin.val_cast,RecursiveInterchangeRows.pack_val]
  have he := ButterflyAxisArray.size_eq D t R p ht
  rw [ButterflyAxisHeadersGeometry.groups_eq] at he
  unfold ButterflyAxisArray.Size at he
  rw [←he]
  ring

theorem unshape_reshape (rows D t R p : ℕ) (ht : t<D) (f : Array rows D R) :
    unshape rows D t R p ht (reshape rows D t R p ht f)=f := by
  funext i
  rw [unshape,joined_reshape]
  simp

theorem word_unshape (rows D t R p : ℕ) (ht : t<D)
    (xs : Fin (RecursiveInterchangeRows.groups 2 (descriptor rows D t R p)) → Fin 2 → Fin (lower t R) → ButterflyStreamData.Coefficient) :
    ButterflyAxisBank.word xs=ButterflyStreamData.full (fun _ => blank) 0 (unshape rows D t R p ht xs) := by
  unfold ButterflyAxisBank.word ButterflyStreamData.full unshape
  rw [List.ofFn_congr (size_eq rows D t R p ht) (fun i => ButterflyStreamData.encoded (ButterflyAxisSerialization.joined xs i))]

theorem source_word (rows D t R p : ℕ) (ht : t<D) (f : Array rows D R) :
    ButterflyAxisBank.word (reshape rows D t R p ht f)=ButterflyStreamData.full (fun _ => blank) 0 f := by
  rw [word_unshape rows D t R p ht,unshape_reshape]

def applyAxis (rows D t R p : ℕ) (ht : t<D) (f : Array rows D R) :=
  unshape rows D t R p ht (ButterflyStreamSemantics.transformed (reshape rows D t R p ht f))

theorem width_apply (rows D t R p : ℕ) (ht : t<D) (f : Array rows D R) (hw : Width rows D R p f) :
    Width rows D R p (applyAxis rows D t R p ht f) := by
  intro i
  unfold applyAxis unshape ButterflyAxisSerialization.joined
  exact ButterflyStreamSemantics.transformed_width (reshape rows D t R p ht f) (ButterflyGuard.width p D)
    (fun h j k => hw _) _ _ _

theorem row_length (rows D t R p : ℕ) :
    RecursiveInterchangeRows.rowLength 2 (descriptor rows D t R p)=lower t R*(2*(ButterflyGuard.width p D+1)) := by
  simp [RecursiveInterchangeRows.rowLength,descriptor,CompactRowHeaders.descriptor,rowLength,recordLength,width_eq,Nat.mul_comm]

theorem positive (rows D t R p : ℕ) (hr : 0<rows) (hR : 0<R) : (descriptor rows D t R p).Positive := by
  have hH : 0<higher D t := pow_pos (by decide) _
  simp only [descriptor,CompactRowHeaders.descriptor,RecursiveInterchangeLayout.Descriptor.Positive]
  refine ⟨by decide,by positivity,?_,by decide,by decide⟩
  unfold rowLength lower recordLength
  positivity

theorem divides (rows D t R p : ℕ) : 2 ∣ (descriptor rows D t R p).rows := dvd_mul_left _ _

theorem headers_spec (rows D t R p : ℕ) :
    RecursiveDimensionBank.Headers (descriptor rows D t R p) (headers rows D t R p) := by
  constructor
  · intro i
    fin_cases i <;> simp [headers,values,descriptor,CompactRowHeaders.descriptor,
      RecursiveDimensionBank.values,RecursiveChildQuotientsConstant.bits_value]
  · intro i; exact RecursiveChildQuotientsConstant.bits_canonical _

theorem paired_count (rows D t R p : ℕ) :
    Counter.value (words rows D t R p 0)=RecursiveInterchangeRows.groups 2 (descriptor rows D t R p)*lower t R := by
  simp [words,groups_eq,pairCount,RecursiveChildQuotientsConstant.bits_value,Fin.addCases,Nat.mul_assoc]

theorem stream_count (rows D t R p : ℕ) :
    Counter.value (words rows D t R p 1)=ButterflyStreamCleanData.streamLength
      (RecursiveInterchangeRows.groups 2 (descriptor rows D t R p)*lower t R) (ButterflyGuard.width p D) := by
  simp [words,groups_eq,streamLength,rowLength,recordLength,ButterflyStreamCleanData.streamLength,
    width_eq,RecursiveChildQuotientsConstant.bits_value,Fin.addCases]
  ring

theorem canonical (rows D t R p : ℕ) (i : Fin 8) : GrowingCounterData.Canonical (words rows D t R p i) := by
  induction i using (Fin.addCases (m:=2) (n:=6)) with
  | left i => fin_cases i <;> exact RecursiveChildQuotientsConstant.bits_canonical _
  | right i => simpa only [words,Fin.addCases_right,headers] using RecursiveChildQuotientsConstant.bits_canonical (values rows D t R p i)

end
end IntegerMultBounds.Machine.ButterflySpectatorGeometry
