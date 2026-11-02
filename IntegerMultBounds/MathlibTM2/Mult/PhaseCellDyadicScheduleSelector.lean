module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicTransposePlan

/-! Arithmetic random access to the canonical Euclidean schedule. A fixed
machine can recompute a requested row instead of storing a recursive plan. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

@[simp] theorem DyadicTransposePlan.stages_cast_left {a a' b W : ℕ}
    (h : a = a') (plan : DyadicTransposePlan a b W) : (h ▸ plan).stages = plan.stages := by
  subst a'; rfl

@[simp] theorem DyadicTransposePlan.stages_cast_right {a b b' W : ℕ}
    (h : b = b') (plan : DyadicTransposePlan a b W) : (h ▸ plan).stages = plan.stages := by
  subst b'; rfl

def dyadicStageCount : ℕ → ℕ → ℕ → ℕ
  | 0,_,_ => 0
  | fuel+1,a,b =>
      if a = 0 ∨ b = 0 then 0
      else if b ≤ a then 1+dyadicStageCount fuel (a-b) b
      else 1+dyadicStageCount fuel (b-a) a

/-- Independent master values of an equal-field stage. The middle count is
one and both field exponents are `fieldBits`. -/
structure DyadicStageRow where
  outerCount : ℕ
  blockWidth : ℕ
  fieldBits : ℕ

def DyadicStageRow.shape (r : DyadicStageRow) : RectangularChunkSwap :=
  ⟨r.outerCount,2^r.fieldBits,2^r.fieldBits,r.blockWidth⟩

/-- `n` is the remaining stage count. In a right branch the residual schedule
is reversed, so the requested residual index becomes `n-2-i`. -/
def selectDyadicStage : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → DyadicStageRow
  | 0,_,_,_,_,_ => ⟨0,0,0⟩
  | fuel+1,a,b,W,n,i =>
      if a = 0 ∨ b = 0 then ⟨0,0,0⟩
      else if b ≤ a then
        if i = 0 then ⟨2^(a-b),W,b⟩
        else selectDyadicStage fuel (a-b) b (2^b*W) (n-1) (i-1)
      else if i+1 = n then ⟨2^(b-a),W,a⟩
      else selectDyadicStage fuel (b-a) a (2^a*W) (n-1) (n-2-i)

theorem dyadicTransposePlan_stages_length (fuel a b W : ℕ) (h : a+b ≤ fuel) :
    (dyadicTransposePlan fuel a b W h).stages.length = dyadicStageCount fuel a b := by
  induction fuel generalizing a b W with
  | zero => have ha : a = 0 := by omega
            subst a
            simp [dyadicTransposePlan,dyadicStageCount,DyadicTransposePlan.stages]
  | succ fuel ih =>
    by_cases ha : a = 0
    · subst a
      simp [dyadicTransposePlan,dyadicStageCount,DyadicTransposePlan.stages]
    by_cases hb : b = 0
    · subst b
      simp [dyadicTransposePlan,dyadicStageCount,DyadicTransposePlan.stages,ha]
    by_cases hba : b ≤ a
    · simp only [dyadicTransposePlan,ha,hb,↓reduceDIte,dyadicStageCount,
        false_or,ite_false,hba,ite_true,DyadicTransposePlan.stages_cast_left,
        DyadicTransposePlan.stages,List.length_cons]
      rw [ih]
      omega
    · simp only [dyadicTransposePlan,ha,hb,↓reduceDIte,dyadicStageCount,
        false_or,ite_false,hba,DyadicTransposePlan.stages_cast_right,
        DyadicTransposePlan.stages,List.length_append,List.length_map,List.length_reverse,List.length_singleton]
      rw [ih]
      omega

theorem dyadicStageCount_le (fuel a b : ℕ) (h : a+b ≤ fuel) :
    dyadicStageCount fuel a b ≤ a+b := by
  rw [←dyadicTransposePlan_stages_length fuel a b 1 h]
  exact (dyadicTransposePlan fuel a b 1 h).stages_length_le.trans
    (dyadicTransposePlan fuel a b 1 h).widthCharge_le

theorem selectDyadicStage_eq_getElem? (fuel a b W : ℕ) (h : a+b ≤ fuel)
    (i : ℕ) (hi : i < dyadicStageCount fuel a b) :
    (dyadicTransposePlan fuel a b W h).stages[i]? =
      some (selectDyadicStage fuel a b W (dyadicStageCount fuel a b) i).shape := by
  induction fuel generalizing a b W i with
  | zero => simp [dyadicStageCount] at hi
  | succ fuel ih =>
    by_cases ha : a = 0
    · simp [dyadicStageCount,ha] at hi
    by_cases hb : b = 0
    · simp [dyadicStageCount,hb] at hi
    by_cases hba : b ≤ a
    · have hs : a-b+b ≤ fuel := by omega
      have hi' : i < 1+dyadicStageCount fuel (a-b) b := by
        simpa only [dyadicStageCount,ha,hb,false_or,ite_false,hba,ite_true] using hi
      cases i with
      | zero =>
        simp [dyadicTransposePlan,selectDyadicStage,dyadicStageCount,ha,hb,hba,DyadicTransposePlan.stages,DyadicStageRow.shape]
      | succ i =>
        have hh := ih (a-b) b (2^b*W) hs i (by omega)
        simpa [dyadicTransposePlan,selectDyadicStage,dyadicStageCount,ha,hb,hba,
          DyadicTransposePlan.stages,DyadicStageRow.shape] using hh
    · have hs : b-a+a ≤ fuel := by omega
      let rest := dyadicTransposePlan fuel (b-a) a (2^a*W) hs
      have hlen : rest.stages.length = dyadicStageCount fuel (b-a) a :=
        dyadicTransposePlan_stages_length fuel (b-a) a (2^a*W) hs
      have hplan : (dyadicTransposePlan (fuel+1) a b W h).stages =
          (rest.stages.reverse.map RectangularChunkSwap.inverse)++[⟨2^(b-a),2^a,2^a,W⟩] := by
        simp [dyadicTransposePlan,ha,hb,hba,DyadicTransposePlan.stages,rest]
      have hi' : i < 1+dyadicStageCount fuel (b-a) a := by
        simpa only [dyadicStageCount,ha,hb,false_or,ite_false,hba] using hi
      rw [hplan]
      by_cases hlast : i+1 = 1+dyadicStageCount fuel (b-a) a
      · have he : i = rest.stages.length := by omega
        rw [List.getElem?_append_right (by simp only [List.length_map,List.length_reverse]; omega)]
        simp [selectDyadicStage,dyadicStageCount,ha,hb,hba,he,hlen,Nat.add_comm,DyadicStageRow.shape]
      · have hlt : i < rest.stages.length := by omega
        rw [List.getElem?_append_left (by simpa only [List.length_map,List.length_reverse] using hlt),
          List.getElem?_map,List.getElem?_reverse hlt,hlen]
        have hj : dyadicStageCount fuel (b-a) a-1-i < dyadicStageCount fuel (b-a) a := by omega
        have hh := ih (b-a) a (2^a*W) hs (dyadicStageCount fuel (b-a) a-1-i) hj
        change rest.stages[dyadicStageCount fuel (b-a) a-1-i]? = _ at hh
        rw [hh]
        have hn : 1+dyadicStageCount fuel (b-a) a-2-i = dyadicStageCount fuel (b-a) a-1-i := by omega
        simp [selectDyadicStage,dyadicStageCount,ha,hb,hba,hlast,hn,DyadicStageRow.shape,RectangularChunkSwap.inverse]

def DyadicStageRow.values (r : DyadicStageRow) : Fin 5 → ℕ :=
  IntegerMultBounds.MathlibTM2.Host.swapValues r.outerCount 1 r.blockWidth r.fieldBits r.fieldBits

def dyadicSelectedRows (fuel a b W : ℕ) : List DyadicStageRow :=
  (List.range (dyadicStageCount fuel a b)).map
    (selectDyadicStage fuel a b W (dyadicStageCount fuel a b))

theorem dyadicSelectedRows_length (fuel a b W : ℕ) :
    (dyadicSelectedRows fuel a b W).length = dyadicStageCount fuel a b := by
  simp [dyadicSelectedRows]

theorem dyadicSelectedRows_shape (fuel a b W : ℕ) (h : a+b ≤ fuel) :
    (dyadicSelectedRows fuel a b W).map DyadicStageRow.shape =
      (dyadicTransposePlan fuel a b W h).stages := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < dyadicStageCount fuel a b
  · simp only [dyadicSelectedRows,List.getElem?_map,List.getElem?_range hi,Option.map_some]
    exact (selectDyadicStage_eq_getElem? fuel a b W h i hi).symm
  · rw [List.getElem?_eq_none (by simp [dyadicSelectedRows]; omega),
      List.getElem?_eq_none (by rw [dyadicTransposePlan_stages_length]; omega)]

theorem DyadicStageRow.values_list (r : DyadicStageRow) :
    List.ofFn r.values = [r.outerCount,1,r.blockWidth,r.fieldBits,r.fieldBits] := by
  simp [DyadicStageRow.values,IntegerMultBounds.MathlibTM2.Host.swapValues,List.ofFn_succ]

def dyadicScheduleValues (fuel a b W : ℕ) : List ℕ :=
  (dyadicSelectedRows fuel a b W).flatMap (fun r => List.ofFn r.values)

theorem dyadicScheduleValues_length (fuel a b W : ℕ) :
    (dyadicScheduleValues fuel a b W).length = 5*dyadicStageCount fuel a b := by
  simp [dyadicScheduleValues,DyadicStageRow.values_list,List.length_flatMap,
    dyadicSelectedRows_length,Nat.mul_comm]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
