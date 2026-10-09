import IntegerMultBounds.Machine.ActiveRepairDestinationPatchRun
import IntegerMultBounds.Machine.ActiveRepairRankFieldsGeometry

/-! Destination ranks in the unchanged active-target layout. The full word
includes row, unused front bits, all source/spectator bits and dirty back bits. -/
namespace IntegerMultBounds.Machine.ActiveRepairDestinationPatchGeometry
noncomputable section
open CompactGadgetReservationShape CompactActiveTargetLayout
open ActiveRepairRankFieldsGeometry BinaryAddressTableData
open ActiveRepairDestinationPatchData

private theorem patch_block (pre old post replacement : List Bool)
    (hw : replacement.length=old.length) :
    patch (pre++old++post) pre.length replacement=pre++replacement++post := by
  apply List.ext_getElem
  · simp [hw]
  · intro j hj hj'
    have hj0 : j<(pre++old++post).length := by simpa using hj
    have hd : (patch (pre++old++post) pre.length replacement).getD j false=
        (pre++replacement++post).getD j false := by
      rw [patch_bit _ _ _ j hj0]
      by_cases hpre : j<pre.length
      · rw [ite_eq_right (by omega)]
        rw [List.getD_append _ _ _ _ (by simp; omega),List.getD_append _ _ _ _ hpre,
          List.getD_append _ _ _ _ (by simp; omega),List.getD_append _ _ _ _ hpre]
      · by_cases hmid : j<pre.length+old.length
        · rw [ite_eq_left (by omega)]
          rw [List.getD_append _ _ _ _ (by simp; omega),List.getD_append_right _ _ _ _ (by omega)]
        · rw [ite_eq_right (by omega)]
          rw [List.getD_append_right _ _ _ _ (by simp; omega),List.getD_append_right _ _ _ _ (by simp; omega)]
          simp only [List.length_append,hw]
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,
      List.getElem?_eq_getElem hj',Option.getD_some] using hd

def encode (s : Shape) (w m before after rows rho : ℕ) (x : Address s w m before after rows) : List Bool :=
  row (s.H+s.B) x.back.val ++ row after x.activeAfter.val ++ row m x.target.val ++
  row before x.activeBefore.val ++ row s.F x.frontSlack.val ++ row (s.H-w) x.tTail.val ++
  row w x.t.val ++ row (s.H-w) x.uTail.val ++ row w x.u.val ++ row rho x.row.val

def replaced (s : Shape) (w m before after rows : ℕ) (x : Address s w m before after rows)
    (v : Fin (2^m)) (t u : Fin (2^w)) : Address s w m before after rows :=
  {x with target := v,t := t,u := u}

 theorem encode_length (s : Shape) (w m before after rows rho : ℕ) (hw : w≤s.H)
    (ha : before+m+after=s.active*s.chunk) (x : Address s w m before after rows) :
    (encode s w m before after rows rho x).length=s.bits+rho := by
  simp only [encode,List.length_append,row_length]
  unfold Shape.bits
  omega

 theorem encode_value (s : Shape) (w m before after rows rho : ℕ) (hw : w≤s.H)
    (ha : before+m+after=s.active*s.chunk) (hp : s.payload=1)
    (hr : rows≤2^rho) (x : Address s w m before after rows) :
    Counter.value (encode s w m before after rows rho x)=
      (index s w m before after rows hw ha x).val := by
  have hx : x.row.val<2^rho := lt_of_lt_of_le x.row.isLt hr
  have hpay : x.payload.val=0 := by have h := x.payload.isLt; omega
  rw [index_val]
  simp only [encode,ColumnTransducer.value_append,List.length_append,row_length,
    row_rank _ _ x.back.isLt,row_rank _ _ x.activeAfter.isLt,row_rank _ _ x.target.isLt,
    row_rank _ _ x.activeBefore.isLt,row_rank _ _ x.frontSlack.isLt,row_rank _ _ x.tTail.isLt,
    row_rank _ _ x.t.isLt,row_rank _ _ x.uTail.isLt,row_rank _ _ x.u.isLt,row_rank _ _ hx,
    hp,hpay,mul_one,add_zero,pow_add]
  ring

 theorem patch_target (s : Shape) (w m before after rows rho : ℕ)
    (x : Address s w m before after rows) (v : Fin (2^m)) :
    patch (encode s w m before after rows rho x) (targetStart s after) (row m v.val)=
      encode s w m before after rows rho {x with target := v} := by
  let pre := row (s.H+s.B) x.back.val++row after x.activeAfter.val
  let post := row before x.activeBefore.val++row s.F x.frontSlack.val++row (s.H-w) x.tTail.val++
    row w x.t.val++row (s.H-w) x.uTail.val++row w x.u.val++row rho x.row.val
  have he : encode s w m before after rows rho x=pre++row m x.target.val++post := by
    simp [encode,pre,post,List.append_assoc]
  have hl : pre.length=targetStart s after := by
    simp only [pre,List.length_append,row_length,targetStart,tailBits]
    omega
  rw [he,←hl,patch_block pre (row m x.target.val) post (row m v.val) (by simp)]
  simp [encode,pre,post,List.append_assoc]

 theorem patch_t (s : Shape) (w m before after rows rho : ℕ)
    (x : Address s w m before after rows) (t : Fin (2^w)) :
    patch (encode s w m before after rows rho x) (tStart s w m before after) (row w t.val)=
      encode s w m before after rows rho {x with t := t} := by
  let pre := row (s.H+s.B) x.back.val++row after x.activeAfter.val++row m x.target.val++
    row before x.activeBefore.val++row s.F x.frontSlack.val++row (s.H-w) x.tTail.val
  let post := row (s.H-w) x.uTail.val++row w x.u.val++row rho x.row.val
  have he : encode s w m before after rows rho x=pre++row w x.t.val++post := by
    simp [encode,pre,post,List.append_assoc]
  have hl : pre.length=tStart s w m before after := by
    simp only [pre,List.length_append,row_length,tStart,prefixStart,targetStart,tailBits]
    omega
  rw [he,←hl,patch_block pre (row w x.t.val) post (row w t.val) (by simp)]
  simp [encode,pre,post,List.append_assoc]

 theorem patch_u (s : Shape) (w m before after rows rho : ℕ)
    (x : Address s w m before after rows) (u : Fin (2^w)) :
    patch (encode s w m before after rows rho x) (uStart s w m before after) (row w u.val)=
      encode s w m before after rows rho {x with u := u} := by
  let pre := row (s.H+s.B) x.back.val++row after x.activeAfter.val++row m x.target.val++
    row before x.activeBefore.val++row s.F x.frontSlack.val++row (s.H-w) x.tTail.val++
    row w x.t.val++row (s.H-w) x.uTail.val
  let post := row rho x.row.val
  have he : encode s w m before after rows rho x=pre++row w x.u.val++post := by
    simp [encode,pre,post,List.append_assoc]
  have hl : pre.length=uStart s w m before after := by
    simp only [pre,List.length_append,row_length,uStart,prefixStart,targetStart,tailBits]
    omega
  rw [he,←hl,patch_block pre (row w x.u.val) post (row w u.val) (by simp)]
  simp [encode,pre,post,List.append_assoc]

variable (s : Shape) (w m before after rows rho : ℕ) (hw : w≤s.H)
variable (ha : before+m+after=s.active*s.chunk) (hp : s.payload=1) (hr : rows≤2^rho)
variable (x : Address s w m before after rows) (cs : List Bool)
variable (hc : Counter.value cs=(index s w m before after rows hw ha x).val)

include hw ha hp hr hc in
 theorem initial_eq_encode : ActiveRepairDestinationPatchRun.initial cs (s.bits+rho)=
    encode s w m before after rows rho x := by
  apply CountedPackedGuarded.word_eq_of_length_value
  · simp only [ActiveRepairDestinationPatchRun.initial,Gather.field_length,
      encode_length s w m before after rows rho hw ha x]
  · rw [ActiveRepairDestinationPatchRun.initial,CountedRankSplitData.value_prefix,hc,
      ←encode_value s w m before after rows rho hw ha hp hr x]
    have hb := Counter.value_lt (encode s w m before after rows rho x)
    rw [encode_length s w m before after rows rho hw ha x] at hb
    exact Nat.mod_eq_of_lt hb

include hw ha hp hr hc in
 theorem destination_eq_encode (v : Fin (2^m)) (t u : Fin (2^w)) :
    ActiveRepairDestinationPatchRun.destination cs (row m v.val) (row w t.val) (row w u.val)
      (s.bits+rho) (targetStart s after) (tStart s w m before after) (uStart s w m before after)=
        encode s w m before after rows rho (replaced s w m before after rows x v t u) := by
  unfold ActiveRepairDestinationPatchRun.destination
  rw [initial_eq_encode s w m before after rows rho hw ha hp hr x cs hc,
      patch_target,patch_t,patch_u]
  rfl

include hw ha hp hr hc in
 theorem destination_value (v : Fin (2^m)) (t u : Fin (2^w)) :
    Counter.value (ActiveRepairDestinationPatchRun.destination cs (row m v.val) (row w t.val) (row w u.val)
      (s.bits+rho) (targetStart s after) (tStart s w m before after) (uStart s w m before after))=
        (index s w m before after rows hw ha (replaced s w m before after rows x v t u)).val := by
  rw [destination_eq_encode s w m before after rows rho hw ha hp hr x cs hc v t u]
  exact encode_value s w m before after rows rho hw ha hp hr _

include hw ha in
 theorem fields_fit :
    targetStart s after+m≤s.bits+rho ∧
      tStart s w m before after+w≤s.bits+rho ∧ uStart s w m before after+w≤s.bits+rho := by
  dsimp only [targetStart,tStart,uStart,prefixStart,tailBits,Shape.bits]
  omega

 theorem fields_disjoint :
    targetStart s after+m≤tStart s w m before after ∧
      tStart s w m before after+w≤uStart s w m before after := by
  dsimp only [targetStart,tStart,uStart,prefixStart,tailBits]
  omega

end
end IntegerMultBounds.Machine.ActiveRepairDestinationPatchGeometry
