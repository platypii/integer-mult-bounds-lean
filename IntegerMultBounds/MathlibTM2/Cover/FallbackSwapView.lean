module

public import IntegerMultBounds.MathlibTM2.Cover.LabelView
public import IntegerMultBounds.Machine.FlatCoordinateLayout

/-! The interchange descriptor for a swap of two payload address coordinates. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine FlatCoordinateLayout
variable {d q w W : ℕ} [NeZero (q^w)]

def swapView (q w W : ℕ) (i j : Fin d) : RecursiveInterchangeLayout.Descriptor where
  beforeRows := 1
  rows := 1
  beforeH := (q^w)^i.val
  width := w
  between := (q^w)^(j.val-i.val-1)
  afterD := (q^w)^suffixFields j*W

theorem swapView_volume (i j : Fin d) (h : i < j) :
    RecursiveInterchangeLayout.volume q (swapView q w W i j) = (q^w)^d*W := by
  have size : d = i.val+1+(j.val-i.val-1)+1+suffixFields j := by
    unfold suffixFields
    change i.val < j.val at h
    have := j.isLt
    omega
  conv_rhs => rw [size,pow_add,pow_succ,pow_add,pow_succ]
  simp [RecursiveInterchangeLayout.volume,swapView,Nat.mul_assoc]

theorem swapView_apply {α : Type*} (i j : Fin d) (h : i < j) {src dst : ℕ → α}
    (swap : LabelView.Swapped q (swapView q w W i j) src dst)
    (x : Fin d → ZMod (q^w)) (k : Fin W) :
    dst (index (x ∘ Equiv.swap i j) k).val = src (index x k).val := by
  obtain ⟨pre,hpre,mid,hmid,post,hpost,packed⟩ := rank_split_pair x i j h
  have after_lt : post*W+k.val < (q^w)^suffixFields j*W := by nlinarith [k.isLt]
  have atFields := swap 0 (by simp [swapView]) 0 (by simp [swapView]) pre hpre (x j).val (x j).val_lt
    mid hmid (x i).val (x i).val_lt _ after_lt
  simp only [RecursiveInterchangeLayout.index,swapView,Nat.zero_mul,Nat.zero_add] at atFields
  rw [index_swap x i j h k pre mid post packed,index_val,packed]
  convert atFields using 2 <;> ring

end IntegerMultBounds.MathlibTM2.Cover.Fallback
