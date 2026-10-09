import IntegerMultBounds.Machine.ActiveTargetHighestPairLayoutGeometry

/-! Literal finite-word split at one selected bit, retaining both surrounding
intervals. These are coordinate equalities, with no machine assumptions. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestBits
open RecursiveInterchangeRows (pack pack_val)
open ActiveTargetHighestLaterValue (xorBit)

theorem rectangle_val {P N G B : ℕ} (p : Fin P) (a : Fin N) (g : Fin G) (b : Fin N) (j : Fin B) :
    (RadixRangePadding.index p a g b j).val=((((p.val*N+a.val)*G+g.val)*N+b.val)*B+j.val) := by
  simp only [RadixRangePadding.index,pack_val]

def Parts (width pos : ℕ) := (Fin (2^(width-pos-1)) × Fin 2) × Fin (2^pos)
theorem size (width pos : ℕ) (h : pos<width) :
    (2^(width-pos-1)*2)*2^pos=2^width := by
  have he : width-pos-1+1+pos=width := by omega
  calc
    _ = 2^(width-pos-1+1+pos) := by simp only [pow_add,pow_one]
    _ = _ := by rw [he]

def equiv (width pos : ℕ) (h : pos<width) : Parts width pos ≃ Fin (2^width) :=
  ((finProdFinEquiv.prodCongr (Equiv.refl _)).trans finProdFinEquiv).trans (finCongr (size width pos h))
def split (width pos : ℕ) (h : pos<width) (x : Fin (2^width)) := (equiv width pos h).symm x
def join (width pos : ℕ) (h : pos<width) (x : Parts width pos) := equiv width pos h x

theorem join_val (width pos : ℕ) (h : pos<width) (x : Parts width pos) :
    (join width pos h x).val=(x.1.1.val*2+x.1.2.val)*2^pos+x.2.val := by
  change (pack (pack x.1.1 x.1.2) x.2).val=_
  simp only [pack_val]

theorem split_join (width pos : ℕ) (h : pos<width) (x : Parts width pos) :
    split width pos h (join width pos h x)=x := (equiv width pos h).symm_apply_apply x

theorem join_split (width pos : ℕ) (h : pos<width) (x : Fin (2^width)) :
    join width pos h (split width pos h x)=x := (equiv width pos h).apply_symm_apply x

theorem split_val (width pos : ℕ) (h : pos<width) (x : Fin (2^width)) :
    ((split width pos h x).1.1.val*2+(split width pos h x).1.2.val)*2^pos+
      (split width pos h x).2.val=x.val := by
  rw [←join_val width pos h (split width pos h x),join_split]

def toggle (width pos : ℕ) (h : pos<width) (source : Fin 2) (x : Fin (2^width)) :=
  let c := split width pos h x
  join width pos h ((c.1.1,xorBit c.1.2 source),c.2)

theorem split_toggle (width pos : ℕ) (h : pos<width) (source : Fin 2) (x : Fin (2^width)) :
    split width pos h (toggle width pos h source x)=
      (((split width pos h x).1.1,xorBit (split width pos h x).1.2 source),(split width pos h x).2) :=
  split_join width pos h _

theorem toggle_twice (width pos : ℕ) (h : pos<width) (source : Fin 2) (x : Fin (2^width)) :
    toggle width pos h source (toggle width pos h source x)=x := by
  change join width pos h
    (((split width pos h (toggle width pos h source x)).1.1,
      xorBit (split width pos h (toggle width pos h source x)).1.2 source),
      (split width pos h (toggle width pos h source x)).2)=x
  rw [split_toggle]
  simp only [ActiveTargetHighestLaterValue.xorBit_twice]
  exact join_split width pos h x

theorem source_value (width pos : ℕ) (h : pos<width) (x : Fin (2^width)) :
    (split width pos h x).1.2.val=x.val/2^pos%2 := by
  rw [←split_val width pos h x,Nat.add_comm,Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (split width pos h x).2.isLt]
  have := (split width pos h x).1.2.isLt
  omega

end IntegerMultBounds.Machine.ActiveTargetHighestBits
