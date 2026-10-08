import IntegerMultBounds.Machine.RecursiveInterchangeLayout

/-! Literal row-major coordinate views for all ordered affine shifts. The first
selected field is the earlier control and the second the later target. They
may both lie inside H, both inside D, or on opposite sides of the original
middle spectator factor. These equalities move no payload symbols; physical
construction and replacement of the six headers require separate programs. -/
namespace IntegerMultBounds.Machine.RecursiveAffineViews
open RecursiveInterchangeLayout (Descriptor volume index child)
variable (q b : ℕ) {m : ℕ}

/-- Select H-control j and H-target i, with j < i. -/
def withinH (v : Descriptor) (j i : Fin m) : Descriptor where
  beforeRows := v.beforeRows
  rows := v.rows
  beforeH := v.beforeH*q^(j.val*b)
  width := b
  between := q^((i.val-j.val-1)*b)
  afterD := q^((m-1-i.val)*b)*v.between*q^(m*b)*v.afterD

/-- Select D-control j and D-target i, with j < i. -/
def withinD (v : Descriptor) (j i : Fin m) : Descriptor where
  beforeRows := v.beforeRows
  rows := v.rows
  beforeH := v.beforeH*q^(m*b)*v.between*q^(j.val*b)
  width := b
  between := q^((i.val-j.val-1)*b)
  afterD := q^((m-1-i.val)*b)*v.afterD

/-- Cross-group selection does not divide the role rows. -/
def cross (v : Descriptor) (i j : Fin m) : Descriptor := child q 1 b v i j

private theorem split_pair (j i : Fin m) (hji : j < i) :
    q^(m*b) = q^(j.val*b)*q^b*q^((i.val-j.val-1)*b)*q^b*q^((m-1-i.val)*b) := by
  rw [← pow_add,← pow_add,← pow_add,← pow_add]
  congr 1
  have hj : j.val < i.val := hji
  have hi := i.isLt
  have he : j.val+1+(i.val-j.val-1)+1+(m-1-i.val) = m := by omega
  nlinarith

theorem withinH_volume (v : Descriptor) (j i : Fin m) (hji : j < i) (hw : v.width=m*b) :
    volume q (withinH q b v j i) = volume q v := by
  simp only [volume,withinH,hw]
  nth_rw 3 [split_pair q b j i hji]
  ring

theorem withinD_volume (v : Descriptor) (j i : Fin m) (hji : j < i) (hw : v.width=m*b) :
    volume q (withinD q b v j i) = volume q v := by
  simp only [volume,withinD,hw]
  nth_rw 3 [split_pair q b j i hji]
  ring

theorem cross_volume (v : Descriptor) (i j : Fin m) (hw : v.width=m*b) :
    volume q (cross q b v i j) = volume q v := by
  simpa only [cross,RecursiveInterchangeLayout.role,Nat.div_one] using
    RecursiveInterchangeLayout.child_volume q 1 b v i j hw

theorem withinH_index (v : Descriptor) (j i : Fin m) (hji : j < i) (hw : v.width=m*b)
    (a row before hp h middle d hs c oldD after : ℕ) :
    index q (withinH q b v j i) a row (before*q^(j.val*b)+hp) h middle d
        (((hs*v.between+c)*q^(m*b)+oldD)*v.afterD+after) =
      index q v a row before
        ((((hp*q^b+h)*q^((i.val-j.val-1)*b)+middle)*q^b+d)*q^((m-1-i.val)*b)+hs)
        c oldD after := by
  simp only [index,withinH,hw]
  simp only [split_pair q b j i hji]
  ring

theorem withinD_index (v : Descriptor) (j i : Fin m) (hji : j < i) (hw : v.width=m*b)
    (a row before oldH c dp h middle d ds after : ℕ) :
    index q (withinD q b v j i) a row (((before*q^(m*b)+oldH)*v.between+c)*q^(j.val*b)+dp)
        h middle d (ds*v.afterD+after) =
      index q v a row before oldH c
        ((((dp*q^b+h)*q^((i.val-j.val-1)*b)+middle)*q^b+d)*q^((m-1-i.val)*b)+ds) after := by
  simp only [index,withinD,hw]
  simp only [split_pair q b j i hji]
  ring

theorem cross_index (v : Descriptor) (i j : Fin m) (hw : v.width=m*b)
    (a row before hp h hs c dp d ds after : ℕ) :
    index q (cross q b v i j) a row (before*q^(i.val*b)+hp) h
        ((hs*v.between+c)*q^(j.val*b)+dp) d (ds*v.afterD+after) =
      index q v a row before ((hp*q^b+h)*q^((m-1-i.val)*b)+hs)
        c ((dp*q^b+d)*q^((m-1-j.val)*b)+ds) after := by
  simpa only [cross,RecursiveInterchangeLayout.role,Nat.div_one] using
    RecursiveInterchangeLayout.child_index q 1 b v i j hw a row before hp h hs c dp d ds after

theorem withinH_positive (hq : 0 < q) (v : Descriptor) (hp : v.Positive) (j i : Fin m) :
    (withinH q b v j i).Positive := by
  rcases hp with ⟨hA,hR,hB,hC,hE⟩
  dsimp [Descriptor.Positive,withinH]
  exact ⟨hA,hR,Nat.mul_pos hB (pow_pos hq _),pow_pos hq _,
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (pow_pos hq _) hC) (pow_pos hq _)) hE⟩

theorem withinD_positive (hq : 0 < q) (v : Descriptor) (hp : v.Positive) (j i : Fin m) :
    (withinD q b v j i).Positive := by
  rcases hp with ⟨hA,hR,hB,hC,hE⟩
  dsimp [Descriptor.Positive,withinD]
  exact ⟨hA,hR,Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hB (pow_pos hq _)) hC) (pow_pos hq _),
    pow_pos hq _,Nat.mul_pos (pow_pos hq _) hE⟩

/-- Equal volume relabels only the dependent array type: the serialized payload
word is literally identical, with no implicit tape traversal or permutation. -/
def array {v w : Descriptor} (he : volume q w = volume q v)
    (a : Fin (volume q v) → Fin 4) : Fin (volume q w) → Fin 4 := fun i => a (Fin.cast he i)

theorem array_word {v w : Descriptor} (he : volume q w = volume q v) (a : Fin (volume q v) → Fin 4) :
    List.ofFn (array q he a) = List.ofFn a := (List.ofFn_congr he.symm a).symm

end IntegerMultBounds.Machine.RecursiveAffineViews
