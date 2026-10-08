import IntegerMultBounds.Machine.RecursiveScalarSelection
import IntegerMultBounds.Machine.RecursiveCoordinateDigits

/-! Typed coordinates for the original heterogeneous recursive layout and its
paid scalar views. All spectators retain their original row-major positions. -/
namespace IntegerMultBounds.Machine.RecursiveScalarCoordinates
noncomputable section
open Networks
open Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewRoleBank (Selection layout)
open RecursiveScalarSelection (first second)
open RecursiveCoordinateDigits (preDigits suffix pairPrefix middle)
variable {m b : ℕ} {v : Descriptor}
local instance : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

structure Address (m b : ℕ) (v : Descriptor) where
  beforeRows : Fin v.beforeRows
  row : Fin v.rows
  before : Fin v.beforeH
  h : Fin m → ZMod (modulus b)
  middle : Fin v.between
  d : Fin m → ZMod (modulus b)
  after : Fin v.afterD

private theorem power (b n : ℕ) : (modulus b)^n = prime^(n*b) := by
  rw [modulus,← pow_mul,Nat.mul_comm]

def packed (hw : v.width=m*b) (x : Address m b v) : RecursiveInterchangeScaling.Address v :=
  ⟨x.beforeRows,x.row,x.before,
    Fin.cast (by rw [power,hw]; rfl) (FlatCoordinateLayout.rank x.h),x.middle,
    Fin.cast (by rw [power,hw]; rfl) (FlatCoordinateLayout.rank x.d),x.after⟩

def index (hw : v.width=m*b) (x : Address m b v) : Fin (volume prime v) :=
  RecursiveInterchangeScaling.index (packed hw x)

theorem index_val (hw : v.width=m*b) (x : Address m b v) :
    (index hw x).val = RecursiveInterchangeLayout.index prime v x.beforeRows.val x.row.val x.before.val
      (FlatCoordinateLayout.rank x.h).val x.middle.val (FlatCoordinateLayout.rank x.d).val x.after.val :=
  RecursiveInterchangeScaling.index_val _

def field (x : Address m b v) : Fin (m+m) → ZMod (modulus b) := Fin.addCases x.h x.d

def update (x : Address m b v) (i : Fin (m+m)) (z : ZMod (modulus b)) : Address m b v :=
  { x with h := fun j => Function.update (field x) i z (AffineFieldCoordinates.hIndex j)
           d := fun j => Function.update (field x) i z (AffineFieldCoordinates.dIndex j) }

@[simp] theorem field_h (x : Address m b v) (i : Fin m) :
    field x (AffineFieldCoordinates.hIndex i) = x.h i := Fin.addCases_left _

@[simp] theorem field_d (x : Address m b v) (i : Fin m) :
    field x (AffineFieldCoordinates.dIndex i) = x.d i := Fin.addCases_right _

@[simp] theorem update_h (x : Address m b v) (i : Fin m) (z : ZMod (modulus b)) :
    update x (AffineFieldCoordinates.hIndex i) z = {x with h := Function.update x.h i z} := by
  unfold update
  congr 1
  · funext j
    by_cases he : j=i
    · subst j; simp only [Function.update_self]
    · have hn : AffineFieldCoordinates.hIndex j ≠ AffineFieldCoordinates.hIndex i :=
        fun hh => he (Fin.castAdd_injective _ _ hh)
      simp only [Function.update_of_ne hn,Function.update_of_ne he,field_h]
  · funext j
    have hn := (AffineFieldCoordinates.h_before_d i j).ne.symm
    simp only [Function.update_of_ne hn,field_d]

@[simp] theorem update_d (x : Address m b v) (i : Fin m) (z : ZMod (modulus b)) :
    update x (AffineFieldCoordinates.dIndex i) z = {x with d := Function.update x.d i z} := by
  unfold update
  congr 1
  · funext j
    have hn := (AffineFieldCoordinates.h_before_d j i).ne
    simp only [Function.update_of_ne hn,field_h]
  · funext j
    by_cases he : j=i
    · subst j; simp only [Function.update_self]
    · have hn : AffineFieldCoordinates.dIndex j ≠ AffineFieldCoordinates.dIndex i :=
        fun hh => he (Fin.natAdd_injective _ _ hh)
      simp only [Function.update_of_ne hn,Function.update_of_ne he,field_d]

private def pack {a c : ℕ} (x : Fin a) (y : Fin c) : Fin (a*c) := finProdFinEquiv (x,y)
private theorem pack_val {a c : ℕ} (x : Fin a) (y : Fin c) : (pack x y).val = x.val*c+y.val := by
  simp [pack,finProdFinEquiv]; ring

private def digit (z : ZMod (modulus b)) : Fin (modulus b) := (ZMod.finEquiv _).symm z
private theorem digit_val (z : ZMod (modulus b)) : (digit z).val = z.val :=
  FlatCoordinateLayout.finEquiv_symm_val z
private def radixCast {n : ℕ} (x : Fin ((modulus b)^n)) : Fin (prime^(n*b)) := Fin.cast (power b n) x

/-- Regroup a cross-H/D pair without moving any array position. -/
def crossAddress (x : Address m b v) (i j : Fin m) :
    RecursiveInterchangeScaling.Address (RecursiveAffineViews.cross prime b v i j) :=
  ⟨x.beforeRows,Fin.cast (Nat.div_one v.rows).symm x.row,
    pack x.before (radixCast (preDigits x.h i)),digit (x.h i),
    pack (pack (radixCast (suffix x.h i)) x.middle) (radixCast (preDigits x.d j)),
    digit (x.d j),pack (radixCast (suffix x.d j)) x.after⟩

/-- Regroup two ordered H fields, retaining C, all D fields and E in the tail. -/
def withinHAddress (x : Address m b v) (j i : Fin m) (hj : j < i) :
    RecursiveInterchangeScaling.Address (RecursiveAffineViews.withinH prime b v j i) :=
  ⟨x.beforeRows,x.row,pack x.before (radixCast (pairPrefix x.h j i hj)),digit (x.h j),
    radixCast (middle x.h j i),digit (x.h i),
    pack (pack (pack (radixCast (suffix x.h i)) x.middle) (radixCast (FlatCoordinateLayout.rank x.d))) x.after⟩

/-- Regroup two ordered D fields, retaining B, all H fields and C in the prefix. -/
def withinDAddress (x : Address m b v) (j i : Fin m) (hj : j < i) :
    RecursiveInterchangeScaling.Address (RecursiveAffineViews.withinD prime b v j i) :=
  ⟨x.beforeRows,x.row,
    pack (pack (pack x.before (radixCast (FlatCoordinateLayout.rank x.h))) x.middle) (radixCast (pairPrefix x.d j i hj)),
    digit (x.d j),radixCast (middle x.d j i),digit (x.d i),pack (radixCast (suffix x.d i)) x.after⟩

def viewAddress (s : Selection m) (x : Address m b v) : RecursiveInterchangeScaling.Address (layout s b v) :=
  match s with
  | .cross i j => crossAddress x i j
  | .within .h j i hj => withinHAddress x j i hj
  | .within .d j i hj => withinDAddress x j i hj

/-- The static view's exposed control really is the originally numbered field. -/
theorem first_value (s : Selection m) (x : Address m b v) :
    (viewAddress s x).h.val = (field x (first s)).val := by
  cases s with
  | cross i j =>
    change (digit (x.h i)).val = (field x (AffineFieldCoordinates.hIndex i)).val
    rw [digit_val,field_h]
  | within g j i hj =>
    cases g <;>
      simp only [viewAddress,withinHAddress,withinDAddress,first,field_h,field_d]
    all_goals exact digit_val _

/-- The static view's exposed target really is the originally numbered field. -/
theorem second_value (s : Selection m) (x : Address m b v) :
    (viewAddress s x).d.val = (field x (second s)).val := by
  cases s with
  | cross i j =>
    change (digit (x.d j)).val = (field x (AffineFieldCoordinates.dIndex j)).val
    rw [digit_val,field_d]
  | within g j i hj =>
    cases g <;>
      simp only [viewAddress,withinHAddress,withinDAddress,second,field_h,field_d]
    all_goals exact digit_val _

private theorem one_radix (x : Fin m → ZMod (modulus b)) (i : Fin m) :
    ((preDigits x i).val*prime^b+(x i).val)*prime^((m-1-i.val)*b)+(suffix x i).val =
      (FlatCoordinateLayout.rank x).val := by
  let P := (preDigits x i).val
  let D := (x i).val
  let S := (suffix x i).val
  let R := (FlatCoordinateLayout.rank x).val
  have hh := RecursiveCoordinateDigits.one x i
  change R = P*modulus b*(modulus b)^(m-1-i.val)+D*(modulus b)^(m-1-i.val)+S at hh
  change (P*prime^b+D)*prime^((m-1-i.val)*b)+S = R
  rw [power] at hh
  change R = P*prime^b*prime^((m-1-i.val)*b)+D*prime^((m-1-i.val)*b)+S at hh
  rw [hh]
  ring

private theorem pair_radix (x : Fin m → ZMod (modulus b)) (j i : Fin m) (hj : j < i) :
    ((((pairPrefix x j i hj).val*prime^b+(x j).val)*prime^((i.val-j.val-1)*b)+
      (middle x j i).val)*prime^b+(x i).val)*prime^((m-1-i.val)*b)+(suffix x i).val =
        (FlatCoordinateLayout.rank x).val := by
  have hh := RecursiveCoordinateDigits.pair x j i hj
  simpa only [modulus,← pow_mul,Nat.mul_comm] using hh.symm

/-- Both typed coordinate systems index literally the same serialized symbol. -/
theorem view_index (s : Selection m) (hw : v.width=m*b) (x : Address m b v) :
    Fin.cast (RecursiveViewRoleBank.layout_volume s b v hw) (RecursiveInterchangeScaling.index (viewAddress s x)) = index hw x := by
  apply Fin.ext
  simp only [Fin.val_cast,RecursiveInterchangeScaling.index_val,index_val]
  cases s with
  | cross i j =>
    have he := RecursiveAffineViews.cross_index prime b v i j hw
      x.beforeRows.val x.row.val x.before.val (preDigits x.h i).val (x.h i).val (suffix x.h i).val
      x.middle.val (preDigits x.d j).val (x.d j).val (suffix x.d j).val x.after.val
    rw [one_radix x.h i,one_radix x.d j] at he
    convert he using 1
    · simp only [viewAddress,crossAddress,pack_val,radixCast,Fin.val_cast,digit,layout,RecursiveAffineViews.cross,RecursiveInterchangeLayout.child]
      congr 1 <;> exact FlatCoordinateLayout.finEquiv_symm_val _
  | within g j i hj =>
    cases g
    · have he := RecursiveAffineViews.withinH_index prime b v j i hj hw
        x.beforeRows.val x.row.val x.before.val (pairPrefix x.h j i hj).val (x.h j).val (middle x.h j i).val
        (x.h i).val (suffix x.h i).val x.middle.val (FlatCoordinateLayout.rank x.d).val x.after.val
      rw [pair_radix x.h j i hj] at he
      convert he using 1
      · simp only [viewAddress,withinHAddress,pack_val,radixCast,Fin.val_cast,digit,layout,RecursiveAffineDimensionsClean.view,RecursiveAffineViews.withinH]
        congr 1 <;> exact FlatCoordinateLayout.finEquiv_symm_val _
    · have he := RecursiveAffineViews.withinD_index prime b v j i hj hw
        x.beforeRows.val x.row.val x.before.val (FlatCoordinateLayout.rank x.h).val x.middle.val
        (pairPrefix x.d j i hj).val (x.d j).val (middle x.d j i).val (x.d i).val (suffix x.d i).val x.after.val
      rw [pair_radix x.d j i hj] at he
      convert he using 1
      · simp only [viewAddress,withinDAddress,pack_val,radixCast,Fin.val_cast,digit,layout,RecursiveAffineDimensionsClean.view,RecursiveAffineViews.withinD]
        congr 1 <;> exact FlatCoordinateLayout.finEquiv_symm_val _

/-- Every selected view exposes fields of the caller's scalar width. -/
theorem layout_width (s : Selection m) : (layout s b v).width = b := by
  cases s with
  | cross i j => rfl
  | within g j i hj => cases g <;> rfl

def setSecond (s : Selection m) (x : Address m b v) (z : ZMod (modulus b)) :
    RecursiveInterchangeScaling.Address (layout s b v) :=
  {viewAddress s x with d := ⟨z.val,by rw [layout_width]; exact ZMod.val_lt z⟩}

def setCrossFirst (x : Address m b v) (i j : Fin m) (z : ZMod (modulus b)) :
    RecursiveInterchangeScaling.Address (layout (.cross i j) b v) :=
  {crossAddress x i j with h := ⟨z.val,ZMod.val_lt z⟩}

private theorem one_update_radix (x : Fin m → ZMod (modulus b)) (i : Fin m) (z : ZMod (modulus b)) :
    ((preDigits x i).val*prime^b+z.val)*prime^((m-1-i.val)*b)+(suffix x i).val =
      (FlatCoordinateLayout.rank (Function.update x i z)).val := by
  have hh := RecursiveCoordinateDigits.one_update x i z
  simpa only [modulus,← pow_mul,Nat.mul_comm] using hh.symm

private theorem pair_update_radix (x : Fin m → ZMod (modulus b)) (j i : Fin m) (hj : j < i)
    (z : ZMod (modulus b)) :
    ((((pairPrefix x j i hj).val*prime^b+(x j).val)*prime^((i.val-j.val-1)*b)+
      (middle x j i).val)*prime^b+z.val)*prime^((m-1-i.val)*b)+(suffix x i).val =
        (FlatCoordinateLayout.rank (Function.update x i z)).val := by
  have hh := RecursiveCoordinateDigits.pair_update x j i hj z
  simpa only [modulus,← pow_mul,Nat.mul_comm] using hh.symm

/-- A write to the view target is exactly a write to the originally numbered
scalar coordinate, with every spectator still at its original physical index. -/
theorem setSecond_index (s : Selection m) (hw : v.width=m*b) (x : Address m b v) (z : ZMod (modulus b)) :
    Fin.cast (RecursiveViewRoleBank.layout_volume s b v hw) (RecursiveInterchangeScaling.index (setSecond s x z)) =
      index hw (update x (second s) z) := by
  apply Fin.ext
  simp only [Fin.val_cast,RecursiveInterchangeScaling.index_val,index_val]
  cases s with
  | cross i j =>
    have he := RecursiveAffineViews.cross_index prime b v i j hw
      x.beforeRows.val x.row.val x.before.val (preDigits x.h i).val (x.h i).val (suffix x.h i).val
      x.middle.val (preDigits x.d j).val z.val (suffix x.d j).val x.after.val
    rw [one_radix x.h i,one_update_radix x.d j z] at he
    simp only [second,update_d]
    convert he using 1
    · simp only [setSecond,viewAddress,crossAddress,pack_val,radixCast,Fin.val_cast,digit,layout,
        RecursiveAffineViews.cross,RecursiveInterchangeLayout.child]
      congr 1
      exact FlatCoordinateLayout.finEquiv_symm_val _
  | within g j i hj =>
    cases g
    · have he := RecursiveAffineViews.withinH_index prime b v j i hj hw
        x.beforeRows.val x.row.val x.before.val (pairPrefix x.h j i hj).val (x.h j).val (middle x.h j i).val
        z.val (suffix x.h i).val x.middle.val (FlatCoordinateLayout.rank x.d).val x.after.val
      rw [pair_update_radix x.h j i hj z] at he
      simp only [second,update_h]
      convert he using 1
      · simp only [setSecond,viewAddress,withinHAddress,pack_val,radixCast,Fin.val_cast,digit,layout,
          RecursiveAffineDimensionsClean.view,RecursiveAffineViews.withinH]
        congr 1
        exact FlatCoordinateLayout.finEquiv_symm_val _
    · have he := RecursiveAffineViews.withinD_index prime b v j i hj hw
        x.beforeRows.val x.row.val x.before.val (FlatCoordinateLayout.rank x.h).val x.middle.val
        (pairPrefix x.d j i hj).val (x.d j).val (middle x.d j i).val z.val (suffix x.d i).val x.after.val
      rw [pair_update_radix x.d j i hj z] at he
      simp only [second,update_d]
      convert he using 1
      · simp only [setSecond,viewAddress,withinDAddress,pack_val,radixCast,Fin.val_cast,digit,layout,
          RecursiveAffineDimensionsClean.view,RecursiveAffineViews.withinD]
        congr 1
        exact FlatCoordinateLayout.finEquiv_symm_val _

/-- Scaling an H field uses the same cross view and writes precisely that
original H field. The selected D field is retained verbatim. -/
theorem setCrossFirst_index (hw : v.width=m*b) (x : Address m b v) (i j : Fin m) (z : ZMod (modulus b)) :
    Fin.cast (RecursiveViewRoleBank.layout_volume (.cross i j) b v hw)
      (RecursiveInterchangeScaling.index (setCrossFirst x i j z)) =
        index hw (update x (AffineFieldCoordinates.hIndex i) z) := by
  apply Fin.ext
  simp only [Fin.val_cast,RecursiveInterchangeScaling.index_val,index_val,update_h]
  have he := RecursiveAffineViews.cross_index prime b v i j hw
    x.beforeRows.val x.row.val x.before.val (preDigits x.h i).val z.val (suffix x.h i).val
    x.middle.val (preDigits x.d j).val (x.d j).val (suffix x.d j).val x.after.val
  rw [one_update_radix x.h i z,one_radix x.d j] at he
  convert he using 1
  · simp only [setCrossFirst,crossAddress,pack_val,radixCast,Fin.val_cast,digit,
      RecursiveAffineViews.cross,RecursiveInterchangeLayout.child]
    congr 1
    exact FlatCoordinateLayout.finEquiv_symm_val _

end
end IntegerMultBounds.Machine.RecursiveScalarCoordinates
