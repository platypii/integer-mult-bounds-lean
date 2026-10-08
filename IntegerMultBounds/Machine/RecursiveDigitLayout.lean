import IntegerMultBounds.Machine.DigitInterchangeRows
import IntegerMultBounds.Machine.RecursiveInterchangeLayout

/-! Literal serialized width-one view of a recursive seven-factor array. The
outer spectator collects A,row,B without moving any symbol. -/
namespace IntegerMultBounds.Machine.RecursiveDigitLayout
open RecursiveInterchangeLayout (Descriptor volume)
variable {q a : ℕ}

def outer (v : Descriptor) := v.beforeRows*v.rows*v.beforeH

theorem split_volume (v : Descriptor) (hw : v.width = 1) :
    volume q v = outer v*(q*(v.between*(q*v.afterD))) := by
  simp only [volume,outer,hw,pow_one]
  ring

def flatView {v : Descriptor} (hw : v.width = 1) (x : Fin (volume q v) → Fin (a+4)) :
    Fin (outer v*(q*(v.between*(q*v.afterD)))) → Fin (a+4) :=
  fun i => x (Fin.cast (split_volume v hw).symm i)

def pack {v : Descriptor} (o : Fin (outer v)) (h : Fin q) (c : Fin v.between) (d : Fin q) (e : Fin v.afterD) :
    Fin (outer v*(q*(v.between*(q*v.afterD)))) :=
  finProdFinEquiv (o,finProdFinEquiv (h,finProdFinEquiv (c,finProdFinEquiv (d,e))))

def view {v : Descriptor} (hw : v.width = 1) (x : Fin (volume q v) → Fin (a+4)) :
    DigitInterchangeRows.Array (outer v) q v.between v.afterD a :=
  fun o h c d e => flatView hw x (pack o h c d e)

private theorem ofFn_pack {α : Type*} {m n : ℕ} (f : Fin (m*n) → α) :
    List.ofFn f = (List.ofFn fun i : Fin m => List.ofFn fun j : Fin n => f (finProdFinEquiv (i,j))).flatten := by
  simpa only [finProdFinEquiv,Equiv.coe_fn_mk,Nat.add_comm,Nat.mul_comm] using List.ofFn_mul f

theorem source_word {v : Descriptor} (hw : v.width = 1) (x : Fin (volume q v) → Fin (a+4)) :
    CyclicRowSplit.sourceWord (DigitInterchangeRows.outerRows (view hw x)) = List.ofFn x := by
  have hc : List.ofFn (flatView hw x) = List.ofFn x := (List.ofFn_congr (split_volume v hw) _).symm
  rw [← hc]
  unfold CyclicRowSplit.sourceWord CyclicRowSplit.cycleWords DigitInterchangeRows.outerRows view
  rw [ofFn_pack (flatView hw x)]
  congr 1
  apply congrArg List.ofFn
  funext o
  rw [ofFn_pack]
  congr 1
  apply congrArg List.ofFn
  funext h
  rw [ofFn_pack]
  congr 1
  apply congrArg List.ofFn
  funext c
  rw [ofFn_pack]
  rfl

def unpack {v : Descriptor} (i : Fin (outer v*(q*(v.between*(q*v.afterD))))) :=
  let p := finProdFinEquiv.symm i
  let h := finProdFinEquiv.symm p.2
  let c := finProdFinEquiv.symm h.2
  let d := finProdFinEquiv.symm c.2
  (p.1,h.1,c.1,d.1,d.2)

@[simp] theorem unpack_pack {v : Descriptor} (o : Fin (outer v)) (h : Fin q) (c : Fin v.between)
    (d : Fin q) (e : Fin v.afterD) : unpack (pack o h c d e) = (o,h,c,d,e) := by
  simp [unpack,pack]

def array {v : Descriptor} (hw : v.width = 1) (x : Fin (volume q v) → Fin (a+4)) :
    Fin (volume q v) → Fin (a+4) := fun i =>
  let p := unpack (Fin.cast (split_volume v hw) i)
  view hw x p.1 p.2.2.2.1 p.2.2.1 p.2.1 p.2.2.2.2

theorem view_array {v : Descriptor} (hw : v.width = 1) (x : Fin (volume q v) → Fin (a+4)) :
    view hw (array hw x) = DigitInterchangeRows.transpose (view hw x) := by
  funext o h c d e
  simp only [view,flatView,array,Fin.cast_cast,Fin.cast_eq_self,unpack_pack,DigitInterchangeRows.transpose]

/-- The output is another literal word in the same recursive flat layout. -/
theorem array_word {v : Descriptor} (hw : v.width = 1) (x : Fin (volume q v) → Fin (a+4)) :
    CyclicRowSplit.sourceWord (DigitInterchangeRows.outerRows (DigitInterchangeRows.transpose (view hw x))) =
      List.ofFn (array hw x) := by
  rw [← view_array,source_word]


theorem array_entry {v : Descriptor} (hw : v.width = 1) (x : Fin (volume q v) → Fin (a+4))
    (o : Fin (outer v)) (h : Fin q) (c : Fin v.between) (d : Fin q) (e : Fin v.afterD) :
    array hw x (Fin.cast (split_volume v hw).symm (pack o d c h e)) =
      x (Fin.cast (split_volume v hw).symm (pack o h c d e)) := by
  change view hw (array hw x) o d c h e = view hw x o h c d e
  rw [view_array]
  rfl

end IntegerMultBounds.Machine.RecursiveDigitLayout
