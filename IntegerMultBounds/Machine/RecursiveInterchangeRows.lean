import IntegerMultBounds.Machine.RecursiveInterchangeLayout
import IntegerMultBounds.Machine.CyclicRowMerge
import Mathlib.Data.List.OfFn

/-! Literal serialization bridge from the seven-factor recursive descriptor to
physical cyclic row split/merge. Descriptors for row length and group count are
explicit inputs; their construction and payload head resets are caller work. -/
namespace IntegerMultBounds.Machine.RecursiveInterchangeRows
open RecursiveInterchangeLayout (Descriptor volume role)
variable {a : ℕ}

def rowLength (q : ℕ) (v : Descriptor) :=
  v.beforeH*q^v.width*v.between*q^v.width*v.afterD

def groups (c : ℕ) (v : Descriptor) := v.beforeRows*(v.rows/c)

theorem volume_split (q c : ℕ) (v : Descriptor) (hdiv : c ∣ v.rows) :
    volume q v = groups c v*(c*rowLength q v) := by
  unfold volume groups rowLength
  calc
    _ = v.beforeRows*((v.rows/c)*c)*v.beforeH*q^v.width*v.between*q^v.width*v.afterD := by
      rw [Nat.div_mul_cancel hdiv]
    _ = _ := by ring

theorem role_volume (q c : ℕ) (v : Descriptor) :
    volume q (role v c) = groups c v*rowLength q v := by
  unfold volume role groups rowLength
  ring

def pack {m n : ℕ} (i : Fin m) (j : Fin n) : Fin (m*n) := finProdFinEquiv (i,j)

theorem pack_val {m n : ℕ} (i : Fin m) (j : Fin n) : (pack i j).val = i.val*n+j.val := by
  simp [pack,finProdFinEquiv]; ring

def view (q c : ℕ) (v : Descriptor) (hdiv : c ∣ v.rows)
    (input : Fin (volume q v) → Fin (a+4)) :
    Fin (groups c v*(c*rowLength q v)) → Fin (a+4) :=
  fun i => input (Fin.cast (volume_split q c v hdiv).symm i)

def rows (q c : ℕ) (v : Descriptor) (hdiv : c ∣ v.rows)
    (input : Fin (volume q v) → Fin (a+4))
    (i : Fin (groups c v)) (j : Fin c) : List (Fin (a+4)) :=
  List.ofFn (fun k : Fin (rowLength q v) => view q c v hdiv input (pack i (pack j k)))

theorem rows_length (q c : ℕ) (v : Descriptor) (hdiv : c ∣ v.rows)
    (input : Fin (volume q v) → Fin (a+4)) (i : Fin (groups c v)) (j : Fin c) :
    (rows q c v hdiv input i j).length = rowLength q v := by simp [rows]

private theorem ofFn_pack {m n : ℕ} (f : Fin (m*n) → Fin (a+4)) :
    List.ofFn f = (List.ofFn (fun i : Fin m => List.ofFn (fun j : Fin n => f (pack i j)))).flatten := by
  simpa only [pack,finProdFinEquiv,Equiv.coe_fn_mk,Nat.add_comm,Nat.mul_comm] using List.ofFn_mul f

/-- The physical split input is exactly the original row-major word, without
any preliminary transposition or free payload copy. -/
theorem source_word (q c : ℕ) (v : Descriptor) (hdiv : c ∣ v.rows)
    (input : Fin (volume q v) → Fin (a+4)) :
    CyclicRowSplit.sourceWord (rows q c v hdiv input) = List.ofFn input := by
  have he : List.ofFn (view q c v hdiv input) = List.ofFn input :=
    (List.ofFn_congr (volume_split q c v hdiv) _).symm
  rw [← he,ofFn_pack]
  unfold CyclicRowSplit.sourceWord CyclicRowSplit.cycleWords rows
  congr 1
  apply congrArg List.ofFn
  funext i
  exact (ofFn_pack (fun k => view q c v hdiv input (pack i k))).symm

/-- Role output as the same row-major descriptor with row count divided by c. -/
def roleArray (q c : ℕ) (v : Descriptor) (hdiv : c ∣ v.rows)
    (input : Fin (volume q v) → Fin (a+4)) (j : Fin c) :
    Fin (volume q (role v c)) → Fin (a+4) := fun z =>
  let ik := finProdFinEquiv.symm (Fin.cast (role_volume q c v) z)
  view q c v hdiv input (pack ik.1 (pack j ik.2))

theorem role_word (q c : ℕ) (v : Descriptor) (hdiv : c ∣ v.rows)
    (input : Fin (volume q v) → Fin (a+4)) (j : Fin c) :
    CyclicRowSplit.roleWord (rows q c v hdiv input) j = List.ofFn (roleArray q c v hdiv input j) := by
  let f : Fin (groups c v*rowLength q v) → Fin (a+4) := fun z =>
    let ik := finProdFinEquiv.symm z
    view q c v hdiv input (pack ik.1 (pack j ik.2))
  have he : List.ofFn (roleArray q c v hdiv input j) = List.ofFn f :=
    (List.ofFn_congr (role_volume q c v).symm f).symm
  rw [he,ofFn_pack]
  unfold CyclicRowSplit.roleWord rows
  congr 1
  apply congrArg List.ofFn
  funext i
  congr 1
  funext k
  simp only [f,pack,Equiv.symm_apply_apply]

def suffixIndex (q : ℕ) (v : Descriptor) (before : Fin v.beforeH)
    (h : Fin (q^v.width)) (middle : Fin v.between) (d : Fin (q^v.width))
    (after : Fin v.afterD) : Fin (rowLength q v) :=
  pack (pack (pack (pack before h) middle) d) after

/-- Group address (a,g), role j is literally original row c*g+j. -/
theorem cyclic_index (q c : ℕ) (v : Descriptor) (hdiv : c ∣ v.rows)
    (aa : Fin v.beforeRows) (g : Fin (v.rows/c)) (j : Fin c)
    (before : Fin v.beforeH) (h : Fin (q^v.width)) (middle : Fin v.between)
    (d : Fin (q^v.width)) (after : Fin v.afterD) :
    (Fin.cast (volume_split q c v hdiv).symm
      (pack (pack aa g) (pack j (suffixIndex q v before h middle d after)))).val =
    RecursiveInterchangeLayout.index q v aa.val (c*g.val+j.val)
      before.val h.val middle.val d.val after.val := by
  change (pack (pack aa g) (pack j (suffixIndex q v before h middle d after))).val = _
  simp only [suffixIndex,pack_val,RecursiveInterchangeLayout.index,rowLength]
  have he := Nat.div_mul_cancel hdiv
  calc
    _ = aa.val*((v.rows/c)*c)*(v.beforeH*q^v.width*v.between*q^v.width*v.afterD)+
      (c*g.val+j.val)*(v.beforeH*q^v.width*v.between*q^v.width*v.afterD)+
      ((((before.val*q^v.width+h.val)*v.between+middle.val)*q^v.width+d.val)*v.afterD+after.val) := by ring
    _ = _ := by rw [he]; ring

/-- Instantiate the actual split with the seven-factor serialization. Initial
and final heads are explicit, so this theorem does not hide normalization. -/
theorem split_hoare (q c : ℕ) (v : Descriptor) (hdiv : c ∣ v.rows)
    (input : Fin (volume q v) → Fin (a+4))
    (source : ℤ → Fin (a+4)) (outputs : Fin c → ℤ → Fin (a+4))
    (p : ℤ) (origins : Fin c → ℤ) (bs gs : List Bool)
    (hb : Counter.value bs = rowLength q v) (hg : Counter.value gs = groups c v) :
    HoareTime (CyclicRowSplit.program c a)
      (fun w => w = CyclicRowSplit.bank (CyclicRowCopy.bank (putWord source p (List.ofFn input))
        outputs p origins bs) gs)
      (fun w => w = CyclicRowSplit.bank (CyclicRowCopy.bank (putWord source p (List.ofFn input))
        (fun j => putWord (outputs j) (origins j) (List.ofFn (roleArray q c v hdiv input j)))
        (p+volume q v) (fun j => origins j+volume q (role v c)) bs) gs)
      (groups c v*(7*(c*rowLength q v)+c*(7*bs.length+17))+6*groups c v+7*gs.length+16) := by
  have hh := CyclicRowSplit.split_hoare source outputs p origins (rows q c v hdiv input)
    (rowLength q v) (rows_length q c v hdiv input) bs gs hb hg
  simpa only [source_word,role_word,volume_split q c v hdiv,role_volume q c v,Nat.cast_mul] using hh

/-- Instantiate the inverse physical merge on the same seven-factor words. -/
theorem merge_hoare (q c : ℕ) (v : Descriptor) (hdiv : c ∣ v.rows)
    (input : Fin (volume q v) → Fin (a+4))
    (dest : ℤ → Fin (a+4)) (sources : Fin c → ℤ → Fin (a+4))
    (p : ℤ) (origins : Fin c → ℤ) (bs gs : List Bool)
    (hb : Counter.value bs = rowLength q v) (hg : Counter.value gs = groups c v) :
    HoareTime (CyclicRowMerge.program c a)
      (fun w => w = CyclicRowSplit.bank (CyclicRowCopy.bank dest
        (fun j => putWord (sources j) (origins j) (List.ofFn (roleArray q c v hdiv input j)))
        p origins bs) gs)
      (fun w => w = CyclicRowSplit.bank (CyclicRowCopy.bank (putWord dest p (List.ofFn input))
        (fun j => putWord (sources j) (origins j) (List.ofFn (roleArray q c v hdiv input j)))
        (p+volume q v) (fun j => origins j+volume q (role v c)) bs) gs)
      (groups c v*(7*(c*rowLength q v)+c*(7*bs.length+17))+6*groups c v+7*gs.length+16) := by
  have hh := CyclicRowMerge.merge_hoare dest sources p origins (rows q c v hdiv input)
    (rowLength q v) (rows_length q c v hdiv input) bs gs hb hg
  simpa only [source_word,role_word,volume_split q c v hdiv,role_volume q c v,Nat.cast_mul] using hh

def roleIndex (q c : ℕ) (v : Descriptor) (i : Fin (groups c v))
    (k : Fin (rowLength q v)) : Fin (volume q (role v c)) :=
  Fin.cast (role_volume q c v).symm (pack i k)

/-- The output entry is the original symbol from the selected cyclic role;
combined with cyclic_index this gives original row c*g+j literally. -/
theorem role_entry (q c : ℕ) (v : Descriptor) (hdiv : c ∣ v.rows)
    (input : Fin (volume q v) → Fin (a+4)) (i : Fin (groups c v))
    (j : Fin c) (k : Fin (rowLength q v)) :
    roleArray q c v hdiv input j (roleIndex q c v i k) =
      input (Fin.cast (volume_split q c v hdiv).symm (pack i (pack j k))) := by
  have he : Fin.cast (role_volume q c v)
      (Fin.cast (role_volume q c v).symm (pack i k)) = pack i k := Fin.ext rfl
  simp only [roleArray,roleIndex]
  rw [he]
  simp only [pack,Equiv.symm_apply_apply,view]

theorem role_index_val (q c : ℕ) (v : Descriptor)
    (aa : Fin v.beforeRows) (g : Fin (v.rows/c))
    (before : Fin v.beforeH) (h : Fin (q^v.width)) (middle : Fin v.between)
    (d : Fin (q^v.width)) (after : Fin v.afterD) :
    (roleIndex q c v (pack aa g) (suffixIndex q v before h middle d after)).val =
    RecursiveInterchangeLayout.index q (role v c) aa.val g.val before.val h.val middle.val d.val after.val := by
  change (pack (pack aa g) (suffixIndex q v before h middle d after)).val = _
  simp only [suffixIndex,pack_val,RecursiveInterchangeLayout.index,role,rowLength]
  ring

/-- Positive recursive descriptors give the explicit linear bound in their
literal parent volume for either physical split or merge. -/
theorem cost_linear (q c : ℕ) (v : Descriptor) (hdiv : c ∣ v.rows)
    (hq : 0 < q) (hc : 0 < c) (hv : v.Positive) (bs gs : List Bool)
    (hb : Counter.value bs = rowLength q v) (hg : Counter.value gs = groups c v)
    (cb : GrowingCounterData.Canonical bs) (cg : GrowingCounterData.Canonical gs) :
    groups c v*(7*(c*rowLength q v)+c*(7*bs.length+17))+6*groups c v+7*gs.length+16 ≤
      74*volume q v := by
  rcases hv with ⟨ha,hr,hb',hm,he⟩
  have hrow : 0 < rowLength q v := by unfold rowLength; positivity
  have hg' : 0 < groups c v := by
    exact Nat.mul_pos ha (Nat.div_pos (Nat.le_of_dvd hr hdiv) hc)
  rw [volume_split q c v hdiv]
  exact CyclicRowSplit.cost_linear _ bs gs hc hg' hrow hb hg cb cg

end IntegerMultBounds.Machine.RecursiveInterchangeRows
