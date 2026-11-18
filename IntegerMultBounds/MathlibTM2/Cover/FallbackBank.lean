module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackFields
public import IntegerMultBounds.MathlibTM2.Cover.FallbackSign
public import IntegerMultBounds.MathlibTM2.Cover.FallbackWord

/-! Lift the row operations to equal-width fields of a flat bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
variable {R : Type*} [CommRing R] {n b : ℕ}

/-- Add a multiple of the earlier slice to the later one, atom by atom. -/
def shearAt (c : R) (start width gap : ℕ) (bank : List R) : List R :=
  let rest := bank.drop start
  let later := rest.drop (width + gap)
  bank.take start ++ rest.take width ++ (rest.drop width).take gap ++
    List.zipWith (fun x y => y + c*x) (rest.take width) (later.take width) ++ later.drop width

theorem shearAt_fields (c : R) (pre gap post : List R) (x y : Fin b → R) :
    shearAt c pre.length b gap.length (pre ++ List.ofFn x ++ gap ++ List.ofFn y ++ post) =
      pre ++ List.ofFn x ++ gap ++ List.ofFn (fun k => y k + c*x k) ++ post := by
  have zip : List.zipWith (fun a z => z+c*a) (List.ofFn x) (List.ofFn y) =
      List.ofFn (fun k => y k + c*x k) := by
    apply List.ext_getElem <;> simp
  simp [shearAt,List.append_assoc,← List.drop_drop,zip]

/-- Concatenate the fields in tape order. A column gives one atom from each field. -/
def bankFields (rows : List (Fin n)) (x : Fin b → Fin n → R) :=
  rows.flatMap (fun i => List.ofFn (fun k => x k i))

omit [CommRing R] in
theorem bankFields_length (rows : List (Fin n)) (x : Fin b → Fin n → R) :
    (bankFields rows x).length = rows.length * b := by
  induction rows with
  | nil => simp [bankFields]
  | cons i rows ih => simp_all [bankFields,Nat.add_mul,Nat.add_comm]

omit [CommRing R] in
private theorem bankFields_congr (rows : List (Fin n)) {x y : Fin b → Fin n → R}
    (h : ∀ i ∈ rows, ∀ k, x k i = y k i) : bankFields rows x = bankFields rows y := by
  induction rows with
  | nil => rfl
  | cons i rows ih =>
    have head := funext (h i (by simp))
    have tail := ih (fun j hj => h j (by simp [hj]))
    simpa only [bankFields,List.flatMap_cons,head] using congrArg (List.ofFn (fun k => y k i) ++ ·) tail

theorem shearAt_rows (c : R) (i j : Fin n) (hij : i < j) (pre gap post : List (Fin n))
    (fresh : j ∉ pre ++ gap ++ post) (x : Fin b → Fin n → R) :
    let rows := pre ++ [i] ++ gap ++ [j] ++ post
    shearAt c (pre.length*b) b (gap.length*b) (bankFields rows x) =
      bankFields rows (fun k => (RowOp.shear i j hij c).apply (x k)) := by
  have unchanged (l : List (Fin n)) (hl : j ∉ l) :
      bankFields l (fun k => (RowOp.shear i j hij c).apply (x k)) = bankFields l x := by
    apply bankFields_congr
    intro a ha k
    simp [RowOp.apply,show a ≠ j by rintro rfl; exact hl ha]
  simp only [List.mem_append,not_or] at fresh
  dsimp only
  have step := shearAt_fields c (bankFields pre x) (bankFields gap x) (bankFields post x)
    (fun k => x k i) (fun k => x k j)
  rw [bankFields_length,bankFields_length] at step
  conv at step => rhs; rw [← unchanged pre fresh.1.1,← unchanged gap fresh.1.2,← unchanged post fresh.2]
  simpa [bankFields,List.flatMap_append,RowOp.apply,hij.ne,List.append_assoc] using step

theorem exchangeAt_rows (i j : Fin n) (pre gap post : List (Fin n))
    (hi : i ∉ pre ++ gap ++ post) (hj : j ∉ pre ++ gap ++ post) (x : Fin b → Fin n → R) :
    let rows := pre ++ [i] ++ gap ++ [j] ++ post
    exchangeAt (pre.length*b) b (gap.length*b) (bankFields rows x) =
      bankFields rows (fun k => (RowOp.swap i j).apply (x k)) := by
  have unchanged (l : List (Fin n)) (hl : i ∉ l) (hl' : j ∉ l) :
      bankFields l (fun k => (RowOp.swap i j).apply (x k)) = bankFields l x := by
    apply bankFields_congr
    intro a ha k
    simp [RowOp.apply,Equiv.swap_apply_of_ne_of_ne (show a ≠ i by rintro rfl; exact hl ha)
      (show a ≠ j by rintro rfl; exact hl' ha)]
  simp only [List.mem_append,not_or] at hi hj
  have step := exchangeAt_fields (bankFields pre x) (List.ofFn fun k => x k i) (bankFields gap x)
    (List.ofFn fun k => x k j) (bankFields post x) (by simp)
  rw [bankFields_length,bankFields_length,List.length_ofFn] at step
  conv at step =>
    rhs
    rw [← unchanged pre hi.1.1 hj.1.1,← unchanged gap hi.1.2 hj.1.2,← unchanged post hi.2 hj.2]
  simpa [bankFields,List.flatMap_append,RowOp.apply,List.append_assoc] using step

private theorem split_rows (i j : Fin n) (h : i < j) :
    ∃ pre gap post, List.finRange n = pre ++ [i] ++ gap ++ [j] ++ post ∧
      pre.length = i.val ∧ gap.length = j.val-i.val-1 ∧
      i ∉ pre ++ gap ++ post ∧ j ∉ pre ++ gap ++ post := by
  let rows := List.finRange n
  let left := rows.take j.val
  have hj : j.val < rows.length := by simp [rows]
  have len : left.length = j.val := by simp [left,rows]
  have hi : i.val < left.length := by simpa [len] using h
  have cut (l : List (Fin n)) (k : ℕ) (hk : k < l.length) :
      l.take k ++ [l[k]] ++ l.drop (k+1) = l := by simp
  have a := cut left i.val hi
  have b := cut rows j.val hj
  have ai : left[i.val] = i := by simp [left,rows]
  have bj : rows[j.val] = j := by simp [rows]
  rw [ai] at a
  rw [bj] at b
  change left ++ [j] ++ _ = rows at b
  let pre := left.take i.val
  let gap := left.drop (i.val+1)
  let post := rows.drop (j.val+1)
  have eqn : rows = pre ++ [i] ++ gap ++ [j] ++ post := by
    dsimp [pre,gap,post]; rw [a,b]
  refine ⟨pre,gap,post,eqn,by simp [pre,Nat.min_eq_left hi.le],by simp [gap,len]; omega,?_⟩
  have nd := List.nodup_finRange n
  change rows.Nodup at nd
  rw [eqn] at nd
  simp only [List.append_assoc,List.singleton_append,List.nodup_append,List.nodup_cons,
    List.mem_append,List.mem_cons] at nd ⊢
  grind

/-- Interpret the indices of a fallback row operation as offsets in the flat bank. -/
def RowOp.onBank (width : ℕ) : RowOp n R → List R → List R
  | .shear i j _ c => shearAt c (i.val*width) width ((j.val-i.val-1)*width)
  | .swap i j => if i = j then id else
      exchangeAt ((min i.val j.val)*width) width (((max i.val j.val)-(min i.val j.val)-1)*width)

theorem RowOp.onBank_fields (op : RowOp n R) (x : Fin b → Fin n → R) :
    op.onBank b (bankFields (List.finRange n) x) =
      bankFields (List.finRange n) (fun k => op.apply (x k)) := by
  have swap (i j : Fin n) (h : i < j) :
      exchangeAt (i.val*b) b ((j.val-i.val-1)*b) (bankFields (List.finRange n) x) =
        bankFields (List.finRange n) (fun k => (RowOp.swap i j).apply (x k)) := by
    obtain ⟨pre,gap,post,eqn,hp,hg,hi,hj⟩ := split_rows i j h
    have step := exchangeAt_rows i j pre gap post hi hj x
    dsimp only at step
    rw [← eqn,hp,hg] at step
    exact step
  cases op with
  | shear i j h c =>
    obtain ⟨pre,gap,post,eqn,hp,hg,_,hj⟩ := split_rows i j h
    simpa only [RowOp.onBank,← eqn,hg,hp] using shearAt_rows c i j h pre gap post hj x
  | swap i j =>
    rcases lt_trichotomy i j with h | rfl | h
    · simpa [RowOp.onBank,h.ne,min_eq_left (Nat.le_of_lt h),max_eq_right (Nat.le_of_lt h)] using swap i j h
    · simp [RowOp.onBank,RowOp.apply]
    · simpa [RowOp.onBank,h.ne.symm,min_eq_right (Nat.le_of_lt h),max_eq_left (Nat.le_of_lt h),RowOp.apply,
        Equiv.swap_comm j i] using swap j i h

theorem rowWord_onBank (ops : List (RowOp n R)) (x : Fin b → Fin n → R) :
    ops.foldl (fun bank op => op.onBank b bank) (bankFields (List.finRange n) x) =
      bankFields (List.finRange n) (fun k => ops.foldl (fun y op => op.apply y) (x k)) := by
  induction ops generalizing x with
  | nil => rfl
  | cons op ops ih => simp only [List.foldl_cons,RowOp.onBank_fields,ih]

def pairOnBank (width : ℕ) (i : Fin n) (u : Rˣ) (bank : List R) :=
  unitChildAt u⁻¹ 0 width (i.val*width) (childAt 0 width (i.val*width) bank)

theorem pairOnBank_fields (i : Fin n) (u : Rˣ) (x : Fin b → Fin (n+1) → R) :
    pairOnBank b i u (bankFields (List.finRange (n+1)) x) =
      bankFields (List.finRange (n+1)) (fun k j => (pair i u j : R) * x k j) := by
  obtain ⟨pre,gap,post,eqn,hp,hg,hi,hj⟩ := split_rows 0 i.succ (Fin.succ_pos i)
  have empty : pre = [] := List.length_eq_zero_iff.mp hp
  subst pre
  simp at hg
  simp only [List.nil_append,List.mem_append,not_or] at hi hj
  have unchanged (l : List (Fin (n+1))) (h : 0 ∉ l) (h' : i.succ ∉ l) :
      bankFields l (fun k j => (pair i u j : R) * x k j) = bankFields l x := by
    apply bankFields_congr
    intro j mem k
    induction j using Fin.cases with
    | zero => exact False.elim (h mem)
    | succ j =>
      have ne : j ≠ i := by rintro rfl; exact h' mem
      simp [pair,ne]
  have step := pairAt_fields u [] (List.ofFn fun k => x k 0) (bankFields gap x)
    (List.ofFn fun k => x k i.succ) (bankFields post x) (by simp)
  rw [bankFields_length,hg] at step
  conv at step => rhs; rw [← unchanged gap hi.1 hj.1,← unchanged post hi.2 hj.2]
  simpa [pairOnBank,eqn,bankFields,pair,List.flatMap_append,List.map_ofFn,Function.comp_def] using step

def anchorOnBank (width : ℕ) (s : Rˣ) (bank : List R) :=
  (bank.take width).map (fun t => (s : R)*t) ++ bank.drop width

theorem anchorOnBank_fields (s : Rˣ) (x : Fin b → Fin (n+1) → R) :
    anchorOnBank b s (bankFields (List.finRange (n+1)) x) =
      bankFields (List.finRange (n+1)) (fun k j =>
        ↑((Fin.cons s (fun _ => 1) : Fin (n+1) → Rˣ) j) * x k j) := by
  simp [anchorOnBank,List.finRange_succ,bankFields,List.map_ofFn,List.flatMap_map,Function.comp_def]

def fallbackBank (b : ℕ) (s : Rˣ) (d : Fin n → Rˣ) (ops : List (RowOp (n+1) R))
    (bank : List R) : List R :=
  let scaled := (List.finRange n).foldl (fun z i => pairOnBank b i (d i) z) (anchorOnBank b s bank)
  ops.foldl (fun z op => op.onBank b z) scaled

theorem fallbackBank_fields (s : Rˣ) (d : Fin n → Rˣ) (ops : List (RowOp (n+1) R))
    (x : Fin b → Fin (n+1) → R) :
    fallbackBank b s d ops (bankFields (List.finRange (n+1)) x) =
      bankFields (List.finRange (n+1)) (fun k => ops.foldl (fun y op => op.apply y)
        (applyPairs d (List.finRange n) (fun j => ↑((Fin.cons s (fun _ => 1) : Fin (n+1) → Rˣ) j) * x k j))) := by
  have pairs (l : List (Fin n)) (y : Fin b → Fin (n+1) → R) :
      l.foldl (fun z i => pairOnBank b i (d i) z) (bankFields (List.finRange (n+1)) y) =
        bankFields (List.finRange (n+1)) (fun k => applyPairs d l (y k)) := by
    induction l generalizing y with
    | nil => rfl
    | cons i l ih => simp only [List.foldl_cons,pairOnBank_fields,ih,applyPairs]
  simp only [fallbackBank,anchorOnBank_fields,pairs,rowWord_onBank]

/-- One fallback schedule works on flat banks of every field width. -/
theorem residual_onBank {ι : Type*} [Fintype ι] [DecidableEq ι] {q w m : ℕ} [Fact q.Prime]
    (hodd : 2 < q) (hw : 0 < w) (dim : n+1 = 2*m) (e : (ι ⊕ ι) ≃ Fin (n+1))
    (A A' C P : Matrix ι ι (ZMod (q ^ w))) (hA : A * A' = 1) (hA' : A' * A = 1)
    (hC : C * C = 1) (hP : P * P = P) :
    ∃ (s : (ZMod (q^w))ˣ) (d : Fin n → (ZMod (q^w))ˣ) (ops : List (RowOp (n+1) (ZMod (q^w)))),
      (s = 1 ∨ s = -1) ∧ (ops.map RowOp.children).sum + 2*n < 24*m^2 ∧
      ∀ b (x : Fin b → Fin (n+1) → ZMod (q^w)),
        fallbackBank b s d ops (bankFields (List.finRange (n+1)) x) =
          bankFields (List.finRange (n+1)) (fun k =>
            (Matrix.reindex e e (residual A A' C P)).mulVec (x k)) := by
  obtain ⟨s,d,ops,hs,cost,action⟩ := residual_word hodd hw dim e A A' C P hA hA' hC hP
  exact ⟨s,d,ops,hs,cost,fun b x => by simp only [fallbackBank_fields,action]⟩

/-- A fixed residue itinerary and its sign-table entry work for all lifts in the class. -/
theorem itinerary_onBank {q w : ℕ} [hq : Fact q.Prime] (hodd : 2 < q) (hw : 0 < w)
    (p : Fin (n+1) → Fin (n+1)) (M : Matrix (Fin (n+1)) (Fin (n+1)) (ZMod q))
    (hv : Itinerary.Valid p M (n+1)) (G : Matrix (Fin (n+1)) (Fin (n+1)) (ZMod (q^w)))
    (lift : (LabelRing.res q w hw).mapMatrix G = M) (hg : G.det = 1 ∨ G.det = -1) :
    let s : (ZMod (q^w))ˣ := if negativeAnchor p M then -1 else 1
    ∃ (d : Fin n → (ZMod (q^w))ˣ) (ops : List (RowOp (n+1) (ZMod (q^w)))),
      (ops.map RowOp.children).sum ≤ 6*((n+1)*n) + 3*(n+1) ∧
      ∀ b (x : Fin b → Fin (n+1) → ZMod (q^w)),
        fallbackBank b s d ops (bankFields (List.finRange (n+1)) x) =
          bankFields (List.finRange (n+1)) (fun k => G.mulVec (x k)) := by
  subst M
  have valid := (Itinerary.valid_map_iff (LabelRing.res q w hw)
    (fun a ha => (LabelRing.isUnit_iff_res q w hw a).mpr ha.ne_zero) p G (n+1)).mpr hv
  obtain ⟨E,d,hE,he⟩ := itinerary_pairs hodd hw p G valid hg
  obtain ⟨ops,cost,undo⟩ := hE.undo_word
  refine ⟨d,ops,cost,fun b x => ?_⟩
  rw [fallbackBank_fields]
  congr 1
  funext k
  rw [← undo (G.mulVec (x k)),Matrix.mulVec_mulVec,he]
  congr 1
  ext j
  simp [applyPairs_eq,Matrix.mulVec_diagonal,Finset.prod_apply,Units.coe_prod,
    List.prod_ofFn,← List.ofFn_eq_map,mul_left_comm,mul_assoc]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
