import IntegerMultBounds.Machine.CyclicRowMerge
import IntegerMultBounds.Machine.RecursiveInterchangeRows

/-! A radix digit can cross an arbitrary spectator block using one cyclic
split with block-length rows and one cyclic merge with singleton rows.
The same role words connect the two actual streaming primitives. -/
namespace IntegerMultBounds.Machine.RadixDigitMoveRows
open RecursiveInterchangeRows (pack pack_val)
variable {P Q S a : ℕ}

def splitRows (x : Fin (P*Q*S) → Fin (a+4)) (p : Fin P) (j : Fin Q) : List (Fin (a+4)) :=
  List.ofFn (fun s : Fin S => x (pack (pack p j) s))

def role (x : Fin (P*Q*S) → Fin (a+4)) (j : Fin Q) : Fin (P*S) → Fin (a+4) := fun z =>
  let ps := finProdFinEquiv.symm z
  x (pack (pack ps.1 j) ps.2)

def mergeRows (x : Fin (P*Q*S) → Fin (a+4)) (ps : Fin (P*S)) (j : Fin Q) : List (Fin (a+4)) :=
  [role x j ps]

def move (x : Fin (P*Q*S) → Fin (a+4)) : Fin (P*S*Q) → Fin (a+4) := fun z =>
  let psj := finProdFinEquiv.symm z
  role x psj.2 psj.1

theorem move_entry (x : Fin (P*Q*S) → Fin (a+4)) (p : Fin P) (s : Fin S) (j : Fin Q) :
    move x (pack (pack p s) j) = x (pack (pack p j) s) := by simp [move,role,pack]

private theorem ofFn_pack {m n : ℕ} {α : Type*} (f : Fin (m*n) → α) :
    List.ofFn f = (List.ofFn fun i : Fin m => List.ofFn fun j : Fin n => f (pack i j)).flatten := by
  simpa only [pack,finProdFinEquiv,Equiv.coe_fn_mk,Nat.add_comm,Nat.mul_comm] using List.ofFn_mul f

private theorem singleton_ofFn {n : ℕ} {α : Type*} (f : Fin n → α) :
    (List.ofFn (fun i => [f i])).flatten = List.ofFn f := by
  simpa only [List.flatMap_def,List.map_ofFn,Function.comp_def] using
    List.flatMap_singleton' (List.ofFn f)

theorem split_source (x : Fin (P*Q*S) → Fin (a+4)) :
    CyclicRowSplit.sourceWord (splitRows x) = List.ofFn x := by
  let regrouped := fun z : Fin (P*(Q*S)) => x (Fin.cast (Nat.mul_assoc P Q S).symm z)
  have hc : List.ofFn regrouped = List.ofFn x := by
    exact (List.ofFn_congr (Nat.mul_assoc P Q S) x).symm
  rw [← hc,ofFn_pack]
  unfold CyclicRowSplit.sourceWord CyclicRowSplit.cycleWords
  congr 1
  apply congrArg List.ofFn
  funext p
  rw [ofFn_pack]
  congr 1
  apply congrArg List.ofFn
  funext j
  apply congrArg List.ofFn
  funext s
  unfold regrouped
  apply congrArg x
  apply Fin.ext
  simp only [Fin.val_cast,pack_val]
  ring

theorem split_role (x : Fin (P*Q*S) → Fin (a+4)) (j : Fin Q) :
    CyclicRowSplit.roleWord (splitRows x) j = List.ofFn (role x j) := by
  rw [ofFn_pack]
  simp only [CyclicRowSplit.roleWord,splitRows,role,pack,Equiv.symm_apply_apply]

theorem merge_role (x : Fin (P*Q*S) → Fin (a+4)) (j : Fin Q) :
    CyclicRowSplit.roleWord (mergeRows x) j = List.ofFn (role x j) := by
  exact singleton_ofFn (role x j)

theorem role_compatible (x : Fin (P*Q*S) → Fin (a+4)) (j : Fin Q) :
    CyclicRowSplit.roleWord (splitRows x) j = CyclicRowSplit.roleWord (mergeRows x) j := by
  rw [split_role,merge_role]

theorem merge_source (x : Fin (P*Q*S) → Fin (a+4)) :
    CyclicRowSplit.sourceWord (mergeRows x) = List.ofFn (move x) := by
  rw [ofFn_pack]
  unfold CyclicRowSplit.sourceWord CyclicRowSplit.cycleWords mergeRows
  congr 1
  apply congrArg List.ofFn
  funext ps
  simpa only [move,pack,Equiv.symm_apply_apply] using singleton_ofFn (fun j => role x j ps)

theorem split_length (x : Fin (P*Q*S) → Fin (a+4)) (p : Fin P) (j : Fin Q) :
    (splitRows x p j).length = S := by simp [splitRows]

theorem merge_length (x : Fin (P*Q*S) → Fin (a+4)) (ps : Fin (P*S)) (j : Fin Q) :
    (mergeRows x ps j).length = 1 := rfl

end IntegerMultBounds.Machine.RadixDigitMoveRows
