import IntegerMultBounds.Machine.RadixDigitMoveRows

/-! Moving a radix digit across a spectator block preserves an arbitrary
following suffix. Long split rows have length S*E; merge rows have length E.
This is the serialization bridge needed for joining high digits in §4. -/
namespace IntegerMultBounds.Machine.RadixDigitMoveBlockRows
open RecursiveInterchangeRows (pack pack_val)
variable {P Q S E a : ℕ}

def splitRows (x : Fin (P*Q*(S*E)) → Fin (a+4)) :=
  RadixDigitMoveRows.splitRows x

def mergeRows (x : Fin (P*Q*(S*E)) → Fin (a+4)) (ps : Fin (P*S)) (j : Fin Q) : List (Fin (a+4)) :=
  let c := finProdFinEquiv.symm ps
  List.ofFn (fun e : Fin E => x (pack (pack c.1 j) (pack c.2 e)))

def move (x : Fin (P*Q*(S*E)) → Fin (a+4)) : Fin (P*S*Q*E) → Fin (a+4) := fun z =>
  let ge := finProdFinEquiv.symm z
  let psj := finProdFinEquiv.symm ge.1
  let ps := finProdFinEquiv.symm psj.1
  x (pack (pack ps.1 psj.2) (pack ps.2 ge.2))

/-- Inverse physical direction: take the digit after the spectator block
and place it immediately after the prefix, retaining the entire suffix. -/
def unmove (y : Fin (P*S*Q*E) → Fin (a+4)) : Fin (P*Q*(S*E)) → Fin (a+4) := fun z =>
  let pqse := finProdFinEquiv.symm z
  let pq := finProdFinEquiv.symm pqse.1
  let se := finProdFinEquiv.symm pqse.2
  y (pack (pack (pack pq.1 se.1) pq.2) se.2)

@[simp] theorem unmove_entry (y : Fin (P*S*Q*E) → Fin (a+4))
    (p : Fin P) (s : Fin S) (j : Fin Q) (e : Fin E) :
    unmove y (pack (pack p j) (pack s e)) = y (pack (pack (pack p s) j) e) := by
  simp [unmove,pack]

@[simp] theorem unmove_move (x : Fin (P*Q*(S*E)) → Fin (a+4)) :
    unmove (move x) = x := by
  funext z
  obtain ⟨⟨pq,se⟩,rfl⟩ := finProdFinEquiv.surjective z
  obtain ⟨⟨p,j⟩,rfl⟩ := finProdFinEquiv.surjective pq
  obtain ⟨⟨s,e⟩,rfl⟩ := finProdFinEquiv.surjective se
  simp [unmove,move,pack]

@[simp] theorem move_unmove (y : Fin (P*S*Q*E) → Fin (a+4)) :
    move (unmove y) = y := by
  funext z
  obtain ⟨⟨psj,e⟩,rfl⟩ := finProdFinEquiv.surjective z
  obtain ⟨⟨ps,j⟩,rfl⟩ := finProdFinEquiv.surjective psj
  obtain ⟨⟨p,s⟩,rfl⟩ := finProdFinEquiv.surjective ps
  simp [unmove,move,pack]

theorem move_entry (x : Fin (P*Q*(S*E)) → Fin (a+4))
    (p : Fin P) (s : Fin S) (j : Fin Q) (e : Fin E) :
    move x (pack (pack (pack p s) j) e) = x (pack (pack p j) (pack s e)) := by
  simp [move,pack]

private theorem ofFn_pack {m n : ℕ} {α : Type*} (f : Fin (m*n) → α) :
    List.ofFn f = (List.ofFn fun i : Fin m => List.ofFn fun j : Fin n => f (pack i j)).flatten := by
  simpa only [pack,finProdFinEquiv,Equiv.coe_fn_mk,Nat.add_comm,Nat.mul_comm] using List.ofFn_mul f

private theorem assoc_pack (p : Fin P) (s : Fin S) (e : Fin E) :
    Fin.cast (Nat.mul_assoc P S E) (pack (pack p s) e) = pack p (pack s e) := by
  apply Fin.ext
  simp only [Fin.val_cast,pack_val]
  ring

theorem split_source (x : Fin (P*Q*(S*E)) → Fin (a+4)) :
    CyclicRowSplit.sourceWord (splitRows x) = List.ofFn x := RadixDigitMoveRows.split_source x

theorem merge_source (x : Fin (P*Q*(S*E)) → Fin (a+4)) :
    CyclicRowSplit.sourceWord (mergeRows x) = List.ofFn (move x) := by
  have hr : mergeRows x = RadixDigitMoveRows.splitRows (move x) := by
    funext ps j
    apply congrArg List.ofFn
    funext e
    simp [move,pack]
  rw [hr]
  exact RadixDigitMoveRows.split_source (move x)

theorem merge_role (x : Fin (P*Q*(S*E)) → Fin (a+4)) (j : Fin Q) :
    CyclicRowSplit.roleWord (mergeRows x) j =
      List.ofFn (fun z : Fin (P*S*E) => RadixDigitMoveRows.role x j (Fin.cast (Nat.mul_assoc P S E) z)) := by
  rw [ofFn_pack]
  unfold CyclicRowSplit.roleWord
  congr 1
  apply congrArg List.ofFn
  funext ps
  apply congrArg List.ofFn
  funext e
  obtain ⟨⟨p,s⟩,rfl⟩ := finProdFinEquiv.surjective ps
  simp only [Equiv.symm_apply_apply]
  change x (pack (pack p j) (pack s e)) =
    RadixDigitMoveRows.role x j (Fin.cast (Nat.mul_assoc P S E) (pack (pack p s) e))
  rw [assoc_pack]
  simp [RadixDigitMoveRows.role,pack]

theorem role_compatible (x : Fin (P*Q*(S*E)) → Fin (a+4)) (j : Fin Q) :
    CyclicRowSplit.roleWord (splitRows x) j = CyclicRowSplit.roleWord (mergeRows x) j := by
  rw [merge_role]
  have hs := RadixDigitMoveRows.split_role x j
  exact hs.trans (List.ofFn_congr (Nat.mul_assoc P S E).symm (RadixDigitMoveRows.role x j))

theorem split_length (x : Fin (P*Q*(S*E)) → Fin (a+4)) (p : Fin P) (j : Fin Q) :
    (splitRows x p j).length = S*E := RadixDigitMoveRows.split_length x p j

theorem merge_length (x : Fin (P*Q*(S*E)) → Fin (a+4)) (ps : Fin (P*S)) (j : Fin Q) :
    (mergeRows x ps j).length = E := by simp [mergeRows]

end IntegerMultBounds.Machine.RadixDigitMoveBlockRows
