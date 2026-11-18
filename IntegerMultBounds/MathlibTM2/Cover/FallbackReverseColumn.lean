module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPivotStream
public import IntegerMultBounds.Machine.FlatCoordinateLayout
public import IntegerMultBounds.MathlibTM2.Cover.FallbackUndoItinerary

/-! Select one pivot for all row additions and the final exchange of a reverse column. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open Matrix GoodForm IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {T Q A d : ℕ} {P U R : Type} [CommRing R]

/-- Contents of the role tape after moving every original coordinate to its current address. -/
def PayloadAt {M W : ℕ} [NeZero M] {α : Type*} (sym : α → Fin (A+4))
    (source : ℤ → Fin (A+4)) (p : ℤ) (io : Fin T) (original : Fin (M^d*W) → α)
    (addr : (Fin d → ZMod M) → Fin d → ZMod M) (S : Stacks T A) : Prop :=
  ∃ word : Fin (M^d*W) → α,
    (∀ z, readAt blank (S.L io) (S.R io) (z-p) = putWord source p (List.ofFn (sym ∘ word)) z) ∧
    ∀ x (j : Fin W), word (FlatCoordinateLayout.index (addr x) j) = original (FlatCoordinateLayout.index x j)

/-- Compose a physical word permutation with the address map already realized on the tape. -/
theorem PayloadAt.step {M W : ℕ} [NeZero M] {α : Type*} {sym : α → Fin (A+4)}
    {source : ℤ → Fin (A+4)} {p : ℤ} {io : Fin T} {original : Fin (M^d*W) → α}
    {addr : (Fin d → ZMod M) → Fin d → ZMod M} {S F : Stacks T A}
    (before : PayloadAt sym source p io original addr S) (op : (Fin d → ZMod M) → Fin d → ZMod M)
    (move : ∀ a : Fin (M^d*W) → α,
      (∀ z, readAt blank (S.L io) (S.R io) (z-p) = putWord source p (List.ofFn (sym ∘ a)) z) →
      ∃ word : Fin (M^d*W) → α,
        (∀ z, readAt blank (F.L io) (F.R io) (z-p) = putWord source p (List.ofFn (sym ∘ word)) z) ∧
        ∀ x (j : Fin W), word (FlatCoordinateLayout.index (op x) j) = a (FlatCoordinateLayout.index x j)) :
    PayloadAt sym source p io original (op ∘ addr) F := by
  obtain ⟨a,tape,placed⟩ := before
  obtain ⟨word,next,step⟩ := move a tape
  exact ⟨word,next,fun x j => (step (addr x) j).trans (placed x j)⟩

def columnSteps (add : Fin d → Pr P T Q A U) (swap : Pr P T Q A U) : List (Fin d) → Pr P T Q A U
  | [] => swap
  | i :: rows => .seq (add i) (columnSteps add swap rows)

def reverseColumn (stream : Fin T) (k : Fin d) (add : Fin d → Fin d → Pr P T Q A U)
    (swap : Fin d → Pr P T Q A U) : Pr P T Q A U :=
  selectPivot stream (fun pivot => columnSteps (add pivot) (swap pivot) ((List.finRange d).erase k)) (List.finRange d)

/-- One execution transports every indexed address in the payload simultaneously. -/
theorem reverseColumn_exec {ι : Type*} (body : P → Pr P T Q A U) (stream : Fin T) (k : Fin d)
    (rows : Fin d → Fin d) (m : Matrix (Fin d) (Fin d) R) (inv : R)
    (add : Fin d → Fin d → Pr P T Q A U) (swap : Fin d → Pr P T Q A U)
    (ready : (ι → Fin d → R) → Stacks T A → Prop) (addCost swapCost : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (rest : List (Fin (A+4))) (x : ι → Fin d → R)
    (code : S.R stream = orderedScheduleCode (((List.finRange d).take (k.val+1)).reverse) rows ++ rest) :
    let pivot := rows k
    let c := fun i => m (Equiv.swap k pivot i) k * inv
    let tail := orderedScheduleCode (((List.finRange d).take k.val).reverse) rows ++ rest
    ready (fun a => stepOp k pivot m inv *ᵥ x a) {S with R := Function.update S.R stream tail} →
    (∀ i, i ≠ k → ∀ y (v : HS T Q A U) D, ready y D →
      ∃ z F n, z.user = v.user ∧ n ≤ addCost ∧ Exec body (add pivot i) (mk v D) n (mk z F) ∧
        ready (fun a => Function.update (y a) i (y a i + c i*y a k)) F) →
    (∀ y (v : HS T Q A U) D, ready y D →
      ∃ z F n, z.user = v.user ∧ n ≤ swapCost ∧ Exec body (swap pivot) (mk v D) n (mk z F) ∧
        ready (fun a => y a ∘ Equiv.swap k pivot) F) →
    ∃ z F n, z.user = v.user ∧ n ≤ 2*(pivot.val+1)+(d-1)*addCost+swapCost ∧
      Exec body (reverseColumn stream k add swap) (mk v S) n (mk z F) ∧ ready x F := by
  intro pivot c tail initial one exchange
  let apply := fun (y : Fin d → R) (op : RowOp d R) => op.apply y
  have loop (is : List (Fin d)) (hk : k ∉ is) (y : ι → Fin d → R) (v : HS T Q A U) D (ok : ready y D) :
      ∃ z F n, z.user = v.user ∧ n ≤ is.length*addCost+swapCost ∧
        Exec body (columnSteps (add pivot) (swap pivot) is) (mk v D) n (mk z F) ∧
        ready (fun a => ((is.flatMap fun i => addWord k i (c i)) ++ [RowOp.swap k pivot]).foldl apply (y a)) F := by
    induction is generalizing y v D with
    | nil => simpa [columnSteps,apply,RowOp.apply] using exchange y v D ok
    | cons i is ih =>
      have ne : i ≠ k := fun e => hk (by simp [e])
      obtain ⟨u,E,l,hu,hl,run,next⟩ := one i ne y v D ok
      obtain ⟨z,F,n,hz,hn,finish,result⟩ := ih (fun h => hk (List.mem_cons_of_mem _ h)) _ u E next
      refine ⟨z,F,l+n,hz.trans hu,by simp only [List.length_cons,Nat.succ_mul]; omega,Exec.seq run finish,?_⟩
      simpa only [List.flatMap_cons,List.append_assoc,List.foldl_append,apply,addWord_apply k i ne] using result
  let is := (List.finRange d).erase k
  have nodup := List.nodup_finRange d
  obtain ⟨z,F,n,hz,hn,run,result⟩ := loop is (by simp [is,nodup.mem_erase_iff]) _ {v with flag := false} _ initial
  have len : is.length = d-1 := by simp [is,List.length_erase_of_mem (List.mem_finRange k)]
  rw [len] at hn
  change ready (fun a => (undoColumnWord k pivot m inv).foldl _ (stepOp k pivot m inv *ᵥ x a)) F at result
  have undo : (fun a => (undoColumnWord k pivot m inv).foldl apply (stepOp k pivot m inv *ᵥ x a)) = x :=
    funext fun a => undoColumnWord_apply k pivot m inv (x a)
  rw [undo] at result
  exact ⟨z,F,_,hz,by omega,reversePivot_exec body stream _ rows k v S rest code run,result⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
