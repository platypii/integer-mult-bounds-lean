module

public import IntegerMultBounds.MathlibTM2.Host.Core

/-! Save a caller stack in return labels while the recursive worker reuses its tape. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2

variable {T Q A : ℕ} {U P : Type}

/-- Both sides of a physical tape hold symbols of the same alphabet. -/
structure TapeSide (T : ℕ) where
  tape : Fin T
  left : Bool

namespace TapeSide

def contents (i : TapeSide T) (S : Stacks T A) :=
  if i.left then S.L i.tape else S.R i.tape

def write (i : TapeSide T) (S : Stacks T A) (xs : List (Fin (A+4))) : Stacks T A :=
  if i.left then {S with L := Function.update S.L i.tape xs}
  else {S with R := Function.update S.R i.tape xs}

@[simp] theorem read_write (i : TapeSide T) (S : Stacks T A) (xs) :
    i.contents (i.write S xs) = xs := by cases i with | mk j l => cases l <;> simp [contents,write]

@[simp] theorem write_read (i : TapeSide T) (S : Stacks T A) :
    i.write S (i.contents S) = S := by cases i with | mk j l => cases l <;> simp [contents,write]

@[simp] theorem write_write (i : TapeSide T) (S : Stacks T A) (xs ys) :
    i.write (i.write S xs) ys = i.write S ys := by cases i with | mk j l => cases l <;> simp [write]

def push (i : TapeSide T) (x : Fin (A+4)) : Act T Q A U :=
  if i.left then .push (.lt i.tape) (fun _ => x) .done else .push (.rt i.tape) (fun _ => x) .done

def pop (i : TapeSide T) : Act T Q A U :=
  if i.left then .pop (.lt i.tape) (fun v o => {v with sym := o}) .done
  else .pop (.rt i.tape) (fun v o => {v with sym := o}) .done

@[simp] theorem push_run (i : TapeSide T) (x) (v : HS T Q A U) (S : Stacks T A) :
    (i.push x).run (Host.mk v S) = Host.mk v (i.write S (x :: i.contents S)) := by
  cases i with | mk j l => cases l <;> simp [push,contents,write,Action.run,update_lt,update_rt]

@[simp] theorem pop_run (i : TapeSide T) (v : HS T Q A U) (S : Stacks T A) :
    i.pop.run (Host.mk v S) = Host.mk {v with sym := (i.contents S).head?} (i.write S (i.contents S).tail) := by
  cases i with | mk j l => cases l <;> simp [pop,contents,write,Action.run,update_lt,update_rt]

end TapeSide

/-- Each successful branch has a distinct continuation which restores its symbol. -/
def resumeSymbol (i : TapeSide T) (again : P) (child : Pr P T Q A U) :
    List (Fin (A+4)) → Pr P T Q A U
  | [] => child
  | x::xs => .cond (fun v => v.sym == some x)
      (.seq (.call again) (.act (i.push x)))
      (resumeSymbol i again child xs)

def suspendSide (i : TapeSide T) (again : P) (child : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act i.pop)
    (resumeSymbol i again child (List.finRange (A+4)))

private theorem resumeSymbol_run (body : P → Pr P T Q A U) (i : TapeSide T) (again : P)
    (child : Pr P T Q A U) (xs : List (Fin (A+4))) (v z : HS T Q A U)
    (S F : Stacks T A) (steps : ℕ)
    (run : match v.sym with
      | none => Exec body child (mk v S) steps (mk z F)
      | some x => x ∈ xs ∧ Exec body (.call again) (mk v S) steps (mk z F)) :
    ∃ n, n ≤ steps+xs.length+1 ∧ Exec body (resumeSymbol i again child xs) (mk v S) n
      (mk z (i.write F (v.sym.toList ++ i.contents F))) := by
  induction xs with
  | nil =>
    cases h : v.sym with
    | none => exact ⟨steps,by simp,by simpa [resumeSymbol,h] using (show Exec body child _ steps _ from by simpa [h] using run)⟩
    | some x => simp [h] at run
  | cons x xs ih =>
    by_cases h : v.sym = some x
    · simp only [h] at run
      refine ⟨steps+1+1,by simp,Exec.cond_true (by simp [h]) ?_⟩
      apply run.2.seq
      simpa [Action.run,h,update_rt] using
        (Exec.act (body := body) (i.push x) (mk z F))
    ·
      cases e : v.sym with
      | none =>
        obtain ⟨n,b,r⟩ := ih (by simpa [e] using run)
        exact ⟨n+1,by simp; omega,Exec.cond_false (by simp [e]) (by simpa only [e] using r)⟩
      | some y =>
        simp only [e,List.mem_cons] at run
        have ne : y ≠ x := by simpa [e] using h
        obtain ⟨n,b,r⟩ := ih (by simpa [e] using And.intro (run.1.resolve_left ne) run.2)
        exact ⟨n+1,by simp; omega,Exec.cond_false (by simp [e,ne]) (by simpa only [e] using r)⟩

/-- A worker runs on the freed stack and leaves it empty. Unwinding restores
all caller symbols while retaining the worker output on every other stack. -/
theorem suspendSide_run (body : P → Pr P T Q A U) (i : TapeSide T) (again : P)
    (child : Pr P T Q A U) (installed : body again = suspendSide i again child)
    (S F : Stacks T A) (empty : i.contents F = []) (price : ℕ)
    (xs : List (Fin (A+4))) (v z : HS T Q A U)
    (run : Exec body child (mk {v with sym := none} (i.write S [])) price (mk z F)) :
    ∃ n, n ≤ price+(A+8)*(xs.length+1) ∧
      Exec body (.call again) (mk v (i.write S xs)) n (mk z (i.write F xs)) := by
  induction xs generalizing v with
  | nil =>
    obtain ⟨t,b,r⟩ := resumeSymbol_run body i again child (List.finRange (A+4))
      {v with sym := none} z (i.write S []) F price run
    refine ⟨1+t+2,by simp at b ⊢; omega,Exec.call (installed ▸ Exec.seq (t := mk {v with sym := none} (i.write S [])) ?_ ?_)⟩
    · apply (Exec.act _ _).cast rfl
      simp
    · simpa [empty] using r
  | cons x xs ih =>
    obtain ⟨n,cost,rec⟩ := ih {v with sym := some x} run
    obtain ⟨t,b,r⟩ := resumeSymbol_run body i again child (List.finRange (A+4))
      {v with sym := some x} z (i.write S xs)
      (i.write F xs) n ⟨by simp,rec⟩
    refine ⟨1+t+2,by simp [Nat.mul_add] at b cost ⊢; omega,Exec.call (installed ▸ Exec.seq (t := mk {v with sym := some x} (i.write S xs)) ?_ ?_)⟩
    · apply (Exec.act _ _).cast rfl
      simp
    · simpa using r

/-- The same physical tape supplies both stacks to a child. Its entry procedure
recursively saves the left side, then the right, before entering the child. -/
theorem suspendTape_run (body : P → Pr P T Q A U) (i : Fin T) (left right : P)
    (child : Pr P T Q A U)
    (saveLeft : body left = suspendSide ⟨i,true⟩ left (.call right))
    (saveRight : body right = suspendSide ⟨i,false⟩ right child)
    (S F : Stacks T A) (cleanL : F.L i = []) (cleanR : F.R i = []) (price : ℕ)
    (v z : HS T Q A U)
    (worker : Exec body child (mk {v with sym := none}
      {S with L := Function.update S.L i [], R := Function.update S.R i []}) price (mk z F)) :
    ∃ n, n ≤ price+(A+8)*((S.L i).length+(S.R i).length+2) ∧
      Exec body (.call left) (mk v S) n
        (mk z {F with L := Function.update F.L i (S.L i), R := Function.update F.R i (S.R i)}) := by
  let L : TapeSide T := ⟨i,true⟩
  let R : TapeSide T := ⟨i,false⟩
  let saved := R.write F (S.R i)
  obtain ⟨m,paid,inner⟩ := suspendSide_run body R right child saveRight
    (L.write S []) F cleanR price (S.R i) {v with sym := none} z worker
  obtain ⟨n,cost,run⟩ := suspendSide_run body L left (.call right) saveLeft S saved
    cleanL m (S.L i) v z (by simpa [L,R,TapeSide.write,saved] using inner)
  refine ⟨n,?_,?_⟩
  · simp only [Nat.mul_add,Nat.mul_two,Nat.mul_one] at *
    omega
  · simpa [L,R,TapeSide.write,saved] using run

/-- The procedure chain visiting a physical bank before entering the worker. -/
inductive SuspendedBank (body : P → Pr P T Q A U) (child : Pr P T Q A U) :
    List (Fin T) → Pr P T Q A U → Prop
  | nil : SuspendedBank body child [] child
  | cons {i tail next left right} :
    body left = suspendSide ⟨i,true⟩ left (.call right) →
    body right = suspendSide ⟨i,false⟩ right next →
    SuspendedBank body child tail next → SuspendedBank body child (i::tail) (.call left)

/-- An installed frame uses two procedure labels per physical tape. The number
of labels is independent of the runtime depth. -/
def bankEntry {k : ℕ} (child : Pr ((Fin k × Bool) ⊕ P) T Q A U)
    (n : ℕ) (bound : n ≤ k) : Pr ((Fin k × Bool) ⊕ P) T Q A U :=
  match n with
  | 0 => child
  | j+1 => .call (.inl (⟨j,bound⟩,true))

def bankTable {k : ℕ} (ports : Fin k ↪ Fin T) (child : Pr ((Fin k × Bool) ⊕ P) T Q A U)
    (work : P → Pr ((Fin k × Bool) ⊕ P) T Q A U) :
    ((Fin k × Bool) ⊕ P) → Pr ((Fin k × Bool) ⊕ P) T Q A U
  | .inr p => work p
  | .inl (j,true) => suspendSide ⟨ports j,true⟩ (.inl (j,true)) (.call (.inl (j,false)))
  | .inl (j,false) => suspendSide ⟨ports j,false⟩ (.inl (j,false)) (bankEntry child j.val j.isLt.le)

theorem bankTable_installed {k : ℕ} (ports : Fin k ↪ Fin T)
    (child : Pr ((Fin k × Bool) ⊕ P) T Q A U) (work : P → Pr ((Fin k × Bool) ⊕ P) T Q A U)
    (n : ℕ) (bound : n ≤ k) :
    SuspendedBank (bankTable ports child work) child
      ((List.finRange n).reverse.map (fun i => ports ⟨i.val,i.isLt.trans_le bound⟩))
      (bankEntry child n bound) := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
    rw [List.finRange_succ_last,List.reverse_append,List.map_append]
    simpa [bankEntry,List.map_map,Function.comp_def] using
      (SuspendedBank.cons (i := ports ⟨n,bound⟩) (left := Sum.inl (⟨n,bound⟩,true))
        (right := Sum.inl (⟨n,bound⟩,false)) rfl rfl (ih (Nat.le_of_succ_le bound)))

/-- Replace exactly the designated physical tapes, including both sides. -/
def replaceBank (tapes : List (Fin T)) (S saved : Stacks T A) : Stacks T A :=
  {S with L := fun j => if j ∈ tapes then saved.L j else S.L j,
          R := fun j => if j ∈ tapes then saved.R j else S.R j}

/-- The total surcharge is linear in the caller symbols and number of saved tapes. -/
theorem SuspendedBank.replay {body : P → Pr P T Q A U} {child entry : Pr P T Q A U}
    {tapes : List (Fin T)} (chain : SuspendedBank body child tapes entry)
    (S F : Stacks T A) (distinct : tapes.Nodup)
    (clean : ∀ j ∈ tapes, F.L j = [] ∧ F.R j = []) (price : ℕ)
    (v z : HS T Q A U)
    (worker : Exec body child (mk (if tapes.isEmpty then v else {v with sym := none})
      (replaceBank tapes S {S with L := fun _ => [], R := fun _ => []})) price (mk z F)) :
    ∃ n, n ≤ price+(A+8)*(tapes.map (fun j => (S.L j).length+(S.R j).length+2)).sum ∧
      Exec body entry (mk v S) n (mk z (replaceBank tapes F S)) := by
  induction chain generalizing S v with
  | nil => exact ⟨price,by simp,by simpa [replaceBank] using worker⟩
  | @cons i tail next left right sl sr _ ih =>
    let D := {S with L := Function.update S.L i [], R := Function.update S.R i []}
    have away := (List.nodup_cons.mp distinct).1
    have eqInput : replaceBank tail D {D with L := fun _ => [], R := fun _ => []} =
        replaceBank (i::tail) S {S with L := fun _ => [], R := fun _ => []} := by
      unfold replaceBank
      congr 1 <;> funext j <;> by_cases h : j = i <;> simp [D,h,away]
    have mass : tail.map (fun j => (D.L j).length+(D.R j).length+2) =
        tail.map (fun j => (S.L j).length+(S.R j).length+2) := by
      apply List.map_congr_left
      intro j mem
      have ne : j ≠ i := fun e => away (e ▸ mem)
      simp [D,ne]
    obtain ⟨m,paid,inner⟩ := ih D (List.nodup_cons.mp distinct).2
      (fun j h => clean j (List.mem_cons_of_mem _ h)) {v with sym := none}
      (by simpa [eqInput] using worker)
    have fresh := clean i (by simp)
    obtain ⟨n,cost,run⟩ := suspendTape_run body i left right next sl sr S (replaceBank tail F D)
      (by simpa [replaceBank,away] using fresh.1) (by simpa [replaceBank,away] using fresh.2)
      m v z inner
    refine ⟨n,?_,?_⟩
    · rw [mass] at paid
      exact cost.trans ((Nat.add_le_add_right paid _).trans_eq (by simp; ring))
    · convert run using 1
      congr 2
      unfold replaceBank
      congr 1 <;> funext j <;> by_cases h : j = i <;> simp [D,h,away]

/-- Run the installed wrapper on the selected child ports, charging only their
initial contents. The child can write the payload and other tapes outside them. -/
theorem bankTable_run {k : ℕ} (ports : Fin k ↪ Fin T)
    (child : Pr ((Fin k × Bool) ⊕ P) T Q A U) (work : P → Pr ((Fin k × Bool) ⊕ P) T Q A U)
    (S F : Stacks T A) (price : ℕ) (clean : ∀ i, F.L (ports i) = [] ∧ F.R (ports i) = []) :
    let tapes := ((List.finRange k).map ports).reverse
    let body := bankTable ports child work
    (∀ v : HS T Q A U, ∃ z n, z.user = v.user ∧ n ≤ price ∧
      Exec body child (mk v (replaceBank tapes S {S with L := fun _ => [], R := fun _ => []}))
        n (mk z F)) → ∀ v : HS T Q A U, ∃ z n, z.user = v.user ∧
      n ≤ price+(A+8)*(tapes.map (fun j => (S.L j).length+(S.R j).length+2)).sum ∧
      Exec body (bankEntry child k le_rfl) (mk v S) n (mk z (replaceBank tapes F S)) := by
  intro tapes body worker v
  have installed : SuspendedBank body child tapes (bankEntry child k le_rfl) := by
    simpa [tapes,List.map_reverse,body] using bankTable_installed ports child work k le_rfl
  obtain ⟨z,m,user,paid,run⟩ := worker (if tapes.isEmpty then v else {v with sym := none})
  obtain ⟨n,cost,replay⟩ := installed.replay S F (by simpa [tapes] using (List.nodup_finRange k).map ports.injective)
    (by intro j hj; obtain ⟨i,_,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hj); exact clean i)
    m v z run
  exact ⟨z,n,by split at user <;> exact user,cost.trans (Nat.add_le_add_right paid _),replay⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
