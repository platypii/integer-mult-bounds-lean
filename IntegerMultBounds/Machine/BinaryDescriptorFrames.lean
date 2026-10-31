module

public import IntegerMultBounds.Machine.BinaryDescriptorStackAt
public import IntegerMultBounds.Machine.ExactFrame

/-! A fixed list of runtime-length descriptor fields, pushed in list order and
popped in reverse order. Only the tape slots, not any descriptor bits or lengths,
enter the finite control. The stack's older contents may be arbitrary. -/

@[expose] public section

namespace IntegerMultBounds.Machine.BinaryDescriptorFrames
open SharedPlacementAlphabet (setTape)
open BinaryDescriptorStack
variable {t a : ℕ}

abbrev Slot (stack : Fin t) := {i : Fin t // i ≠ stack}

def pushStates {stack : Fin t} : List (Slot stack) → ℕ
  | [] => 1
  | _::ops => 8+pushStates ops

def popStates {stack : Fin t} : List (Slot stack) → ℕ
  | [] => 1
  | _::ops => popStates ops+8

noncomputable def pushProgram (stack : Fin t) : (ops : List (Slot stack)) → Program t (pushStates ops) a
  | [] => skip t a (Nat.zero_lt_of_lt stack.isLt)
  | op::ops => seq (BinaryDescriptorStackAt.pushProgram op.val stack op.property) (pushProgram stack ops)

noncomputable def popProgram (stack : Fin t) : (ops : List (Slot stack)) → Program t (popStates ops) a
  | [] => skip t a (Nat.zero_lt_of_lt stack.isLt)
  | op::ops => seq (popProgram stack ops) (BinaryDescriptorStackAt.popProgram stack op.val op.property.symm)

def write (stack : Fin t) (i : Slot stack) (xs : Fin t → List Bool) (v : Tapes t a) : Tapes t a :=
  setTape v stack (frame (v.tape stack) (v.head stack) (xs i)) (v.head stack+1+(xs i).length)

def saved (stack : Fin t) : List (Slot stack) → (Fin t → List Bool) → Tapes t a → Tapes t a
  | [],_,v => v
  | i::ops,xs,v => saved stack ops xs (write stack i xs v)

def restored {stack : Fin t} : List (Slot stack) → (Fin t → List Bool) → Tapes t a → Tapes t a
  | [],_,v => v
  | i::ops,xs,v => setTape (restored ops xs v) i.val (descriptor (xs i)) 1

def cost {stack : Fin t} (ops : List (Slot stack)) (xs : Fin t → List Bool) : ℕ :=
  (ops.map (fun i : Slot stack => 2*(xs i).length+8)).sum

def span {stack : Fin t} (ops : List (Slot stack)) (xs : Fin t → List Bool) : ℕ :=
  (ops.map (fun i : Slot stack => 1+(xs i).length)).sum

def Free (stack : Fin t) (ops : List (Slot stack)) (xs : Fin t → List Bool) (v : Tapes t a) : Prop :=
  ∀ z, v.head stack ≤ z → z < v.head stack+span ops xs → v.tape stack z = blank

theorem saved_frame (stack : Fin t) (ops : List (Slot stack)) (xs : Fin t → List Bool)
    (v : Tapes t a) (i : Fin t) (hi : i ≠ stack) :
    (saved stack ops xs v).head i = v.head i ∧ (saved stack ops xs v).tape i = v.tape i := by
  induction ops generalizing v with
  | nil => exact ⟨rfl,rfl⟩
  | cons op ops ih => simpa [saved,write,setTape,hi] using ih (write stack op xs v)

theorem restored_frame {stack : Fin t} (ops : List (Slot stack)) (xs : Fin t → List Bool)
    (v : Tapes t a) (i : Fin t) (hi : ∀ op ∈ ops, i ≠ op.val) :
    (restored ops xs v).head i = v.head i ∧ (restored ops xs v).tape i = v.tape i := by
  induction ops with
  | nil => exact ⟨rfl,rfl⟩
  | cons op ops ih =>
    have h0 := hi op List.mem_cons_self
    simpa [restored,setTape,h0] using ih (fun j hj => hi j (List.mem_cons_of_mem _ hj))

theorem restored_stack {stack : Fin t} (ops : List (Slot stack)) (xs : Fin t → List Bool) (v : Tapes t a) :
    (restored ops xs v).head stack = v.head stack ∧ (restored ops xs v).tape stack = v.tape stack :=
  restored_frame ops xs v stack (fun op _ => op.property.symm)

private theorem set_comm (v : Tapes t a) (i j : Fin t) (h : i ≠ j)
    (f g : ℤ → Fin (a+4)) (p q : ℤ) :
    setTape (setTape v i f p) j g q = setTape (setTape v j g q) i f p := by
  apply congrArg₂ Tapes.mk <;> funext k <;> by_cases hi : k = i <;> by_cases hj : k = j <;>
    simp_all [setTape]

private theorem restored_setStack {stack : Fin t} (ops : List (Slot stack)) (xs : Fin t → List Bool)
    (v : Tapes t a) (f : ℤ → Fin (a+4)) (p : ℤ) :
    restored ops xs (setTape v stack f p) = setTape (restored ops xs v) stack f p := by
  induction ops with
  | nil => rfl
  | cons i ops ih => rw [restored,ih,set_comm _ stack i.val i.property.symm]; rfl

private theorem free_tail (stack : Fin t) (i : Slot stack) (ops : List (Slot stack))
    (xs : Fin t → List Bool) (v : Tapes t a) (hf : Free stack (i::ops) xs v) :
    Free stack ops xs (write stack i xs v) := by
  intro z hz he
  simp only [write,setTape,Function.update_self] at hz he ⊢
  rw [frame_outside _ _ _ _ (Or.inr hz)]
  apply hf z (by omega)
  simpa only [span,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one] using (show z < v.head stack+(1+(xs i).length+span ops xs : ℕ) by omega)

theorem push_hoare (stack : Fin t) (ops : List (Slot stack)) (xs : Fin t → List Bool) (v : Tapes t a)
    (hs : ∀ i ∈ ops, v.head i = 1 ∧ v.tape i = descriptor (xs i)) :
    HoareTime (pushProgram stack ops) (fun w => w = v) (fun w => w = saved stack ops xs v) (cost ops xs) := by
  induction ops generalizing v with
  | nil => exact skip_hoare _ v
  | cons i ops ih =>
    have h0 := hs i List.mem_cons_self
    have hp := BinaryDescriptorStackAt.push_hoare i.val stack i.property v (xs i) h0.2 h0.1
    have ht := ih (write stack i xs v) (by
      intro j hj
      simpa only [write,setTape,Function.update_of_ne j.property] using hs j (List.mem_cons_of_mem _ hj))
    exact (hp.seq ht).consequence (fun _ h => h) (fun _ h => h) (by simp only [cost,List.map_cons,List.sum_cons]; omega)

theorem pop_hoare (stack : Fin t) (ops : List (Slot stack)) (hu : ops.Nodup)
    (xs : Fin t → List Bool) (v : Tapes t a)
    (hd : ∀ i ∈ ops, v.head i = 0 ∧ v.tape i = fun _ => blank)
    (hf : Free stack ops xs v) :
    HoareTime (popProgram stack ops) (fun w => w = saved stack ops xs v)
      (fun w => w = restored ops xs v) (cost ops xs) := by
  induction ops generalizing v with
  | nil => exact skip_hoare _ v
  | cons i ops ih =>
    have hu' := List.nodup_cons.mp hu
    have ht := ih hu'.2 (write stack i xs v) (by
      intro j hj
      simpa only [write,setTape,Function.update_of_ne j.property] using hd j (List.mem_cons_of_mem _ hj))
      (free_tail stack i ops xs v hf)
    have hstack := restored_stack ops xs (write stack i xs v)
    have hi := restored_frame ops xs (write stack i xs v) i.val (by
      intro j hj he
      exact hu'.1 (by have hij : i = j := Subtype.ext he; simpa [hij] using hj))
    simp only [write,setTape,Function.update_of_ne i.property] at hi
    have hdi := hd i List.mem_cons_self
    have hp := BinaryDescriptorStackAt.pop_hoare stack i.val i.property.symm
      (restored ops xs (write stack i xs v)) (v.tape stack) (v.head stack) (xs i)
      (by simpa [write,setTape] using hstack.2) (by simpa [write,setTape] using hstack.1)
      (hi.2.trans hdi.2)
      (hi.1.trans hdi.1)
      (by
        intro z hz he
        apply hf z hz
        simp only [span,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one]
        omega)
    have heq : setTape (restored ops xs (write stack i xs v)) stack (v.tape stack) (v.head stack) = restored ops xs v := by
      rw [write,restored_setStack,SharedPlacementAlphabet.setTape_setTape]
      rw [← restored_setStack,SharedPlacementAlphabet.setTape_self]
    have hp' := hp.consequence (fun _ h => h) (fun w hw => by simpa only [heq] using hw) le_rfl
    exact (ht.seq hp').consequence (fun _ h => h) (fun _ h => h) (by simp only [cost,List.map_cons,List.sum_cons]; omega)

/-- The next-free stack position includes one delimiter per runtime word. -/
theorem saved_head (stack : Fin t) (ops : List (Slot stack)) (xs : Fin t → List Bool) (v : Tapes t a) :
    (saved stack ops xs v).head stack = v.head stack+span ops xs := by
  induction ops generalizing v with
  | nil => simp [saved,span]
  | cons i ops ih =>
    rw [saved,ih]
    simp only [write,setTape,Function.update_self,span,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one]
    omega

/-- Older frames and all cells beyond the allocated interval are unchanged. -/
theorem saved_outside (stack : Fin t) (ops : List (Slot stack)) (xs : Fin t → List Bool)
    (v : Tapes t a) (z : ℤ) (hz : z < v.head stack ∨ v.head stack+span ops xs ≤ z) :
    (saved stack ops xs v).tape stack z = v.tape stack z := by
  induction ops generalizing v with
  | nil => rfl
  | cons i ops ih =>
    simp only [span,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one] at hz
    rw [saved,ih (write stack i xs v) (by simp only [write,setTape,Function.update_self,span]; omega)]
    simp only [write,setTape,Function.update_self]
    exact frame_outside _ _ _ _ (by omega)

/-- Every requested field returns to its own slot with its exact word/head. -/
theorem restored_field {stack : Fin t} (ops : List (Slot stack)) (hu : ops.Nodup)
    (xs : Fin t → List Bool) (v : Tapes t a) (i : Slot stack) (hi : i ∈ ops) :
    (restored ops xs v).head i = 1 ∧ (restored ops xs v).tape i = descriptor (xs i) := by
  induction ops with
  | nil => exact (List.not_mem_nil hi).elim
  | cons j ops ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp hu
    rcases List.mem_cons.mp hi with rfl | hi
    · simp [restored,setTape]
    · have hne : i.val ≠ j.val := by
        intro he
        have hij : i = j := Subtype.ext he
        exact hn (by simpa [hij] using hi)
      simpa only [restored,setTape,Function.update_of_ne hne] using ih ht hi

/-- Explicit sum of runtime word lengths plus the fixed per-field overhead. -/
theorem cost_eq {stack : Fin t} (ops : List (Slot stack)) (xs : Fin t → List Bool) :
    cost ops xs = 2*(ops.map (fun i : Slot stack => (xs i).length)).sum+8*ops.length := by
  induction ops with
  | nil => rfl
  | cons i ops ih =>
    simp only [cost,List.map_cons,List.sum_cons,List.length_cons] at *
    omega

theorem cost_le {stack : Fin t} (ops : List (Slot stack)) (xs : Fin t → List Bool)
    (L : ℕ) (hL : ∀ i ∈ ops, (xs i).length ≤ L) : cost ops xs ≤ ops.length*(2*L+8) := by
  induction ops with
  | nil => simp [cost]
  | cons i ops ih =>
    have h0 := hL i List.mem_cons_self
    have ht := ih (fun j hj => hL j (List.mem_cons_of_mem _ hj))
    simp only [cost,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

/-- In particular, a fixed six-field descriptor frame has this uniform cost. -/
theorem six_field_cost {stack : Fin t} (ops : List (Slot stack)) (hlen : ops.length = 6)
    (xs : Fin t → List Bool) (L : ℕ) (hL : ∀ i ∈ ops, (xs i).length ≤ L) :
    cost ops xs ≤ 12*L+48 := by
  have h := cost_le ops xs L hL
  rw [hlen] at h
  omega

/-- Storage depends on field lengths, independently of push/pop runtime. -/
theorem span_le {stack : Fin t} (ops : List (Slot stack)) (xs : Fin t → List Bool)
    (L : ℕ) (hL : ∀ i ∈ ops, (xs i).length ≤ L) : span ops xs ≤ ops.length*(L+1) := by
  induction ops with
  | nil => simp [span]
  | cons i ops ih =>
    have h := hL i List.mem_cons_self
    have ht := ih (fun j hj => hL j (List.mem_cons_of_mem _ hj))
    simp only [span] at ht
    simp only [span,List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [h,ht]

end IntegerMultBounds.Machine.BinaryDescriptorFrames
