module

public import IntegerMultBounds.MathlibTM2.Host.StackLoops
public import IntegerMultBounds.MathlibTM2.StackNativeStock

/-! Native swap lifecycle traces retain their existing executions. Guarded
unload and sieve loops do not increase boundary stock; list setup costs only
its fixed number of registers, independently of stream lengths. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {s t : Store (HΓ (T := T) A) (HS T Q A U)} {n : ℕ}

private theorem nonempty_of_flag {xs : List (Fin (A+4))} {flag : Bool}
    (hf : flag = xs.head?.isSome) (ht : flag = true) : xs ≠ [] := by
  intro hx
  simp [hx] at hf
  simp [hf] at ht

theorem unload_within (i : Fin T) (he : Exec body (unload i) s n t)
    (depth B : ℕ) (hb : mnSize s+depth ≤ B) :
    ExecWithin body (fun d z => mnSize z+d ≤ B) depth (unload i) s n t := by
  cases he with
  | seq hp hq =>
    cases hp
    have hg := mn_act_size (peekL (Q := Q) (A := A) (U := U) i) s
    rw [show mnActPush (peekL (Q := Q) (A := A) (U := U) i) = 0 from rfl,Nat.add_zero] at hg
    apply ExecWithin.seq (.act _ _ hb (by omega))
    apply loop_action_within body (unloadStep i) (·.flag)
      (fun z => z.var.flag = (z.stk (.lt i)).head?.isSome) ?_ hq (by rfl) depth B (by omega)
    intro z hz hf
    constructor
    · simp [unloadStep,peekL,Action.run]
    · apply mn_pop_one_push z (.lt i) _ _ (by simp [mnActPush,peekL])
      exact nonempty_of_flag hz hf

theorem sieve_within (i : Fin T) (he : Exec body (sieve i) s n t)
    (depth B : ℕ) (hb : mnSize s+depth ≤ B) :
    ExecWithin body (fun d z => mnSize z+d ≤ B) depth (sieve i) s n t := by
  cases he with
  | seq hp hq =>
    cases hp
    have hg := mn_act_size (peekR (Q := Q) (A := A) (U := U) i) s
    rw [show mnActPush (peekR (Q := Q) (A := A) (U := U) i) = 0 from rfl,Nat.add_zero] at hg
    apply ExecWithin.seq (.act _ _ hb (by omega))
    apply loop_action_within body (sieveStep i) (·.flag)
      (fun z => z.var.flag = (z.stk (.rt i)).head?.isSome) ?_ hq (by rfl) depth B (by omega)
    intro z hz hf
    constructor
    · simp [sieveStep,peekR,Action.run]
      split <;> simp
    · apply mn_pop_one_push z (.rt i) _ _ (by simp [mnActPush,peekR])
      exact nonempty_of_flag hz hf

theorem normTape_within (i : Fin T) (he : Exec body (normTape i) s n t)
    (depth B : ℕ) (hb : mnSize s+depth ≤ B) :
    ExecWithin body (fun d z => mnSize z+d ≤ B) depth (normTape i) s n t := by
  cases he with
  | seq hp hq =>
    cases hq with
    | seq hq hr =>
      have hw := unload_within i hp depth B hb
      have hx := sieve_within i hq depth B hw.final
      exact .seq hw (.seq hx (unload_within i hr depth B hx.final))

theorem normList_within (l : List (Fin T)) (he : Exec body (normList l) s n t)
    (depth B : ℕ) (hb : mnSize s+depth ≤ B) :
    ExecWithin body (fun d z => mnSize z+d ≤ B) depth (normList l) s n t := by
  induction l generalizing s n t with
  | nil =>
    cases he
    exact .act _ _ hb hb
  | cons i l ih =>
    cases he with
    | seq hp hq =>
      have hw := normTape_within i hp depth B hb
      exact .seq hw (ih hq hw.final)

private theorem list_action_native (a : Fin T → Act T Q A U) (c : ℕ)
    (ha : ∀ i, mnActPush (a i) ≤ c) (l : List (Fin T)) :
    mnNativePushBound c (Prog.seqList (l.map fun i => (Prog.act (a i) : Pr P T Q A U))) := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons i l ih => exact ⟨ha i,ih⟩

theorem markList_within (l : List (Fin T))
    (he : Exec body (markList l) s (l.length+1) t) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize s+depth+(l.length+1))
      depth (markList l) s (l.length+1) t :=
  mn_native_exec_within he 1 (list_action_native markStep 1 (fun _ => by simp [markStep,mnActPush]) l)
    depth _ (by omega)

theorem shiftList_within (l : List (Fin T))
    (he : Exec body (shiftList l) s (l.length+1) t) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize s+depth+(l.length+1))
      depth (shiftList l) s (l.length+1) t :=
  mn_native_exec_within he 1 (list_action_native shiftStep 1 (fun _ => by simp [shiftStep,mnActPush]) l)
    depth _ (by omega)

theorem dropList_within (l : List (Fin T)) (he : Exec body (dropList l) s n t)
    (depth B : ℕ) (hb : mnSize s+depth ≤ B) :
    ExecWithin body (fun d z => mnSize z+d ≤ B) depth (dropList l) s n t :=
  mn_native_exec_within he 0 (list_action_native dropStep 0 (fun _ => by simp [dropStep,mnActPush]) l)
    depth B (by omega)

end IntegerMultBounds.MathlibTM2.Host
