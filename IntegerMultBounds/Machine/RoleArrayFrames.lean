import IntegerMultBounds.Machine.RoleArrayStackAt

/-! A fixed list of inactive role arrays is destructively parked in order and
recovered in reverse. No payload symbol is reserved, all vacated role slots and
work clock return to blank/head-zero, and the exact older stack is restored. -/
namespace IntegerMultBounds.Machine.RoleArrayFrames
open SharedPlacementAlphabet (setTape)
variable {t a : ℕ}

structure Layout (t : ℕ) where
  stack : Fin t
  clock : Fin t
  count : Fin t
  stack_clock : stack ≠ clock
  stack_count : stack ≠ count
  clock_count : clock ≠ count

abbrev Role (L : Layout t) := {i : Fin t // i ≠ L.stack ∧ i ≠ L.clock ∧ i ≠ L.count}

def slots (L : Layout t) (i : Role L) : Fin 4 → Fin t := ![i.val,L.stack,L.clock,L.count]

theorem slots_injective (L : Layout t) (i : Role L) : Function.Injective (slots L i) := by
  intro j k h
  fin_cases j <;> fin_cases k <;>
    simp_all [slots,i.property.1,i.property.2.1,i.property.2.2,L.stack_clock,L.stack_count,L.clock_count,eq_comm]
  exact i.property.1 h.symm

def Controls (L : Layout t) (bs : List Bool) (v : Tapes t a) : Prop :=
  v.head L.clock = 0 ∧ v.tape L.clock = (fun _ => blank) ∧
  v.head L.count = 1 ∧ v.tape L.count = CountedLoopReuseAlphabet.binary bs

def saveOne (L : Layout t) (i : Role L) (n : ℕ) (v : Tapes t a) := RoleArrayStackAt.pushed (slots L i) v n

def saved (L : Layout t) : List (Role L) → ℕ → Tapes t a → Tapes t a
  | [],_,v => v
  | i::ops,n,v => saved L ops n (saveOne L i n v)

def Free (L : Layout t) (ops : List (Role L)) (n : ℕ) (v : Tapes t a) : Prop :=
  ∀ z, v.head L.stack ≤ z → z < v.head L.stack+(ops.length*n : ℕ) → v.tape L.stack z = blank

def pushStates {L : Layout t} : List (Role L) → ℕ
  | [] => 1
  | _::ops => 46+pushStates ops

def popStates {L : Layout t} : List (Role L) → ℕ
  | [] => 1
  | _::ops => popStates ops+50

noncomputable def pushProgram (L : Layout t) : (ops : List (Role L)) → Program t (pushStates ops) a
  | [] => skip t a (Nat.zero_lt_of_lt L.stack.isLt)
  | i::ops => seq (RoleArrayStackAt.pushProgram (slots L i) (slots_injective L i)) (pushProgram L ops)

noncomputable def popProgram (L : Layout t) : (ops : List (Role L)) → Program t (popStates ops) a
  | [] => skip t a (Nat.zero_lt_of_lt L.stack.isLt)
  | i::ops => seq (popProgram L ops) (RoleArrayStackAt.popProgram (slots L i) (slots_injective L i))

theorem one_frame (L : Layout t) (i : Role L) (n : ℕ) (v : Tapes t a) (j : Fin t)
    (hs : j ≠ L.stack) (hi : j ≠ i.val) :
    (saveOne L i n v).head j = v.head j ∧ (saveOne L i n v).tape j = v.tape j := by
  simp [saveOne,RoleArrayStackAt.pushed,slots,setTape,hs,hi]

private theorem one_controls (L : Layout t) (i : Role L) (n : ℕ) (bs : List Bool) (v : Tapes t a)
    (hc : Controls L bs v) : Controls L bs (saveOne L i n v) := by
  have h1 := one_frame L i n v L.clock L.stack_clock.symm i.property.2.1.symm
  have h2 := one_frame L i n v L.count L.stack_count.symm i.property.2.2.symm
  simpa only [Controls,h1.1,h1.2,h2.1,h2.2] using hc

private theorem one_stack (L : Layout t) (i : Role L) (n : ℕ) (v : Tapes t a) :
    (saveOne L i n v).head L.stack = v.head L.stack+n ∧
    (saveOne L i n v).tape L.stack = RoleArrayStack.parked (v.tape L.stack) (v.tape i.val) (v.head L.stack) n := by
  simp [saveOne,RoleArrayStackAt.pushed,slots,setTape]

private theorem free_tail (L : Layout t) (i : Role L) (ops : List (Role L)) (n : ℕ)
    (v : Tapes t a) (hf : Free L (i::ops) n v) : Free L ops n (saveOne L i n v) := by
  intro z hz he
  have hstack := one_stack L i n v
  rw [hstack.1] at hz he
  rw [hstack.2,RoleArrayStack.parked_outside _ _ _ _ _ (Or.inr hz)]
  apply hf z (by omega)
  simp only [List.length_cons,Nat.add_mul,one_mul,Nat.cast_add]
  omega

private theorem one_roundtrip (L : Layout t) (i : Role L) (n : ℕ) (v : Tapes t a)
    (hh : v.head i.val = 0) :
    setTape (setTape (saveOne L i n v) i.val (v.tape i.val) 0) L.stack (v.tape L.stack) (v.head L.stack) = v := by
  apply congrArg₂ Tapes.mk <;> funext j <;> by_cases hs : j = L.stack <;> by_cases hi : j = i.val <;>
    simp_all [saveOne,RoleArrayStackAt.pushed,slots,setTape,i.property.1]

/-- All original role positions are returned to blank origin slots for reuse. -/
theorem push_hoare (L : Layout t) (ops : List (Role L)) (hu : ops.Nodup) (v : Tapes t a)
    (bs : List Bool) (n : ℕ) (hn : Counter.value bs = n) (hc : Controls L bs v)
    (hr : ∀ i ∈ ops, v.head i = 0 ∧ RoleArrayStack.Supported (v.tape i) n) :
    HoareTime (pushProgram L ops) (fun w => w = v) (fun w => w = saved L ops n v)
      (ops.length*(14*n+14*bs.length+46)) := by
  induction ops generalizing v with
  | nil => simpa [pushProgram,pushStates,saved] using skip_hoare (a := a) (Nat.zero_lt_of_lt L.stack.isLt) v
  | cons i ops ih =>
    have hu' := List.nodup_cons.mp hu
    have h0 := hr i List.mem_cons_self
    have hp := RoleArrayStackAt.push_hoare (slots L i) (slots_injective L i) v bs n hn hc h0.1 h0.2
    have ht := ih hu'.2 (saveOne L i n v) (one_controls L i n bs v hc) (by
      intro j hj
      have hne : j.val ≠ i.val := fun he => hu'.1 (by have hij : j = i := Subtype.ext he; simpa [hij] using hj)
      have hh := one_frame L i n v j.val j.property.1 hne
      simpa only [hh.1,hh.2] using hr j (List.mem_cons_of_mem _ hj))
    exact (hp.seq ht).consequence (fun _ h => h) (fun _ h => h) (by simp only [List.length_cons,Nat.add_mul,one_mul]; omega)

/-- Actual reverse-order recovery restores the entire original bank exactly. -/
theorem pop_hoare (L : Layout t) (ops : List (Role L)) (hu : ops.Nodup) (v : Tapes t a)
    (bs : List Bool) (n : ℕ) (hn : Counter.value bs = n) (hc : Controls L bs v)
    (hr : ∀ i ∈ ops, v.head i = 0 ∧ RoleArrayStack.Supported (v.tape i) n) (hf : Free L ops n v) :
    HoareTime (popProgram L ops) (fun w => w = saved L ops n v) (fun w => w = v)
      (ops.length*(14*n+14*bs.length+50)) := by
  induction ops generalizing v with
  | nil => simpa [popProgram,popStates,saved] using skip_hoare (a := a) (Nat.zero_lt_of_lt L.stack.isLt) v
  | cons i ops ih =>
    have hu' := List.nodup_cons.mp hu
    have h0 := hr i List.mem_cons_self
    have hc' := one_controls L i n bs v hc
    have ht := ih hu'.2 (saveOne L i n v) hc' (by
      intro j hj
      have hne : j.val ≠ i.val := fun he => hu'.1 (by have hij : j = i := Subtype.ext he; simpa [hij] using hj)
      have hh := one_frame L i n v j.val j.property.1 hne
      simpa only [hh.1,hh.2] using hr j (List.mem_cons_of_mem _ hj)) (free_tail L i ops n v hf)
    have hstack := one_stack L i n v
    have hp := RoleArrayStackAt.pop_hoare (slots L i) (slots_injective L i) (saveOne L i n v)
      (v.tape i.val) (v.tape L.stack) (v.head L.stack) bs n hn hc'
      (by simp [saveOne,RoleArrayStackAt.pushed,slots,setTape,i.property.1])
      (by simp [saveOne,RoleArrayStackAt.pushed,slots,setTape,i.property.1])
      hstack.1 hstack.2 h0.2 (by
        intro z hz he
        apply hf z hz
        simp only [List.length_cons,Nat.add_mul,one_mul,Nat.cast_add]
        have hnonneg : (0 : ℤ) ≤ ops.length*n := by positivity
        omega)
    have hp' : HoareTime (RoleArrayStackAt.popProgram (slots L i) (slots_injective L i))
        (fun w => w = saveOne L i n v) (fun w => w = v) (14*n+14*bs.length+49) := by
      apply hp.consequence (fun _ h => h) _ le_rfl
      intro w hw
      exact hw.trans (one_roundtrip L i n v h0.1)
    exact (ht.seq hp').consequence (fun _ h => h) (fun _ h => h) (by simp only [List.length_cons,Nat.add_mul,one_mul]; omega)

theorem saved_frame (L : Layout t) (ops : List (Role L)) (n : ℕ) (v : Tapes t a) (j : Fin t)
    (hs : j ≠ L.stack) (hi : ∀ i ∈ ops, j ≠ i.val) :
    (saved L ops n v).head j = v.head j ∧ (saved L ops n v).tape j = v.tape j := by
  induction ops generalizing v with
  | nil => exact ⟨rfl,rfl⟩
  | cons i ops ih =>
    have ht := ih (saveOne L i n v) (fun k hk => hi k (List.mem_cons_of_mem _ hk))
    have ho := one_frame L i n v j hs (hi i List.mem_cons_self)
    exact ⟨ht.1.trans ho.1,ht.2.trans ho.2⟩

/-- Each parked role is literally blank at origin, ready for nested reuse. -/
theorem saved_role (L : Layout t) (ops : List (Role L)) (hu : ops.Nodup) (n : ℕ)
    (v : Tapes t a) (i : Role L) (hi : i ∈ ops) :
    (saved L ops n v).head i.val = 0 ∧ (saved L ops n v).tape i.val = fun _ => blank := by
  induction ops generalizing v with
  | nil => exact (List.not_mem_nil hi).elim
  | cons j ops ih =>
    have hu' := List.nodup_cons.mp hu
    rcases List.mem_cons.mp hi with rfl | hi
    · have h := saved_frame L ops n (saveOne L i n v) i.val i.property.1 (by
        intro j hj he
        exact hu'.1 (by have hij : i = j := Subtype.ext he; simpa [hij] using hj))
      simpa [saved,saveOne,RoleArrayStackAt.pushed,slots,setTape,i.property.1] using h
    · exact ih hu'.2 _ hi

theorem saved_head (L : Layout t) (ops : List (Role L)) (n : ℕ) (v : Tapes t a) :
    (saved L ops n v).head L.stack = v.head L.stack+(ops.length*n : ℕ) := by
  induction ops generalizing v with
  | nil => simp [saved]
  | cons i ops ih =>
    rw [saved,ih,(one_stack L i n v).1]
    simp only [List.length_cons,Nat.add_mul,one_mul,Nat.cast_add]
    omega

theorem saved_outside (L : Layout t) (ops : List (Role L)) (n : ℕ) (v : Tapes t a) (z : ℤ)
    (hz : z < v.head L.stack ∨ v.head L.stack+(ops.length*n : ℕ) ≤ z) :
    (saved L ops n v).tape L.stack z = v.tape L.stack z := by
  induction ops generalizing v with
  | nil => rfl
  | cons i ops ih =>
    simp only [List.length_cons,Nat.add_mul,one_mul,Nat.cast_add] at hz
    rw [saved,ih (saveOne L i n v) (by rw [(one_stack L i n v).1]; omega),(one_stack L i n v).2]
    exact RoleArrayStack.parked_outside _ _ _ _ _ (by omega)

theorem saved_controls (L : Layout t) (ops : List (Role L)) (n : ℕ) (v : Tapes t a)
    (bs : List Bool) (hc : Controls L bs v) : Controls L bs (saved L ops n v) := by
  induction ops generalizing v with
  | nil => exact hc
  | cons i ops ih => exact ih _ (one_controls L i n bs v hc)

theorem states_eq (L : Layout t) (ops : List (Role L)) :
    pushStates ops = 46*ops.length+1 ∧ popStates ops = 50*ops.length+1 := by
  induction ops with
  | nil => exact ⟨rfl,rfl⟩
  | cons i ops ih => simp only [pushStates,popStates,List.length_cons]; omega

private theorem canonical_length (bs : List Bool) (n : ℕ) (hn : Counter.value bs = n)
    (hc : GrowingCounterData.Canonical bs) (hp : 0 < n) : bs.length ≤ 2*n := by
  have h := GrowingCounterData.canonical_width bs hc
  rw [hn] at h
  have hl := Nat.log2_le_self n
  omega

theorem push_hoare_linear (L : Layout t) (ops : List (Role L)) (hu : ops.Nodup) (v : Tapes t a)
    (bs : List Bool) (n : ℕ) (hn : Counter.value bs = n) (hcanon : GrowingCounterData.Canonical bs)
    (hp : 0 < n) (hc : Controls L bs v)
    (hr : ∀ i ∈ ops, v.head i = 0 ∧ RoleArrayStack.Supported (v.tape i) n) :
    HoareTime (pushProgram L ops) (fun w => w = v) (fun w => w = saved L ops n v) (88*ops.length*n) := by
  apply (push_hoare L ops hu v bs n hn hc hr).consequence (fun _ h => h) (fun _ h => h)
  have hl := canonical_length bs n hn hcanon hp
  have hbound : 14*n+14*bs.length+46 ≤ 88*n := by omega
  calc
    _ ≤ ops.length*(88*n) := Nat.mul_le_mul_left _ hbound
    _ = _ := by ring

theorem pop_hoare_linear (L : Layout t) (ops : List (Role L)) (hu : ops.Nodup) (v : Tapes t a)
    (bs : List Bool) (n : ℕ) (hn : Counter.value bs = n) (hcanon : GrowingCounterData.Canonical bs)
    (hp : 0 < n) (hc : Controls L bs v)
    (hr : ∀ i ∈ ops, v.head i = 0 ∧ RoleArrayStack.Supported (v.tape i) n) (hf : Free L ops n v) :
    HoareTime (popProgram L ops) (fun w => w = saved L ops n v) (fun w => w = v) (92*ops.length*n) := by
  apply (pop_hoare L ops hu v bs n hn hc hr hf).consequence (fun _ h => h) (fun _ h => h)
  have hl := canonical_length bs n hn hcanon hp
  have hbound : 14*n+14*bs.length+50 ≤ 92*n := by omega
  calc
    _ ≤ ops.length*(92*n) := Nat.mul_le_mul_left _ hbound
    _ = _ := by ring

/-- A literal same-bank roundtrip, with all array/clock resets and the join. -/
theorem roundtrip_hoare_linear (L : Layout t) (ops : List (Role L)) (hu : ops.Nodup) (v : Tapes t a)
    (bs : List Bool) (n : ℕ) (hn : Counter.value bs = n) (hcanon : GrowingCounterData.Canonical bs)
    (hp : 0 < n) (hc : Controls L bs v)
    (hr : ∀ i ∈ ops, v.head i = 0 ∧ RoleArrayStack.Supported (v.tape i) n) (hf : Free L ops n v) :
    HoareTime (seq (pushProgram L ops) (popProgram L ops)) (fun w => w = v) (fun w => w = v)
      ((180*ops.length+1)*n) := by
  have h := (push_hoare_linear L ops hu v bs n hn hcanon hp hc hr).seq
    (pop_hoare_linear L ops hu v bs n hn hcanon hp hc hr hf)
  exact h.consequence (fun _ h => h) (fun _ h => h) (by nlinarith)

end IntegerMultBounds.Machine.RoleArrayFrames
