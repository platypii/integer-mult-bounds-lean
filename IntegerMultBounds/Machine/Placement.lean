import IntegerMultBounds.Machine.Frame

/-! Exact placement of a small program into any fixed slots of a larger tape
bank. Projection and replacement retain the complete complementary tapes and
their heads. The lift preserves actual transition counts and genuine halting. -/

namespace IntegerMultBounds.Machine.Placement

variable {s u t q r a : ℕ}

def active (e : Fin (s+u) ≃ Fin t) (v : Tapes t a) : Tapes s a :=
  ⟨fun i => v.head (e (Fin.castAdd u i)),fun i => v.tape (e (Fin.castAdd u i))⟩

def extra (e : Fin (s+u) ≃ Fin t) (v : Tapes t a) : Tapes u a :=
  ⟨fun i => v.head (e (Fin.natAdd s i)),fun i => v.tape (e (Fin.natAdd s i))⟩

def combine (e : Fin (s+u) ≃ Fin t) (small : Tapes s a) (frame : Tapes u a) : Tapes t a :=
  (small.append frame).reindex e

/-- Change the selected bank and retain all other complete tapes and heads. -/
def replace (e : Fin (s+u) ≃ Fin t) (v : Tapes t a) (small : Tapes s a) : Tapes t a :=
  combine e small (extra e v)

@[simp] theorem combine_head_active (e : Fin (s+u) ≃ Fin t) (small : Tapes s a)
    (frame : Tapes u a) (i : Fin s) :
    (combine e small frame).head (e (Fin.castAdd u i)) = small.head i := by
  simp [combine,Tapes.reindex,Tapes.append]

@[simp] theorem combine_tape_active (e : Fin (s+u) ≃ Fin t) (small : Tapes s a)
    (frame : Tapes u a) (i : Fin s) :
    (combine e small frame).tape (e (Fin.castAdd u i)) = small.tape i := by
  simp [combine,Tapes.reindex,Tapes.append]

@[simp] theorem combine_head_extra (e : Fin (s+u) ≃ Fin t) (small : Tapes s a)
    (frame : Tapes u a) (i : Fin u) :
    (combine e small frame).head (e (Fin.natAdd s i)) = frame.head i := by
  simp [combine,Tapes.reindex,Tapes.append]

@[simp] theorem combine_tape_extra (e : Fin (s+u) ≃ Fin t) (small : Tapes s a)
    (frame : Tapes u a) (i : Fin u) :
    (combine e small frame).tape (e (Fin.natAdd s i)) = frame.tape i := by
  simp [combine,Tapes.reindex,Tapes.append]

@[simp] theorem active_combine (e : Fin (s+u) ≃ Fin t) (small : Tapes s a) (frame : Tapes u a) :
    active e (combine e small frame) = small := by
  cases small
  simp [active,combine,Tapes.append,Tapes.reindex]

@[simp] theorem extra_combine (e : Fin (s+u) ≃ Fin t) (small : Tapes s a) (frame : Tapes u a) :
    extra e (combine e small frame) = frame := by
  cases frame
  simp [extra,combine,Tapes.append,Tapes.reindex]

/-- Every arbitrary whole bank decomposes into its active projection and frame. -/
@[simp] theorem view (e : Fin (s+u) ≃ Fin t) (v : Tapes t a) :
    combine e (active e v) (extra e v) = v := by
  cases v with
  | mk head tape =>
    unfold combine active extra Tapes.append Tapes.reindex
    congr 1
    · funext i
      obtain ⟨j,rfl⟩ := e.surjective i
      induction j using Fin.addCases with
      | left j => simp
      | right j => simp
    · funext i
      obtain ⟨j,rfl⟩ := e.surjective i
      induction j using Fin.addCases with
      | left j => simp
      | right j => simp

@[simp] theorem active_replace (e : Fin (s+u) ≃ Fin t) (v : Tapes t a) (small : Tapes s a) :
    active e (replace e v small) = small := active_combine e small (extra e v)

@[simp] theorem extra_replace (e : Fin (s+u) ≃ Fin t) (v : Tapes t a) (small : Tapes s a) :
    extra e (replace e v small) = extra e v := extra_combine e small (extra e v)

@[simp] theorem replace_active (e : Fin (s+u) ≃ Fin t) (v : Tapes t a) :
    replace e v (active e v) = v := view e v

def placed (M : Program s q a) (e : Fin (s+u) ≃ Fin t) : Program t q a :=
  reindex (extend M u) e

def result (e : Fin (s+u) ≃ Fin t) (v : Tapes t a) (c : Config s q a) : Config t q a :=
  (c.extend (extra e v)).reindex e

@[simp] theorem result_tapes (e : Fin (s+u) ≃ Fin t) (v : Tapes t a) (c : Config s q a) :
    (result e v c).tapes = replace e v c.tapes := rfl

theorem start_view (M : Program s q a) (e : Fin (s+u) ≃ Fin t) (v : Tapes t a) :
    result e v ((active e v).start M) = v.start (placed M e) := by
  have hv := view e v
  unfold result Config.reindex Config.extend Tapes.start
  congr 1
  · exact congrArg Tapes.head hv
  · exact congrArg Tapes.tape hv

/-- Every actual small transition run lifts with exactly the same length. -/
theorem placed_run (M : Program s q a) (e : Fin (s+u) ≃ Fin t) (v : Tapes t a)
    {n : ℕ} {c : Config s q a} (h : run M n ((active e v).start M) = some c) :
    run (placed M e) n (v.start (placed M e)) = some (result e v c) := by
  have hs := reindex_run (extend M u) e (extend_run M (extra e v) h)
  change run (placed M e) n (result e v ((active e v).start M)) = _ at hs
  rw [start_view] at hs
  exact hs

theorem placed_halt (M : Program s q a) (e : Fin (s+u) ≃ Fin t) (v : Tapes t a)
    {c : Config s q a} (h : step M c = none) :
    step (placed M e) (result e v c) = none :=
  reindex_halt (extend M u) e (extend_halt M (extra e v) h)

/-- A concrete run, halt, and complete tape postcondition at an exact cost. -/
def ExactRun (M : Program s q a) (n : ℕ) (v w : Tapes s a) : Prop :=
  ∃ c, run M n (v.start M) = some c ∧ step M c = none ∧ c.tapes = w

theorem placed_exact (M : Program s q a) (e : Fin (s+u) ≃ Fin t) (v : Tapes t a)
    (w : Tapes s a) {n : ℕ} (h : ExactRun M n (active e v) w) :
    ExactRun (placed M e) n v (replace e v w) := by
  obtain ⟨c,hr,hh,hc⟩ := h
  refine ⟨result e v c,placed_run M e v hr,placed_halt M e v hh,?_⟩
  rw [result_tapes,hc]

/-- Exact-run composition charges the real connecting transition. -/
theorem exact_seq {M : Program s q a} {N : Program s r a}
    {k l : ℕ} {v w z : Tapes s a} (hm : ExactRun M k v w) (hn : ExactRun N l w z) :
    ExactRun (seq M N) (k+1+l) v z := by
  obtain ⟨c,hr,hh,hc⟩ := hm
  obtain ⟨d,hs,hd,he⟩ := hn
  refine ⟨d.mapState (Fin.natAdd q),?_,seq_halt_right M N hd,he⟩
  rw [← hc] at hs
  exact seq_run M N hr hh hs

/-- Local Hoare contracts preserve arbitrary complete complementary tapes. -/
theorem hoare {M : Program s q a} {pre post : TapePred s a} {bound : ℕ}
    (h : HoareTime M pre post bound) (e : Fin (s+u) ≃ Fin t) (frame : Tapes u a) :
    HoareTime (placed M e)
      (fun v => pre (active e v) ∧ extra e v = frame)
      (fun v => post (active e v) ∧ extra e v = frame) bound := by
  rintro v ⟨hp,hframe⟩
  obtain ⟨n,c,hn,hr,hh,hpost⟩ := h (active e v) hp
  refine ⟨n,result e v c,hn,placed_run M e v hr,placed_halt M e v hh,?_⟩
  simpa only [result_tapes,active_replace,extra_replace,hframe,and_true] using hpost

/-- Convenient concrete-bank form: only the projected bank is replaced. -/
theorem hoare_at {M : Program s q a} {pre post : TapePred s a} {bound : ℕ}
    (h : HoareTime M pre post bound) (e : Fin (s+u) ≃ Fin t) (v : Tapes t a)
    (hp : pre (active e v)) :
    HoareTime (placed M e) (fun input => input = v)
      (fun output => ∃ w, post w ∧ output = replace e v w) bound := by
  intro input hi
  subst input
  obtain ⟨n,c,hn,hr,hh,hpost⟩ := h (active e v) hp
  exact ⟨n,result e v c,hn,placed_run M e v hr,placed_halt M e v hh,c.tapes,hpost,rfl⟩

end IntegerMultBounds.Machine.Placement
