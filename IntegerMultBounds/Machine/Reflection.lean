import IntegerMultBounds.Machine.Hoare
import IntegerMultBounds.Machine.WordTape

/-! Reverse the physical direction of any chosen tapes in a finite program.
This changes its actual local transition table, with exactly the same runtime.
It supports backwards payload transfers while leaving a binary clock forward;
it does not implement a free reversal of an existing tape's contents. -/

namespace IntegerMultBounds.Machine.Reflection

variable {t q a : ℕ}

def coord (reverse : Bool) (j : ℤ) : ℤ := if reverse then -j else j

def direction (reverse : Bool) (m : Move) : Move :=
  if reverse then match m with
    | .left => .right
    | .stay => .stay
    | .right => .left
  else m

@[simp] theorem coord_coord (b : Bool) (j : ℤ) : coord b (coord b j) = j := by
  cases b <;> simp [coord]

@[simp] theorem coord_add (b : Bool) (j k : ℤ) :
    coord b (j+k) = coord b j + coord b k := by
  cases b <;> simp [coord, add_comm]

@[simp] theorem direction_offset (b : Bool) (m : Move) :
    (direction b m).offset = coord b m.offset := by
  cases b <;> cases m <;> rfl

@[simp] theorem coord_eq_iff (b : Bool) (j k : ℤ) :
    coord b j = coord b k ↔ j = k := by
  cases b <;> simp [coord]

/-- The transformed transition table still reads and writes only scanned cells. -/
def program (M : Program t q a) (reverse : Fin t → Bool) : Program t q a where
  tapes_pos := M.tapes_pos
  start := M.start
  transition := fun s symbols => (M.transition s symbols).map fun (s',action) =>
    (s', fun i => ((action i).1, direction (reverse i) (action i).2))

def tapes (reverse : Fin t → Bool) (v : Tapes t a) : Tapes t a where
  head := fun i => coord (reverse i) (v.head i)
  tape := fun i j => v.tape i (coord (reverse i) j)

def config (reverse : Fin t → Bool) (c : Config t q a) : Config t q a :=
  ⟨c.state, (tapes reverse c.tapes).head, (tapes reverse c.tapes).tape⟩

@[simp] theorem config_tapes (reverse : Fin t → Bool) (c : Config t q a) :
    (config reverse c).tapes = tapes reverse c.tapes := rfl

@[simp] theorem tapes_tapes (reverse : Fin t → Bool) (v : Tapes t a) :
    tapes reverse (tapes reverse v) = v := by
  cases v
  simp [tapes]

/-- Exact one-step conjugacy, including the halting case. -/
theorem step_eq (M : Program t q a) (reverse : Fin t → Bool) (c : Config t q a) :
    step (program M reverse) (config reverse c) = (step M c).map (config reverse) := by
  simp only [step, program, config, tapes, Config.tapes, coord_coord]
  cases h : M.transition c.state (fun i => c.tape i (c.head i)) with
  | none => rfl
  | some v =>
    rcases v with ⟨s, action⟩
    simp only [Option.map_some, config, tapes, Config.tapes, direction_offset, coord_add]
    congr 1
    congr 1
    funext i j
    have he : j = coord (reverse i) (c.head i) ↔ coord (reverse i) j = c.head i := by
      cases hb : reverse i <;> simp [coord]
      omega
    simp only [he]

/-- Exact execution time is unchanged by reversing selected head directions. -/
theorem run_eq (M : Program t q a) (reverse : Fin t → Bool) (n : ℕ)
    (c : Config t q a) :
    run (program M reverse) n (config reverse c) = (run M n c).map (config reverse) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [run,step_eq]
    cases h : step M c with
    | none => rfl
    | some d => simpa only [Option.map_some,Option.bind_some] using ih d

/-- A time contract transports to the physically reflected transition table. -/
theorem hoare {M : Program t q a} {pre post : TapePred t a} {bound : ℕ}
    (h : HoareTime M pre post bound) (reverse : Fin t → Bool) :
    HoareTime (program M reverse)
      (fun v => ∃ original, pre original ∧ v = tapes reverse original)
      (fun v => ∃ original, post original ∧ v = tapes reverse original) bound := by
  rintro v ⟨original,hpre,rfl⟩
  obtain ⟨n,c,hn,hr,hh,hpost⟩ := h original hpre
  refine ⟨n,config reverse c,hn,?_,?_,c.tapes,hpost,rfl⟩
  · have hh := run_eq M reverse n (original.start M)
    rw [hr] at hh
    exact hh
  · rw [step_eq,hh]
    rfl

/-- A reflected placed word occupies the reflected interval in reverse order.
This is an equality of representations, not a tape operation. -/
theorem word (f : ℤ → Fin (a+4)) (p : ℤ) (xs : List (Fin (a+4))) :
    (fun j => putWord f p xs (-j)) =
      putWord (fun j => f (-j)) (-p-xs.length+1) xs.reverse := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons, ← putWord_append_forward]
    simp only [List.length_cons,List.length_reverse,Nat.cast_add,Nat.cast_one]
    have hbase : -p - ((xs.length : ℤ)+1)+1 = -(p+1)-xs.length+1 := by omega
    have hend : -p - ((xs.length : ℤ)+1)+1+xs.length = -p := by omega
    rw [hend,hbase,← ih]
    funext j
    simp only [putWord,Function.update_apply]
    have he : -j = p ↔ j = -p := by omega
    simp only [he]

end IntegerMultBounds.Machine.Reflection
