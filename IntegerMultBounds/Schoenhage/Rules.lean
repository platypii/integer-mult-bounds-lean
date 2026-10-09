import IntegerMultBounds.Schoenhage.Stream

/-! Streaming rules for word arithmetic, least significant bit first, and
the exact words they emit: copy, constant fill, fit to a width, drop a
prefix, addition with carry, subtraction with borrow, halving a unary word,
and a delayed marker. Each output lemma states the emitted symbols as the
symbols of an explicit word list. -/

namespace IntegerMultBounds.Schoenhage

open Strm

/-- The value of a word, least significant bit first. -/
def bval : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bval bs

@[simp] theorem bval_nil : bval [] = 0 := rfl
@[simp] theorem bval_cons (b : Bool) (bs : List Bool) :
    bval (b :: bs) = (if b then 1 else 0) + 2 * bval bs := rfl

theorem bval_lt (bs : List Bool) : bval bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih => cases b <;> simp [pow_succ] <;> omega

theorem bval_append (xs ys : List Bool) : bval (xs ++ ys) = bval xs + 2 ^ xs.length * bval ys := by
  induction xs with
  | nil => simp
  | cons b xs ih => simp [ih, pow_succ]; ring

theorem bval_replicate_false (n : ℕ) : bval (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

/-- The `n`-bit word of `v` (its residue modulo `2^n`). -/
def bits : ℕ → ℕ → List Bool
  | 0, _ => []
  | n + 1, v => (v % 2 = 1) :: bits n (v / 2)

@[simp] theorem length_bits (n v : ℕ) : (bits n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [bits, ih]

theorem bval_bits (n v : ℕ) : bval (bits n v) = v % 2 ^ n := by
  induction n generalizing v with
  | zero => simp [bits, Nat.mod_one]
  | succ n ih =>
    simp only [bits, bval_cons, ih, decide_eq_true_eq, pow_succ]
    rw [mul_comm (2 ^ n) 2, Nat.mod_mul]
    split_ifs with h <;> omega

theorem bits_bval (bs : List Bool) : bits bs.length (bval bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, bits, bval_cons]
    cases b
    · have : 2 * bval bs / 2 = bval bs := by omega
      simp [this, ih]
    · have : (1 + 2 * bval bs) / 2 = bval bs := by omega
      simp [this, ih]

theorem bits_mod (n v : ℕ) : bits n (v % 2 ^ n) = bits n v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    simp only [bits]
    have h1 : v % 2 ^ (n + 1) % 2 = v % 2 := by
      rw [pow_succ, Nat.mod_mul_left_mod]
    have h2 : v % 2 ^ (n + 1) / 2 = v / 2 % 2 ^ n := by
      rw [pow_succ, mul_comm, Nat.mod_mul_right_div_self]
    rw [h1, h2, ih]

theorem bval_take_drop (k : ℕ) (v : List Bool) :
    bval v = bval (v.take k) + 2 ^ (v.take k).length * bval (v.drop k) := by
  conv_lhs => rw [← List.take_append_drop k v]
  rw [bval_append]

theorem bval_drop (k : ℕ) (v : List Bool) (hk : k ≤ v.length) : bval (v.drop k) = bval v / 2 ^ k := by
  have h := bval_take_drop k v
  have hl : (v.take k).length = k := by simp; omega
  rw [hl] at h
  have hlt : bval (v.take k) < 2 ^ k := by have := bval_lt (v.take k); rwa [hl] at this
  rw [h, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hlt, zero_add]

theorem bval_take (k : ℕ) (v : List Bool) (hk : k ≤ v.length) : bval (v.take k) = bval v % 2 ^ k := by
  have h := bval_take_drop k v
  have hl : (v.take k).length = k := by simp; omega
  rw [hl] at h
  have hlt : bval (v.take k) < 2 ^ k := by have := bval_lt (v.take k); rwa [hl] at this
  rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

theorem bval_replicate_append (t : ℕ) (w : List Bool) :
    bval (List.replicate t false ++ w) = 2 ^ t * bval w := by
  rw [bval_append, bval_replicate_false]; simp

/-- A unary word. -/
def ones (n : ℕ) : List Bool := List.replicate n true

@[simp] theorem length_ones (n : ℕ) : (ones n).length = n := by simp [ones]

@[simp] theorem drop_ones (t n : ℕ) : (ones n).drop t = ones (n - t) := by simp [ones, List.drop_replicate]

namespace Rules

/-! ### Copy and constant fill -/

/-- Emit the driver's bits. -/
abbrev copy : Rule 0 where
  Q := Unit
  q0 := ()
  step _ b _ := ((), some (some b), fun _ => false)
  flush _ := [none]
  B := 1
  hB _ := le_rfl

@[simp] theorem copy_step (q : Unit) (b : Bool) (o) : (copy).step q b o = ((), some (some b), fun _ => false) := rfl
@[simp] theorem copy_flush (q : Unit) : (copy).flush q = [none] := rfl
@[simp] theorem copy_q0 : (copy).q0 = () := rfl

theorem go_copy (w : List Bool) (ws : Fin 0 → List Bool) :
    (go copy () w ws).2.1 = w.map some ∧ (go copy () w ws).1 = () := by
  induction w generalizing ws with
  | nil => simp [go]
  | cons b w ih => simp [go, ih]

theorem output_copy (w : List Bool) (ws : Fin 0 → List Bool) : output copy w ws = syms [w] := by
  simp [output, syms_cons, (go_copy w ws).1, (go_copy w ws).2]

/-- Emit the constant `c` once per driver bit. -/
abbrev fill (c : Bool) : Rule 0 where
  Q := Unit
  q0 := ()
  step _ _ _ := ((), some (some c), fun _ => false)
  flush _ := [none]
  B := 1
  hB _ := le_rfl

@[simp] theorem fill_step (c : Bool) (q : Unit) (b : Bool) (o) : (fill c).step q b o = ((), some (some c), fun _ => false) := rfl
@[simp] theorem fill_flush (c : Bool) (q : Unit) : (fill c).flush q = [none] := rfl
@[simp] theorem fill_q0 (c : Bool) : (fill c).q0 = () := rfl

theorem go_fill (c : Bool) (w : List Bool) (ws : Fin 0 → List Bool) :
    (go (fill c) () w ws).2.1 = (List.replicate w.length c).map some := by
  induction w generalizing ws with
  | nil => simp [go]
  | cons b w ih => simp [go, ih, List.replicate_succ]

theorem output_fill (c : Bool) (w : List Bool) (ws : Fin 0 → List Bool) :
    output (fill c) w ws = syms [List.replicate w.length c] := by
  simp [output, syms_cons, go_fill]

/-! ### Fit to the driver's width -/

/-- The first `n` bits of `x`, padded with zeros. -/
def fit : ℕ → List Bool → List Bool
  | 0, _ => []
  | n + 1, x => x.headD false :: fit n x.tail

@[simp] theorem length_fit (n : ℕ) (x : List Bool) : (fit n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [fit, ih]

theorem bval_fit (n : ℕ) (x : List Bool) (h : x.length ≤ n) : bval (fit n x) = bval x := by
  induction n generalizing x with
  | zero =>
    have : x = [] := List.length_eq_zero_iff.mp (by omega)
    subst this; rfl
  | succ n ih =>
    rcases x with _ | ⟨b, x⟩
    · simp [fit]
      have := ih [] (by simp)
      simpa using this
    · simp only [fit, List.headD_cons, List.tail_cons, bval_cons]
      rw [ih x (by simp at h; omega)]

theorem fit_eq_bits (n : ℕ) (x : List Bool) : fit n x = bits n (bval x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rcases x with _ | ⟨b, x⟩
    · simp only [fit, List.headD_nil, List.tail_nil, bval_nil, bits]
      rw [ih]; simp
    · simp only [fit, List.headD_cons, List.tail_cons, bval_cons, bits, ih]
      congr 1
      · cases b <;> simp <;> omega
      · congr 1; cases b <;> simp <;> omega

theorem bval_fit_mod (n : ℕ) (x : List Bool) : bval (fit n x) = bval x % 2 ^ n := by
  rw [fit_eq_bits, bval_bits]

theorem fit_of_length (x : List Bool) : fit x.length x = x := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [fit, ih]

/-- Emit the other input's bits, padded with zeros, for the driver's length. -/
abbrev take : Rule 1 where
  Q := Unit
  q0 := ()
  step _ _ o := ((), some (some ((o 0).getD false)), fun _ => true)
  flush _ := [none]
  B := 1
  hB _ := le_rfl

@[simp] theorem take_step (q : Unit) (b : Bool) (o) : (take).step q b o = ((), some (some ((o 0).getD false)), fun _ => true) := rfl
@[simp] theorem take_flush (q : Unit) : (take).flush q = [none] := rfl
@[simp] theorem take_q0 : (take).q0 = () := rfl

theorem go_take (w : List Bool) (ws : Fin 1 → List Bool) :
    (go take () w ws).2.1 = (fit w.length (ws 0)).map some := by
  induction w generalizing ws with
  | nil => simp [go, fit]
  | cons b w ih =>
    simp only [go, List.length_cons, fit]
    rw [ih]
    rcases h : ws 0 with _ | ⟨x, xs⟩ <;> simp [h]

theorem output_take (w : List Bool) (ws : Fin 1 → List Bool) :
    output take w ws = syms [fit w.length (ws 0)] := by
  simp [output, syms_cons, go_take]

/-! ### Drop a prefix -/

/-- Emit the driver's bits once the other input has run out. -/
abbrev drop : Rule 1 where
  Q := Unit
  q0 := ()
  step _ b o := ((), if (o 0).isSome then none else some (some b), fun _ => true)
  flush _ := [none]
  B := 1
  hB _ := le_rfl

@[simp] theorem drop_step (q : Unit) (b : Bool) (o) : (drop).step q b o = ((), if (o 0).isSome then none else some (some b), fun _ => true) := rfl
@[simp] theorem drop_flush (q : Unit) : (drop).flush q = [none] := rfl
@[simp] theorem drop_q0 : (drop).q0 = () := rfl

theorem go_drop (w : List Bool) (ws : Fin 1 → List Bool) :
    (go drop () w ws).2.1 = (w.drop (ws 0).length).map some := by
  induction w generalizing ws with
  | nil => simp [go]
  | cons b w ih =>
    obtain ⟨l, hl⟩ : ∃ l, ws 0 = l := ⟨_, rfl⟩
    simp only [go, drop_step, ↓reduceIte]
    rw [ih]
    rcases l with _ | ⟨x, xs⟩ <;> simp [hl]

theorem output_drop (w : List Bool) (ws : Fin 1 → List Bool) :
    output drop w ws = syms [w.drop (ws 0).length] := by
  simp [output, syms_cons, go_drop]

/-! ### Addition -/

/-- The sum word: `x + y + c` in `|x| + 1` bits (`y` padded or cut to `|x|`). -/
def addW : Bool → List Bool → List Bool → List Bool
  | c, [], _ => [c]
  | c, b :: x, y =>
    let d := y.headD false
    (b ^^ d ^^ c) :: addW ((b && d) || (b && c) || (d && c)) x y.tail

theorem length_addW (c : Bool) (x y : List Bool) : (addW c x y).length = x.length + 1 := by
  induction x generalizing c y with
  | nil => rfl
  | cons b x ih => simp [addW, ih]

theorem bval_addW (c : Bool) (x y : List Bool) :
    bval (addW c x y) = bval x + bval (fit x.length y) + (if c then 1 else 0) := by
  induction x generalizing c y with
  | nil => cases c <;> simp [addW, fit]
  | cons b x ih =>
    have h := ih ((b && y.headD false) || (b && c) || (y.headD false && c)) y.tail
    simp only [addW, bval_cons, List.length_cons, fit]
    generalize y.headD false = d at h ⊢
    generalize addW ((b && d) || (b && c) || (d && c)) x y.tail = r at h ⊢
    rw [h]
    cases b <;> cases c <;> cases d <;> simp <;> omega

/-- Ripple-carry addition. -/
abbrev add : Rule 1 where
  Q := Bool
  q0 := false
  step c b o :=
    let d := (o 0).getD false
    ((b && d) || (b && c) || (d && c), some (some (b ^^ d ^^ c)), fun _ => true)
  flush c := [some c, none]
  B := 2
  hB _ := le_rfl

@[simp] theorem add_step (q : Bool) (b : Bool) (o) : (add).step q b o = ((b && (o 0).getD false) || (b && q) || ((o 0).getD false && q), some (some (b ^^ (o 0).getD false ^^ q)), fun _ => true) := rfl
@[simp] theorem add_flush (q : Bool) : (add).flush q = [some q, none] := rfl
@[simp] theorem add_q0 : (add).q0 = false := rfl

theorem go_add (c : Bool) (x : List Bool) (ws : Fin 1 → List Bool) :
    (go add c x ws).2.1 ++ add.flush (go add c x ws).1 = (addW c x (ws 0)).map some ++ [none] := by
  induction x generalizing c ws with
  | nil => simp [go, add, addW]
  | cons b x ih =>
    simp only [go, addW]
    have := ih ((b && (ws 0).head?.getD false) || (b && c) || ((ws 0).head?.getD false && c))
      (fun j => (ws j).tail)
    
    rcases h : ws 0 with _ | ⟨y, ys⟩ <;> simp_all

theorem output_add (x : List Bool) (ws : Fin 1 → List Bool) :
    output add x ws = syms [addW false x (ws 0)] := by
  unfold output
  rw [add_q0, go_add]
  simp [syms_cons]

/-! ### Subtraction -/

/-- The difference word `x - y - c` modulo `2^|x|`, and the final borrow. -/
def subW : Bool → List Bool → List Bool → List Bool × Bool
  | c, [], _ => ([], c)
  | c, b :: x, y =>
    let d := y.headD false
    let r := subW ((!b && d) || (!b && c) || (d && c)) x y.tail
    ((b ^^ d ^^ c) :: r.1, r.2)

theorem length_subW (c : Bool) (x y : List Bool) : (subW c x y).1.length = x.length := by
  induction x generalizing c y with
  | nil => rfl
  | cons b x ih => simp [subW, ih]

/-- `x - y - c = diff - 2^|x| borrow`. -/
theorem bval_subW (c : Bool) (x y : List Bool) :
    (bval x : ℤ) - bval (fit x.length y) - c.toNat =
      bval (subW c x y).1 - 2 ^ x.length * (subW c x y).2.toNat := by
  induction x generalizing c y with
  | nil => cases c <;> simp [subW, fit]
  | cons b x ih =>
    rcases y with _ | ⟨d, y⟩
    · have h := ih ((!b && false) || (!b && c) || (false && c)) []
      simp only [subW, bval_cons, List.length_cons, fit, List.headD_nil, List.tail_nil]
      revert h
      cases b <;> cases c <;> simp <;> intro h <;> push_cast [pow_succ] <;> linarith
    · have h := ih ((!b && d) || (!b && c) || (d && c)) y
      simp only [subW, bval_cons, List.length_cons, fit, List.headD_cons, List.tail_cons]
      revert h
      cases b <;> cases c <;> cases d <;> simp <;> intro h <;> push_cast [pow_succ] <;> linarith

/-- Ripple-borrow subtraction; the flush emits the borrow as its own word. -/
abbrev sub : Rule 1 where
  Q := Bool
  q0 := false
  step c b o :=
    let d := (o 0).getD false
    ((!b && d) || (!b && c) || (d && c), some (some (b ^^ d ^^ c)), fun _ => true)
  flush c := [none, some c, none]
  B := 3
  hB _ := le_rfl

@[simp] theorem sub_step (q : Bool) (b : Bool) (o) : (sub).step q b o = ((!b && (o 0).getD false) || (!b && q) || ((o 0).getD false && q), some (some (b ^^ (o 0).getD false ^^ q)), fun _ => true) := rfl
@[simp] theorem sub_flush (q : Bool) : (sub).flush q = [none, some q, none] := rfl
@[simp] theorem sub_q0 : (sub).q0 = false := rfl

theorem go_sub (c : Bool) (x : List Bool) (ws : Fin 1 → List Bool) :
    (go sub c x ws).2.1 ++ sub.flush (go sub c x ws).1 =
      (subW c x (ws 0)).1.map some ++ [none, some (subW c x (ws 0)).2, none] := by
  induction x generalizing c ws with
  | nil => simp [go, sub, subW]
  | cons b x ih =>
    simp only [go, subW]
    have := ih ((!b && (ws 0).head?.getD false) || (!b && c) || ((ws 0).head?.getD false && c))
      (fun j => (ws j).tail)
    
    rcases h : ws 0 with _ | ⟨y, ys⟩ <;> simp_all

theorem output_sub (x : List Bool) (ws : Fin 1 → List Bool) :
    output sub x ws = syms [(subW false x (ws 0)).1, [(subW false x (ws 0)).2]] := by
  unfold output
  rw [sub_q0, go_sub]
  simp [syms_cons]

/-! ### Halving and markers -/

/-- Emit every second driver bit (positions `1, 3, 5, …`). -/
abbrev half : Rule 0 where
  Q := Bool
  q0 := false
  step p b _ := (!p, if p then some (some b) else none, fun _ => false)
  flush _ := [none]
  B := 1
  hB _ := le_rfl

@[simp] theorem half_step (q : Bool) (b : Bool) (o) : (half).step q b o = (!q, if q then some (some b) else none, fun _ => false) := rfl
@[simp] theorem half_flush (q : Bool) : (half).flush q = [none] := rfl
@[simp] theorem half_q0 : (half).q0 = false := rfl

theorem go_half_ones (p : Bool) (n : ℕ) (ws : Fin 0 → List Bool) :
    (go half p (ones n) ws).2.1 = (ones ((n + if p then 1 else 0) / 2)).map some := by
  induction n generalizing p ws with
  | zero => cases p <;> simp [go, ones]
  | succ n ih =>
    simp only [ones, List.replicate_succ, go] at ih ⊢
    rw [ih]
    cases p
    · simp
    · simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true, add_zero, Option.toList_some,
        List.singleton_append]
      rw [show (n + 1 + 1) / 2 = n / 2 + 1 by omega]
      simp [List.replicate_succ]

theorem output_half_ones (n : ℕ) (ws : Fin 0 → List Bool) :
    output half (ones n) ws = syms [ones (n / 2)] := by
  simp [output, syms_cons, go_half_ones]

/-- Emit `n - 1` zeros and a final one for a driver word of length `n ≥ 1`. -/
abbrev mark : Rule 0 where
  Q := Bool
  q0 := false
  step s _ _ := (true, if s then some (some false) else none, fun _ => false)
  flush s := if s then [some true, none] else [none]
  B := 2
  hB s := by cases s <;> simp

@[simp] theorem mark_step (q : Bool) (b : Bool) (o) : (mark).step q b o = (true, if q then some (some false) else none, fun _ => false) := rfl
@[simp] theorem mark_flush (q : Bool) : (mark).flush q = if q then [some true, none] else [none] := rfl
@[simp] theorem mark_q0 : (mark).q0 = false := rfl

theorem go_mark (s : Bool) (w : List Bool) (ws : Fin 0 → List Bool) :
    (go mark s w ws).1 = (s || !w.isEmpty) ∧
      (go mark s w ws).2.1 = (List.replicate (if s then w.length else w.length - 1) false).map some := by
  induction w generalizing s ws with
  | nil => cases s <;> simp [go]
  | cons b w ih =>
    simp only [go]
    obtain ⟨h1, h2⟩ := ih true (fun j => if false = true then (ws j).tail else ws j)
    rw [h1, h2]
    cases s <;> simp [List.replicate_succ]

theorem output_mark (w : List Bool) (ws : Fin 0 → List Bool) (h : w ≠ []) :
    output mark w ws = syms [List.replicate (w.length - 1) false ++ [true]] := by
  unfold output
  obtain ⟨h1, h2⟩ := go_mark false w ws
  rw [mark_q0, h2, mark_flush, h1]
  cases w with
  | nil => exact absurd rfl h
  | cons b w => simp [syms_cons]

end Rules

end IntegerMultBounds.Schoenhage
