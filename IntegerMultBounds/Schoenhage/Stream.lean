import IntegerMultBounds.Schoenhage.FMachine
import IntegerMultBounds.Schoenhage.Words

/-! A generic streaming machine over word tapes. Tape `0` is the driver,
tapes `1 … r` are further inputs and tape `r + 1` is the output. For each
bit of the driver's current word, a finite rule reads that bit and the
current bit of every other input (or the information that its word has
ended), updates its state and emits at most one symbol; then the other
inputs skip the rest of their words, the rule's final flush is emitted, and
all inputs step past their separators. In extend mode the first symbol
overwrites the output's last separator, so the output continues the last
word. This file proves the raw run: exact final heads and tapes and the
exact number of transitions. -/

namespace IntegerMultBounds.Schoenhage

open Machine

namespace Strm

variable {a r : ℕ}

/-- The bit on a cell, if any. -/
def decode (x : Fin (a + 4)) : Option Bool :=
  if x = bitSymbol true then some true else if x = bitSymbol false then some false else none

@[simp] theorem decode_bit (b : Bool) : decode (a := a) (bitSymbol b) = some b := by
  cases b <;> simp [decode, bitSymbol, Fin.ext_iff]

@[simp] theorem decode_sep : decode (a := a) separator = none := by
  simp [decode, bitSymbol, separator, Fin.ext_iff]

theorem bit_ne_sep (b : Bool) : bitSymbol (a := a) b ≠ separator := by
  cases b <;> simp [bitSymbol, separator, Fin.ext_iff]

/-- A streaming rule with a finite state type. -/
structure Rule (r : ℕ) where
  Q : Type
  [fin : Fintype Q]
  [dec : DecidableEq Q]
  q0 : Q
  step : Q → Bool → (Fin r → Option Bool) → Q × Option (Option Bool) × (Fin r → Bool)
  flush : Q → List (Option Bool)
  B : ℕ
  hB : ∀ q, (flush q).length ≤ B

attribute [instance] Rule.fin Rule.dec

/-- Control states of the streaming machine. -/
inductive St (Q : Type) (B : ℕ) where
  | init
  | run (q : Q)
  | skip (q : Q)
  | fl (q : Q) (i : Fin (B + 1))
  | fin
  | done
  deriving DecidableEq, Fintype

/-- The driver tape. -/
def drv : Fin (r + 2) := ⟨0, by omega⟩
/-- The other input tapes. -/
def oth (j : Fin r) : Fin (r + 2) := ⟨j.val + 1, by omega⟩
/-- The output tape. -/
def out : Fin (r + 2) := ⟨r + 1, by omega⟩

/-- Whether tape `i` advances under the advance flags `adv`. -/
def advOf (adv : Fin r → Bool) (i : Fin (r + 2)) : Bool :=
  if h : 0 < i.val ∧ i.val ≤ r then adv ⟨i.val - 1, by omega⟩ else false

theorem drv_ne_out : (drv : Fin (r + 2)) ≠ out := by simp [drv, out, Fin.ext_iff]
theorem oth_ne_out (j : Fin r) : oth j ≠ out := by simp [oth, out, Fin.ext_iff]; omega
theorem oth_ne_drv (j : Fin r) : oth j ≠ drv := by simp [oth, drv, Fin.ext_iff]

theorem advOf_oth (adv : Fin r → Bool) (j : Fin r) : advOf adv (oth j) = adv j := by
  unfold advOf
  have h : 0 < (oth j).val ∧ (oth j).val ≤ r := by simp [oth]
  simp only [h, ↓reduceDIte]
  congr 1

/-- Every tape is the driver, another input or the output. -/
theorem cases_tape (i : Fin (r + 2)) : i = drv ∨ (∃ j, i = oth j) ∨ i = out := by
  rcases i with ⟨i, hi⟩
  rcases Nat.eq_zero_or_pos i with rfl | h
  · left; rfl
  · by_cases h' : i = r + 1
    · right; right; simp [out, h']
    · right; left; exact ⟨⟨i - 1, by omega⟩, by simp [oth, Fin.ext_iff]; omega⟩

/-- The machine. -/
def machine (R : Rule r) (ext : Bool) : FMachine (r + 2) a where
  S := St R.Q R.B
  start := .init
  δ s syms := match s with
    | .init => some (.run R.q0, fun i => (syms i, if i = out ∧ ext = true then .left else .stay))
    | .run q =>
      if syms drv = separator then some (.skip q, fun i => (syms i, .stay)) else
        let res := R.step q (decide (syms drv = bitSymbol true)) (fun j => decode (syms (oth j)))
        some (.run res.1, fun i => if i = out then
            (match res.2.1 with
              | none => (syms i, .stay)
              | some o => (sym o, .right))
          else if i = drv then (syms i, .right)
          else (syms i, if (decode (syms i)).isSome ∧ advOf res.2.2 i then .right else .stay))
    | .skip q =>
      if ∀ j : Fin r, syms (oth j) = separator then some (.fl q 0, fun i => (syms i, .stay))
      else some (.skip q, fun i =>
        (syms i, if i ≠ out ∧ (decode (syms i)).isSome then .right else .stay))
    | .fl q i =>
      if h : i.val < (R.flush q).length then
        some (.fl q ⟨i.val + 1, by have := R.hB q; omega⟩, fun j => if j = out then
          (sym ((R.flush q)[i.val]), .right) else (syms j, .stay))
      else some (.fin, fun i => (syms i, .stay))
    | .fin => some (.done, fun i => (syms i, if i = out then .stay else .right))
    | .done => none

/-! ### Abstract semantics -/

/-- Run the rule over the driver bits; the other inputs are consumed in step. -/
def go (R : Rule r) : R.Q → List Bool → (Fin r → List Bool) →
    R.Q × List (Option Bool) × (Fin r → List Bool)
  | q, [], ws => (q, [], ws)
  | q, b :: bs, ws =>
    let p := R.step q b (fun j => (ws j).head?)
    let rest := go R p.1 bs (fun j => if p.2.2 j then (ws j).tail else ws j)
    (rest.1, p.2.1.toList ++ rest.2.1, rest.2.2)

/-- All emitted symbols, flush included. -/
def output (R : Rule r) (w : List Bool) (ws : Fin r → List Bool) : List (Option Bool) :=
  (go R R.q0 w ws).2.1 ++ R.flush (go R R.q0 w ws).1

/-- The longest unread remainder of the other inputs. -/
def rest (R : Rule r) (w : List Bool) (ws : Fin r → List Bool) : ℕ :=
  Finset.univ.sup fun j => ((go R R.q0 w ws).2.2 j).length

/-- Exact number of transitions. -/
def time (R : Rule r) (w : List Bool) (ws : Fin r → List Bool) : ℕ :=
  w.length + rest R w ws + (R.flush (go R R.q0 w ws).1).length + 5

theorem go_rest_le (R : Rule r) : ∀ (q : R.Q) (w : List Bool) (ws : Fin r → List Bool) (j : Fin r),
    ((go R q w ws).2.2 j).length ≤ (ws j).length
  | q, [], ws, j => by simp [go]
  | q, b :: bs, ws, j => by
    simp only [go]
    refine (go_rest_le R _ bs _ j).trans ?_
    split_ifs <;> simp

theorem time_le (R : Rule r) (w : List Bool) (ws : Fin r → List Bool) (L : ℕ)
    (hL : ∀ j, (ws j).length ≤ L) : time R w ws ≤ w.length + L + R.B + 5 := by
  unfold time rest
  have h1 : (Finset.univ.sup fun j => ((go R R.q0 w ws).2.2 j).length) ≤ L :=
    Finset.sup_le fun j _ => (go_rest_le R _ w ws j).trans (hL j)
  have h2 := R.hB (go R R.q0 w ws).1
  omega

/-! ### Raw runs -/

/-- `l` is written from `h` on, followed by a separator. -/
def Rd (f : ℤ → Fin (a + 4)) (h : ℤ) (l : List Bool) : Prop :=
  (∀ c : ℕ, (hc : c < l.length) → f (h + c) = bitSymbol l[c]) ∧ f (h + l.length) = separator

theorem Rd.read {f : ℤ → Fin (a + 4)} {h : ℤ} {l : List Bool} (hr : Rd f h l) :
    decode (f h) = l.head? := by
  rcases l with _ | ⟨x, l⟩
  · simpa using congrArg decode hr.2
  · have := hr.1 0 (by simp)
    simp only [Nat.cast_zero, add_zero] at this
    simp [this]

theorem Rd.tail {f : ℤ → Fin (a + 4)} {h : ℤ} {l : List Bool} (hr : Rd f h l) :
    Rd f (h + if l = [] then 0 else 1) l.tail := by
  rcases l with _ | ⟨x, l⟩
  · simpa using hr
  · refine ⟨fun c hc => ?_, ?_⟩
    · have := hr.1 (c + 1) (by simp at hc ⊢; omega)
      simp only [List.getElem_cons_succ] at this
      simp only [List.cons_ne_nil, ↓reduceIte, List.tail_cons]
      rw [show h + 1 + (c : ℤ) = h + ((c + 1 : ℕ) : ℤ) by push_cast; ring]
      exact this
    · have := hr.2
      simp only [List.length_cons, List.cons_ne_nil, ↓reduceIte, List.tail_cons] at this ⊢
      rw [show h + 1 + (l.length : ℤ) = h + ((l.length + 1 : ℕ) : ℤ) by push_cast; ring]
      exact this

/-- The bank during a run: inputs keep their tapes, the output has tape `g`. -/
def tp (v : Tapes (r + 2) a) (hd : Fin (r + 2) → ℤ) (g : ℤ → Fin (a + 4)) : Tapes (r + 2) a :=
  ⟨hd, fun i => if i = out then g else v.tape i⟩

theorem update_self (f : ℤ → Fin (a + 4)) (h : ℤ) :
    (fun j => if j = h then f h else f j) = f := by
  funext j; split_ifs with hj <;> simp [hj]

theorem putWord_update_after (f : ℤ → Fin (a + 4)) (p j : ℤ) (x : Fin (a + 4))
    (xs : List (Fin (a + 4))) (hj : p + xs.length ≤ j) :
    putWord (Function.update f j x) p xs = Function.update (putWord f p xs) j x := by
  induction xs generalizing p with
  | nil => rfl
  | cons y xs ih =>
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hj
    simp only [putWord, ih (p + 1) (by omega)]
    exact Function.update_comm (β := fun _ : ℤ => Fin (a + 4)) (show j ≠ p by omega) x y _

theorem putWord_snoc (f : ℤ → Fin (a + 4)) (p : ℤ) (xs : List (Fin (a + 4))) (x : Fin (a + 4)) :
    putWord f p (xs ++ [x]) = Function.update (putWord f p xs) (p + xs.length) x := by
  rw [putWord_append]
  simp only [putWord]
  exact putWord_update_after _ _ _ _ _ le_rfl

theorem tapes_ext {t : ℕ} {v w : Tapes t a} (h1 : v.head = w.head) (h2 : v.tape = w.tape) :
    v = w := by
  cases v; cases w; simp_all

/-- Output tape after one optional symbol. -/
def wr (g : ℤ → Fin (a + 4)) (h : ℤ) : Option (Option Bool) → ℤ → Fin (a + 4)
  | none => g
  | some o => Function.update g h (sym o)

/-- Head moves of one run step. -/
def adv (v : Tapes (r + 2) a) (hd : Fin (r + 2) → ℤ) (o : Option (Option Bool)) (fl : Fin r → Bool)
    (i : Fin (r + 2)) : ℤ :=
  hd i + if i = out then (if o.isSome then 1 else 0)
    else if i = drv then 1
    else if (decode (v.tape i (hd i))).isSome ∧ advOf fl i then 1 else 0

theorem tp_tape_out (v : Tapes (r + 2) a) (hd) (g : ℤ → Fin (a + 4)) :
    (tp v hd g).tape out = g := by simp [tp]

theorem tp_tape_in (v : Tapes (r + 2) a) (hd) (g : ℤ → Fin (a + 4)) (i : Fin (r + 2)) (hi : i ≠ out) :
    (tp v hd g).tape i = v.tape i := by simp [tp, hi]

theorem Rd.step {f : ℤ → Fin (a + 4)} {h : ℤ} {l : List Bool} (hr : Rd f h l) (b : Bool) :
    Rd f (h + if l ≠ [] ∧ b = true then 1 else 0) (if b then l.tail else l) := by
  cases b
  · simpa using hr
  · have := hr.tail
    rcases l with _ | ⟨x, l⟩ <;> simpa using this

theorem run_step (R : Rule r) (ext : Bool) (v : Tapes (r + 2) a) (hd : Fin (r + 2) → ℤ)
    (g : ℤ → Fin (a + 4)) (q : R.Q) (b : Bool) (bs : List Bool) (rems : Fin r → List Bool)
    (hdrv : Rd (v.tape drv) (hd drv) (b :: bs))
    (hoth : ∀ j, Rd (v.tape (oth j)) (hd (oth j)) (rems j)) :
    (machine (a := a) R ext).fstep ⟨.run q, tp v hd g⟩ =
      some ⟨.run (R.step q b (fun j => (rems j).head?)).1,
        tp v (adv v hd (R.step q b (fun j => (rems j).head?)).2.1
            (R.step q b (fun j => (rems j).head?)).2.2)
          (wr g (hd out) (R.step q b (fun j => (rems j).head?)).2.1)⟩ := by
  have hb : v.tape drv (hd drv) = bitSymbol b := by
    have := hdrv.1 0 (by simp)
    simp only [Nat.cast_zero, add_zero, List.getElem_cons_zero] at this
    exact this
  have hrd : ∀ j, decode (v.tape (oth j) (hd (oth j))) = (rems j).head? := fun j => (hoth j).read
  have hread : (fun j => decode ((tp v hd g).tape (oth j) ((tp v hd g).head (oth j)))) =
      fun j => (rems j).head? := by
    funext j; rw [tp_tape_in _ _ _ _ (oth_ne_out j)]; exact hrd j
  have hdrvr : (tp v hd g).tape drv ((tp v hd g).head drv) = bitSymbol b := by
    rw [tp_tape_in _ _ _ _ drv_ne_out]; exact hb
  have hbit : decide (bitSymbol (a := a) b = bitSymbol true) = b := by
    cases b <;> simp [bitSymbol, Fin.ext_iff]
  simp only [FMachine.fstep, machine, hdrvr, bit_ne_sep, ↓reduceIte, hread, hbit]
  congr 2
  set o := (R.step q b (fun j => (rems j).head?)).2.1
  refine tapes_ext (funext fun i => ?_) (funext fun i => ?_)
  · simp only [adv, tp]
    by_cases hi : i = out
    · subst hi; simp only [↓reduceIte]; cases o <;> simp [Move.offset]
    · simp only [hi, ↓reduceIte]
      split_ifs <;> simp_all [Move.offset]
  · funext c
    simp only [tp]
    by_cases hi : i = out
    · subst hi
      simp only [↓reduceIte, wr]
      cases o with
      | none => simp only; split_ifs with hc <;> simp [hc]
      | some s =>
        simp only
        by_cases hc : c = hd out
        · simp [hc]
        · simp [hc, Function.update_of_ne hc]
    · simp only [hi, ↓reduceIte]
      split_ifs with hc <;> simp [hc]

theorem wr_put (g0 : ℤ → Fin (a + 4)) (s0 : ℤ) (O : List (Option Bool)) (o : Option (Option Bool)) :
    wr (putWord g0 s0 (O.map sym)) (s0 + O.length) o = putWord g0 s0 ((O ++ o.toList).map sym) := by
  cases o with
  | none => simp [wr]
  | some x =>
    simp only [wr, Option.toList_some, List.map_append, List.map_cons, List.map_nil]
    rw [putWord_snoc]; simp

theorem adv_drv (v : Tapes (r + 2) a) (hd) (o) (fl : Fin r → Bool) :
    adv v hd o fl drv = hd drv + 1 := by
  simp [adv, drv_ne_out]

theorem adv_oth (v : Tapes (r + 2) a) (hd) (o) (fl : Fin r → Bool) (j : Fin r) (l : List Bool)
    (h : Rd (v.tape (oth j)) (hd (oth j)) l) :
    adv v hd o fl (oth j) = hd (oth j) + if l ≠ [] ∧ fl j = true then 1 else 0 := by
  simp only [adv, oth_ne_out, oth_ne_drv, ↓reduceIte, h.read, advOf_oth]
  cases l <;> simp

theorem adv_out (v : Tapes (r + 2) a) (hd) (o : Option (Option Bool)) (fl : Fin r → Bool) :
    adv v hd o fl out = hd out + o.toList.length := by
  cases o <;> simp [adv]

/-- The run phase: one transition per driver bit. -/
theorem run_phase (R : Rule r) (ext : Bool) (v : Tapes (r + 2) a) (g0 : ℤ → Fin (a + 4)) (s0 : ℤ) :
    ∀ (bs : List Bool) (q : R.Q) (hd : Fin (r + 2) → ℤ) (O : List (Option Bool))
      (rems : Fin r → List Bool),
    Rd (v.tape drv) (hd drv) bs → (∀ j, Rd (v.tape (oth j)) (hd (oth j)) (rems j)) →
    hd out = s0 + O.length →
    ∃ hd', (machine (a := a) R ext).frun bs.length ⟨.run q, tp v hd (putWord g0 s0 (O.map sym))⟩ =
        some ⟨.run (go R q bs rems).1, tp v hd' (putWord g0 s0 ((O ++ (go R q bs rems).2.1).map sym))⟩ ∧
      hd' drv = hd drv + bs.length ∧
      (∀ j, Rd (v.tape (oth j)) (hd' (oth j)) ((go R q bs rems).2.2 j)) ∧
      (∀ j, hd' (oth j) + ((go R q bs rems).2.2 j).length = hd (oth j) + (rems j).length) ∧
      hd' out = s0 + (O ++ (go R q bs rems).2.1).length
  | [], q, hd, O, rems, _, hoth, hout => ⟨hd, by simp [go, FMachine.frun], by simp, by simpa [go] using hoth,
      by simp [go], by simpa [go] using hout⟩
  | b :: bs, q, hd, O, rems, hdrv, hoth, hout => by
    set p := R.step q b (fun j => (rems j).head?)
    have h1 := run_step R ext v hd (putWord g0 s0 (O.map sym)) q b bs rems hdrv hoth
    rw [hout, wr_put] at h1
    set hd1 := adv v hd p.2.1 p.2.2
    have hdrv1 : Rd (v.tape drv) (hd1 drv) bs := by
      have := hdrv.tail
      simpa [hd1, adv_drv] using this
    have hoth1 : ∀ j, Rd (v.tape (oth j)) (hd1 (oth j))
        (if p.2.2 j then (rems j).tail else rems j) := fun j => by
      rw [show hd1 (oth j) = _ from adv_oth v hd p.2.1 p.2.2 j (rems j) (hoth j)]
      exact (hoth j).step _
    have hout1 : hd1 out = s0 + (O ++ p.2.1.toList).length := by
      rw [show hd1 out = _ from adv_out v hd p.2.1 p.2.2, hout]; simp; ring
    obtain ⟨hd', hrun, hd'drv, hd'oth, hd'inv, hd'out⟩ :=
      run_phase R ext v g0 s0 bs p.1 hd1 (O ++ p.2.1.toList)
        (fun j => if p.2.2 j then (rems j).tail else rems j) hdrv1 hoth1 hout1
    refine ⟨hd', ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_cons, FMachine.frun, h1, Option.bind_some]
      simpa [go, p, List.append_assoc] using hrun
    · rw [hd'drv, show hd1 drv = _ from adv_drv v hd p.2.1 p.2.2]; simp; ring
    · simpa [go, p] using hd'oth
    · intro j
      have := hd'inv j
      simp only [go, p] at this ⊢
      rw [this, show hd1 (oth j) = _ from adv_oth v hd p.2.1 p.2.2 j (rems j) (hoth j)]
      cases hf : p.2.2 j <;> rcases rems j with _ | ⟨x, l⟩ <;> simp [hf] <;> ring
    · simpa [go, p, List.append_assoc] using hd'out

/-- The longest remainder. -/
def maxLen (rems : Fin r → List Bool) : ℕ := Finset.univ.sup fun j => (rems j).length

theorem le_maxLen (rems : Fin r → List Bool) (j : Fin r) : (rems j).length ≤ maxLen rems :=
  Finset.le_sup (f := fun j => (rems j).length) (Finset.mem_univ j)

theorem maxLen_tail (rems : Fin r → List Bool) :
    maxLen (fun j => (rems j).tail) = maxLen rems - 1 := by
  apply le_antisymm
  · exact Finset.sup_le fun j _ => by
      simp only [List.length_tail]; have := le_maxLen rems j; omega
  · rcases Nat.eq_zero_or_pos (maxLen rems) with h | h
    · omega
    · have hne : (Finset.univ : Finset (Fin r)).Nonempty := by
        by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        simp [maxLen, hne] at h
      obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin r)) hne
        (fun j => (rems j).length)
      have : (rems j).tail.length ≤ maxLen (fun j => (rems j).tail) :=
        le_maxLen (fun j => (rems j).tail) j
      simp only [maxLen] at h ⊢
      rw [hj] at h ⊢
      simp only [List.length_tail] at this
      simpa [maxLen] using this

/-- The skip phase: the other inputs run to their separators. -/
theorem skip_phase (R : Rule r) (ext : Bool) (v : Tapes (r + 2) a) (g : ℤ → Fin (a + 4)) (q : R.Q) :
    ∀ (n : ℕ) (hd : Fin (r + 2) → ℤ) (rems : Fin r → List Bool), maxLen rems = n →
    Rd (v.tape drv) (hd drv) [] → (∀ j, Rd (v.tape (oth j)) (hd (oth j)) (rems j)) →
    ∃ hd', (machine (a := a) R ext).frun (n + 1) ⟨.skip q, tp v hd g⟩ =
        some ⟨.fl q 0, tp v hd' g⟩ ∧ hd' drv = hd drv ∧ hd' out = hd out ∧
      (∀ j, hd' (oth j) = hd (oth j) + (rems j).length ∧ Rd (v.tape (oth j)) (hd' (oth j)) [])
  | 0, hd, rems, hn, hdrv, hoth => by
    have hnil : ∀ j, rems j = [] := fun j => by
      have := le_maxLen rems j; rw [hn] at this; exact List.length_eq_zero_iff.mp (by omega)
    have hsep : ∀ j : Fin r, (tp v hd g).tape (oth j) ((tp v hd g).head (oth j)) = separator := by
      intro j
      have := (hoth j).2; rw [hnil j] at this; simpa [tp, oth_ne_out j] using this
    refine ⟨hd, ?_, rfl, rfl, fun j => ⟨by simp [hnil j], by simpa [hnil j] using hoth j⟩⟩
    rw [FMachine.frun, FMachine.fstep]
    simp only [machine, hsep, implies_true, ↓reduceIte, Option.bind_some, FMachine.frun]
    congr 2
    refine tapes_ext (funext fun i => by simp [Move.offset]) (funext fun i => ?_)
    funext c; dsimp only; split_ifs with hc <;> simp [hc]
  | n + 1, hd, rems, hn, hdrv, hoth => by
    have hsome : ∃ j, rems j ≠ [] := by
      by_contra h; simp only [ne_eq, not_exists, not_not] at h
      have : maxLen rems = 0 := by
        apply le_antisymm _ (Nat.zero_le _)
        exact Finset.sup_le fun j _ => by simp [h j]
      omega
    obtain ⟨j0, hj0⟩ := hsome
    have hnot : ¬ ∀ j : Fin r, (tp v hd g).tape (oth j) ((tp v hd g).head (oth j)) = separator := by
      intro h
      have := h j0
      rw [tp_tape_in _ _ _ _ (oth_ne_out j0)] at this
      have hr := (hoth j0).read
      simp only [tp] at this
      rw [this, decode_sep] at hr
      rcases hrj : rems j0 with _ | ⟨x, l⟩
      · exact hj0 hrj
      · rw [hrj] at hr; simp at hr
    set hd1 : Fin (r + 2) → ℤ := fun i =>
      hd i + if i ≠ out ∧ (decode (v.tape i (hd i))).isSome then 1 else 0
    have h1 : (machine (a := a) R ext).fstep ⟨.skip q, tp v hd g⟩ = some ⟨.skip q, tp v hd1 g⟩ := by
      rw [FMachine.fstep]
      simp only [machine, hnot, ↓reduceIte]
      congr 2
      refine tapes_ext (funext fun i => ?_) (funext fun i => ?_)
      · simp only [tp, hd1]
        by_cases hi : i = out
        · simp [hi, Move.offset]
        · simp only [hi, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
          split_ifs <;> simp [Move.offset]
      · funext c; simp only [tp]; split_ifs with h1 h2 <;> simp_all
    have hdrv0 : v.tape drv (hd drv) = separator := by simpa using hdrv.2
    have hd1drv : hd1 drv = hd drv := by simp [hd1, drv_ne_out, hdrv0]
    have hd1out : hd1 out = hd out := by simp [hd1]
    have hd1oth : ∀ j, hd1 (oth j) = hd (oth j) + if rems j = [] then 0 else 1 := fun j => by
      simp only [hd1, ne_eq, oth_ne_out, not_false_eq_true, true_and, (hoth j).read]
      cases rems j <;> simp
    obtain ⟨hd', hrun, e1, e2, e3⟩ := skip_phase R ext v g q n hd1 (fun j => (rems j).tail)
      (by rw [maxLen_tail, hn]; rfl) (by rw [hd1drv]; exact hdrv)
      (fun j => by rw [hd1oth]; exact (hoth j).tail)
    refine ⟨hd', ?_, by rw [e1, hd1drv], by rw [e2, hd1out], fun j => ⟨?_, (e3 j).2⟩⟩
    · rw [show n + 1 + 1 = 1 + (n + 1) by omega, FMachine.frun_add, FMachine.frun_one, h1,
        Option.bind_some, hrun]
    · rw [(e3 j).1, hd1oth]
      rcases rems j with _ | ⟨x, l⟩ <;> simp; ring

theorem run_to_skip (R : Rule r) (ext : Bool) (v : Tapes (r + 2) a) (hd : Fin (r + 2) → ℤ)
    (g : ℤ → Fin (a + 4)) (q : R.Q) (hdrv : Rd (v.tape drv) (hd drv) []) :
    (machine (a := a) R ext).fstep ⟨.run q, tp v hd g⟩ = some ⟨.skip q, tp v hd g⟩ := by
  have h0 : (tp v hd g).tape drv ((tp v hd g).head drv) = separator := by
    simpa [tp, drv_ne_out] using hdrv.2
  rw [FMachine.fstep]
  simp only [machine, h0, ↓reduceIte]
  congr 2
  refine tapes_ext (funext fun i => by simp [Move.offset]) (funext fun i => ?_)
  funext c; dsimp only; split_ifs with hc <;> simp [hc]

/-- The flush phase. -/
theorem flush_phase (R : Rule r) (ext : Bool) (v : Tapes (r + 2) a) (g0 : ℤ → Fin (a + 4)) (s0 : ℤ)
    (q : R.Q) : ∀ (m : ℕ) (i : Fin (R.B + 1)) (hd : Fin (r + 2) → ℤ) (O : List (Option Bool)),
    i.val + m = (R.flush q).length → hd out = s0 + O.length →
    ∃ hd', (machine (a := a) R ext).frun (m + 1) ⟨.fl q i, tp v hd (putWord g0 s0 (O.map sym))⟩ =
        some ⟨.fin, tp v hd' (putWord g0 s0 ((O ++ (R.flush q).drop i.val).map sym))⟩ ∧
      hd' out = s0 + (O ++ (R.flush q).drop i.val).length ∧ ∀ x, x ≠ out → hd' x = hd x
  | 0, i, hd, O, hm, hout => by
    have hi : ¬ i.val < (R.flush q).length := by omega
    refine ⟨hd, ?_, ?_, fun _ _ => rfl⟩
    · rw [FMachine.frun, FMachine.fstep]
      simp only [machine, hi, ↓reduceDIte, Option.bind_some, FMachine.frun,
        List.drop_eq_nil_of_le (show (R.flush q).length ≤ i.val by omega), List.append_nil]
      congr 2
      refine tapes_ext (funext fun i => by simp [Move.offset]) (funext fun i => ?_)
      funext c; dsimp only; split_ifs with hc <;> simp [hc]
    · rw [List.drop_eq_nil_of_le (show (R.flush q).length ≤ i.val by omega)]; simpa using hout
  | m + 1, i, hd, O, hm, hout => by
    have hi : i.val < (R.flush q).length := by omega
    set x := (R.flush q)[i.val]
    set i1 : Fin (R.B + 1) := ⟨i.val + 1, by have := R.hB q; omega⟩
    set hd1 : Fin (r + 2) → ℤ := fun y => hd y + if y = out then 1 else 0
    have h1 : (machine (a := a) R ext).fstep ⟨.fl q i, tp v hd (putWord g0 s0 (O.map sym))⟩ =
        some ⟨.fl q i1, tp v hd1 (putWord g0 s0 ((O ++ [x]).map sym))⟩ := by
      rw [FMachine.fstep]
      simp only [machine, hi, ↓reduceDIte]
      congr 2
      refine tapes_ext (funext fun y => ?_) (funext fun y => ?_)
      · simp only [tp, hd1]; split_ifs <;> simp [Move.offset]
      · funext c
        simp only [tp]
        by_cases hy : y = out
        · subst hy
          simp only [↓reduceIte, List.map_append, List.map_cons, List.map_nil]
          rw [putWord_snoc, List.length_map, ← hout]
          by_cases hc : c = hd out
          · simp [hc, x]
          · simp [hc]
        · simp only [hy, ↓reduceIte]; split_ifs with hc <;> simp [hc]
    obtain ⟨hd', hrun, hout', hother⟩ := flush_phase R ext v g0 s0 q m i1 hd1 (O ++ [x])
      (by simp [i1]; omega) (by simp [hd1, hout]; ring)
    have hdrop : (R.flush q).drop i.val = x :: (R.flush q).drop (i.val + 1) :=
      List.drop_eq_getElem_cons hi
    refine ⟨hd', ?_, ?_, fun y hy => by rw [hother y hy]; simp [hd1, hy]⟩
    · rw [show m + 1 + 1 = 1 + (m + 1) by omega, FMachine.frun_add, FMachine.frun_one, h1,
        Option.bind_some, hrun, hdrop]
      simp [i1]
    · rw [hout', hdrop]; simp [i1]

theorem fin_step (R : Rule r) (ext : Bool) (v : Tapes (r + 2) a) (hd : Fin (r + 2) → ℤ)
    (g : ℤ → Fin (a + 4)) :
    (machine (a := a) R ext).fstep ⟨.fin, tp v hd g⟩ =
      some ⟨.done, tp v (fun i => hd i + if i = out then 0 else 1) g⟩ := by
  rw [FMachine.fstep]
  simp only [machine]
  congr 2
  refine tapes_ext (funext fun i => ?_) (funext fun i => ?_)
  · simp only [tp]; split_ifs <;> simp [Move.offset]
  · funext c; dsimp only; split_ifs with hc
    · rw [hc]; rfl
    · rfl

theorem done_halt (R : Rule r) (ext : Bool) (w : Tapes (r + 2) a) :
    (machine (a := a) R ext).fstep ⟨.done, w⟩ = none := by
  simp [FMachine.fstep, machine]

theorem init_step (R : Rule r) (ext : Bool) (v : Tapes (r + 2) a) :
    (machine (a := a) R ext).fstep ⟨.init, v⟩ =
      some ⟨.run R.q0, tp v (fun i => v.head i - if i = out ∧ ext = true then 1 else 0)
        (v.tape out)⟩ := by
  rw [FMachine.fstep]
  simp only [machine]
  congr 2
  refine tapes_ext (funext fun i => ?_) (funext fun i => ?_)
  · simp only [tp]; split_ifs <;> simp [Move.offset] <;> ring
  · funext c; simp only [tp]
    by_cases hi : i = out
    · subst hi; simp only [↓reduceIte]; split_ifs with hc <;> simp [hc]
    · simp only [hi, ↓reduceIte]; split_ifs with hc <;> simp [hc]

/-- The complete run of the streaming machine. -/
theorem stream_run (R : Rule r) (ext : Bool) (v : Tapes (r + 2) a) (w : List Bool)
    (ws : Fin r → List Bool) (hdrv : Rd (v.tape drv) (v.head drv) w)
    (hoth : ∀ j, Rd (v.tape (oth j)) (v.head (oth j)) (ws j)) :
    ∃ v' : Tapes (r + 2) a,
      (machine (a := a) R ext).frun (time R w ws) ⟨.init, v⟩ = some ⟨.done, v'⟩ ∧
      (machine (a := a) R ext).fstep ⟨.done, v'⟩ = none ∧
      v'.tape = (fun i => if i = out then
        putWord (v.tape out) (v.head out - if ext = true then 1 else 0) ((output R w ws).map sym)
        else v.tape i) ∧
      v'.head drv = v.head drv + w.length + 1 ∧
      (∀ j, v'.head (oth j) = v.head (oth j) + (ws j).length + 1) ∧
      v'.head out = (v.head out - if ext = true then 1 else 0) + (output R w ws).length := by
  set s0 := v.head out - if ext = true then 1 else 0
  set hd0 : Fin (r + 2) → ℤ := fun i => v.head i - if i = out ∧ ext = true then 1 else 0
  have h0drv : hd0 drv = v.head drv := by simp [hd0, drv_ne_out]
  have h0oth : ∀ j, hd0 (oth j) = v.head (oth j) := fun j => by simp [hd0, oth_ne_out]
  have h0out : hd0 out = s0 + ([] : List (Option Bool)).length := by simp [hd0, s0]
  have hg : v.tape out = putWord (v.tape out) s0 (([] : List (Option Bool)).map sym) := rfl
  obtain ⟨hd1, hrun1, e1drv, e1oth, e1inv, e1out⟩ := run_phase R ext v (v.tape out) s0 w R.q0 hd0 []
    (fun j => ws j) (by rw [h0drv]; exact hdrv) (fun j => by rw [h0oth]; exact hoth j) h0out
  set G := go R R.q0 w ws
  have hdrv1 : Rd (v.tape drv) (hd1 drv) [] := by
    rw [e1drv, h0drv]
    exact ⟨fun c hc => absurd hc (by simp), by simpa using hdrv.2⟩
  obtain ⟨hd2, hrun2, e2drv, e2out, e2oth⟩ := skip_phase R ext v
    (putWord (v.tape out) s0 (([] ++ G.2.1).map sym)) G.1 (rest R w ws) hd1 G.2.2 rfl hdrv1 e1oth
  obtain ⟨hd3, hrun3, e3out, e3oth⟩ := flush_phase R ext v (v.tape out) s0 G.1
    (R.flush G.1).length 0 hd2 ([] ++ G.2.1) (by simp) (by rw [e2out, e1out])
  refine ⟨tp v (fun i => hd3 i + if i = out then 0 else 1)
    (putWord (v.tape out) s0 (([] ++ G.2.1 ++ (R.flush G.1).drop 0).map sym)), ?_,
    done_halt R ext _, ?_, ?_, ?_, ?_⟩
  · have ht : time R w ws = 1 + w.length + 1 + (rest R w ws + 1) + ((R.flush G.1).length + 1) + 1 := by
      simp only [time, G]; ring
    rw [ht]
    exact FMachine.frun_trans _ (FMachine.frun_trans _ (FMachine.frun_trans _ (FMachine.frun_trans _
      (FMachine.frun_trans _ (FMachine.frun_of_step _ (init_step R ext v)) hrun1)
      (FMachine.frun_of_step _ (run_to_skip R ext v hd1 _ G.1 hdrv1)))
      hrun2) hrun3) (FMachine.frun_of_step _ (fin_step R ext v hd3 _))
  · funext i; simp only [tp, output, G, List.nil_append, List.drop_zero]
  · simp only [tp, drv_ne_out, ↓reduceIte]
    rw [e3oth drv drv_ne_out, e2drv, e1drv, h0drv]
  · intro j
    simp only [tp, oth_ne_out, ↓reduceIte]
    rw [e3oth _ (oth_ne_out j), (e2oth j).1, e1inv j, h0oth]
  · simp only [tp, ↓reduceIte, add_zero]
    rw [e3out]; simp [output, G]

end Strm

end IntegerMultBounds.Schoenhage
