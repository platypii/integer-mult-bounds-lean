import IntegerMultBounds.Machine.RecordRewind

/-! Walking over blank-separated records: a three-tape machine (source,
destination, ruler) that moves the source head over whole records, copying
them to the destination when `cp`, and stops at a record origin either when
the source reads blank (`ct = false`: to the end of the records) or when the
ruler reads blank (`ct = true`: one ruler cell per record). Copy-all, copy-`n`,
skip-all and skip-`n` are its four instances. -/

namespace IntegerMultBounds.Machine.RecordCopy

open OrderedSelect (flat flat_cons)

variable {a : ℕ}

/-- State one: at a record origin; state zero: inside a record. -/
def program (cp ct : Bool) : Program 3 2 a where
  tapes_pos := by decide
  start := 1
  transition := fun s sy =>
    if s = 1 ∧ (if ct then sy 2 = blank else sy 0 = blank) then none
    else if sy 0 ≠ blank then
      some (0, fun i => if i = 0 then (sy 0, .right)
        else if i = 1 then (if cp then sy 0 else sy 1, if cp then .right else .stay)
        else (sy 2, .stay))
    else
      some (1, fun i => if i = 0 then (sy 0, .right)
        else if i = 1 then (if cp then blank else sy 1, if cp then .right else .stay)
        else (sy 2, if ct then .right else .stay))

def cfg (f g h : ℤ → Fin (a + 4)) (x y r : ℤ) (s : Fin 2) : Config 3 2 a :=
  ⟨s, fun i => if i = 0 then x else if i = 1 then y else r,
    fun i => if i = 0 then f else if i = 1 then g else h⟩

/-- The destination after writing `xs` from `y`. -/
def dst (cp : Bool) (g : ℤ → Fin (a + 4)) (y : ℤ) (xs : List (Fin (a + 4))) : ℤ → Fin (a + 4) :=
  if cp then putWord g y xs else g

def adv (b : Bool) (n : ℕ) : ℤ := if b then n else 0

theorem step_sym (cp ct : Bool) (f g h : ℤ → Fin (a + 4)) (x y r : ℤ) (s : Fin 2)
    (hc : f x ≠ blank) (hs : s = 1 → (if ct then h r ≠ blank else True)) :
    step (program cp ct) (cfg f g h x y r s) =
      some (cfg f (dst cp g y [f x]) h (x + 1) (y + adv cp 1) r 0) := by
  have ht : (program (a := a) cp ct).transition s
      (fun i => (cfg f g h x y r s).tape i ((cfg f g h x y r s).head i)) =
      some (0, fun i => if i = 0 then (f x, Move.right)
        else if i = 1 then (if cp then f x else g y, if cp then Move.right else Move.stay)
        else (h r, Move.stay)) := by
    fin_cases s <;> cases ct <;> simp_all [program, cfg]
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Option.some.injEq, Config.mk.injEq, true_and]
  constructor
  · funext i; fin_cases i <;> cases cp <;> simp [Move.offset, adv]
  · funext i j; fin_cases i <;> cases cp <;> simp [dst, putWord, Function.update_apply]
    all_goals (try (intro hj; rw [hj]))

theorem step_sep (cp ct : Bool) (f g h : ℤ → Fin (a + 4)) (x y r : ℤ)
    (hc : f x = blank) :
    step (program cp ct) (cfg f g h x y r 0) =
      some (cfg f (dst cp g y [blank]) h (x + 1) (y + adv cp 1) (r + adv ct 1) 1) := by
  have ht : (program (a := a) cp ct).transition 0
      (fun i => (cfg f g h x y r 0).tape i ((cfg f g h x y r 0).head i)) =
      some (1, fun i => if i = 0 then (f x, Move.right)
        else if i = 1 then (if cp then blank else g y, if cp then Move.right else Move.stay)
        else (h r, if ct then Move.right else Move.stay)) := by
    cases ct <;> simp_all [program, cfg]
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Option.some.injEq, Config.mk.injEq, true_and]
  constructor
  · funext i; fin_cases i <;> cases cp <;> cases ct <;> simp [Move.offset, adv]
  · funext i j; fin_cases i <;> cases cp <;> simp [dst, putWord, Function.update_apply, hc]
    all_goals (try (intro hj; rw [hj]))
    all_goals (try exact hc.symm)

theorem dst_cons (cp : Bool) (g : ℤ → Fin (a + 4)) (y : ℤ) (c : Fin (a + 4)) (xs : List (Fin (a + 4))) :
    dst cp (dst cp g y [c]) (y + adv cp 1) xs = dst cp g y (c :: xs) := by
  cases cp
  · simp [dst]
  · simp only [dst, adv, ite_true, Nat.cast_one]
    rw [putWord_cons g y c xs]; rfl

theorem dst_append (cp : Bool) (g : ℤ → Fin (a + 4)) (y : ℤ) (xs ys : List (Fin (a + 4))) :
    dst cp (dst cp g y xs) (y + adv cp xs.length) ys = dst cp g y (xs ++ ys) := by
  cases cp <;> simp [dst, adv, putWord_append_forward]

/-- Walking over a nonempty nonblank word. -/
theorem word_run (cp ct : Bool) (f h : ℤ → Fin (a + 4)) (r : ℤ) (c : Fin (a + 4))
    (xs : List (Fin (a + 4))) (hx : ∀ z ∈ c :: xs, z ≠ blank) :
    ∀ (g : ℤ → Fin (a + 4)) (x y : ℤ) (s : Fin 2),
    (∀ k : ℕ, k < (c :: xs).length → f (x + k) = (c :: xs).getD k blank) →
    (s = 1 → (if ct then h r ≠ blank else True)) →
    run (program cp ct) (c :: xs).length (cfg f g h x y r s) =
      some (cfg f (dst cp g y (c :: xs)) h (x + (c :: xs).length) (y + adv cp (c :: xs).length) r 0) := by
  induction xs generalizing c with
  | nil =>
    intro g x y s hf hs
    have hfx : f x = c := by simpa using hf 0 (by simp)
    rw [List.length_singleton, run, step_sym cp ct f g h x y r s (by rw [hfx]; exact hx c (by simp)) hs]
    simp [run, hfx]
  | cons d xs ih =>
    intro g x y s hf hs
    have hfx : f x = c := by simpa using hf 0 (by simp)
    rw [List.length_cons, run, step_sym cp ct f g h x y r s (by rw [hfx]; exact hx c (by simp)) hs]
    simp only [Option.bind_some]
    rw [ih d (fun z hz => hx z (by simp_all)) (dst cp g y [f x]) (x + 1) (y + adv cp 1) 0
      (fun k hk => by
        have := hf (k + 1) (by simp at hk ⊢; omega)
        rw [show x + 1 + (k : ℤ) = x + ((k + 1 : ℕ) : ℤ) by push_cast; ring, this]
        simp) (by intro h; exact absurd h (by decide)), hfx, dst_cons]
    congr 2
    · push_cast; ring
    · cases cp <;> simp [adv]; ring

/-- Walking over a list of records from a record origin. -/
theorem records_run (cp ct : Bool) (f h : ℤ → Fin (a + 4)) (recs : List (List (Fin (a + 4))))
    (hne : ∀ z ∈ recs, z ≠ [] ∧ ∀ c ∈ z, c ≠ blank) :
    ∀ (g : ℤ → Fin (a + 4)) (x y r : ℤ),
    (∀ k : ℕ, k < (flat recs).length → f (x + k) = (flat recs).getD k blank) →
    (ct → ∀ k : ℕ, k < recs.length → h (r + k) ≠ blank) →
    run (program cp ct) (flat recs).length (cfg f g h x y r 1) =
      some (cfg f (dst cp g y (flat recs)) h (x + (flat recs).length)
        (y + adv cp (flat recs).length) (r + adv ct recs.length) 1) := by
  induction recs with
  | nil => intro g x y r _ _; cases cp <;> simp [OrderedSelect.flat_nil, run, dst, adv, putWord]
  | cons z zs ih =>
    intro g x y r hf hr
    obtain ⟨hz0, hzb⟩ := hne z (by simp)
    obtain ⟨c, xs, rfl⟩ := List.exists_cons_of_ne_nil hz0
    have hflat : flat ((c :: xs) :: zs) = (c :: xs) ++ (blank :: flat zs) := flat_cons _ _
    rw [hflat] at hf ⊢
    have hlen : ((c :: xs) ++ (blank :: flat zs)).length = (c :: xs).length + (1 + (flat zs).length) := by
      simp; ring
    rw [hlen, run_add]
    rw [word_run cp ct f h r c xs hzb g x y 1 (fun k hk => by
        rw [hf k (by simp at hk ⊢; omega), List.getD_append _ _ _ _ hk])
      (fun _ => by
        cases ct with
        | false => trivial
        | true => simpa using hr rfl 0 (by simp))]
    simp only [Option.bind_some]
    have hsep : f (x + (c :: xs).length) = blank := by
      rw [hf (c :: xs).length (by simp), List.getD_append_right _ _ _ _ le_rfl]; simp
    rw [run_add, run_one, step_sep cp ct f _ h _ _ r hsep]
    simp only [Option.bind_some]
    have := ih (fun z' hz' => hne z' (by simp [hz'])) (dst cp (dst cp g y (c :: xs)) (y + adv cp (c :: xs).length) [blank])
      (x + (c :: xs).length + 1) (y + adv cp (c :: xs).length + adv cp 1) (r + adv ct 1)
      (fun k hk => by
        rw [show x + ((c :: xs).length : ℤ) + 1 + k = x + (((c :: xs).length + 1 + k : ℕ) : ℤ) by push_cast; ring,
          hf _ (by simp at hk ⊢; omega), List.getD_append_right _ _ _ _ (by omega)]
        simp only [List.length_cons]
        rw [show xs.length + 1 + 1 + k - (xs.length + 1) = k + 1 by omega]
        simp)
      (fun hct k hk => by
        have := hr hct (k + 1) (by simp; omega)
        rw [show r + adv ct 1 + k = r + ((k + 1 : ℕ) : ℤ) by simp [adv, hct]; ring]
        exact this)
    have hy : y + adv cp (c :: xs).length + adv cp 1 = y + adv cp (c :: xs ++ [blank]).length := by
      cases cp <;> simp [adv]; ring
    rw [this, dst_append, hy, dst_append, List.append_assoc, List.singleton_append]
    congr 2
    · push_cast; ring
    · cases cp <;> simp [adv]; ring
    · cases ct <;> simp [adv]; ring

/-- The contract: from a record origin, walk over `recs`, copying them when `cp`;
stop at the end of the records (`ct = false`) or after one record per ruler cell. -/
theorem walk_hoare (cp ct : Bool) (f g h : ℤ → Fin (a + 4)) (x y r : ℤ)
    (recs : List (List (Fin (a + 4)))) (hne : ∀ z ∈ recs, z ≠ [] ∧ ∀ c ∈ z, c ≠ blank)
    (hf : ∀ k : ℕ, k < (flat recs).length → f (x + k) = (flat recs).getD k blank)
    (hr : ct → ∀ k : ℕ, k < recs.length → h (r + k) ≠ blank)
    (hend : if ct then h (r + recs.length) = blank else f (x + (flat recs).length) = blank) :
    HoareTime (program cp ct) (fun v => v = (cfg f g h x y r 1).tapes)
      (fun v => v = (cfg f (dst cp g y (flat recs)) h (x + (flat recs).length)
        (y + adv cp (flat recs).length) (r + adv ct recs.length) 1).tapes) (flat recs).length := by
  rintro v rfl
  refine ⟨_, _, le_rfl, records_run cp ct f h recs hne g x y r hf hr, ?_, rfl⟩
  unfold step
  cases ct <;> simp_all [program, cfg, adv]

end IntegerMultBounds.Machine.RecordCopy
