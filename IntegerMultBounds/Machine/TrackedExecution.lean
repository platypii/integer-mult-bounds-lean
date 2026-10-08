import IntegerMultBounds.Machine.TrackedCleanup
import IntegerMultBounds.Machine.Frame

/-! Synchronized visited tapes for literal machine execution. Every original
transition is simulated by two transitions; the second records the arrival cell.
No input length or runtime bound enters the finite transition table. -/
namespace IntegerMultBounds.Machine.TrackedExecution
open TrackedCleanup (tracker)
variable {t s a : ℕ}

def mark (x : Fin (a+4)) : Fin (a+4) := if x = separator then separator else bitSymbol false

def program (M : Program t s a) : Program (t+t) (s+s) a where
  tapes_pos := by have h := M.tapes_pos; omega
  start := Fin.castAdd s M.start
  transition := fun st sy => Fin.addCases
    (fun st => (M.transition st (fun i => sy (Fin.castAdd t i))).map (fun (next,act) =>
      (Fin.natAdd s next,Fin.addCases act
        (fun i => (mark (sy (Fin.natAdd t i)),(act i).2)))))
    (fun st => some (Fin.castAdd s st,Fin.addCases
      (fun i => (sy (Fin.castAdd t i),Move.stay))
      (fun i => (mark (sy (Fin.natAdd t i)),Move.stay)))) st

def lift (c : Config t s a) (lo hi : Fin t → ℤ) : Config (t+t) (s+s) a :=
  ⟨Fin.castAdd s c.state,Fin.addCases c.head c.head,
    Fin.addCases c.tape (fun i => tracker (lo i) (hi i))⟩

def middle (c : Config t s a) (lo hi : Fin t → ℤ) : Config (t+t) (s+s) a :=
  ⟨Fin.natAdd s c.state,Fin.addCases c.head c.head,
    Fin.addCases c.tape (fun i => tracker (lo i) (hi i))⟩

/-- Shape of a real visited interval, including the distinguished origin. -/
def Shape (c : Config t s a) (lo hi : Fin t → ℤ) : Prop :=
  ∀ i, lo i ≤ 0 ∧ 0 ≤ hi i ∧ lo i ≤ c.head i ∧ c.head i ≤ hi i

private theorem mark_interior (lo hi p : ℤ) (hl : lo ≤ p) (hh : p ≤ hi) :
    mark (tracker (q := a) lo hi p) = tracker lo hi p := by
  by_cases hp : p = 0
  · simp [mark,tracker,hp]
  · simp [mark,tracker,hp,hl,hh,bitSymbol,separator,Fin.ext_iff]

/-- A unit head move extends the marked interval by at most one cell. -/
theorem mark_extend (lo hi p : ℤ) (hl : lo ≤ 0) (hh : 0 ≤ hi)
    (hp : lo-1 ≤ p ∧ p ≤ hi+1) :
    Function.update (tracker (q := a) lo hi) p (mark (tracker lo hi p)) =
      tracker (min lo p) (max hi p) := by
  funext z
  by_cases hz : z = p
  · subst z
    by_cases hp0 : p = 0
    · simp [tracker,mark,hp0]
    · by_cases hr : lo ≤ p ∧ p ≤ hi <;>
        simp [Function.update_self,mark,tracker,hp0,hr,bitSymbol,separator,blank,Fin.ext_iff]
  · rw [Function.update_of_ne hz]
    by_cases hz0 : z = 0
    · simp [tracker,hz0]
    · have he : (lo ≤ z ∧ z ≤ hi) ↔ (min lo p ≤ z ∧ z ≤ max hi p) := by omega
      simp only [tracker,hz0,ite_false,he]

private theorem step_first (M : Program t s a) (c d : Config t s a) (lo hi : Fin t → ℤ)
    (hc : Shape c lo hi) (h : step M c = some d) :
    step (program M) (lift c lo hi) = some (middle d lo hi) := by
  unfold step at h
  cases he : M.transition c.state (fun i => c.tape i (c.head i)) with
  | none => simp only [he] at h; cases h
  | some act =>
    simp only [he,Option.some.injEq] at h
    subst d
    simp only [step,program,lift,Fin.addCases_left,Fin.addCases_right,he,Option.map_some,middle]
    congr 1
    congr 1
    · funext i
      induction i using Fin.addCases <;> simp only [Fin.addCases_left,Fin.addCases_right]
    · funext i z
      induction i using Fin.addCases with
      | left i => simp only [Fin.addCases_left]
      | right i =>
        simp only [Fin.addCases_right]
        rw [mark_interior _ _ _ (hc i).2.2.1 (hc i).2.2.2]
        by_cases hz : z = c.head i <;> simp [hz]

private theorem step_head (M : Program t s a) (c d : Config t s a) (h : step M c = some d) (i : Fin t) :
    c.head i-1 ≤ d.head i ∧ d.head i ≤ c.head i+1 := by
  unfold step at h
  cases he : M.transition c.state (fun i => c.tape i (c.head i)) with
  | none => simp only [he] at h; cases h
  | some act =>
    simp only [he,Option.some.injEq] at h
    subst d
    have hm := Move.unit (act.2 i).2
    dsimp
    omega

private theorem step_second (M : Program t s a) (d : Config t s a) (lo hi : Fin t → ℤ)
    (hzero : ∀ i, lo i ≤ 0 ∧ 0 ≤ hi i)
    (hd : ∀ i, lo i-1 ≤ d.head i ∧ d.head i ≤ hi i+1) :
    step (program M) (middle d lo hi) =
      some (lift d (fun i => min (lo i) (d.head i)) (fun i => max (hi i) (d.head i))) := by
  simp only [step,program,middle,lift,Fin.addCases_left,Fin.addCases_right]
  congr 1
  congr 1
  · funext i
    induction i using Fin.addCases <;> simp only [Fin.addCases_left,Fin.addCases_right,Move.offset,add_zero]
  · funext i z
    induction i using Fin.addCases with
    | left i =>
      simp only [Fin.addCases_left]
      by_cases hz : z = d.head i <;> simp [hz]
    | right i =>
      simp only [Fin.addCases_right]
      have he := congrFun (mark_extend (a := a) (lo i) (hi i) (d.head i)
        (hzero i).1 (hzero i).2 (hd i)) z
      simpa only [Function.update_apply] using he

/-- Two real transitions simulate one original transition and record its new
head cells. All original symbols, states and heads are exact. -/
theorem step_two (M : Program t s a) (c d : Config t s a) (lo hi : Fin t → ℤ)
    (hc : Shape c lo hi) (h : step M c = some d) :
    run (program M) 2 (lift c lo hi) =
      some (lift d (fun i => min (lo i) (d.head i)) (fun i => max (hi i) (d.head i))) := by
  rw [run,step_first M c d lo hi hc h]
  simp only [Option.bind_some,run_one]
  apply step_second M d lo hi (fun i => ⟨(hc i).1,(hc i).2.1⟩)
  intro i
  have hh := step_head M c d h i
  have hi := hc i
  omega


/-- Only designated scratch tapes need initially bounded nonblank support. -/
def Supported (work : Fin t → Prop) (c : Config t s a) (lo hi : Fin t → ℤ) : Prop :=
  ∀ i, work i → ∀ z, z < lo i ∨ hi i < z → c.tape i z = blank

private theorem shape_next (c d : Config t s a) (lo hi : Fin t → ℤ) (hc : Shape c lo hi) :
    Shape d (fun i => min (lo i) (d.head i)) (fun i => max (hi i) (d.head i)) := by
  intro i
  have hh := hc i
  dsimp
  exact ⟨by omega,by omega,by omega,by omega⟩

private theorem supported_next (M : Program t s a) (c d : Config t s a)
    (lo hi : Fin t → ℤ) (hc : Shape c lo hi) (work : Fin t → Prop)
    (hw : Supported work c lo hi) (h : step M c = some d) :
    Supported work d (fun i => min (lo i) (d.head i)) (fun i => max (hi i) (d.head i)) := by
  unfold step at h
  cases he : M.transition c.state (fun i => c.tape i (c.head i)) with
  | none => simp only [he] at h; cases h
  | some act =>
    simp only [he,Option.some.injEq] at h
    subst d
    intro i hi' z hz
    have hh := hc i
    have hne : z ≠ c.head i := by dsimp at hz; omega
    change (if z = c.head i then _ else _) = blank
    rw [ite_eq_right hne]
    apply hw i hi' z
    dsimp at hz
    omega

/-- The wrapper records genuine visited intervals, keeps exact original
execution, and bounds scratch support and tracker radius by elapsed time. -/
theorem run_tracked (M : Program t s a) (n B : ℕ) (c d : Config t s a)
    (lo hi : Fin t → ℤ) (hc : Shape c lo hi) (work : Fin t → Prop)
    (hw : Supported work c lo hi) (hb : ∀ i, -(B : ℤ) ≤ lo i ∧ hi i ≤ B)
    (h : run M n c = some d) :
    ∃ lo' hi' : Fin t → ℤ,
      run (program M) (2*n) (lift c lo hi) = some (lift d lo' hi') ∧
      Shape d lo' hi' ∧ Supported work d lo' hi' ∧
      ∀ i, -((B+n : ℕ) : ℤ) ≤ lo' i ∧ hi' i ≤ (B+n : ℕ) := by
  induction n generalizing B c lo hi with
  | zero =>
    have he : c = d := Option.some.inj h
    subst c
    exact ⟨lo,hi,rfl,hc,hw,by simpa using hb⟩
  | succ n ih =>
    change (step M c >>= run M n) = some d at h
    cases hs : step M c with
    | none => simp only [hs] at h; cases h
    | some e =>
      simp only [hs] at h
      let nextlo := fun i => min (lo i) (e.head i)
      let nexthi := fun i => max (hi i) (e.head i)
      have hn : ∀ i, -((B+1 : ℕ) : ℤ) ≤ nextlo i ∧ nexthi i ≤ (B+1 : ℕ) := by
        intro i
        have hs' := step_head M c e hs i
        have hc' := hc i
        have hb' := hb i
        dsimp [nextlo,nexthi]
        constructor <;> omega
      obtain ⟨lo',hi',hr,hshape,hsupport,hbound⟩ := ih (B+1) e nextlo nexthi
        (shape_next c e lo hi hc) (supported_next M c e lo hi hc work hw hs) hn h
      refine ⟨lo',hi',?_,hshape,hsupport,?_⟩
      · rw [show 2*(n+1) = 2+2*n by omega,run_add,step_two M c e lo hi hc hs]
        exact hr
      · intro i
        have hh := hbound i
        constructor <;> omega

/-- Genuine halting is preserved, not just finite-run projection. -/
theorem halt (M : Program t s a) (c : Config t s a) (lo hi : Fin t → ℤ)
    (h : step M c = none) : step (program M) (lift c lo hi) = none := by
  unfold step at h ⊢
  simp only [program,lift,Fin.addCases_left]
  cases he : M.transition c.state (fun i => c.tape i (c.head i)) with
  | none => simp
  | some act => simp [he] at h

end IntegerMultBounds.Machine.TrackedExecution
