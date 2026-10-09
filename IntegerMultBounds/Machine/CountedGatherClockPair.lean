import IntegerMultBounds.Machine.CountedLoopReuseAlphabet
import IntegerMultBounds.Machine.FixedHeaderBankCopy

/-! Physical initialization and erasure of two independent gather clocks.
The outer digit loop and inner field loop each need their own marked zero. -/
namespace IntegerMultBounds.Machine.CountedGatherClockPair
variable {a t : ℕ}

def empty : Tapes 2 a := FixedHeaderBankCopy.empty 2
def marked : Tapes 2 a := CountedLoopReuseAlphabet.controls
  CountedLoopReuseAlphabet.empty CountedLoopReuseAlphabet.empty 1 1

def init (a : ℕ) : Program 2 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun s _ => if s = 0 then some (1,fun _ => (separator,.right)) else none

def clear (a : ℕ) : Program 2 3 a where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols =>
    if s = 0 then some (1,fun i => (symbols i,.left))
    else if s = 1 then some (2,fun _ => (blank,.stay)) else none

private def cfg {q : ℕ} (f : ℤ → Fin (a+4)) (p : ℤ) (s : Fin q) : Config 2 q a :=
  ⟨s,fun _ => p,fun _ => f⟩

theorem init_hoare : HoareTime (init a) (fun z => z = (empty : Tapes 2 a))
    (fun z => z = marked) 1 := by
  rintro z rfl
  refine ⟨1,cfg CountedLoopReuseAlphabet.empty 1 (1 : Fin 2),le_rfl,?_,?_,?_⟩
  · rw [run_one]
    simp only [step,init,empty,FixedHeaderBankCopy.empty,Tapes.start,cfg,
      ↓reduceIte,Move.offset]
    congr 2
  · simp [step,init,cfg]
  · unfold Config.tapes cfg marked CountedLoopReuseAlphabet.controls
    congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem clear_hoare : HoareTime (clear a) (fun z => z = (marked : Tapes 2 a))
    (fun z => z = empty) 2 := by
  rintro z rfl
  let mid := cfg (a := a) CountedLoopReuseAlphabet.empty 0 (1 : Fin 3)
  let last := cfg (a := a) (fun _ => blank) 0 (2 : Fin 3)
  have h1 : step (clear a) (marked.start (clear a)) = some mid := by
    simp only [step,clear,marked,CountedLoopReuseAlphabet.controls,Tapes.start,
      ↓reduceIte,Move.offset,mid,cfg]
    congr 2
    · funext i; fin_cases i <;> rfl
    · funext i j
      fin_cases i <;> by_cases hj : j = 1 <;> simp [CountedLoopReuseAlphabet.empty,hj]
  have h2 : step (clear a) mid = some last := by
    simp only [step,clear,mid,last,cfg,show (1 : Fin 3) ≠ 0 by decide,↓reduceIte,Move.offset,add_zero]
    congr 2
    funext i j
    by_cases hj : j = 0 <;> simp [CountedLoopReuseAlphabet.empty,hj]
  refine ⟨2,last,le_rfl,?_,?_,rfl⟩
  · change run (clear a) (1+1) (marked.start (clear a)) = some last
    rw [run_add,run_one,h1]
    simpa only [Option.bind_some,run_one] using h2
  · simp [step,clear,last,cfg]

def placement (t : ℕ) : Fin (2+t) ≃ Fin (t+2) := finAddFlip
def program (a t : ℕ) : Program (t+2) 2 a := Placement.placed (init a) (placement t)
def cleanup (a t : ℕ) : Program (t+2) 3 a := Placement.placed (clear a) (placement t)

private theorem lift {q c : ℕ} {M : Program 2 q a} {v w : Tapes 2 a}
    (h : HoareTime M (fun z => z = v) (fun z => z = w) c) (caller : Tapes t a) :
    HoareTime (Placement.placed M (placement t))
      (fun z => z = caller.append v) (fun z => z = caller.append w) c := by
  have ha : Placement.active (placement t) (caller.append v) = v := by
    cases v
    simp [Placement.active,placement,Tapes.append,finAddFlip_apply_castAdd]
  have he : Placement.extra (placement t) (caller.append v) = caller := by
    cases caller
    simp [Placement.extra,placement,Tapes.append,finAddFlip_apply_natAdd]
  apply (Placement.hoare_at h (placement t) (caller.append v) ha).consequence
    (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  rw [Placement.replace,he]
  have hw : Placement.active (placement t) (caller.append small) = small := by
    cases small
    simp [Placement.active,placement,Tapes.append,finAddFlip_apply_castAdd]
  have hew : Placement.extra (placement t) (caller.append small) = caller := by
    cases caller
    simp [Placement.extra,placement,Tapes.append,finAddFlip_apply_natAdd]
  simpa only [hw,hew] using Placement.view (placement t) (caller.append small)

theorem constructs (caller : Tapes t a) :
    HoareTime (program a t) (fun z => z = caller.append empty)
      (fun z => z = caller.append marked) 1 := lift init_hoare caller

theorem cleans (caller : Tapes t a) :
    HoareTime (cleanup a t) (fun z => z = caller.append marked)
      (fun z => z = caller.append empty) 2 := lift clear_hoare caller

end IntegerMultBounds.Machine.CountedGatherClockPair
