import IntegerMultBounds.Machine.TrackedCleanup

/-! Erase a visited tracker alone, so shared data tapes and their heads can be
framed unchanged. The control flow is the tracker projection of paired cleanup. -/
namespace IntegerMultBounds.Machine.TrackedCleanupOne
variable {a : ℕ}

def project (c : Config 2 4 a) : Config 1 4 a :=
  ⟨c.state,fun _ => c.head 1,fun _ => c.tape 1⟩

def program (a : ℕ) : Program 1 4 a where
  tapes_pos := by decide
  start := 0
  transition := fun s sy => if s = 0 then
    if sy 0 = blank then some (1,fun _ => (sy 0,.right)) else some (0,fun _ => (sy 0,.left))
    else if s = 1 then
      if sy 0 = blank then some (2,fun _ => (sy 0,.left))
      else some (1,fun _ => (if sy 0 = separator then separator else blank,.right))
    else if s = 2 then
      if sy 0 = separator then some (3,fun _ => (blank,.stay))
      else some (2,fun _ => (sy 0,.left))
    else none

theorem step_project (c : Config 2 4 a) :
    step (program a) (project c) = (step (TrackedCleanup.program a) c).map project := by
  cases c with
  | mk st head tape =>
    fin_cases st <;> simp [step,program,TrackedCleanup.program,project]
    all_goals split_ifs <;> simp_all [project] <;> rfl

theorem run_project (n : ℕ) (c : Config 2 4 a) :
    run (program a) n (project c) = (run (TrackedCleanup.program a) n c).map project := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [run,step_project,run]
    cases hs : step (TrackedCleanup.program a) c with
    | none => rfl
    | some d => simpa only [Option.map_some,Option.bind_some] using ih d

def one (f : ℤ → Fin (a+4)) (p : ℤ) : Tapes 1 a := ⟨fun _ => p,fun _ => f⟩

theorem cleanup_hoare (lo hi p : ℤ) (B : ℕ) (hl : lo ≤ 0) (hh : 0 ≤ hi)
    (hp : lo ≤ p ∧ p ≤ hi) (hlo : -(B : ℤ) ≤ lo) (hhi : hi ≤ B) :
    HoareTime (program a) (fun v => v = one (TrackedCleanup.tracker lo hi) p)
      (fun v => v = one (fun _ => blank) 0) (5*B+5) := by
  have hc := TrackedCleanup.cleanup_hoare_linear (q := a) (fun _ => blank) lo hi p B hl hh hp hlo hhi
    (by intros; rfl)
  obtain ⟨n,c,hn,hr,hhalt,hpost⟩ := hc _ rfl
  have hrun := run_project n ((TrackedCleanup.bank (fun _ => blank) (TrackedCleanup.tracker lo hi) p).start
    (TrackedCleanup.program a))
  rw [hr] at hrun
  intro v hv
  subst v
  refine ⟨n,project c,hn,hrun,?_,?_⟩
  · rw [step_project,hhalt]
    rfl
  · have hh' := congrFun (congrArg Tapes.head hpost) 1
    have ht' := congrFun (congrArg Tapes.tape hpost) 1
    change c.head 1 = 0 at hh'
    change c.tape 1 = (fun _ => blank) at ht'
    simp only [project,Config.tapes,one,hh',ht']

end IntegerMultBounds.Machine.TrackedCleanupOne
