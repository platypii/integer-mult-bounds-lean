import IntegerMultBounds.Machine.Hoare

/-! A literal rightward sentinel scan preserves every tape cell and charges
one transition per scanned symbol. -/
namespace IntegerMultBounds.Machine.ScanRight
variable {a : ℕ}

def program (stop : Fin (a+4)) : Program 1 1 a where
  tapes_pos := by decide
  start := 0
  transition := fun _ sy => if sy 0 = stop then none else some (0,fun i => (sy i,.right))

def cfg (f : ℤ → Fin (a+4)) (p : ℤ) : Config 1 1 a := ⟨0,fun _ => p,fun _ => f⟩

theorem scan_step (stop : Fin (a+4)) (f : ℤ → Fin (a+4)) (p : ℤ) (h : f p ≠ stop) :
    step (program stop) (cfg f p) = some (cfg f (p+1)) := by
  simp only [step,program,cfg,h,ite_false,Move.offset]
  congr 1
  congr 1
  funext i j
  by_cases hj : j = p
  · subst j; simp
  · simp [hj]

theorem scan_run (stop : Fin (a+4)) (f : ℤ → Fin (a+4)) (p : ℤ) (n : ℕ)
    (h : ∀ j : ℕ, j < n → f (p+j) ≠ stop) :
    run (program stop) n (cfg f p) = some (cfg f (p+n)) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [run_add,ih (fun j hj => h j (by omega))]
    simp only [Option.bind_some,run_one]
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using scan_step stop f (p+n) (h n (by omega))

theorem scan_hoare (stop : Fin (a+4)) (f : ℤ → Fin (a+4)) (p : ℤ) (n : ℕ)
    (h : ∀ j : ℕ, j < n → f (p+j) ≠ stop) (hend : f (p+n) = stop) :
    HoareTime (program stop) (fun v => v = ⟨fun _ => p,fun _ => f⟩)
      (fun v => v = ⟨fun _ => p+n,fun _ => f⟩) n := by
  rintro v rfl
  refine ⟨n,cfg f (p+n),le_rfl,scan_run stop f p n h,?_,rfl⟩
  simp [step,program,cfg,hend]

end IntegerMultBounds.Machine.ScanRight
