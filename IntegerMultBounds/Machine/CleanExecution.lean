import IntegerMultBounds.Machine.TrackedHoare
import IntegerMultBounds.Machine.TrackedCleanupList

/-! Execute a fixed machine with physical tracking, then erase every private
work tape and all tracking tapes. Selected common tapes and heads are retained. -/
namespace IntegerMultBounds.Machine.CleanExecution
variable {t s a : ℕ}
noncomputable section

def program (M : Program t s a) (right keep : Fin t → Bool) :=
  seq (TrackedHoare.program M right) (TrackedCleanupList.program (a := a) keep M.tapes_pos)

/-- No generated tracker, marker, descriptor, or private tape remains after
this actual run. Only the selected exact original output tapes are retained. -/
theorem realizes (M : Program t s a) (right keep : Fin t → Bool) (v w : Tapes t a)
    (bound : ℕ) (hh : v.head = TrackedInit.position right)
    (hw : ∀ i, keep i = false → v.tape i = fun _ => blank)
    (h : HoareTime M (fun x => x = v) (fun x => x = w) bound) :
    HoareTime (program M right keep) (fun x => x = v.append (SharedBank.empty t a))
      (fun x => x = (TrackedCleanupList.retained keep w).append (SharedBank.empty t a))
      ((2+5*t)*bound+11*t+4) := by
  have hh' := (TrackedHoare.initialized_hoare M right v w bound (fun i => keep i = false) hh hw h).seq
    (TrackedCleanupList.cleanup_exists_hoare keep M.tapes_pos w (bound+1))
  exact hh'.consequence (fun _ h => h) (fun _ h => h) (le_of_eq (by ring))

end
end IntegerMultBounds.Machine.CleanExecution
