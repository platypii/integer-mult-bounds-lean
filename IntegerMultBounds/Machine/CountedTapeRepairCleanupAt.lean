import IntegerMultBounds.Machine.CountedTapeRepairCleanupWord

/-! Fixed-slot literal final cleanup, retaining the complete complementary bank. -/
namespace IntegerMultBounds.Machine.CountedTapeRepairCleanupAt
noncomputable section
open SharedPlacementAlphabet
open CountedTapeRepairCleanupWord

def atProgram {q : ℕ} (M : Program 1 q 1) (i : Fin 42) := Placement.placed M (FiniteReturnStackAt.placement i)

theorem at_runs {q B : ℕ} (M : Program 1 q 1) (v : Tapes 42 1) (i : Fin 42)
    (f g : ℤ → Fin 5) (p r : ℤ) (ht : v.tape i=f) (hp : v.head i=p)
    (h0 : HoareTime M (fun w => w=one f p) (fun w => w=one g r) B) :
    HoareTime (atProgram M i) (fun w => w=v) (fun w => w=setTape v i g r) B := by
  have h := Placement.hoare_at h0 (FiniteReturnStackAt.placement i) v (by
    rw [FiniteReturnStackAt.active_bank,ht,hp]; rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank _ _) = _
  rw [FiniteReturnStackAt.replace_bank]

def markedEndAt := atProgram markedEndProgram
def markedScanAt := atProgram markedScanProgram
def plainEndAt := atProgram plainEndProgram
def plainBackAt := atProgram plainBackProgram
def counterAt := atProgram counterProgram

theorem clears_marked_end (v : Tapes 42 1) (i : Fin 42) (xs : List (Fin 5))
    (ht : v.tape i=marked xs) (hp : v.head i=xs.length) (hx : ∀ x ∈ xs,x≠blank) :
    HoareTime (markedEndAt i) (fun w => w=v) (fun w => w=setTape v i (fun _ => blank) 0) (xs.length+5) :=
  at_runs _ v i _ _ _ _ ht hp (marked_end xs hx)

theorem clears_marked_scan (v : Tapes 42 1) (i : Fin 42) (xs : List (Fin 5))
    (ht : v.tape i=marked xs) (hp : v.head i=0) (hx : ∀ x ∈ xs,x≠blank) :
    HoareTime (markedScanAt i) (fun w => w=v) (fun w => w=setTape v i (fun _ => blank) 0) (2*xs.length+6) :=
  at_runs _ v i _ _ _ _ ht hp (marked_scan xs hx)

theorem clears_plain_end (v : Tapes 42 1) (i : Fin 42) (xs : List (Fin 5))
    (ht : v.tape i=putWord (fun _ => blank) 0 xs) (hp : v.head i=xs.length) (hx : ∀ x ∈ xs,x≠blank) :
    HoareTime (plainEndAt i) (fun w => w=v) (fun w => w=setTape v i (fun _ => blank) 0) (xs.length+2) :=
  at_runs _ v i _ _ _ _ ht hp (plain_end xs hx)

theorem returns_plain (v : Tapes 42 1) (i : Fin 42) (xs : List (Fin 5))
    (ht : v.tape i=putWord (fun _ => blank) 0 xs) (hp : v.head i=xs.length) (hx : ∀ x ∈ xs,x≠blank) :
    HoareTime (plainBackAt i) (fun w => w=v) (fun w => w=setTape v i (putWord (fun _ => blank) 0 xs) 0) (xs.length+2) :=
  at_runs _ v i _ _ _ _ ht hp (plain_back xs hx)

theorem clears_counter (v : Tapes 42 1) (i : Fin 42) (cs : List Bool)
    (ht : v.tape i=RepairScan.ctrTape cs) (hp : v.head i=1) :
    HoareTime (counterAt i) (fun w => w=v) (fun w => w=setTape v i (fun _ => blank) 0) (2*cs.length+4) :=
  at_runs _ v i _ _ _ _ ht hp (counter_runs cs)

end
end IntegerMultBounds.Machine.CountedTapeRepairCleanupAt
