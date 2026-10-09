import IntegerMultBounds.Machine.ActivePrefixStageWidthPlaced
import IntegerMultBounds.Machine.ActivePrefixStageDispatchCommon

/-! An actual width selector precedes a genuine finite-state branch. The
computed flag is erased before entering either original-input stage; branch
selection costs one transition and introduces no supplied Boolean premise. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageWidthBranch
noncomputable section
open ActivePrefixStageWidthPlaced
variable {t a q r B : ℕ}

def program (focus : Fin 2 → Fin t) (hf : Function.Injective focus)
    (packed : Program (t+3) q a) (singleton : Program (t+3) r a) :=
  seq (ActivePrefixStageWidthPlaced.program focus hf)
    (branch (test focus) (seq (cleanup focus hf) packed) (seq (cleanup focus hf) singleton))

theorem packed_runs (focus : Fin 2 → Fin t) (hf : Function.Injective focus)
    (packed : Program (t+3) q a) (singleton : Program (t+3) r a)
    (v : Tapes t a) (w : Tapes (t+3) a) (fs : List Bool) (f : ℕ)
    (hsrc : SharedBank.payload v focus=sources fs) (hv : Counter.value fs=f) (hwide : 2≤f)
    (hr : HoareTime packed (fun x => x=CleanSubbank.bank (s := 3) v) (fun x => x=w) B) :
    HoareTime (program focus hf packed singleton)
      (fun x => x=CleanSubbank.bank (s := 3) v) (fun x => x=w)
      (ActivePrefixStageWidthSelector.cost fs+B+4) := by
  have h0 := ActivePrefixStageWidthPlaced.runs v focus hf fs hsrc
  have h1 := (cleans v focus hf fs hsrc).seq hr
  have ht : test focus (CleanSubbank.bank (s := 3) (marked v focus fs)).reads=true := by
    rw [test_eq,hv]
    simp only [show 1<f by omega,decide_true]
  have h2 := ActivePrefixStageDispatchCommon.branch_true (test focus)
    (seq (cleanup focus hf) packed) (seq (cleanup focus hf) singleton) _ w ht h1
  exact (h0.seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem singleton_runs (focus : Fin 2 → Fin t) (hf : Function.Injective focus)
    (packed : Program (t+3) q a) (singleton : Program (t+3) r a)
    (v : Tapes t a) (w : Tapes (t+3) a) (fs : List Bool)
    (hsrc : SharedBank.payload v focus=sources fs) (hv : Counter.value fs=1)
    (hr : HoareTime singleton (fun x => x=CleanSubbank.bank (s := 3) v) (fun x => x=w) B) :
    HoareTime (program focus hf packed singleton)
      (fun x => x=CleanSubbank.bank (s := 3) v) (fun x => x=w)
      (ActivePrefixStageWidthSelector.cost fs+B+4) := by
  have h0 := ActivePrefixStageWidthPlaced.runs v focus hf fs hsrc
  have h1 := (cleans v focus hf fs hsrc).seq hr
  have ht : test focus (CleanSubbank.bank (s := 3) (marked v focus fs)).reads=false := by
    rw [test_eq,hv]
    rfl
  have h2 := ActivePrefixStageDispatchCommon.branch_false (test focus)
    (seq (cleanup focus hf) packed) (seq (cleanup focus hf) singleton) _ w ht h1
  exact (h0.seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- Positivity of the original stage width excludes every other false case. -/
theorem alternatives (f : ℕ) (hf : 0<f) : 2≤f ∨ f=1 := by omega

end
end IntegerMultBounds.Machine.ActivePrefixStageWidthBranch
