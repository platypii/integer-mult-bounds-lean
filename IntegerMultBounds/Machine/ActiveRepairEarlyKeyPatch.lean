import IntegerMultBounds.Machine.ActiveRepairEarlyKeyPlacement

/-! Full original-rank reconstruction and runtime V/T/U patching on the
shared early-key bank. All fifty-two private tapes are erased. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyKeyPatch
noncomputable section
open ActiveRepairEarlyKeyPlacement
open ActiveRepairDestinationPatchRun
variable {k : ℕ}

def native := extend ActiveRepairDestinationPatchRun.program 31
def program (focus : Fin 12 → Fin k) (hf : Function.Injective focus) :=
  ActiveRepairEarlyKeyPlacement.program (s := 40) native focus hf

theorem pad (v : Tapes 12 1) :
    (CleanSubbank.bank (s := 9) v).append (SharedBank.empty 31 1)=
      CleanSubbank.bank (s := 40) v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (caller : Tapes k 1) (focus : Fin 12 → Fin k)
    (hf : Function.Injective focus) (cs v t u : List Bool) (hs : Fin 7 → List Bool)
    (hp : SharedBank.payload caller focus=bank cs v t u (fun _ => blank) hs)
    (total sv st su : ℕ)
    (hz : Counter.value (hs 0)=0) (hA : Counter.value (hs 1)=total)
    (hsv : Counter.value (hs 2)=sv) (hv : Counter.value (hs 3)=v.length)
    (hst : Counter.value (hs 4)=st) (ht : Counter.value (hs 5)=t.length)
    (hsu : Counter.value (hs 6)=su) (hu : u.length=t.length)
    (fv : sv+v.length≤total) (ft : st+t.length≤total) (fu : su+u.length≤total)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program focus hf)
      (fun z => z=CleanSubbank.bank (s := 52) caller)
      (fun z => z=CleanSubbank.bank (s := 52)
        (install caller focus (bank cs v t u
          (word (destination cs v t u total sv st su)) hs)))
      (800*(total+1)+3) := by
  have h := hoare_extend_eq
    (ActiveRepairDestinationPatchRun.runs_linear cs v t u hs total sv st su
      hz hA hsv hv hst ht hsu hu fv ft fu hc) (SharedBank.empty 31 1)
  simp only [pad] at h
  exact ActiveRepairEarlyKeyPlacement.runs (c := 12) (s := 40)
    native caller focus hf _ _ _ hp h

end
end IntegerMultBounds.Machine.ActiveRepairEarlyKeyPatch
