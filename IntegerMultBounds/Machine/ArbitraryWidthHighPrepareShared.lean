import IntegerMultBounds.Machine.ArbitraryWidthHighPrepare
import IntegerMultBounds.Machine.SharedPlacementAlphabet

/-! Runtime metadata preparation reads the caller's sole width header through
an actual shared physical tape. Its private width slot stays wholly blank. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighPrepareShared
noncomputable section
variable {a l : ℕ}
open SharedPlacementAlphabet (setTape)

def privateInput : Tapes 19 a := ⟨fun _ => 0,fun _ _ => blank⟩
def privateOutput (q e : ℕ) : Tapes 19 a :=
  setTape (ArbitraryWidthHighPrepare.output q e []) 0 (fun _ => blank) 0

def program (focus : Fin l) (q : ℕ) := Placement.placed
  (ArbitraryWidthHighPrepare.program (a := a) q)
  (SharedPlacementAlphabet.sharedPlacement focus (0 : Fin 19))
def cleanup (focus : Fin l) := Placement.placed
  (ArbitraryWidthHighPrepare.cleanupProgram (a := a))
  (SharedPlacementAlphabet.sharedPlacement focus (0 : Fin 19))

theorem strip_input (es : List Bool) :
    setTape (ArbitraryWidthHighPrepare.input (a := a) es) 0 (fun _ => blank) 0 = privateInput := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem strip_output (q e : ℕ) (es : List Bool) :
    setTape (ArbitraryWidthHighPrepare.output (a := a) q e es) 0 (fun _ => blank) 0 =
      privateOutput q e := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem retained_caller (caller : Tapes l a) (focus : Fin l) (q e : ℕ)
    (es : List Bool) (ht : caller.tape focus = RadixZeroFill.encodedBinary es)
    (hh : caller.head focus = 1) :
    setTape caller focus ((ArbitraryWidthHighPrepare.output (a := a) q e es).tape 0)
      ((ArbitraryWidthHighPrepare.output (a := a) q e es).head 0) = caller := by
  change setTape caller focus (RadixZeroFill.encodedBinary es) 1 = caller
  rw [← ht,← hh]
  exact SharedPlacementAlphabet.setTape_self _ _

theorem constructs (focus : Fin l) (caller : Tapes l a) (q e : ℕ)
    (hq : 2 ≤ q) (he : 0 < e) (es : List Bool)
    (hv : Counter.value es = e) (hc : GrowingCounterData.Canonical es)
    (ht : caller.tape focus = RadixZeroFill.encodedBinary es) (hh : caller.head focus = 1) :
    HoareTime (program (a := a) focus q)
      (fun z => z = caller.append privateInput)
      (fun z => z = caller.append (privateOutput q e))
      (ArbitraryWidthHighPrepare.constant q*ArbitraryWidthHighPrepare.rounded q e) := by
  have h := SharedPlacementAlphabet.shared_hoare
    (ArbitraryWidthHighPrepare.construct_hoare (a := a) q e hq he es hv hc)
    caller focus (0 : Fin 19) (fun _ => blank) 0 ht hh
  rw [strip_input,strip_output,retained_caller caller focus q e es ht hh] at h
  exact h

theorem cleans (focus : Fin l) (caller : Tapes l a) (q e : ℕ)
    (hq : 2 ≤ q) (es : List Bool)
    (ht : caller.tape focus = RadixZeroFill.encodedBinary es) (hh : caller.head focus = 1) :
    HoareTime (cleanup (a := a) focus)
      (fun z => z = caller.append (privateOutput q e))
      (fun z => z = caller.append privateInput) (45*ArbitraryWidthHighPrepare.rounded q e) := by
  have h := SharedPlacementAlphabet.shared_hoare
    (ArbitraryWidthHighPrepare.cleanup_hoare (a := a) q e hq es)
    caller focus (0 : Fin 19) (fun _ => blank) 0 ht hh
  have hr : setTape caller focus ((ArbitraryWidthHighPrepare.input (a := a) es).tape 0)
      ((ArbitraryWidthHighPrepare.input (a := a) es).head 0) = caller := by
    change setTape caller focus (RadixZeroFill.encodedBinary es) 1 = caller
    rw [← ht,← hh]
    exact SharedPlacementAlphabet.setTape_self _ _
  rw [strip_output,strip_input,hr] at h
  exact h

theorem private_output_width (q e : ℕ) :
    (privateOutput (a := a) q e).head 0 = 0 ∧
    (privateOutput (a := a) q e).tape 0 = fun _ => blank := ⟨rfl,rfl⟩

theorem private_output_headers (q e : ℕ) (i : Fin 5) :
    (privateOutput (a := a) q e).head (ArbitraryWidthHighPrepare.slots i) = 1 ∧
    (privateOutput (a := a) q e).tape (ArbitraryWidthHighPrepare.slots i) =
      RadixZeroFill.encodedBinary (ArbitraryWidthHighPrepare.words q e i) := by
  fin_cases i <;> exact ⟨rfl,rfl⟩

theorem private_output_blank (q e : ℕ) (i : Fin 19)
    (hi : i.val = 0 ∨ i.val = 2 ∨ 7 ≤ i.val) :
    (privateOutput (a := a) q e).head i = 0 ∧
    (privateOutput (a := a) q e).tape i = fun _ => blank := by
  fin_cases i <;> first | exact ⟨rfl,rfl⟩ | norm_num at hi

end
end IntegerMultBounds.Machine.ArbitraryWidthHighPrepareShared
