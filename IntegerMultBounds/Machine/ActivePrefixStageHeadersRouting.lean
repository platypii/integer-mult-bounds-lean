import IntegerMultBounds.Machine.ActivePrefixStageHeadersRun
import IntegerMultBounds.Machine.SharedBankFamily

/-! Each consumer descriptor has its own physically copied tape, including
repeated numeric values. Copies retain original inputs; erase clears synthesis. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageHeadersRouting
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}
abbrev State := Fin 65 → Option ℕ

def caller (st : State) : Tapes 65 a :=
  ⟨fun i => if (st i).isSome then 1 else 0,
    fun i => match st i with | none => fun _ => blank | some n => RadixZeroFill.encodedBinary (bits n)⟩
def put (st : State) (i : Fin 65) (n : ℕ) := Function.update st i (some n)
inductive Command where
  | copy (src dst : Fin 65) (distinct : src≠dst)
  | erase (dst : Fin 65)
def eval (c : Command) (st : State) : State := match c with
  | .copy src dst _ => put st dst ((st src).getD 0)
  | .erase dst => Function.update st dst none
def valid (c : Command) (st : State) : Prop := match c with
  | .copy src dst _ => ∃ n, st src=some n ∧ st dst=none
  | .erase dst => ∃ n, st dst=some n
def cost (c : Command) (st : State) := 100*(match c with
  | .copy src _ _ => (st src).getD 0+1
  | .erase dst => (st dst).getD 0+1)
def two (i j : Fin 65) : Fin 2 → Fin 65 := ![i,j]
theorem two_injective (i j : Fin 65) (h : i≠j) : Function.Injective (two i j) := by
  intro x y he; fin_cases x <;> fin_cases y <;> simp_all [two]
def one (c : Command) : Σ k, Program 65 k a := match c with
  | .copy src dst h => ⟨_,BinaryDescriptorCopyPlaced.program (two src dst) (two_injective src dst h)⟩
  | .erase dst => ⟨_,BinaryDescriptorCleanupList.oneProgram (a := a) dst⟩
theorem put_caller (st : State) (i : Fin 65) (n : ℕ) :
    caller (a := a) (put st i n)=setTape (caller st) i (RadixZeroFill.encodedBinary (bits n)) 1 := by
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals by_cases hj : j=i <;> simp [caller,put,Function.update,hj]
theorem erase_caller (st : State) (i : Fin 65) :
    caller (a := a) (Function.update st i none)=setTape (caller st) i (fun _ => blank) 0 := by
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals by_cases hj : j=i <;> simp [caller,Function.update,hj]
theorem runs (c : Command) (st : State) (hv : valid c st) :
    HoareTime (one (a := a) c).2 (fun x => x=caller st)
      (fun x => x=caller (eval c st)) (cost c st) := by
  cases c with
  | copy src dst hd =>
    obtain ⟨n,hs,ht⟩ := hv
    have hi : SharedBank.payload (caller (a := a) st) (two src dst)=BinaryDescriptorCopy.encodedInput a (bits n) := by
      apply congrArg₂ Tapes.mk <;> funext j <;> fin_cases j <;> simp [caller,two,hs,ht] <;> rfl
    have h := BinaryDescriptorCopyPlaced.copies (caller (a := a) st)
      (two src dst) (two_injective src dst hd) (bits n) hi
    have hl := ActiveRepairRankHeadersCommands.bits_length n
    exact h.consequence (fun _ h => h) (fun _ h => by simpa [eval,hs,put_caller,two] using h)
      (by simp [cost,hs]; omega)
  | erase dst =>
    obtain ⟨n,hn⟩ := hv
    have h := BinaryDescriptorCleanupList.one_hoare dst (caller (a := a) st) (bits n)
      (by simp [caller,hn,BinaryDescriptorStackRoundtrip.descriptor_encoded]) (by simp [caller,hn])
    have hl := ActiveRepairRankHeadersCommands.bits_length n
    exact h.consequence (fun _ h => h)
      (fun _ h => by simpa only [eval,erase_caller] using h) (by simp [cost,hn]; omega)
def compile : List Command → Σ k, Program 65 k a
  | [] => ⟨1,skip 65 a (by decide)⟩
  | c::cs => ⟨_,seq (one c).2 (compile cs).2⟩
def execute : List Command → State → State
  | [],st => st
  | c::cs,st => execute cs (eval c st)
def validSchedule : List Command → State → Prop
  | [],_ => True
  | c::cs,st => valid c st ∧ validSchedule cs (eval c st)
def scheduleCost : List Command → State → ℕ
  | [],_ => 0
  | c::cs,st => cost c st+1+scheduleCost cs (eval c st)
theorem schedule_runs (cs : List Command) (st : State) (hv : validSchedule cs st) :
    HoareTime (compile (a := a) cs).2 (fun x => x=caller st)
      (fun x => x=caller (execute cs st)) (scheduleCost cs st) := by
  induction cs generalizing st with
  | nil => exact skip_hoare (by decide) (caller st)
  | cons c cs ih => exact (runs c st hv.1).seq (ih (eval c st) hv.2)
end
end IntegerMultBounds.Machine.ActivePrefixStageHeadersRouting
