import IntegerMultBounds.Machine.NativeColumnPhaseFlags
import IntegerMultBounds.Machine.InjectivePlacement
import IntegerMultBounds.Machine.SharedPlacementAlphabet

/-! Place the runtime column-phase reader on an original caller header and
two private flags, retaining every other complete tape and head. -/
namespace IntegerMultBounds.Machine.NativeColumnPhaseFlagsPlaced
noncomputable section
variable {u t : ℕ}
open MarkedWordCleanup (one)
open SharedPlacementAlphabet (setTape)

def placement (slot : Fin 3 → Fin t) (hi : Function.Injective slot) (ht : 3+u=t) :=
  InjectivePlacement.placement slot hi ht

def program (slot : Fin 3 → Fin t) (hi : Function.Injective slot) (ht : 3+u=t) :=
  Placement.placed NativeColumnPhaseFlags.program (placement slot hi ht)

def output (slot : Fin 3 → Fin t) (v : Tapes t 2) (p : Fin 4) :=
  setTape (setTape v (slot 1) ((UnitPhaseNumerator.flags p).tape 0) 0)
    (slot 2) ((UnitPhaseNumerator.flags p).tape 1) 0

theorem replace_output (slot : Fin 3 → Fin t) (hi : Function.Injective slot)
    (ht : 3+u=t) (v : Tapes t 2) (p : Fin 4) :
    Placement.replace (placement slot hi ht) v
      ((one (v.tape (slot 0)) (v.head (slot 0))).append (UnitPhaseNumerator.flags p))=
      output slot v p := by
  apply congrArg₂ Tapes.mk
  all_goals funext i
  all_goals obtain ⟨j,rfl⟩ := (placement slot hi ht).surjective i
  all_goals induction j using Fin.addCases with
    | left j =>
      simp only [Equiv.symm_apply_apply]
      simp only [placement,InjectivePlacement.active_slot]
      fin_cases j <;> simp [setTape,hi.eq_iff,
        Tapes.append,one,UnitPhaseNumerator.flags,MarkedWordCleanup.one,Fin.addCases]
    | right j =>
      have h1 : (placement slot hi ht) (Fin.natAdd 3 j)≠slot 1 := by
        rw [←InjectivePlacement.active_slot slot hi ht 1]
        intro h
        have hv := congrArg Fin.val ((placement slot hi ht).injective h)
        simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
        omega
      have h2 : (placement slot hi ht) (Fin.natAdd 3 j)≠slot 2 := by
        rw [←InjectivePlacement.active_slot slot hi ht 2]
        intro h
        have hv := congrArg Fin.val ((placement slot hi ht).injective h)
        simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
        omega
      simp [Placement.extra,setTape,h1,h2,Tapes.append]

theorem runs (slot : Fin 3 → Fin t) (hi : Function.Injective slot)
    (ht : 3+u=t) (v : Tapes t 2) (columns : ℕ)
    (hc : v.head (slot 0)=1 ∧ v.tape (slot 0)=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits columns))
    (hf : ∀ i : Fin 2,v.head (slot i.succ)=0 ∧ v.tape (slot i.succ)=(fun _ => blank)) :
    HoareTime (program slot hi ht) (fun w => w=v)
      (fun w => w=output slot v ⟨(27*columns)%4,Nat.mod_lt _ (by decide)⟩) 2 := by
  have ha : Placement.active (placement slot hi ht) v=
      NativeColumnPhaseFlags.input (RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits columns)) := by
    rw [show placement slot hi ht=InjectivePlacement.placement slot hi ht from rfl,InjectivePlacement.active_bank]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals first | exact hc.1 | exact hc.2 | exact (hf 0).1 | exact (hf 0).2 |
      exact (hf 1).1 | exact (hf 1).2
  have h := Placement.hoare_at (NativeColumnPhaseFlags.runs_columns columns)
    (placement slot hi ht) v ha
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  rw [←hc.2,←hc.1,replace_output]

theorem frame (slot : Fin 3 → Fin t) (v : Tapes t 2) (p : Fin 4)
    (i : Fin t) (h1 : i≠slot 1) (h2 : i≠slot 2) :
    (output slot v p).head i=v.head i ∧ (output slot v p).tape i=v.tape i := by
  simp [output,setTape,h1,h2]

end
end IntegerMultBounds.Machine.NativeColumnPhaseFlagsPlaced
