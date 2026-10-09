import IntegerMultBounds.Machine.CountedLateRepairGuard

/-! The actual later repair prefix first classifies the original address,
then physically executes the unrestricted inverse while retaining its flag. -/
namespace IntegerMultBounds.Machine.CountedLateRepairPrefix
noncomputable section
variable {a : ℕ}
open CountedLateRepairGuard (flag)

def flagBank (x : Bool) : Tapes 2 a :=
  ⟨![1,0],![CountedLateRepairFlag.key x,fun _ => blank]⟩

theorem bank_eq (V W U X : List Bool) (hs : Fin 3 → List Bool)
    (F G : ℤ → Fin (a+4)) (pf pg : ℤ) :
    CountedLateRepairGuard.bank V W U X hs F G pf pg =
      (CountedPackedLateRun.bank V W U X [] (fun _ => blank) (fun _ => blank)
        (fun _ => blank) (fun _ => blank) 0 0 0 0 hs).append ⟨![pf,pg],![F,G]⟩ := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> first | rfl |
    (change CountedLoopReuseAlphabet.binary _=RadixZeroFill.encodedBinary _;
      exact CountedGuardGadgetHeaders.binary_eq _)

theorem flagged_eq (q b : ℕ) (V W U X : List Bool) (hs : Fin 3 → List Bool) :
    CountedLateRepairGuard.after (a := a) q b V W U X hs =
      (CountedPackedLateRun.bank V W U X [] (fun _ => blank) (fun _ => blank)
        (fun _ => blank) (fun _ => blank) 0 0 0 0 hs).append
        (flagBank (flag q b V W X || flag q b V U X)) := by
  have hb := bank_eq (a := a) V W U X hs
    (CountedLateRepairFlag.key (flag q b V W X || flag q b V U X)) (fun _ => blank) 1 0
  unfold flagBank
  rw [← hb]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def program := seq (CountedLateRepairGuard.program (a := a))
  (extend (CountedLateRepairInverse.program a) 2)

def output (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (V W U X : List Bool) (hs : Fin 3 → List Bool) : Tapes 30 a :=
  (CountedPackedLateRun.bank (CountedLateRepairInverse.target q b hb hbq V W U X)
    (CountedLateRepairInverse.temp q b hb hbq V W U X) (CountedLateRepairInverse.restored b hb U X)
    X [] (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0 0 hs).append
      (flagBank (flag q b V W X || flag q b V U X))

theorem runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (hbq3 : b+3≤q)
    (V W U X : List Bool) (hs : Fin 3 → List Bool)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b)
    (hv : ∀ i, Counter.value (hs i)=CountedPackedShapeHeaders.originalValues q b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a)) (fun v => v=CountedLateRepairGuard.before V W U X hs)
      (fun v => v=output q b hb hbq V W U X hs) (9005*((X.length+1)*(q+b+1))) := by
  have hg := CountedLateRepairGuard.runs (a := a) q b hb hbq3 V W U X hs hV hW hU hv hc
  have hi := CountedLateRepairInverse.runs (a := a) q b hb hbq V W U X
    (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0 0 hs
    hv hc hV hW hU rfl rfl rfl rfl rfl rfl rfl rfl
  have hp := hoare_extend_eq hi (flagBank (flag q b V W X || flag q b V U X))
  rw [← flagged_eq q b V W U X hs] at hp
  refine (hg.seq hp).consequence (fun _ h => h) (fun _ h => h) ?_
  have hpos : 1≤(X.length+1)*(q+b+1) :=
    Nat.mul_pos (by omega : 0<X.length+1) (by omega : 0<q+b+1)
  omega

end
end IntegerMultBounds.Machine.CountedLateRepairPrefix
