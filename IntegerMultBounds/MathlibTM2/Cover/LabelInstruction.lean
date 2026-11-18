module

public import IntegerMultBounds.MathlibTM2.Cover.LabelScalar
public import IntegerMultBounds.MathlibTM2.Cover.LabelSchedule

/-! A scalar operation on two selected label atoms spans the whole descriptor. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelInstruction
noncomputable section

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.M8.RevMachine
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewedAction (Action transform Data)
open RecursiveShiftRoleBank (source)
open LabelView (colView)
open LabelCall (bank)
open M8.Stage2Machine.Straight (words)

variable {T k : ℕ}

private theorem action_bound (act : Action 1) (v : Descriptor) (hp : 0 < volume prime v) :
    RecursiveViewedAction.cost v act ≤ RecursiveViewedAction.coefficient act * volume prime v := by
  cases act with
  | shift => simp only [RecursiveViewedAction.cost, RecursiveViewedAction.coefficient]; omega
  | scale wire r hr target =>
    apply (RecursiveInterchangeScalingClean.bound_linear r _ hp).trans_eq
    unfold RecursiveViewedAction.coefficient RecursiveInterchangeScalingClean.bound
    ring


def program (p : LabelSchedule.Pair k) (io : Fin T) (act : Action 1) :=
  LabelSchedule.atPair p (LabelSwap.withView (LabelScalar.block io act))

/-- One call handles every row, prefix and payload, with the three selection counters
and all arithmetic scratch blank again on return. -/
theorem runs {v : Descriptor} {c B : ℕ} (p : LabelSchedule.Pair k)
    (hc : 0 < c) (hb : 0 < B) (hv : v.beforeH = B*prime^(k*c)) (hp : v.Positive)
    (io : Fin T) (roles : Tapes T prime) (act : Action 1)
    (a : Data 1 (colView prime c k p.val.1 p.val.2 B v))
    (hh : roles.head io = 0) (hx : roles.tape io = source (a 0)) :
    let s := p.val.1.val
    let t := p.val.2.val
    let d := words (LabelSchedule.base v c)
    GraphContract.Runs (program p io act) (bank roles v d)
      (bank (SharedPlacementAlphabet.setTape roles io (source (transform act a 0)) 0) v d)
      ((3808274 + RecursiveViewedAction.coefficient act + LabelSchedule.setupCost k s t +
        LabelSchedule.clearCost k s t + 2) * volume prime v) := by
  let u := colView prime c k p.val.1 p.val.2 B v
  have hvol : volume prime u = volume prime v := LabelView.colView_volume _ _ _ _ _ _ _ hv p.property p.val.2.isLt
  have hpv := RecursiveAffinePrepare.volume_positive prime_prime.two_le v hp
  have ha := action_bound act u (hvol ▸ hpv)
  rw [hvol] at ha
  have h := LabelSchedule.atPair_runs p (Blocks.seq_leading _ _)
    (LabelSwap.withView_runs p.property p.val.2.isLt hc hb hv hp (fun _ => rfl)
      (LabelScalar.runs p.property p.val.2.isLt hv hp io roles act a hh hx))
  apply Blocks.runs_mono h
  have hset := Nat.le_mul_of_pos_right (LabelSchedule.setupCost k p.val.1 p.val.2) hpv
  have hend := Nat.le_mul_of_pos_right (LabelSchedule.clearCost k p.val.1 p.val.2) hpv
  change RecursiveViewedAction.cost (colView prime c k p.val.1 p.val.2 B v) act ≤ _ at ha
  simp only [Nat.add_mul]
  omega

end
end IntegerMultBounds.MathlibTM2.Cover.LabelInstruction
