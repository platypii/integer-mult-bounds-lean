module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleLoop
public import IntegerMultBounds.Machine.LevelLoopSpace

/-! Workspace of actual refined atom loops. Parked heads are independent of
role data and counter words, so all levels reuse one stage allowance. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleLoop

open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewRoleBank (Selection layout)
open RecursiveViewFrameRoleBank (count bank)
open RecursiveRoleSerialization (roles)
open SharedBankStageInput (raw)
open FlatCoordinateSchedule (bits)
open AtomStep (words machine)
variable {t u : ℕ}
noncomputable section

/-- Data changes and counter-word changes leave all parked head positions fixed. -/
theorem levelBank_head_eq (T : ℕ) {v : Descriptor} (hs : Fin 6 → List Bool)
    (aux : Tapes u prime) (data data' : RecursiveViewedAction.Data t v)
    (ws ws' : Fin 5 → List Bool) :
    (levelBank T hs aux data ws).head = (levelBank T hs aux data' ws').head := by
  rfl

/-- Every prefix of the actual atom level loop uses one refined-stage allowance. -/
theorem loop_heads {N b : ℕ} (hb0 : 0 < b) (K : Selection N) (s : ℕ → Selection N)
    (act : RecursiveViewedAction.Action t)
    (hk : ∀ l, machine (u := u) (s l) act = machine (u := u) K act)
    (v : Descriptor) (hw : v.width = N*b) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (aux : Tapes u prime) (f : ℕ) (hf : 0 < f)
    {sU : ℕ} (U : Program (machine (u := u) K act).tapes sU prime) (cu : ℕ)
    (hU : ∀ l, l + 1 < f → ∀ data : RecursiveViewedAction.Data t v,
      HoareTime U (fun x => x = levelBank _ hs aux data (words b (s l)))
        (fun x => x = levelBank _ hs aux data (words b (s (l+1)))) cu)
    (data : RecursiveViewedAction.Data t v)
    (lo hi : ℤ)
    (hbank : ∀ i, lo ≤ (levelBank (machine (u := u) K act).tapes hs aux data (words b (s 0))).head i ∧
      (levelBank (machine (u := u) K act).tapes hs aux data (words b (s 0))).head i ≤ hi)
    {c} {n : ℕ}
    (hrun : Machine.run (LevelLoop.program (seq (machine (u := u) K act).program U)
      (machine (u := u) K act).program) n
      ((LevelLoop.bank (levelBank _ hs aux data (words b (s 0))) f).start (LevelLoop.program (seq (machine (u := u) K act).program U)
        (machine (u := u) K act).program)) = some c) :

    ∀ i, min lo 0-(AtomStepCost.constant act * volume prime v + 1 + cu +
        3*(bits (f-1)).length+8 : ℕ) ≤ c.head i ∧
      c.head i ≤ max hi (((bits (f-1)).length : ℤ)+1)+
        (AtomStepCost.constant act * volume prime v + 1 + cu + 3*(bits (f-1)).length+8 : ℕ) := by
  have step (l : ℕ) : HoareTime (machine (u := u) K act).program
      (fun x => x = levelBank _ hs aux (datas s act v hw data l) (words b (s l)))
      (fun x => x = levelBank _ hs aux (datas s act v hw data (l+1)) (words b (s l)))
      (AtomStepCost.constant act * volume prime v) := by
    have h := AtomStepCost.realizes_le (u := u) hb0 (s l) act v hw hp hs hv aux (datas s act v hw data l)
    rw [hk l] at h
    exact h
  have hlast := step (f-1)
  rw [show f-1+1 = f by omega] at hlast
  exact LevelLoop.level_heads _ _ f hf
    (fun l => levelBank _ hs aux (datas s act v hw data l) (words b (s l)))
    _ _ (fun l hl => (step l).seq (hU l hl _))
    (hlast.consequence (fun _ h => h) (fun _ h => h) (by omega)) lo hi (fun l _ => by
      rw [levelBank_head_eq _ hs aux (datas s act v hw data l) data (words b (s l)) (words b (s 0))]
      exact hbank) hrun

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleLoop
