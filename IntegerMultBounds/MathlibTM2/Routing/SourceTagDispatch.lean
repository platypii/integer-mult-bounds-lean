module

public import IntegerMultBounds.MathlibTM2.Routing.OptionalAffineSourceCall

/-! Read a two-bit source-region tag and dispatch to one of four fixed programs.
Both tag bits are archived in reverse order for subsequent source restoration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def sourceTagIndex (lo hi : Bool) : Fin 4 :=
  ⟨lo.toNat + 2 * hi.toNat, by cases lo <;> cases hi <;> decide⟩

def sourceTagDispatchProgram (src saved : Fin T) (branch : Fin 4 → Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (sourceActivityArchive src saved))
    (.cond (·.flag)
      (.seq (.act (sourceActivityArchive src saved)) (.cond (·.flag) (branch 3) (branch 1)))
      (.seq (.act (sourceActivityArchive src saved)) (.cond (·.flag) (branch 2) (branch 0))))

def sourceTagDispatchBank (R : Fin T → List (Fin (A + 4))) (src saved : Fin T)
    (lo hi : Bool) (rest : List (Fin (A + 4))) :=
  Function.update (Function.update R src rest) saved (bitSymbol hi :: bitSymbol lo :: R saved)

def sourceTagDispatchState (v : HS T Q A U) (hi : Bool) : HS T Q A U :=
  { v with sym := some (bitSymbol hi), flag := hi }

theorem sourceTagDispatch_exec (body : P → Pr P T Q A U)
    (src saved : Fin T) (hss : src ≠ saved) (branch : Fin 4 → Pr P T Q A U)
    (lo hi : Bool) (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = bitSymbol lo :: bitSymbol hi :: rest)
    (m : ℕ) (v' : HS T Q A U) (S' : Stacks T A)
    (hx : Exec body (branch (sourceTagIndex lo hi))
      (mk (sourceTagDispatchState v hi) { S with R := sourceTagDispatchBank S.R src saved lo hi rest }) m (mk v' S')) :
    Exec body (sourceTagDispatchProgram src saved branch) (mk v S) (m + 4) (mk v' S') := by
  let u₁ := sourceTagDispatchState v lo
  let B₁ : Stacks T A := { S with R := Function.update (Function.update S.R src (bitSymbol hi :: rest)) saved (bitSymbol lo :: S.R saved) }
  let u₂ := sourceTagDispatchState v hi
  let B₂ : Stacks T A := { S with R := sourceTagDispatchBank S.R src saved lo hi rest }
  have hp₁ : (sourceActivityArchive src saved : Act T Q A U).run (mk v S) = mk u₁ B₁ := by
    simp [sourceActivityArchive, Action.run, update_rt, hsrc, u₁, B₁, sourceTagDispatchState, hss.symm]
  have hp₂ : (sourceActivityArchive src saved : Act T Q A U).run (mk u₁ B₁) = mk u₂ B₂ := by
    simp [sourceActivityArchive, Action.run, update_rt, u₁, u₂, B₁, B₂, sourceTagDispatchState,
      sourceTagDispatchBank, hss, hss.symm]
    congr 2
    funext j
    by_cases hj : j = src <;> by_cases hk : j = saved <;>
      simp_all
  have ha₁ := hp₁ ▸ Exec.act (body := body) (sourceActivityArchive src saved) (mk v S)
  have ha₂ := hp₂ ▸ Exec.act (body := body) (sourceActivityArchive src saved) (mk u₁ B₁)
  cases lo <;> cases hi
  · exact Exec.cast (Exec.seq ha₁ (Exec.cond_false rfl (Exec.seq ha₂ (Exec.cond_false rfl hx)))) (by omega) rfl
  · exact Exec.cast (Exec.seq ha₁ (Exec.cond_false rfl (Exec.seq ha₂ (Exec.cond_true rfl hx)))) (by omega) rfl
  · exact Exec.cast (Exec.seq ha₁ (Exec.cond_true rfl (Exec.seq ha₂ (Exec.cond_false rfl hx)))) (by omega) rfl
  · exact Exec.cast (Exec.seq ha₁ (Exec.cond_true rfl (Exec.seq ha₂ (Exec.cond_true rfl hx)))) (by omega) rfl

end IntegerMultBounds.MathlibTM2.Routing
