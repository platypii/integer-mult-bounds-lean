module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Write a fixed region tag followed by a live activity bit. The activity
input and both copy scratch tapes are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def sourceSuffixWriteProgram (lo hi : Bool) (activity dst tmp work : Fin T) : Pr P T Q A U :=
  .seq (bcopy activity dst tmp work)
    (.act (.push (.rt dst) (fun _ => bitSymbol hi) (.push (.rt dst) (fun _ => bitSymbol lo) .done)))

theorem sourceSuffixWrite_exec (body : P → Pr P T Q A U)
    (lo hi enabled : Bool) (activity dst tmp work : Fin T)
    (hreg : [activity, dst, tmp, work].Nodup)
    (v : HS T Q A U) (S : Stacks T A)
    (hactivity : S.R activity = [bitSymbol enabled]) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ (v' : HS T Q A U), v'.user = v.user ∧
      Exec body (sourceSuffixWriteProgram lo hi activity dst tmp work) (mk v S) 13
        (mk v' { S with R := Function.update S.R dst (bitSymbol lo :: bitSymbol hi :: bitSymbol enabled :: S.R dst) }) := by
  obtain ⟨v', hu, hx⟩ := bcopy_exec body hreg v S htmp hwork
  rw [hactivity] at hx
  let G : Stacks T A := { S with R := Function.update S.R dst (bitSymbol enabled :: S.R dst) }
  have hp : (Action.push (.rt dst) (fun _ => bitSymbol hi)
      (.push (.rt dst) (fun _ => bitSymbol lo) .done) : Act T Q A U).run (mk v' G) =
      mk v' { S with R := Function.update S.R dst (bitSymbol lo :: bitSymbol hi :: bitSymbol enabled :: S.R dst) } := by
    simp [Action.run, update_rt, G]
  exact ⟨v', hu, Exec.cast (Exec.seq hx (hp ▸ Exec.act (body := body) _ (mk v' G))) (by simp) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
