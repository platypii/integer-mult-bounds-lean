module

public import IntegerMultBounds.MathlibTM2.Routing.SourceRecordWrite
public import IntegerMultBounds.MathlibTM2.Routing.SourceSuffixWrite

/-! Emit a canonical source record from decoded numeric fields and a live
activity bit. The tag suffix is generated and cleared inside the program. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def sourceRecordEmitProgram (lo hi : Bool)
    (index localOffset activity suffix dst tmp work : Fin T) : Pr P T Q A U :=
  .seq (sourceSuffixWriteProgram lo hi activity suffix tmp work)
    (.seq (sourceRecordWriteProgram index localOffset suffix dst tmp work) (bclear suffix))

theorem sourceRecordEmit_exec (body : P → Pr P T Q A U)
    (lo hi enabled : Bool) (index localOffset activity suffix dst tmp work : Fin T)
    (hreg : [index, localOffset, activity, suffix, dst, tmp, work].Nodup)
    (Li Lk i r : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hindex : S.R index = binSyms Li i) (hlocal : S.R localOffset = binSyms (Li + Lk) r)
    (hactivity : S.R activity = [bitSymbol enabled])
    (hsuffix : S.R suffix = []) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ (v' : HS T Q A U), v'.user = v.user ∧
      Exec body (sourceRecordEmitProgram lo hi index localOffset activity suffix dst tmp work) (mk v S)
        (6 * Li + 6 * (Li + Lk) + 60)
        (mk v' { S with R := Function.update S.R dst (gatedSelectedSourceRecord Li Lk i r lo hi enabled ++ S.R dst) }) := by
  have hn := hreg
  regs_ne hn
  obtain ⟨v₁, hu₁, hx₁⟩ := sourceSuffixWrite_exec body lo hi enabled activity suffix tmp work
    (by regs_nodup) v S hactivity htmp hwork
  rw [hsuffix] at hx₁
  let G : Stacks T A := { S with R := Function.update S.R suffix [bitSymbol lo, bitSymbol hi, bitSymbol enabled] }
  have hkeep (j : Fin T) (hj : j ≠ suffix) : G.R j = S.R j := by simp [G, hj]
  obtain ⟨v₂, hu₂, hx₂⟩ := sourceRecordWrite_exec body index localOffset suffix dst tmp work
    (by regs_nodup) Li Lk i r lo hi enabled v₁ G
    ((hkeep index ‹index ≠ suffix›).trans hindex) ((hkeep localOffset ‹localOffset ≠ suffix›).trans hlocal)
    (by simp [G]) ((hkeep tmp ‹suffix ≠ tmp›.symm).trans htmp) ((hkeep work ‹suffix ≠ work›.symm).trans hwork)
  let H : Stacks T A := { G with R := Function.update G.R dst (gatedSelectedSourceRecord Li Lk i r lo hi enabled ++ G.R dst) }
  obtain ⟨v₃, hu₃, _, hx₃⟩ := bclear_exec body suffix v₂ H
  have hs : (H.R suffix).length = 3 := by simp [H, G, ‹suffix ≠ dst›]
  have hf : Function.update H.R suffix [] =
      Function.update S.R dst (gatedSelectedSourceRecord Li Lk i r lo hi enabled ++ S.R dst) := by
    funext j
    by_cases ha : j = suffix <;> by_cases hd : j = dst <;> simp_all [H, G]
  rw [hs, hf] at hx₃
  exact ⟨v₃, hu₃.trans (hu₂.trans hu₁), Exec.cast (Exec.seq hx₁ (Exec.seq hx₂ hx₃)) (by omega) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
