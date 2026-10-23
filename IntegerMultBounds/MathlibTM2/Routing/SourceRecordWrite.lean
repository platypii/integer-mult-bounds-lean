module

public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationWrite
public import IntegerMultBounds.MathlibTM2.Routing.GatedSelectedSourceCall

/-! Serialize live decoded source fields and a three-bit suffix into exactly
the canonical record consumed by profile and activity generation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def sourceRecordWriteProgram (index localOffset suffix dst tmp work : Fin T) : Pr P T Q A U :=
  .seq (bcopy suffix dst tmp work) (configurationWrite dst tmp work [index, localOffset])

theorem sourceRecordWrite_exec (body : P → Pr P T Q A U)
    (index localOffset suffix dst tmp work : Fin T)
    (hreg : [index, localOffset, suffix, dst, tmp, work].Nodup)
    (Li Lk i r : ℕ) (lo hi enabled : Bool) (v : HS T Q A U) (S : Stacks T A)
    (hindex : S.R index = binSyms Li i) (hlocal : S.R localOffset = binSyms (Li + Lk) r)
    (hsuffix : S.R suffix = [bitSymbol lo, bitSymbol hi, bitSymbol enabled])
    (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ (v' : HS T Q A U), v'.user = v.user ∧
      Exec body (sourceRecordWriteProgram index localOffset suffix dst tmp work) (mk v S)
        (6 * Li + 6 * (Li + Lk) + 39)
        (mk v' { S with R := Function.update S.R dst (gatedSelectedSourceRecord Li Lk i r lo hi enabled ++ S.R dst) }) := by
  have hn := hreg
  regs_ne hn
  obtain ⟨v₁, hu₁, hx₁⟩ := bcopy_exec body (a := suffix) (c := dst) (t₁ := tmp) (t₂ := work)
    (by regs_nodup) v S htmp hwork
  rw [hsuffix] at hx₁
  let G : Stacks T A := { S with R := Function.update S.R dst ([bitSymbol lo, bitSymbol hi, bitSymbol enabled] ++ S.R dst) }
  have hkeep (j : Fin T) (hj : j ≠ dst) : G.R j = S.R j := by simp [G, hj]
  obtain ⟨v₂, hu₂, hx₂⟩ := configurationWrite_exec body dst tmp work (by regs_nodup) [index, localOffset]
    (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl <;> simp_all)
    v₁ G ((hkeep tmp ‹dst ≠ tmp›.symm).trans htmp) ((hkeep work ‹dst ≠ work›.symm).trans hwork)
  have hc : configurationWriteCost G.R [index, localOffset] = 6 * Li + 6 * (Li + Lk) + 15 := by
    simp [configurationWriteCost, hkeep index ‹index ≠ dst›, hkeep localOffset ‹localOffset ≠ dst›, hindex, hlocal]
    omega
  have hf : Function.update G.R dst (configurationWords ([index, localOffset].map G.R) ++ G.R dst) =
      Function.update S.R dst (gatedSelectedSourceRecord Li Lk i r lo hi enabled ++ S.R dst) := by
    simp only [List.map_cons, List.map_nil, hkeep index ‹index ≠ dst›,
      hkeep localOffset ‹localOffset ≠ dst›, hindex, hlocal]
    simp [G, configurationWords, gatedSelectedSourceRecord, List.append_assoc]
  rw [hc, hf] at hx₂
  exact ⟨v₂, hu₂.trans hu₁, Exec.cast (Exec.seq hx₁ hx₂) (by simp; omega) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
