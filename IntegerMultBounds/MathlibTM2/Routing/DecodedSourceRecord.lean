module

public import IntegerMultBounds.MathlibTM2.Routing.SourceRecordEmit

/-! Any source-field decoder with an exact two-output frame composes with
serialization and field cleanup. Only the emitted record remains afterward. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def decodedSourceRecordProgram (decode : Pr P T Q A U) (lo hi : Bool)
    (index localOffset activity suffix dst tmp work : Fin T) : Pr P T Q A U :=
  .seq decode (.seq (sourceRecordEmitProgram lo hi index localOffset activity suffix dst tmp work)
    (.seq (bclear index) (bclear localOffset)))

theorem decodedSourceRecord_exec (body : P → Pr P T Q A U)
    (decode : Pr P T Q A U) (lo hi enabled : Bool)
    (index localOffset activity suffix dst tmp work : Fin T)
    (hreg : [index, localOffset, activity, suffix, dst, tmp, work].Nodup)
    (Li Lk i r steps : ℕ) (v v₁ : HS T Q A U) (S : Stacks T A)
    (hu₁ : v₁.user = v.user)
    (hdecode : Exec body decode (mk v S) steps
      (mk v₁ { S with R := Function.update (Function.update S.R localOffset (binSyms (Li + Lk) r)) index (binSyms Li i) }))
    (hindex : S.R index = []) (hlocal : S.R localOffset = [])
    (hactivity : S.R activity = [bitSymbol enabled])
    (hsuffix : S.R suffix = []) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ (v' : HS T Q A U), v'.user = v.user ∧
      Exec body (decodedSourceRecordProgram decode lo hi index localOffset activity suffix dst tmp work) (mk v S)
        (steps + (8 * Li + 8 * (Li + Lk) + 64))
        (mk v' { S with R := Function.update S.R dst (gatedSelectedSourceRecord Li Lk i r lo hi enabled ++ S.R dst) }) := by
  have hn := hreg
  regs_ne hn
  let G : Stacks T A := { S with R := Function.update (Function.update S.R localOffset (binSyms (Li + Lk) r)) index (binSyms Li i) }
  have hkeep (j : Fin T) (hi : j ≠ index) (hl : j ≠ localOffset) : G.R j = S.R j := by simp [G, hi, hl]
  obtain ⟨v₂, hu₂, hx₂⟩ := sourceRecordEmit_exec body lo hi enabled index localOffset activity suffix dst tmp work
    hreg Li Lk i r v₁ G (by simp [G]) (by simp [G, ‹index ≠ localOffset›.symm])
    ((hkeep activity ‹index ≠ activity›.symm ‹localOffset ≠ activity›.symm).trans hactivity)
    ((hkeep suffix ‹index ≠ suffix›.symm ‹localOffset ≠ suffix›.symm).trans hsuffix)
    ((hkeep tmp ‹index ≠ tmp›.symm ‹localOffset ≠ tmp›.symm).trans htmp)
    ((hkeep work ‹index ≠ work›.symm ‹localOffset ≠ work›.symm).trans hwork)
  let H : Stacks T A := { G with R := Function.update G.R dst (gatedSelectedSourceRecord Li Lk i r lo hi enabled ++ G.R dst) }
  obtain ⟨v₃, hu₃, _, hx₃⟩ := bclear_exec body index v₂ H
  let J : Stacks T A := { H with R := Function.update H.R index [] }
  obtain ⟨v₄, hu₄, _, hx₄⟩ := bclear_exec body localOffset v₃ J
  have hiH : (H.R index).length = Li := by simp [H, G, ‹index ≠ dst›]
  have hlJ : (J.R localOffset).length = Li + Lk := by
    simp [J, H, G, ‹index ≠ localOffset›.symm, ‹localOffset ≠ dst›]
  have hf : Function.update J.R localOffset [] =
      Function.update S.R dst (gatedSelectedSourceRecord Li Lk i r lo hi enabled ++ S.R dst) := by
    funext j
    by_cases hiJ : j = index <;> by_cases hlJ : j = localOffset <;> by_cases hdJ : j = dst <;>
      simp_all [J, H, G]
  rw [hiH] at hx₃
  rw [hlJ, hf] at hx₄
  exact ⟨v₄, hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    Exec.cast (Exec.seq hdecode (Exec.seq hx₂ (Exec.seq hx₃ hx₄))) (by omega) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
