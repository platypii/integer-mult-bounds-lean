module

public import IntegerMultBounds.MathlibTM2.Routing.SourceSuffixActivity
public import IntegerMultBounds.MathlibTM2.Routing.SelectorRunLoad
public import IntegerMultBounds.MathlibTM2.Routing.GatedSelectedSourceCall

/-! Extract one activity bit from a complete raw source record. Coordinate
fields are archived, loaded scratch is cleared, and the suffix is archived too. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def sourceActivityRecordProgram (src saved index localOffset tmp dst : Fin T) : Pr P T Q A U :=
  .seq (selectorRunLoadProgram src saved index localOffset tmp)
    (.seq (bclear index) (.seq (bclear localOffset) (.act (sourceSuffixActivity src saved dst))))

def sourceActivityRecordBank (R : Fin T → List (Fin (A + 4))) (src saved dst : Fin T)
    (Li Lk i r : ℕ) (lo hi enabled : Bool) (rest : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update R src rest)
    saved ((gatedSelectedSourceRecord Li Lk i r lo hi enabled).reverse ++ R saved)) dst
    (bitSymbol enabled :: R dst)

theorem sourceActivityRecord_exec (body : P → Pr P T Q A U)
    (src saved index localOffset tmp dst : Fin T)
    (hreg : [src, saved, index, localOffset, tmp, dst].Nodup)
    (Li Lk i r : ℕ) (lo hi enabled : Bool) (rest : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hraw : S.R src = binSyms Li i ++ separator :: (binSyms (Li + Lk) r ++ separator ::
      (bitSymbol lo :: bitSymbol hi :: bitSymbol enabled :: rest)))
    (hindex : S.R index = []) (hlocal : S.R localOffset = []) (htmp : S.R tmp = []) :
    ∃ (v' : HS T Q A U), v'.user = v.user ∧
      Exec body (sourceActivityRecordProgram src saved index localOffset tmp dst) (mk v S)
        (6 * Li + 6 * (Li + Lk) + 17)
        (mk v' { S with R := sourceActivityRecordBank S.R src saved dst Li Lk i r lo hi enabled rest }) := by
  have hn := hreg
  regs_ne hn
  let suffix := bitSymbol lo :: bitSymbol hi :: bitSymbol enabled :: rest
  obtain ⟨v₁, hu₁, hx₁⟩ := selectorRunLoad_exec body src saved index localOffset tmp (by regs_nodup)
    Li (Li + Lk) i r suffix v S hraw hindex hlocal htmp
  let G : Stacks T A := { S with R := selectorRunLoaded S.R src saved index localOffset (binSyms Li i) (binSyms (Li + Lk) r) suffix }
  obtain ⟨v₂, hu₂, _, hx₂⟩ := bclear_exec body index v₁ G
  have hiG : G.R index = binSyms Li i := by simp [G, selectorRunLoaded, ‹index ≠ localOffset›]
  let H : Stacks T A := { G with R := Function.update G.R index [] }
  obtain ⟨v₃, hu₃, _, hx₃⟩ := bclear_exec body localOffset v₂ H
  have hlH : H.R localOffset = binSyms (Li + Lk) r := by
    simp [H, G, selectorRunLoaded, ‹index ≠ localOffset›.symm]
  let J : Stacks T A := { H with R := Function.update H.R localOffset [] }
  have hjraw : J.R src = suffix := by
    simp [J, H, G, selectorRunLoaded, ‹src ≠ index›, ‹src ≠ localOffset›, ‹src ≠ saved›]
  let u := { v₃ with sym := some (bitSymbol enabled), flag := enabled }
  have hp := sourceSuffixActivity_run src saved dst ‹src ≠ saved› ‹src ≠ dst›.symm ‹saved ≠ dst›.symm
    lo hi enabled rest v₃ J hjraw
  have hbank : Function.update (Function.update (Function.update J.R src rest) saved
      (bitSymbol enabled :: bitSymbol hi :: bitSymbol lo :: J.R saved)) dst (bitSymbol enabled :: J.R dst) =
      sourceActivityRecordBank S.R src saved dst Li Lk i r lo hi enabled rest := by
    funext j
    by_cases hs : j = src <;> by_cases ha : j = saved <;> by_cases hd : j = dst <;>
      by_cases hiJ : j = index <;> by_cases hlJ : j = localOffset <;>
      simp_all [J, H, G, selectorRunLoaded, sourceActivityRecordBank, gatedSelectedSourceRecord,
        suffix, List.reverse_append, List.append_assoc]
  rw [hbank] at hp
  rw [hiG, length_binSyms] at hx₂
  rw [hlH, length_binSyms] at hx₃
  refine ⟨u, hu₃.trans (hu₂.trans hu₁), ?_⟩
  exact Exec.cast (Exec.seq hx₁ (Exec.seq hx₂ (Exec.seq hx₃
    (hp ▸ Exec.act (body := body) _ (mk v₃ J))))) (by omega) rfl

end IntegerMultBounds.MathlibTM2.Routing
