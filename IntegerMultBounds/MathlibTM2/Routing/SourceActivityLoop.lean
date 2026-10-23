module

public import IntegerMultBounds.MathlibTM2.Routing.SourceActivityRecord
public import IntegerMultBounds.MathlibTM2.Routing.GatedSelectedSourceWords

/-! Scan canonical source records to collect their activity bits in reverse.
The complete raw records are retained in a rewind archive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def sourceActivityLoopBody (src saved index localOffset tmp dst : Fin T) : Pr P T Q A U :=
  .seq (sourceActivityRecordProgram src saved index localOffset tmp dst) (.act (peekR src))

def sourceActivityTraceBank (R : Fin T → List (Fin (A + 4))) (src saved dst : Fin T)
    (Li Lk : ℕ) : List GatedSelectedSourceChoice → Fin T → List (Fin (A + 4))
  | [] => R
  | x :: xs => sourceActivityTraceBank
      (sourceActivityRecordBank R src saved dst Li Lk x.index x.offset x.lo x.hi x.enabled
        (gatedSelectedSourceWords Li Lk xs)) src saved dst Li Lk xs

theorem sourceActivityLoop_exec (body : P → Pr P T Q A U)
    (src saved index localOffset tmp dst : Fin T)
    (hreg : [src, saved, index, localOffset, tmp, dst].Nodup)
    (Li Lk : ℕ) (xs : List GatedSelectedSourceChoice)
    (v : HS T Q A U) (S : Stacks T A)
    (hraw : S.R src = gatedSelectedSourceWords Li Lk xs)
    (hindex : S.R index = []) (hlocal : S.R localOffset = []) (htmp : S.R tmp = [])
    (hflag : v.flag = xs.head?.isSome) :
    ∃ (v' : HS T Q A U), v'.user = v.user ∧
      Exec body (.loop (·.flag) (sourceActivityLoopBody src saved index localOffset tmp dst))
        (mk v S) (xs.length * (6 * Li + 6 * (Li + Lk) + 19) + 1)
        (mk v' { S with R := sourceActivityTraceBank S.R src saved dst Li Lk xs }) := by
  have hn := hreg
  regs_ne hn
  induction xs generalizing v S with
  | nil =>
    refine ⟨v, rfl, ?_⟩
    simp only [List.length_nil, Nat.zero_mul, Nat.zero_add, sourceActivityTraceBank]
    exact Exec.loop_false (by simpa only [List.head?_nil, Option.isSome_none, mk_var] using hflag)
  | cons x xs ih =>
    obtain ⟨v₁, hu₁, hx₁⟩ := sourceActivityRecord_exec body src saved index localOffset tmp dst hreg
      Li Lk x.index x.offset x.lo x.hi x.enabled (gatedSelectedSourceWords Li Lk xs) v S
      (by simpa [gatedSelectedSourceWords, GatedSelectedSourceChoice.word, gatedSelectedSourceRecord,
        List.append_assoc] using hraw) hindex hlocal htmp
    let G : Stacks T A := { S with R := sourceActivityRecordBank S.R src saved dst Li Lk x.index x.offset x.lo x.hi x.enabled (gatedSelectedSourceWords Li Lk xs) }
    have hc : G.R src = gatedSelectedSourceWords Li Lk xs := by
      simp [G, sourceActivityRecordBank, ‹src ≠ dst›, ‹src ≠ saved›]
    have hkeep (j : Fin T) (hs : j ≠ src) (ha : j ≠ saved) (hd : j ≠ dst) : G.R j = S.R j := by
      simp [G, sourceActivityRecordBank, hs, ha, hd]
    let u := { v₁ with flag := xs.head?.isSome }
    have hp : (peekR src : Act T Q A U).run (mk v₁ G) = mk u G := by
      simp only [peekR_run, hc, gatedSelectedSourceWords_head]; rfl
    obtain ⟨v₂, hu₂, hx₂⟩ := ih u G hc
      ((hkeep index ‹src ≠ index›.symm ‹saved ≠ index›.symm ‹index ≠ dst›).trans hindex)
      ((hkeep localOffset ‹src ≠ localOffset›.symm ‹saved ≠ localOffset›.symm ‹localOffset ≠ dst›).trans hlocal)
      ((hkeep tmp ‹src ≠ tmp›.symm ‹saved ≠ tmp›.symm ‹tmp ≠ dst›).trans htmp) rfl
    refine ⟨v₂, hu₂.trans hu₁, ?_⟩
    exact Exec.cast (Exec.loop_true
      (by simpa only [List.head?_cons, Option.isSome_some, mk_var] using hflag)
      (Exec.seq hx₁ (hp ▸ Exec.act (body := body) _ (mk v₁ G))) hx₂)
      (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega) rfl

end IntegerMultBounds.MathlibTM2.Routing
