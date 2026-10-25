module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! # Recover the per-branch batch count from the retained doubled header -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Consume two header symbols, save their exact values and emit one tick. -/
def halfPairAct (count saved dst : Fin T) : Act T Q A U :=
  .pop (.rt count) (fun v o => { v with sym := o })
    (.push (.rt saved) (fun v => v.sym.getD blank)
      (.pop (.rt count) (fun v o => { v with sym := o })
        (.push (.rt saved) (fun v => v.sym.getD blank)
          (.push (.rt dst) (fun _ => tick) (peekR count)))))

/-- Structural execution over pairs of actual header symbols. -/
theorem halfCount_loop_exec {count saved dst : Fin T}
    (hreg : [count, saved, dst].Nodup) (m : ℕ) (cs : List (Fin (A + 4))) (hlen : cs.length = 2 * m)
    (v : HS T Q A U) (S : Stacks T A) (hcount : S.R count = cs) (hflag : v.flag = cs.head?.isSome) :
    ∃ v', v'.user = v.user ∧
      Exec body (.loop (·.flag) (.act (halfPairAct count saved dst))) (mk v S) (2 * m + 1)
        (mk v' { S with R := (Function.update (Function.update (Function.update S.R count []) saved
          (cs.reverse ++ S.R saved)) dst (List.replicate m tick ++ S.R dst)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  induction m generalizing cs v S with
  | zero =>
      have hc : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      simp only [hc] at hcount hflag ⊢
      refine ⟨v, rfl, (Exec.loop_false (body := body)
        (p := .act (halfPairAct count saved dst)) (by simpa [hcount] using hflag) (s := mk v S)).cast rfl ?_⟩
      congr 1
      ext1
      · rfl
      · rfl
      · rfl
      funext k
      simp only [Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
  | succ m ih =>
      cases cs with
      | nil => simp at hlen
      | cons x cs =>
          cases cs with
          | nil => simp at hlen; omega
          | cons y cs =>
              have hlen' : cs.length = 2 * m := by simp at hlen; omega
              let S₁ : Stacks T A := { S with R := (Function.update (Function.update
                (Function.update S.R count cs) saved (y :: x :: S.R saved)) dst (tick :: S.R dst)) }
              let v₁ : HS T Q A U := { v with sym := some y, flag := cs.head?.isSome }
              have hrun : (halfPairAct count saved dst : Act T Q A U).run (mk v S) = mk v₁ S₁ := by
                simp [halfPairAct, Action.run, peekR, update_rt, hcount, v₁,
                  ‹count ≠ saved›, ‹count ≠ saved›.symm, ‹count ≠ dst›, ‹count ≠ dst›.symm,
                  ‹saved ≠ dst›.symm]
                congr 1
                ext1
                · rfl
                · rfl
                · rfl
                funext k
                simp only [S₁, Function.update_apply]
                split_ifs <;> subst_vars <;> simp_all
              obtain ⟨v₂, hu₂, he₂⟩ := ih cs hlen' v₁ S₁
                (by simp [S₁, ‹count ≠ saved›, ‹count ≠ dst›]) rfl
              refine ⟨v₂, hu₂, (Exec.loop_true (by simpa using hflag)
                (hrun ▸ Exec.act (body := body) (halfPairAct count saved dst) (mk v S)) he₂).cast (by omega) ?_⟩
              congr 1
              ext1
              · rfl
              · rfl
              · rfl
              clear he₂ hrun hu₂ ih
              funext k
              simp only [S₁, Function.update_apply]
              split_ifs <;> subst_vars <;> simp_all [List.reverse_cons, List.replicate_succ', List.append_assoc]

/-- Restore the doubled header after producing the half count. -/
def halfCount (count saved dst : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR count))
    (.seq (.loop (·.flag) (.act (halfPairAct count saved dst))) (moveR saved count id))

/-- The original header's symbols survive exactly, and the saved stack returns empty. -/
theorem halfCount_exec {count saved dst : Fin T} (hreg : [count, saved, dst].Nodup)
    (m : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hlen : (S.R count).length = 2 * m) (hsaved : S.R saved = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (halfCount count saved dst) (mk v S) (6 * m + 4)
        (mk v' { S with R := Function.update S.R dst (List.replicate m tick ++ S.R dst) }) := by
  have hreg' := hreg
  regs_ne hreg'
  have hp := Exec.act (body := body) (peekR count) (mk v S)
  rw [peekR_run] at hp
  obtain ⟨v₁, hu₁, he₁⟩ := halfCount_loop_exec (body := body) hreg m (S.R count) hlen
    { v with flag := (S.R count).head?.isSome } S rfl rfl
  let S₁ : Stacks T A := { S with R := (Function.update (Function.update (Function.update S.R count []) saved
    ((S.R count).reverse ++ S.R saved)) dst (List.replicate m tick ++ S.R dst)) }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body saved count ‹count ≠ saved›.symm id v₁ S₁
  refine ⟨v₂, hu₂.trans hu₁, (Exec.seq hp (Exec.seq he₁ he₂)).cast ?_ ?_⟩
  · simp [S₁, ‹saved ≠ dst›, hsaved, hlen]
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    simp only [S₁, movedR, Function.update_apply, List.map_id, hsaved, List.append_nil]
    split_ifs <;> subst_vars <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
