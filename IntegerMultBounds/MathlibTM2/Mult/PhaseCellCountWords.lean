module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! Count fixed-width words without receiving their count. The source is
restored after a structural scan; the count gains one tick per word. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def countWordsBody (width src dst saved tmp : Fin T) : Pr P T Q A U :=
  .seq (transfer width src saved tmp) (.act (pushN dst (fun _ => tick) 1 (peekR src)))

def countWords (width src dst saved tmp : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR src)) (.seq (.loop (·.flag) (countWordsBody width src dst saved tmp)) (moveR saved src id))

theorem countWords_exec {width src dst saved tmp : Fin T}
    (hreg : [width, src, dst, saved, tmp].Nodup) (V : ℕ) (hV : 0 < V)
    (words : List (List (Fin (A+4)))) (hlen : ∀ xs ∈ words, xs.length = V)
    (v : HS T Q A U) (S : Stacks T A) (hw : (S.R width).length = V)
    (hsrc : S.R src = words.flatten) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧ Exec body (countWords width src dst saved tmp) (mk v S)
      (words.length*(6*V+6)+4)
      (mk v' { S with R := Function.update S.R dst (List.replicate words.length tick ++ S.R dst) }) := by
  have hr := hreg
  regs_ne hr
  have hloop : ∀ (ws : List (List (Fin (A+4)))), (∀ xs ∈ ws, xs.length = V) →
      ∀ vi Si, (Si.R width).length = V → Si.R src = ws.flatten → Si.R tmp = [] →
      vi.flag = ws.flatten.head?.isSome →
      ∃ vf, vf.user = vi.user ∧
        Exec body (.loop (·.flag) (countWordsBody width src dst saved tmp)) (mk vi Si)
          (ws.length*(4*V+6)+1)
          (mk vf { Si with R := (Function.update (Function.update (Function.update Si.R src [])
            saved (ws.flatten.reverse ++ Si.R saved)) dst (List.replicate ws.length tick ++ Si.R dst)) }) := by
    intro ws
    induction ws with
    | nil =>
      intro _ vi Si _ hs ht hf
      refine ⟨vi, rfl, (Exec.loop_false (body := body) (by simpa using hf)).cast (by simp) ?_⟩
      congr 1
      ext1
      · rfl
      · rfl
      · rfl
      · funext k
        by_cases hk : k = src
        · subst k; simp [hs, ‹src ≠ saved›, ‹src ≠ dst›]
        by_cases hks : k = saved
        · subst k; simp [‹src ≠ saved›.symm, ‹dst ≠ saved›.symm]
        by_cases hkd : k = dst
        · subst k; simp
        simp [Function.update_apply, hk, hks, hkd]
    | cons xs ws ih =>
      intro hlen vi Si hw hs ht hf
      have hx : xs.length = V := hlen xs (by simp)
      have hxs : xs ≠ [] := by intro he; simp [he] at hx; omega
      obtain ⟨v₁, hu₁, he₁⟩ := transfer_exec (body := body)
        (show [width, src, saved, tmp].Nodup by simp_all) vi Si xs ws.flatten (by simpa using hs)
        (by omega) ht
      let S₁ : Stacks T A := { Si with R := (Function.update (Function.update Si.R src ws.flatten)
        saved (xs.reverse ++ Si.R saved)) }
      let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst (tick :: Si.R dst) }
      have ha : Exec body (.act (pushN dst (fun _ => tick) 1 (peekR src))) (mk v₁ S₁) 1
          (mk { v₁ with flag := ws.flatten.head?.isSome } S₂) := by
        have hh := Exec.act (body := body) (pushN dst (fun _ => tick) 1 (peekR src)) (mk v₁ S₁)
        rw [pushN_run] at hh
        simpa [S₂, S₁, Action.run, peekR_run, ‹src ≠ saved›, ‹src ≠ dst›, ‹src ≠ dst›.symm, ‹dst ≠ saved›, ‹dst ≠ saved›.symm] using hh
      obtain ⟨vf, hv, he⟩ := ih (fun ys hy => hlen ys (by simp [hy]))
        { v₁ with flag := ws.flatten.head?.isSome } S₂
        (by simpa [S₂, S₁, ‹width ≠ dst›, ‹width ≠ src›, ‹width ≠ saved›] using hw)
        (by simp [S₂, S₁, ‹src ≠ dst›, ‹src ≠ saved›])
        (by simpa [S₂, S₁, ‹dst ≠ tmp›.symm, ‹src ≠ tmp›.symm, ‹saved ≠ tmp›.symm] using ht) rfl
      refine ⟨vf, hv.trans hu₁, (Exec.loop_true (body := body)
        (by cases xs <;> simp_all) (Exec.seq he₁ ha) he).cast (by simp [hx]; ring) ?_⟩
      congr 1
      ext1
      · rfl
      · rfl
      · rfl
      · funext k
        simp only [S₂, S₁, Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all [List.reverse_append, List.append_assoc, List.replicate_succ']
  have hp := Exec.act (body := body) (peekR src) (mk v S)
  rw [peekR_run] at hp
  obtain ⟨v₁, hu₁, he₁⟩ := hloop words hlen { v with flag := (S.R src).head?.isSome } S hw hsrc htmp (by rw [hsrc])
  let S₁ : Stacks T A := { S with R := (Function.update (Function.update (Function.update S.R src [])
    saved words.flatten.reverse) dst (List.replicate words.length tick ++ S.R dst)) }
  have he₁' : Exec body (.loop (·.flag) (countWordsBody width src dst saved tmp))
      (mk { v with flag := (S.R src).head?.isSome } S) (words.length*(4*V+6)+1) (mk v₁ S₁) := by
    simpa [S₁, hsaved] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body saved src ‹src ≠ saved›.symm id v₁ S₁
  have htotal : words.flatten.length = words.length*V := by
    rw [List.length_flatten]
    have hh : words.map List.length = List.replicate words.length V := List.map_eq_replicate_iff.mpr hlen
    rw [hh, List.sum_replicate, smul_eq_mul]
  refine ⟨v₂, hu₂.trans hu₁, (Exec.seq hp (Exec.seq he₁' he₂)).cast ?_ ?_⟩
  · simp [S₁, ‹dst ≠ saved›.symm, htotal]
    ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases hk : k = src
      · subst k; simp [S₁, movedR, ‹src ≠ saved›, ‹src ≠ dst›, ‹dst ≠ saved›.symm, hsrc]
      by_cases hks : k = saved
      · subst k; simp [S₁, movedR, ‹src ≠ saved›.symm, ‹dst ≠ saved›.symm, hsaved]
      simp [S₁, movedR, Function.update_apply, hk, hks]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
