module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpGather
public import IntegerMultBounds.MathlibTM2.Host.WordTape

/-! # Read a delimited unary advance packet

A packet consists of ticks followed by a blank delimiter. Reading copies its ticks to
the advance counter and saves every packet symbol, so a single final move restores the
whole control stream. The fixed parser does not depend on the packet length.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Host.WordCmd

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

private theorem gatherTicks_cons (n : ℕ) (l : List (Fin (A + 4))) :
    List.replicate n tick ++ tick :: l = tick :: (List.replicate n tick ++ l) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons tick) ih

def gatherReadStep (src dst saved : Fin T) : Act T Q A U :=
  .pop (.rt src) (fun v o => { v with sym := o })
    (.push (.rt saved) (fun v => v.sym.getD blank)
      (.push (.rt dst) (fun _ => tick) (peekRp src (fun x => decide (x.val = 2)))))

def gatherRead (src dst saved : Fin T) : Pr P T Q A U :=
  .seq (.act (peekRp src (fun x => decide (x.val = 2))))
    (.seq (.loop (·.flag) (.act (gatherReadStep src dst saved))) (.act (popPush src saved)))

private theorem gatherRead_loop {src dst saved : Fin T}
    (hreg : [src, dst, saved].Nodup) (n : ℕ) (tail : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = List.replicate n tick ++ blank :: tail)
    (hflag : v.flag = decide (0 < n)) :
    ∃ v', v'.user = v.user ∧
      Exec body (.loop (·.flag) (.act (gatherReadStep src dst saved))) (mk v S) (2 * n + 1)
        (mk v' { S with R := (Function.update (Function.update
          (Function.update S.R src (blank :: tail)) dst (List.replicate n tick ++ S.R dst))
          saved (List.replicate n tick ++ S.R saved)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  have hds := Ne.symm ‹src ≠ dst›
  have hss := Ne.symm ‹src ≠ saved›
  have hsd := Ne.symm ‹dst ≠ saved›
  induction n generalizing v S with
  | zero =>
    refine ⟨v, rfl, ?_⟩
    have he := Exec.loop_false (body := body) (p := .act (gatherReadStep src dst saved))
      (s := mk v S) (by simpa using hflag)
    (convert he using 1; simp only [List.replicate_zero, List.nil_append])
    congr 1
    simp only [List.replicate_zero, List.nil_append] at hsrc
    simp [← hsrc]
  | succ n ih =>
    let S₁ : Stacks T A := { S with R := (Function.update (Function.update
      (Function.update S.R src (List.replicate n tick ++ blank :: tail)) dst (tick :: S.R dst))
      saved (tick :: S.R saved)) }
    let v₁ : HS T Q A U := { v with sym := some tick, flag := decide (0 < n) }
    have hr : (gatherReadStep src dst saved : Act T Q A U).run (mk v S) = mk v₁ S₁ := by
      cases n <;> simp [gatherReadStep, peekRp, Action.run, update_rt, S₁, v₁,
        List.replicate_succ, tick, bitSymbol, blank, Function.update_comm, *]
      congr 1
      ext1
      · rfl
      · rfl
      · rfl
      funext k
      simp only [Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    obtain ⟨v', hu, he⟩ := ih v₁ S₁ (by simp [S₁, *]) rfl
    refine ⟨v', hu, (Exec.loop_true (by simpa using hflag)
      (hr ▸ Exec.act (body := body) (gatherReadStep src dst saved) _) he).cast (by omega) ?_⟩
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    simp only [S₁, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [List.replicate_succ, gatherTicks_cons]

/-- Linear parser cost, with the packet saved including its delimiter. -/
theorem gatherRead_exec {src dst saved : Fin T} (hreg : [src, dst, saved].Nodup)
    (n : ℕ) (tail : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = List.replicate n tick ++ blank :: tail) :
    ∃ v', v'.user = v.user ∧
      Exec body (gatherRead src dst saved) (mk v S) (2 * n + 3)
        (mk v' { S with R := (Function.update (Function.update (Function.update S.R src tail)
          dst (List.replicate n tick ++ S.R dst))
          saved (blank :: (List.replicate n tick ++ S.R saved))) }) := by
  have hreg' := hreg
  regs_ne hreg'
  have hds := Ne.symm ‹src ≠ dst›
  have hss := Ne.symm ‹src ≠ saved›
  have hsd := Ne.symm ‹dst ≠ saved›
  let v₀ : HS T Q A U := { v with flag := decide (0 < n) }
  have hpeek : (peekRp src (fun x => decide (x.val = 2)) : Act T Q A U).run (mk v S) = mk v₀ S := by
    cases n <;> simp [peekRp, Action.run, hsrc, List.replicate_succ, v₀, tick, bitSymbol, blank]
  obtain ⟨v₁, hu₁, he₁⟩ := gatherRead_loop (body := body) hreg n tail v₀ S hsrc rfl
  let S₁ : Stacks T A := { S with R := (Function.update (Function.update
    (Function.update S.R src (blank :: tail)) dst (List.replicate n tick ++ S.R dst))
    saved (List.replicate n tick ++ S.R saved)) }
  refine ⟨{ v₁ with sym := some blank }, hu₁, ?_⟩
  have hend : (popPush src saved : Act T Q A U).run (mk v₁ S₁) =
      mk { v₁ with sym := some blank } { S with R := (Function.update (Function.update
        (Function.update S.R src tail) dst (List.replicate n tick ++ S.R dst))
        saved (blank :: (List.replicate n tick ++ S.R saved))) } := by
    simp [popPush, Action.run, update_rt, S₁, Function.update_comm, *]
  exact (Exec.seq (hpeek ▸ Exec.act (body := body) (peekRp src (fun x => decide (x.val = 2))) _)
    (Exec.seq he₁ (hend ▸ Exec.act (body := body) (popPush src saved) _))).cast (by omega) rfl

def gatherPacket (control savedControl advance window src acc current savedSource buf tmp : Fin T) :
    Pr P T Q A U :=
  .seq (gatherRead control advance savedControl)
    (.seq (gatherNext window advance src acc current savedSource buf tmp) (uclear advance))

/-- One complete sweep step reads its own advance packet and restores its transient counter. -/
theorem gatherPacket_exec {control savedControl advance window src acc current savedSource buf tmp : Fin T}
    (hreg : [control, savedControl, advance, window, src, acc, current, savedSource, buf, tmp].Nodup)
    (d : ℕ) (ctail xs tail ds rest : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hcontrol : S.R control = List.replicate d tick ++ blank :: ctail)
    (hwindow : S.R src = xs ++ tail) (hadvance : S.R src = ds ++ rest)
    (hw : (S.R window).length = xs.length) (hd : ds.length = d)
    (hadvance0 : S.R advance = []) (hcurrent : S.R current = [])
    (hbuf : S.R buf = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (gatherPacket control savedControl advance window src acc current savedSource buf tmp)
        (mk v S) (12 * xs.length + 8 * d + 21)
        (mk v' { S with R := (Function.update (Function.update (Function.update
          (Function.update (Function.update S.R control ctail)
            savedControl (blank :: (List.replicate d tick ++ S.R savedControl))) src rest)
            savedSource (ds.reverse ++ S.R savedSource)) acc (xs.reverse ++ S.R acc)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := gatherRead_exec (body := body)
    (show [control, advance, savedControl].Nodup by regs_nodup) d ctail v S hcontrol
  let S₁ : Stacks T A := { S with R := (Function.update (Function.update
    (Function.update S.R control ctail) advance (List.replicate d tick ++ S.R advance))
    savedControl (blank :: (List.replicate d tick ++ S.R savedControl))) }
  have frame₁ (k : Fin T) (hc : k ≠ control) (ha : k ≠ advance) (hs : k ≠ savedControl) :
      S₁.R k = S.R k := by simp [S₁, hc, ha, hs]
  obtain ⟨v₂, hu₂, he₂⟩ := gatherNext_exec (body := body)
    (show [window, advance, src, acc, current, savedSource, buf, tmp].Nodup by regs_nodup)
    v₁ S₁ xs tail ds rest
    (by rw [frame₁ _ ‹control ≠ src›.symm ‹advance ≠ src›.symm ‹savedControl ≠ src›.symm]; exact hwindow)
    (by rw [frame₁ _ ‹control ≠ src›.symm ‹advance ≠ src›.symm ‹savedControl ≠ src›.symm]; exact hadvance)
    (by rw [frame₁ _ ‹control ≠ window›.symm ‹advance ≠ window›.symm ‹savedControl ≠ window›.symm]; exact hw)
    (by simp [S₁, ‹savedControl ≠ advance›.symm, hadvance0, hd])
    (by rw [frame₁ _ ‹control ≠ current›.symm ‹advance ≠ current›.symm ‹savedControl ≠ current›.symm]; exact hcurrent)
    (by rw [frame₁ _ ‹control ≠ buf›.symm ‹advance ≠ buf›.symm ‹savedControl ≠ buf›.symm]; exact hbuf)
    (by rw [frame₁ _ ‹control ≠ tmp›.symm ‹advance ≠ tmp›.symm ‹savedControl ≠ tmp›.symm]; exact htmp)
  let S₂ : Stacks T A := { S₁ with R := (Function.update (Function.update
    (Function.update S₁.R src rest) savedSource (ds.reverse ++ S₁.R savedSource))
    acc (xs.reverse ++ S₁.R acc)) }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body advance v₂ S₂
  refine ⟨v₃, hu₃.trans (hu₂.trans hu₁), (Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · simp [S₂, S₁, ‹advance ≠ acc›, ‹advance ≠ savedSource›, ‹advance ≠ src›,
      ‹savedControl ≠ advance›.symm, hadvance0, hd]
    omega
  · clear he₁ he₂ he₃ hreg
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    simp only [S₂, S₁, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all only [ne_eq, eq_self, not_true_eq_false, not_false_eq_true]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
