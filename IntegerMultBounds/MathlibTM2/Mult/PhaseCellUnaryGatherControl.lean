module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherLoop
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Fast.Input

/-! Build delimited gather controls directly from retained unary dimensions.
Repeated equal strides use counted copying and restore all control sources. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def unaryGatherControl (count dst saved : Fin T) : Pr P₀ T Q A U :=
  .seq (.act (.push (.rt dst) (fun _ => blank) .done)) (copyR count dst saved id)

theorem unaryGatherControl_exec {count dst saved : Fin T}
    (hreg : [count,dst,saved].Nodup) (d : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hcount : S.R count = List.replicate d tick) (hsaved : S.R saved = []) :
    ∃ v', v'.user = v.user ∧ Exec body (unaryGatherControl count dst saved) (mk v S) (4*d+5)
      (mk v' { S with R := Function.update S.R dst (List.replicate d tick++blank::S.R dst) }) := by
  have hr := hreg
  regs_ne hr
  let S₁ : Stacks T A := { S with R := Function.update S.R dst (blank::S.R dst) }
  have he₁ : Exec body (.act (.push (.rt dst) (fun _ => blank) .done)) (mk v S) 1 (mk v S₁) := by
    simpa [S₁,Action.run,update_rt] using Exec.act (body := body) (.push (.rt dst) (fun _ => blank) .done) (mk v S)
  obtain ⟨v',hu,he⟩ := copyR_exec body count dst saved ‹count ≠ dst› ‹count ≠ saved› ‹dst ≠ saved› id v S₁
    (by simpa [S₁,‹dst ≠ saved›.symm] using hsaved)
  refine ⟨v',hu,(Exec.seq he₁ he).cast ?_ ?_⟩
  · simp [S₁,‹count ≠ dst›,hcount]
    omega
  · simp [S₁,‹count ≠ dst›,hcount]

def repeatUnaryGatherControl (batch batchSaved count dst saved : Fin T) : Pr P₀ T Q A U :=
  scanP batch batchSaved (unaryGatherControl count dst saved)

theorem repeatUnaryGatherControl_exec {batch batchSaved count dst saved : Fin T}
    (hreg : [batch,batchSaved,count,dst,saved].Nodup) (B d : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (hB : (S.R batch).length = B)
    (hcount : S.R count = List.replicate d tick)
    (hbatchSaved : S.R batchSaved = []) (hsaved : S.R saved = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ B*(4*d+10)+4 ∧
      Exec body (repeatUnaryGatherControl batch batchSaved count dst saved) (mk v S) n
        (mk v' { S with R := Function.update S.R dst (gatherControls A (List.replicate B d)++S.R dst) }) := by
  have hr := hreg
  regs_ne hr
  let Ψ : ℕ → Regs T A := fun i => Function.update S.R dst (gatherControls A (List.replicate i d)++S.R dst)
  have hstep : IterSpec body (unaryGatherControl count dst saved) batch batchSaved Ψ (fun _ => 4*d+5) B := by
    intro i hi vi Si hSi
    obtain ⟨vi',hu,he⟩ := unaryGatherControl_exec (body := body)
      (show [count,dst,saved].Nodup by regs_nodup) d vi Si (by
        rw [hSi count ‹batch ≠ count›.symm ‹batchSaved ≠ count›.symm]
        simpa [Ψ,‹count ≠ dst›] using hcount) (by
        rw [hSi saved ‹batch ≠ saved›.symm ‹batchSaved ≠ saved›.symm]
        simpa [Ψ,‹dst ≠ saved›.symm] using hsaved)
    let R' := Function.update Si.R dst (List.replicate d tick++blank::Si.R dst)
    refine ⟨vi',R',4*d+5,hu,le_rfl,he,by simp [R',‹batch ≠ dst›],
      by simp [R',‹batchSaved ≠ dst›],?_⟩
    intro k hkb hks
    by_cases hk : k = dst
    · subst k
      rw [show R' dst = List.replicate d tick++blank::Si.R dst by simp [R'],
        hSi dst ‹batch ≠ dst›.symm ‹batchSaved ≠ dst›.symm]
      simp [Ψ,List.replicate_succ,gatherControls,List.append_assoc]
    rw [show R' k = Si.R k by simp [R',hk],hSi k hkb hks]
    simp [Ψ,hk]
  obtain ⟨v',R',n,hu,hn,he,hb,hs,hrest⟩ := scanP_exec (body := body) ‹batch ≠ batchSaved› hstep 0 v S
    (by simp [hB]) (by intro k _ _; simp [Ψ,gatherControls])
  have hR : R' = Ψ B := by
    funext k
    by_cases hkb : k = batch
    · subst k; simpa [Ψ,‹batch ≠ dst›,hbatchSaved] using hb
    by_cases hks : k = batchSaved
    · subst k; simpa [Ψ,‹batchSaved ≠ dst›,hbatchSaved] using hs
    simpa [hB] using hrest k hkb hks
  rw [hR] at he
  refine ⟨v',n,hu,?_,he⟩
  simp [hB,hbatchSaved] at hn
  nlinarith only [hn]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
