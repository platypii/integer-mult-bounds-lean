module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaGatherSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalGather

/-! One restoring sweep gathers a common ambient window from distinct RHS
lines. Source movement is linear in the total encoded input, not per replica. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

theorem replicaGather_exec {dst control savedControl advance window src acc current savedSource buf tmp
    initialControl initialSource rowCount wordR : Fin T}
    (hreg : [dst,control,savedControl,advance,window,src,acc,current,savedSource,buf,tmp,
      initialControl,initialSource,rowCount,wordR].Nodup)
    {s : ℕ} (B p L w : ℕ) (C : ℕ → ZMod s → GaussianInt) (hB : 0 < B) (hspan : p+L ≤ s)
    (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = replicaGatherControls A B s p w)
    (hs : S.R src = cstream A w (replicaAmbientWords B C))
    (hrow : (S.R rowCount).length = L) (hw : (S.R wordR).length = w)
    (hclean : ∀ k ∈ [savedControl,advance,window,acc,current,savedSource,buf,tmp,
      initialControl,initialSource], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ B*(14*L*w+25)+12*(B*s*w)+6*L*w+9*L+29 ∧
      Exec body (naturalGather dst control savedControl advance window src acc current savedSource buf tmp
        initialControl initialSource rowCount wordR) (mk v S) n
        (mk v' { S with R := (Function.update S.R dst
          (cstream A w ((List.range B).flatMap (cellSourceRows L (fun _ => (p : ZMod s)) C))++S.R dst)) }) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨q,ps,hps⟩ : ∃ q ps, replicaSymbolOrigins B s p w = q::ps := by
    have hh : 0 < (replicaSymbolOrigins B s p w).length := by simpa [replicaSymbolOrigins] using hB
    cases he : replicaSymbolOrigins B s p w with
    | nil => simp [he] at hh
    | cons q ps => exact ⟨q,ps,rfl⟩
  let E := cstream A w (replicaAmbientWords B C)
  have hElength : E.length = B*s*w := by simp [E]
  have ho := replicaSymbolOrigins_ordered B s p w
  have hf := replicaSymbolOrigins_fit B s p L w hspan
  rw [hps] at ho hf
  have hp : q ≤ E.length := by have hh := hf q (by simp); rw [hElength]; omega
  have hfit : GatherFits (L*w) (E.drop q) (windowAdvances q ps) :=
    windowAdvances_fits (L*w) q ps E ho (by simpa only [hElength] using hf)
  have hvol : q+(windowAdvances q ps).sum ≤ B*s*w := by
    simpa only [hElength] using windowAdvances_volume (L*w) q ps E ho (by simpa only [hElength] using hf)
  have hrows : gatherRows (L*w) (E.drop q) (windowAdvances q ps) =
      cstream A w ((List.range B).flatMap (cellSourceRows L (fun _ => (p : ZMod s)) C)) :=
    replicaGatherRows_eq_rhs (A := A) B p L w C hspan q ps hps
  have hcount : ps.length+1 = B := by
    have hh := congrArg List.length hps
    simpa [replicaSymbolOrigins] using hh.symm
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [rowCount, wordR, window, buf, tmp].Nodup by regs_nodup) v S
    (hclean buf (by simp)) (hclean tmp (by simp))
  let S₁ : Stacks T A := { S with R := Function.update S.R window (List.replicate (L*w) tick) }
  have he₁' : Exec body (unaryProduct rowCount wordR window buf tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁, hrow, hw, hclean window (by simp)] using he₁
  have hoff (k : Fin T) (hk : k ≠ window) : S₁.R k = S.R k := by simp [S₁, hk]
  obtain ⟨v₂, hu₂, he₂⟩ := gatherOffset_exec (body := body)
    (show [dst, control, savedControl, advance, window, src, acc, current, savedSource, buf, tmp,
      initialControl, initialSource].Nodup by regs_nodup) (L*w) q (windowAdvances q ps) E hp hfit v₁ S₁
    (by rw [hoff control ‹control ≠ window›]; simpa [replicaGatherControls, hps] using hc)
    (by rw [hoff src ‹window ≠ src›.symm]; exact hs) (by simp [S₁]) (by
      intro k hk
      have hne : k ≠ window := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      rw [hoff k hne]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact hclean _ (by simp))
  let S₂ : Stacks T A := { S₁ with R := (Function.update S₁.R dst
    (gatherRows (L*w) (E.drop q) (windowAdvances q ps) ++ S₁.R dst)) }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body window v₂ S₂
  have hwindow : (S₂.R window).length = L*w := by simp [S₂, S₁, ‹dst ≠ window›.symm]
  refine ⟨v₃, n₁+((windowAdvances q ps).length*(14*(L*w)+25)+12*(q+(windowAdvances q ps).sum)+23)+(2*(L*w)+2),
    hu₃.trans (hu₂.trans hu₁), ?_, (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hwindow]; omega) ?_⟩
  · rw [hrow, hw] at hn₁
    rw [windowAdvances_length, hcount]
    nlinarith only [hn₁, hvol]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases hkw : k = window
      · subst k; simp [S₂, hclean window (by simp), ‹dst ≠ window›.symm]
      by_cases hkd : k = dst
      · subst k; simp [S₂, S₁, ‹dst ≠ window›, hrows]
      simp [S₂, S₁, hkw, hkd]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
