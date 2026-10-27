module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedGroupWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinishHaloClass

/-! Reuse the existing publication and teardown program with the weight cache outside its workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 148 Q A U}

def cachedFinishHaloClass : Pr P 148 Q A U :=
  embProg cachedGroupLegacyReg Empty.elim (finishNaturalClass (P := Empty))

theorem cachedGroup_finished_frame (S : Stacks 148 A)
    (ambient sourceTail published : List (Fin (A+4))) :
    embOvr cachedGroupLegacyReg
      ({embStk cachedGroupLegacyReg S with R := (finishedClassR (embStk cachedGroupLegacyReg S).R
        ambient sourceTail published)} : Stacks 144 A).get S =
      {S with R := finishedClassR S.R ambient sourceTail published} := by
  refine Stacks.ext rfl rfl ?_ ?_
  · change embExt cachedGroupLegacyReg (S.L ∘ cachedGroupLegacyReg) S.L = S.L
    exact embExt_comp S.L
  · funext i
    by_cases hi : i.val < 144
    · let j : Fin 144 := ⟨i.val,hi⟩
      have heq : cachedGroupLegacyReg j = i := Fin.ext rfl
      have hview := embStk_ovr cachedGroupLegacyReg_injective
        ({embStk cachedGroupLegacyReg S with R := (finishedClassR (embStk cachedGroupLegacyReg S).R
          ambient sourceTail published)} : Stacks 144 A) S
      have h := congrArg (fun T : Stacks 144 A => T.R j) hview
      have hn : finishedClassR (embStk cachedGroupLegacyReg S).R ambient sourceTail published j =
          finishedClassR S.R ambient sourceTail published (cachedGroupLegacyReg j) := by
        simp [finishedClassR,embStk,cachedGroupLegacyReg,Function.update_apply,Fin.ext_iff]
      rw [← heq]
      exact h.trans hn
    · have hoff := (embOvr_off (e := cachedGroupLegacyReg)
        ({embStk cachedGroupLegacyReg S with R := (finishedClassR (embStk cachedGroupLegacyReg S).R
          ambient sourceTail published)} : Stacks 144 A).get S
          (cachedGroupLegacyReg_off i (by omega))).2
      have hne (k : Fin 148) (hk : k.val < 144) : i ≠ k := by
        intro he; subst i; omega
      simpa [finishedClassR,hne 110 (by decide),hne 93 (by decide),hne 132 (by decide),
        hne 140 (by decide),hne 128 (by decide),hne 129 (by decide)] using hoff

theorem cachedFinishHaloClass_exec {s t : ℕ} [NeZero s] (hst : s < t) (band a b L w : ℕ) (hwpos : 1 ≤ w)
    (hgroup : 0 < (haloLengthGroup s t band a b L).length)
    (rhs ambient E ys sourceTail outputTail : List (Fin (A+4)))
    (hE : E.length = s*w) (hys : ys.length = (haloLengthGroup s t band a b L).length*(L*w))
    (hrhs : rhs.length = (haloLengthGroup s t band a b L).length*L*w)
    (v : HS 148 Q A U) (S : Stacks 148 A)
    (hL : (S.R 128).length = L) (hw : (S.R 130).length = w)
    (hB : (S.R 129).length = (haloLengthGroup s t band a b L).length)
    (hr : S.R 110 = rhs++ambient) (hc : S.R 140 = gatherControls A (haloScatterGaps s t band a b L w))
    (hdst : S.R 132 = E++outputTail) (hsrc : S.R 93 = ys++sourceTail)
    (hz : ∀ k ∈ ([(88 : Fin 148),89,90,92,94,131,134,135,136,137] : List (Fin 148)), S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 94*s*w+39 ∧
      Exec body cachedFinishHaloClass (mk v S) n
        (mk v' {S with R := (finishedClassR S.R ambient sourceTail
          (scatterRows (L*w) E (ys++sourceTail) (haloScatterGaps s t band a b L w)++outputTail))}) := by
  obtain ⟨vi,n,hu,hn,he⟩ := finishHaloClass_exec (body := fun p : Empty => nomatch p)
    hst band a b L w hwpos hgroup rhs ambient E ys sourceTail outputTail hE hys hrhs
    (embDn cachedGroupLegacyReg v) (embStk cachedGroupLegacyReg S) hL hw hB hr hc hdst hsrc (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact hz _ (by simp [cachedGroupLegacyReg]))
  obtain ⟨v',hv',hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    cachedGroupLegacyReg_injective (fun p => nomatch p) he v rfl S rfl
  exact ⟨v',n,hu'.trans hu,hn,he'.cast rfl (congrArg (mk v') (cachedGroup_finished_frame S _ _ _))⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
