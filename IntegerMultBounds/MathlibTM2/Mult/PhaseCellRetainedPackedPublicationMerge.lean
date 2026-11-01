module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeedPublicationMask

/-! Assemble a packed recovery row from the retained boundary-mask master.
Only disposable copies are consumed; the same geometry serves every replica. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def retainedPackedPublicationMerge (master count width mask x y reversed dst trash tmp : Fin T) : Pr P T Q A U :=
  .seq (seedPublicationMask master count mask reversed tmp (complementSelector A))
    (packedPublicationMerge count width mask x y reversed dst trash tmp)

def retainedPackedPublicationMergeCost (N w : ℕ) := N*(12*w+25)+14

theorem retainedPackedPublicationMerge_native (master count width mask x y reversed dst trash tmp : Fin T) :
    mnNativePushBound 2 (retainedPackedPublicationMerge (P := P) (Q := Q) (A := A) (U := U)
      master count width mask x y reversed dst trash tmp) := by
  simp [retainedPackedPublicationMerge,seedPublicationMask,packedPublicationMerge_native,
    copyR,copyStep,scanP,popPush,keepIn,moveR,moveStep,drainR,whileR,peekR,uclear,
    mnNativePushBound,mnActPush]

theorem retainedPackedPublicationMerge_exec (master count width mask x y reversed dst trash tmp : Fin T)
    (hreg : [master,count,width,mask,x,y,reversed,dst,trash,tmp].Nodup)
    {s t band a N w : ℕ} [NeZero s] (hA : 4 ≤ A) (hst : s < t) (hfit : a+N ≤ s)
    (D Y : ZMod s → GaussianInt) (tailX tailY : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hmaster : S.R master = couplingSourceIntervalMaskSymbols true A s t band a (a+N) a N)
    (hwidth : (S.R width).length = w)
    (hX : S.R x = cstream A w (packedInterval a N D)++tailX)
    (hY : S.R y = cstream A w (packedInterval a N Y)++tailY)
    (hcount : S.R count = []) (hmask : S.R mask = [])
    (hreversed : S.R reversed = []) (htrash : S.R trash = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ retainedPackedPublicationMergeCost N w ∧
      Exec body (retainedPackedPublicationMerge master count width mask x y reversed dst trash tmp)
        (mk v S) n (mk v' {S with R := (Function.update (Function.update (Function.update S.R x tailX)
          y tailY) dst (cstream A w (packedInterval a N (publicationField t band a (a+N) D Y))++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₀,hu₀,he₀⟩ := seedPublicationMask_exec (body := body) master count mask reversed tmp (by regs_nodup)
    (complementSelector A) v S hcount hmask hreversed htmp
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R count (S.R master).reverse)
    mask ((S.R master).map (complementSelector A)))}
  have hlen : (S.R master).length = N := by rw [hmaster]; simp
  obtain ⟨v₁,n,hu₁,hn,he₁⟩ := packedPublicationMerge_exec (body := body)
    (band := band) (a := a) (b := a+N) (origin := a) (N := N) (w := w)
    count width mask x y reversed dst trash tmp (by regs_nodup) hA hst hfit hfit D Y tailX tailY v₀ M
    (by simp [M,‹count ≠ mask›,hlen])
    (by simpa [M,‹count ≠ width›.symm,‹width ≠ mask›] using hwidth)
    (by simp [M,hmaster,boundaryMask_complement hA])
    (by simpa [M,‹count ≠ x›.symm,‹mask ≠ x›.symm] using hX)
    (by simpa [M,‹count ≠ y›.symm,‹mask ≠ y›.symm] using hY)
    (by simpa [M,‹count ≠ reversed›.symm,‹mask ≠ reversed›.symm] using hreversed)
    (by simpa [M,‹count ≠ trash›.symm,‹mask ≠ trash›.symm] using htrash)
    (by simpa [M,‹count ≠ tmp›.symm,‹mask ≠ tmp›.symm] using htmp)
  refine ⟨v₁,(10*N+10)+n,hu₁.trans hu₀,?_,(Exec.seq he₀ he₁).cast ?_ ?_⟩
  · unfold retainedPackedPublicationMergeCost packedPublicationMergeCost at *
    nlinarith only [hn]
  · rw [hlen]
  · apply congrArg (mk v₁)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hc : k = count
    · subst k
      simp [M,Function.update_apply,hcount,‹count ≠ mask›,‹count ≠ x›,‹count ≠ y›,‹count ≠ dst›]
    by_cases hm : k = mask
    · subst k
      simp [M,Function.update_apply,hmask,‹count ≠ mask›.symm,‹mask ≠ x›,‹mask ≠ y›,‹mask ≠ dst›]
    · simp [M,Function.update_apply,hc,hm,‹count ≠ dst›.symm,‹mask ≠ dst›.symm]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
