module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedStandardBoundaryCounters

/-! Export a retained crop count from the existing restored metadata computation.
Move its count word to the caller destination and release the unused skip. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix BoundaryCropMetadata
variable {Q A : ℕ} {P U : Type}

def exportBoundaryCount (last : Bool) (dst : Fin 117) : Pr P 117 Q A U :=
  .seq (preparedStandardBoundaryCounters last) (.seq (moveR 24 dst id) (uclear 26))

theorem exportBoundaryCount_exec (body : P → Pr P 117 Q A U)
    (last : Bool) (dst : Fin 117) (hreg : [dst,26,24].Nodup)
    (D s width w : ℕ) (hw : 0 < width) (hword : 0 < w) (hroom : 3*width < s)
    (hvolumeFit : s*w < 2^D) (value : Fin 117 → ℕ)
    (hvalues : ∀ j, value (boundarySeedGlobals j) = ![s,width,w] j)
    (hfit : ∀ j, value (boundarySeedGlobals j) < 2^D)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hwidth : (S.R 58).length = D) (hzero : S.R 59 = [])
    (hwords : ∀ j, S.R (boundarySeedGlobals j) = binSyms D (value (boundarySeedGlobals j)))
    (hblank : ∀ r, S.R (boundaryCounterRegister r) = [])
    (hmasters : S.R 26 = [] ∧ S.R 24 = []) (hdst : S.R dst = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (64*D+81)+(16*tblC D 0+6*(s*w)+22*D+13)+(20*D+21)+
        (2*(coreStart width (index last s width)*w)+2*(coreLength s width (index last s width)*w)+4) ∧
      Exec body (exportBoundaryCount last dst) (mk v S) n
        (mk v' {S with R := (Function.update S.R dst
          (List.replicate (coreLength s width (index last s width)*w) tick))}) := by
  obtain ⟨h26,h24⟩ := hmasters
  have hr := hreg
  regs_ne hr
  obtain ⟨u,a,hu,ha,he⟩ := preparedStandardBoundaryCounters_exec body last D s width w hw hword hroom
    hvolumeFit value hvalues hfit v S hwidth hzero hwords hblank ⟨h26,h24⟩ depth
  let skip := List.replicate (coreStart width (index last s width)*w) (tick : Fin (A+4))
  let count := List.replicate (coreLength s width (index last s width)*w) (tick : Fin (A+4))
  let M : Stacks 117 A := {S with R := Function.update (Function.update S.R 26 skip) 24 count}
  obtain ⟨u',hu',hm⟩ := moveR_exec body 24 dst ‹dst ≠ 24›.symm id u M
  have hmove : Exec body (moveR 24 dst id) (mk u M) (2*count.length+2)
      (mk u' {M with R := Function.update (Function.update M.R 24 []) dst count}) := by
    simpa [M,count,movedR,hdst,Function.update_of_ne,‹dst ≠ 24›,‹dst ≠ 26›] using hm
  let N : Stacks 117 A := {M with R := Function.update (Function.update M.R 24 []) dst count}
  obtain ⟨v',hv,hc⟩ := uclear_exec (body := body) 26 u' N
  have hclear : Exec body (uclear 26) (mk u' N) (2*skip.length+2)
      (mk v' {S with R := Function.update S.R dst count}) := by
    have hlen : N.R 26 = skip := by simp [N,M,Ne.symm ‹dst ≠ 26›]
    rw [hlen] at hc
    convert hc using 1
    congr 1
    refine Stacks.ext (by rfl) (by rfl) (by rfl) ?_
    funext i
    by_cases hi : i = 26
    · subst i; simp [h26,Ne.symm ‹dst ≠ 26›]
    by_cases hj : i = 24
    · subst i; simp [N,M,h24,Ne.symm ‹dst ≠ 24›]
    · simp [N,M,hi,hj,Function.update_apply]
  refine ⟨v',a+((2*count.length+2)+(2*skip.length+2)),hv.trans (hu'.trans hu),?_,?_⟩
  · simp only [skip,count,List.length_replicate]
    omega
  · exact Exec.seq he (Exec.seq hmove hclear)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
