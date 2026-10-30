module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Borrow the dimensions; allocate padding/core symbol counts, halo row count
and a disposable replica counter. Only the four destination tapes change. -/
def packedCoreArchiveControls (radius core width replicas skip count rows clock trash tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct radius width skip trash tmp)
    (.seq (unaryProduct core width count trash tmp)
      (.seq (umul 2 radius rows tmp) (.seq (ucopy core rows tmp) (ucopy replicas clock tmp))))

def packedCoreArchiveControlsCost (R L w N : ℕ) : ℕ := (R+L)*(4*w+13)+4*N+20

def packedCoreArchiveControlsState {A : ℕ} (S : Stacks T A)
    (skip count rows clock : Fin T) (R L w N : ℕ) : Stacks T A :=
  {S with R := (Function.update (Function.update (Function.update (Function.update S.R
    skip (List.replicate (R*w) tick)) count (List.replicate (L*w) tick))
      rows (List.replicate (L+2*R) tick)) clock (List.replicate N tick))}

theorem packedCoreArchiveControls_exec
    (radius core width replicas skip count rows clock trash tmp : Fin T)
    (hreg : [radius,core,width,replicas,skip,count,rows,clock,trash,tmp].Nodup)
    (R L w N : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hR : (S.R radius).length = R) (hL : (S.R core).length = L)
    (hw : (S.R width).length = w) (hN : (S.R replicas).length = N)
    (hclean : ∀ i ∈ [skip,count,rows,clock,trash,tmp], S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ packedCoreArchiveControlsCost R L w N ∧
      Exec body (packedCoreArchiveControls radius core width replicas skip count rows clock trash tmp)
        (mk v S) n (mk v' (packedCoreArchiveControlsState S skip count rows clock R L w N)) := by
  have hr := hreg
  regs_ne hr
  have h5a : [radius,width,skip,trash,tmp].Nodup := by regs_nodup
  have h5b : [core,width,count,trash,tmp].Nodup := by regs_nodup
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body) h5a v S
    (hclean trash (by simp)) (hclean tmp (by simp))
  let S₁ : Stacks T A := {S with R := Function.update S.R skip (List.replicate (R*w) tick)}
  have he₁' : Exec body (unaryProduct radius width skip trash tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hR,hw,hclean skip (by simp),List.append_nil] using he₁
  have hn₁' : n₁ ≤ R*(4*w+9)+4 := by simpa only [hR,hw] using hn₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := unaryProduct_exec (body := body) h5b v₁ S₁
    (by simpa [S₁,‹skip ≠ trash›.symm] using hclean trash (by simp))
    (by simpa [S₁,‹skip ≠ tmp›.symm] using hclean tmp (by simp))
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R count (List.replicate (L*w) tick)}
  have he₂' : Exec body (unaryProduct core width count trash tmp) (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    simpa [S₂,S₁,‹core ≠ skip›,‹width ≠ skip›,‹skip ≠ count›.symm,hL,hw,hclean count (by simp)] using he₂
  have hn₂' : n₂ ≤ L*(4*w+9)+4 := by simpa [S₁,‹core ≠ skip›,‹width ≠ skip›,hL,hw] using hn₂
  obtain ⟨v₃,hu₃,he₃⟩ := umul_exec (body := body) 2 ‹radius ≠ rows› ‹radius ≠ tmp› ‹rows ≠ tmp› v₂ S₂
    (by simp [S₂,S₁,‹count ≠ tmp›.symm,‹skip ≠ tmp›.symm,hclean tmp (by simp)])
  let S₃ : Stacks T A := {S₂ with R := Function.update S₂.R rows (List.replicate (2*R) tick)}
  have he₃' : Exec body (umul 2 radius rows tmp) (mk v₂ S₂) (4*R+4) (mk v₃ S₃) := by
    simpa [S₃,S₂,S₁,‹radius ≠ count›,‹radius ≠ skip›,‹count ≠ rows›.symm,‹skip ≠ rows›.symm,
      hR,hclean rows (by simp)] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := ucopy_exec (body := body) ‹core ≠ rows› ‹core ≠ tmp› ‹rows ≠ tmp› v₃ S₃
    (by simp [S₃,S₂,S₁,‹rows ≠ tmp›.symm,‹count ≠ tmp›.symm,‹skip ≠ tmp›.symm,hclean tmp (by simp)])
  let S₄ : Stacks T A := {S₃ with R := Function.update S₃.R rows (List.replicate (L+2*R) tick)}
  have he₄' : Exec body (ucopy core rows tmp) (mk v₃ S₃) (4*L+4) (mk v₄ S₄) := by
    have hc : (S₃.R core).length = L := by simp [S₃,S₂,S₁,‹core ≠ rows›,‹core ≠ count›,‹core ≠ skip›,hL]
    have hr : S₃.R rows = List.replicate (2*R) tick := by simp [S₃]
    rw [hc,hr,←List.replicate_add] at he₄
    exact he₄
  obtain ⟨v₅,hu₅,he₅⟩ := ucopy_exec (body := body) ‹replicas ≠ clock› ‹replicas ≠ tmp› ‹clock ≠ tmp› v₄ S₄
    (by simp [S₄,S₃,S₂,S₁,‹rows ≠ tmp›.symm,‹count ≠ tmp›.symm,‹skip ≠ tmp›.symm,hclean tmp (by simp)])
  let S₅ : Stacks T A := {S₄ with R := Function.update S₄.R clock (List.replicate N tick)}
  have he₅' : Exec body (ucopy replicas clock tmp) (mk v₄ S₄) (4*N+4) (mk v₅ S₅) := by
    simpa [S₅,S₄,S₃,S₂,S₁,‹replicas ≠ rows›,‹replicas ≠ count›,‹replicas ≠ skip›,
      ‹rows ≠ clock›.symm,‹count ≠ clock›.symm,‹skip ≠ clock›.symm,hN,hclean clock (by simp)] using he₅
  refine ⟨v₅,n₁+(n₂+((4*R+4)+((4*L+4)+(4*N+4)))),hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,?_⟩
  · dsimp only [packedCoreArchiveControlsCost]
    simp only [Nat.add_mul,Nat.mul_add] at hn₁' hn₂' ⊢
    omega
  · simpa only [S₅,S₄,S₃,S₂,S₁,Function.update_idem,packedCoreArchiveControlsState,packedCoreArchiveControls]
      using Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄' he₅')))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
